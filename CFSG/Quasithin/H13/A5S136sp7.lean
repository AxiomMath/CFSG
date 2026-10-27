module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFormZero
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13.A5.SpBorel

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

variable {K : Type} [Field K]

theorem isUnit_det_one : IsUnit (1 : Matrix (Fin 2) (Fin 2) K).det := by
  rw [det_one]
  exact isUnit_one

@[expose] def aT (t : K) : Matrix (Fin 2) (Fin 2) K := !![1, t; 0, 1]

theorem aT_unitriangular (t : K) : IsUnitriangular (aT t) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [aT]
  · fin_cases i <;> simp [aT]

theorem aT_mul (t t' : K) : aT t * aT t' = aT (t + t') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aT, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[expose] noncomputable def zHom (C₀ : Matrix (Fin 2) (Fin 2) K) (hC₀ : C₀ᵀ = C₀) :
    Multiplicative K →* StatedSp 2 K where
  toFun c := blockElt isUnit_det_one (C := Multiplicative.toAdd c • C₀) (by
    rw [transpose_smul, hC₀])
  map_one' := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [coe_blockElt, toAdd_one, zero_smul, blockMat_one]
    rfl
  map_mul' c d := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_blockElt, coe_blockElt, coe_blockElt,
      blockMat_mul isUnit_det_one, Matrix.one_mul, inv_one, transpose_one, Matrix.one_mul,
      Matrix.mul_one, toAdd_mul, add_smul, add_comm]

theorem coe_zHom (C₀ : Matrix (Fin 2) (Fin 2) K) (hC₀ : C₀ᵀ = C₀) (c : Multiplicative K) :
    (((zHom C₀ hC₀ c : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      fromBlocks 1 (Multiplicative.toAdd c • C₀) 0 1 := by
  show (((blockElt isUnit_det_one _ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
  rw [coe_blockElt, blockMat]
  simp

theorem zHom_mem_unipotent (C₀ : Matrix (Fin 2) (Fin 2) K) (hC₀ : C₀ᵀ = C₀)
    (c : Multiplicative K) : zHom C₀ hC₀ c ∈ unipotent 2 K :=
  ⟨1, _, isUnitriangular_one, by rw [transpose_smul, hC₀], coe_blockElt _ _⟩

@[expose] noncomputable def xHom : Multiplicative K →* StatedSp 2 K where
  toFun t := blockElt (aT_unitriangular (Multiplicative.toAdd t)).isUnit_det (C := 0)
    transpose_zero
  map_one' := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [coe_blockElt, toAdd_one, show aT (0 : K) = 1 by
      ext i j; fin_cases i <;> fin_cases j <;> simp [aT], blockMat_one]
    rfl
  map_mul' c d := by
    apply SymplecticTorusWeyl.statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_blockElt, coe_blockElt, coe_blockElt,
      blockMat_mul (aT_unitriangular _).isUnit_det, aT_mul, toAdd_mul]
    simp

theorem coe_xHom (t : Multiplicative K) :
    (((xHom t : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = blockMat (aT (Multiplicative.toAdd t)) 0 :=
  coe_blockElt _ _

theorem xHom_mem_unipotent (t : Multiplicative K) : xHom t ∈ unipotent 2 K :=
  ⟨_, 0, aT_unitriangular _, transpose_zero, coe_blockElt _ _⟩

theorem exists_ne_zero_mem [Finite K] {D U : Subgroup (StatedSp 2 K)}
    (hD2 : D.relIndex U = 2) (ψ : Multiplicative K →* StatedSp 2 K) (hψ : ψ.range ≤ U)
    (hK4 : 4 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ ψ (Multiplicative.ofAdd c) ∈ D := by
  have hidx : (D.comap ψ).index ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_right (H := D) hψ (by rw [hD2]; norm_num)
    rw [Subgroup.index_comap]
    omega
  have hK : Nat.card (Multiplicative K) = Nat.card K := rfl
  have hne : D.comap ψ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot, hK] at hidx
    omega
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨Multiplicative.toAdd (x : Multiplicative K), fun h => hx1 ?_, x.2⟩
  exact Subtype.ext (by simpa using h)

theorem mem_isoFlag_one {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ isoFlag 2 K 1 ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 ∧ v (Sum.inl 1) = 0 := by
  rw [mem_isoFlag]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0, h1 1, h2 1 (by decide)⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · fin_cases j
      · exact h0
      · exact h1
    · fin_cases j
      · exact absurd hj (by decide)
      · exact h2

theorem mem_isoFlag_two {v : Fin 2 ⊕ Fin 2 → K} :
    v ∈ isoFlag 2 K 2 ↔ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  rw [mem_isoFlag]
  constructor
  · rintro ⟨h1, -⟩
    exact ⟨h1 0, h1 1⟩
  · rintro ⟨h0, h1⟩
    refine ⟨fun j => ?_, fun j hj => absurd hj (not_le.mpr j.isLt)⟩
    fin_cases j
    · exact h0
    · exact h1

theorem unipotent_mulVec_eq {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ isoFlag 2 K 1) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v := by
  obtain ⟨A, C, ⟨hU, hD⟩, -, hg⟩ := hg
  obtain ⟨h0, h1, h2⟩ := mem_isoFlag_one.mp hv
  have h10 : A 1 0 = 0 := hU (by decide)
  rw [hg, blockMat]
  ext x
  rcases x with i | i <;> fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1, h2, h10, hD 0]

theorem unipotent_mulVec_sub_mem {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ isoFlag 2 K 2) :
    ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v - v ∈
      isoFlag 2 K 1 := by
  obtain ⟨A, C, ⟨hU, hD⟩, -, hg⟩ := hg
  obtain ⟨h0, h1⟩ := mem_isoFlag_two.mp hv
  have h10 : A 1 0 = 0 := hU (by decide)
  rw [mem_isoFlag_one, hg, blockMat]
  simp [fromBlocks_mulVec, h0, h1, h10, hD 1]

theorem zHom_mulVec_inl (C₀ : Matrix (Fin 2) (Fin 2) K) (hC₀ : C₀ᵀ = C₀) (c : K)
    (v : Fin 2 ⊕ Fin 2 → K) (i : Fin 2) :
    ((((zHom C₀ hC₀ (Multiplicative.ofAdd c) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) (Sum.inl i) =
      v (Sum.inl i) + c * (C₀ i 0 * v (Sum.inr 0) + C₀ i 1 * v (Sum.inr 1)) := by
  rw [coe_zHom, fromBlocks_mulVec]
  fin_cases i <;> simp [Matrix.vecHead, Matrix.vecTail] <;> ring

theorem xHom_mulVec_inl_zero (t : K) (v : Fin 2 ⊕ Fin 2 → K) :
    ((((xHom (Multiplicative.ofAdd t) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) (Sum.inl 0) =
      v (Sum.inl 0) + t * v (Sum.inl 1) := by
  rw [coe_xHom, blockMat, fromBlocks_mulVec]
  simp [dotProduct, Fin.sum_univ_two, aT]

theorem normalizer_le_borel [Finite K] {D : Subgroup (StatedSp 2 K)} (hDU : D ≤ unipotent 2 K)
    (hD2 : D.relIndex (unipotent 2 K) = 2) (hK4 : 4 ≤ Nat.card K) :
    Subgroup.normalizer (D : Set (StatedSp 2 K)) ≤ borelSubgroup 2 K := by
  have hz : ∀ (C₀ : Matrix (Fin 2) (Fin 2) K) (hC₀ : C₀ᵀ = C₀), ∃ c : K, c ≠ 0 ∧
      zHom C₀ hC₀ (Multiplicative.ofAdd c) ∈ D := fun C₀ hC₀ =>
    exists_ne_zero_mem hD2 (zHom C₀ hC₀)
      (by rintro _ ⟨c, rfl⟩; exact zHom_mem_unipotent _ _ c) hK4
  obtain ⟨c₀, hc₀, hd₀⟩ := hz !![1, 0; 0, 0] (by
    ext i j; fin_cases i <;> fin_cases j <;> rfl)
  obtain ⟨c₁, hc₁, hd₁⟩ := hz !![0, 0; 0, 1] (by
    ext i j; fin_cases i <;> fin_cases j <;> rfl)
  obtain ⟨c₂, hc₂, hd₂⟩ := hz !![0, 1; 1, 0] (by
    ext i j; fin_cases i <;> fin_cases j <;> rfl)
  obtain ⟨t, ht, hdt⟩ := exists_ne_zero_mem hD2 xHom
    (by rintro _ ⟨t, rfl⟩; exact xHom_mem_unipotent t) hK4
  have hF1 : ∀ v : Fin 2 ⊕ Fin 2 → K, v ∈ isoFlag 2 K 1 ↔ ∀ d ∈ D,
      ((d : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v = v := by
    intro v
    refine ⟨fun hv d hd => unipotent_mulVec_eq (hDU hd) hv, fun h => ?_⟩
    have e0 := congrFun (h _ hd₀) (Sum.inl 0)
    have e1 := congrFun (h _ hd₁) (Sum.inl 1)
    have e2 := congrFun (h _ hdt) (Sum.inl 0)
    rw [zHom_mulVec_inl] at e0 e1
    rw [xHom_mulVec_inl_zero] at e2
    simp [hc₀, hc₁, ht] at e0 e1 e2
    exact mem_isoFlag_one.mpr ⟨e0, e1, e2⟩
  have hF2 : ∀ v : Fin 2 ⊕ Fin 2 → K, v ∈ isoFlag 2 K 2 ↔ ∀ d ∈ D,
      ((d : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v - v ∈
        isoFlag 2 K 1 := by
    intro v
    refine ⟨fun hv d hd => unipotent_mulVec_sub_mem (hDU hd) hv, fun h => ?_⟩
    have e1 := (mem_isoFlag_one.mp (h _ hd₁)).2.2
    have e2 := (mem_isoFlag_one.mp (h _ hd₂)).2.2
    rw [Pi.sub_apply, zHom_mulVec_inl] at e1 e2
    simp [hc₁, hc₂] at e1 e2
    exact mem_isoFlag_two.mpr ⟨e2, e1⟩
  have hmul : ∀ (a b : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K),
      (((a * b : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v =
      ((a : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((b : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
    intro a b v
    rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
  have hconj : ∀ (g d : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K),
      ((d : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        ((((g⁻¹ * d * g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) := by
    intro g d v
    rw [← hmul, ← hmul, show g * (g⁻¹ * d * g) = d * g by group]
  have hmemD : ∀ g ∈ Subgroup.normalizer (D : Set (StatedSp 2 K)), ∀ d ∈ D, g⁻¹ * d * g ∈ D := by
    intro g hg d hd
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) d).mp hd
    rwa [inv_inv] at this
  have h1 : ∀ g ∈ Subgroup.normalizer (D : Set (StatedSp 2 K)), ∀ v ∈ isoFlag 2 K 1,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈
        isoFlag 2 K 1 := by
    intro g hg v hv
    rw [hF1] at hv ⊢
    intro d hd
    rw [hconj, hv _ (hmemD g hg d hd)]
  have h2 : ∀ g ∈ Subgroup.normalizer (D : Set (StatedSp 2 K)), ∀ v ∈ isoFlag 2 K 2,
      ((g : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v ∈
        isoFlag 2 K 2 := by
    intro g hg v hv
    rw [hF2] at hv ⊢
    intro d hd
    rw [hconj, ← mulVec_sub]
    exact h1 g hg _ (hv _ (hmemD g hg d hd))
  intro g hg
  rw [mem_borelSubgroup_iff_isoFlag]
  intro i hi1 hi2
  have hgi := Subgroup.inv_mem _ hg
  interval_cases i
  · exact mem_stabilizer_of_mulVec_mem (h1 g hg) (h1 g⁻¹ hgi)
  · exact mem_stabilizer_of_mulVec_mem (h2 g hg) (h2 g⁻¹ hgi)

end CFSG.Quasithin.H13.A5.SpBorel
