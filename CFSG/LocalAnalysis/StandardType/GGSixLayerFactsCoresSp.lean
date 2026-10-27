module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSp
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresTransport
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix CFSG.Assembly.LowTwoRank

variable {n : ℕ} {F : Type} [Field F]

variable (n F) in
abbrev spJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := fromBlocks 0 1 (-1) 0

theorem neg_one_matrix_eq_one [CharP F 2] {m : Type} [Fintype m] [DecidableEq m] :
    (-1 : Matrix m m F) = 1 := by
  ext i j
  rw [Matrix.neg_apply, CharTwo.neg_eq]

theorem spJ_mul_self [CharP F 2] : spJ n F * spJ n F = 1 := by
  rw [spJ, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg, neg_zero]
  rw [neg_one_matrix_eq_one, fromBlocks_one]

theorem spJ_transpose [CharP F 2] : (spJ n F)ᵀ = spJ n F := by
  rw [spJ, fromBlocks_transpose]
  simp only [transpose_zero, transpose_one, neg_one_matrix_eq_one]

theorem mem_statedSp_iff_spJ {g : GL (Fin n ⊕ Fin n) F} :
    g ∈ StatedSp n F ↔ (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * spJ n F *
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = spJ n F :=
  CFSG.Open.StatedAPI.mem_statedSp_iff

variable (n F) in
@[expose] def spAdj (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  spJ n F * Xᵀ * spJ n F

theorem isInvol_spAdj [CharP F 2] : IsInvol (spAdj n F) where
  map_add x y := by simp only [spAdj, transpose_add, Matrix.mul_add, Matrix.add_mul]
  map_mul x y := by
    simp only [spAdj, transpose_mul]
    calc spJ n F * (yᵀ * xᵀ) * spJ n F
        = spJ n F * yᵀ * (spJ n F * spJ n F) * xᵀ * spJ n F := by
          rw [spJ_mul_self]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  map_one := by simp only [spAdj, transpose_one, Matrix.mul_one, spJ_mul_self]
  invol x := by
    simp only [spAdj, transpose_mul, transpose_transpose, spJ_transpose]
    calc spJ n F * (spJ n F * (x * spJ n F)) * spJ n F
        = (spJ n F * spJ n F) * x * (spJ n F * spJ n F) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [spJ_mul_self, Matrix.one_mul, Matrix.mul_one]

theorem spAdj_smul (c : F) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :
    spAdj n F (c • X) = c • spAdj n F X := by
  simp only [spAdj, transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_unitaryOf_spAdj_iff [CharP F 2] {g : GL (Fin n ⊕ Fin n) F} :
    g ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) ↔ g ∈ StatedSp n F := by
  rw [mem_unitaryOf, mem_statedSp_iff_spJ, spAdj]
  constructor
  · intro h
    calc (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * spJ n F * g
        = spJ n F * (spJ n F * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * spJ n F * g) := by
          simp only [← Matrix.mul_assoc, spJ_mul_self, Matrix.one_mul]
      _ = spJ n F := by rw [h, Matrix.mul_one]
  · intro h
    calc spJ n F * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * spJ n F * g
        = spJ n F * ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ * spJ n F * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, spJ_mul_self]

theorem spAdj_eq_inv [CharP F 2] {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F) :
    spAdj n F (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  have h := mem_unitaryOf.mp ((mem_unitaryOf_spAdj_iff (g := g)).mpr hg)
  calc spAdj n F (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      = spAdj n F g * ((g * g⁻¹ : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
        rw [mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = _ := by rw [Units.val_mul, ← Matrix.mul_assoc, h, Matrix.one_mul]


section Symd

variable [CharP F 2]

theorem spY_add_spAdj :
    spJ n F * fromBlocks 0 1 0 0 + spAdj n F (spJ n F * fromBlocks 0 1 0 0) = 1 := by
  have h1 : spAdj n F (spJ n F * fromBlocks 0 1 0 0) =
      spJ n F * (fromBlocks 0 1 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ := by
    rw [spAdj, transpose_mul, spJ_transpose]
    calc spJ n F * ((fromBlocks 0 1 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
          spJ n F) * spJ n F
        = spJ n F * (fromBlocks 0 1 0 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
          (spJ n F * spJ n F) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [spJ_mul_self, Matrix.mul_one]
  rw [h1, ← Matrix.mul_add, fromBlocks_transpose, fromBlocks_add]
  simp only [transpose_zero, transpose_one, add_zero, zero_add]
  rw [show (fromBlocks 0 1 1 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = spJ n F by
    rw [spJ, neg_one_matrix_eq_one], spJ_mul_self]

theorem spAdj_conj {a : GL (Fin n ⊕ Fin n) F} (ha : a ∈ StatedSp n F)
    (Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :
    spAdj n F ((a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * Y *
      ((a⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) =
      (a : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * spAdj n F Y *
        ((a⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  rw [isInvol_spAdj.map_mul, isInvol_spAdj.map_mul, spAdj_eq_inv ha,
    spAdj_eq_inv (Subgroup.inv_mem _ ha), inv_inv, Matrix.mul_assoc]

theorem exists_symd_spAdj [Finite F] {A : Subgroup (GL (Fin n ⊕ Fin n) F)}
    (hAsp : ∀ g ∈ A, g ∈ StatedSp n F) (hA : (Nat.card A : F) ≠ 0) :
    ∃ Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F,
      (∀ g ∈ A, Y * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * Y) ∧ Y + spAdj n F Y = 1 := by
  classical
  have : Finite (GL (Fin n ⊕ Fin n) F) := inferInstance
  have : Fintype A := Fintype.ofFinite A
  set Y₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := spJ n F * fromBlocks 0 1 0 0
  let conjA : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    fun X => ∑ a : A, ((a : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      X * (((a : GL (Fin n ⊕ Fin n) F)⁻¹ : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  refine ⟨(Nat.card A : F)⁻¹ • conjA Y₀, fun g hg => ?_, ?_⟩
  · have key : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * conjA Y₀ *
        ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = conjA Y₀ := by
      simp only [conjA, Finset.mul_sum, Finset.sum_mul]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg⟩ : A)) _ _ fun a => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, _root_.mul_inv_rev, Units.val_mul,
        Matrix.mul_assoc]
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    calc conjA Y₀ * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        = (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * conjA Y₀ *
          ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
          (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by rw [key]
      _ = _ := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.mul_one]
  · have hadd : conjA Y₀ + spAdj n F (conjA Y₀) =
        ∑ _a : A, (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
      have h1 : spAdj n F (conjA Y₀) = conjA (spAdj n F Y₀) := by
        simp only [conjA, spAdj, transpose_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        have := spAdj_conj (hAsp _ a.2) Y₀
        simp only [spAdj] at this
        rw [this]
      rw [h1]
      simp only [conjA, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Matrix.add_mul, ← Matrix.mul_add, spY_add_spAdj, Matrix.mul_one, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    rw [spAdj_smul, ← smul_add, hadd, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hA,
      one_smul]

end Symd


theorem spAdj_mul_comm [CharP F 2] {A : Subgroup (GL (Fin n ⊕ Fin n) F)}
    (hAsp : ∀ g ∈ A, g ∈ StatedSp n F) (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hX : ∀ g ∈ A, X * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * X) {g : GL (Fin n ⊕ Fin n) F}
    (hg : g ∈ A) : spAdj n F X * (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * spAdj n F X := by
  have hgi : spAdj n F ((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    rw [spAdj_eq_inv (Subgroup.inv_mem _ (hAsp g hg)), inv_inv]
  rw [← hgi, ← isInvol_spAdj.map_mul, ← isInvol_spAdj.map_mul, hX _ (Subgroup.inv_mem _ hg)]

theorem ggSpCentralizerCoreInput_of (hHerm : HermCoreInput) (hAlt : AltCoreInput) :
    GGSpCentralizerCoreInput := by
  intro F _ _ _ n _ p hp hp2 A hA _
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A' : Subgroup (GL (Fin n ⊕ Fin n) F) := A.map (StatedSp n F).subtype with hA'
  have hA'sp : ∀ g ∈ A', g ∈ StatedSp n F := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hcard : (Nat.card A' : F) ≠ 0 := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ (Subgroup.subtype_injective _)).toEquiv.symm]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
    rw [hk, Nat.cast_pow]
    refine pow_ne_zero _ fun h => hp2 ?_
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm
  obtain ⟨β, S, hS⟩ := exists_coreFamily_adjCent hHerm hAlt hcard isInvol_spAdj
    (fun X hX g hg => spAdj_mul_comm hA'sp X hX hg) (exists_symd_spAdj hA'sp hcard)
  have hle : adjCent A' (isInvol_spAdj (n := n) (F := F)) ≤ (StatedSp n F).subtype.range := by
    intro g hg
    exact ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hC : (adjCent A' (isInvol_spAdj (n := n) (F := F))).comap (StatedSp n F).subtype =
      Subgroup.centralizer (A : Set (StatedSp n F)) := by
    ext x
    rw [Subgroup.mem_comap, adjCent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hx1, -⟩ a ha
      exact Subtype.ext (hx1 _ ⟨a, ha, rfl⟩)
    · intro hx
      refine ⟨fun g hg => ?_, mem_unitaryOf_spAdj_iff.mpr x.2⟩
      obtain ⟨a, ha, rfl⟩ := hg
      exact congrArg Subtype.val (hx a ha)
  have h := hS.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) hle
  rw [hC] at h
  exact ⟨β, fun c => (S c).comap (StatedSp n F).subtype, h⟩

end LayerCores

end CFSG.StandardType
