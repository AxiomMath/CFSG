module

public import CFSG.RankThree.PartOne.KFOUT3.L12Levi
public import CFSG.RankThree.PartOne.KFOUT3.L12Plane
public import CFSG.RankThree.PartOne.KF.R9Rad
public import CFSG.RankThree.PartOne.KF.R12Unitary

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix CFSG CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

variable {f : ℕ} {K : Type} [Field K]

theorem mem_range_suBlock12_of_blkB (hU : UnitaryFieldData 2 f K) {g : ↥(unitarySU 2 f K 5)}
    {X : Matrix (Fin 3) (Fin 3) K} (hg : gU g = blkB X 1 1) : g ∈ (suBlock12 hU).range := by
  obtain ⟨hdet, hgram⟩ := (mem_unitarySU_iff hU).mp g.2
  have hg' : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = blkB X 1 1 := hg
  rw [hg'] at hdet hgram
  rw [blkB_map, blkB_transpose, blkB_mul, ← blkB_one] at hgram
  obtain ⟨hX, -, -⟩ := blkB_injective hgram
  rw [det_blkB, mul_one, mul_one] at hdet
  have hXX : X * (X.map hU.bar)ᵀ = 1 := mul_eq_one_comm.mp hX
  let Xu : GL (Fin 3) K := Units.mk X ((X.map hU.bar)ᵀ) hXX hX
  have hXU : Xu ∈ unitarySU 2 f K 3 := (mem_unitarySU_iff hU).mpr ⟨hdet, hX⟩
  refine ⟨⟨Xu, hXU⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [coe_suBlock12]
  exact hg'.symm

section Rad

variable [CharP K 2]

@[expose] def rad5 (f : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup ↥(unitarySU 2 f K 5) :=
  (radH (K := K) (0 : Fin 5) 1 2 (by decide) (by decide) (by decide)).subgroupOf
    (unitarySU 2 f K 5)

theorem mem_rad5_iff {g : ↥(unitarySU 2 f K 5)} :
    g ∈ rad5 f K ↔ ∃ α β γ : K,
      ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 1 + Nrad (0 : Fin 5) 1 2 α β γ :=
  Iff.rfl

theorem isPGroup_rad5 : IsPGroup 2 ↥(rad5 f K) := by
  intro x
  refine ⟨2, ?_⟩
  have h4 := radH_pow_four (K := K) (0 : Fin 5) 1 2 (by decide) (by decide) (by decide)
    (Subgroup.mem_subgroupOf.mp x.2)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have := congrArg (fun y : GL (Fin 5) K => (y : Matrix (Fin 5) (Fin 5) K)) h4
  simpa using this

omit [CharP K 2] in
theorem Nrad_apply_eq_zero {α β γ : K} {i j : Fin 5} (h : 3 ≤ i.val ∨ 3 ≤ j.val) :
    Nrad (0 : Fin 5) 1 2 α β γ i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp [Nrad, vecMulVec_apply, vvec, uvec] at h ⊢

theorem rad5_le_range (hU : UnitaryFieldData 2 f K) : rad5 f K ≤ (suBlock12 hU).range := by
  intro g hg
  obtain ⟨α, β, γ, hgα⟩ := mem_rad5_iff.mp hg
  have hz : ∀ i j : Fin 5, (3 ≤ i.val ∨ 3 ≤ j.val) → i ≠ j → gU g i j = 0 := by
    intro i j h hij
    have : gU g i j = (1 + Nrad (0 : Fin 5) 1 2 α β γ) i j := by rw [← hgα]
    rw [this, Matrix.add_apply, Matrix.one_apply_ne hij, Nrad_apply_eq_zero h, add_zero]
  have h33 : gU g 3 3 = 1 := by
    have : gU g 3 3 = (1 + Nrad (0 : Fin 5) 1 2 α β γ) 3 3 := by rw [← hgα]
    rw [this, Matrix.add_apply, Matrix.one_apply_eq, Nrad_apply_eq_zero (Or.inl (by decide)),
      add_zero]
  have h44 : gU g 4 4 = 1 := by
    have : gU g 4 4 = (1 + Nrad (0 : Fin 5) 1 2 α β γ) 4 4 := by rw [← hgα]
    rw [this, Matrix.add_apply, Matrix.one_apply_eq, Nrad_apply_eq_zero (Or.inl (by decide)),
      add_zero]
  have hblk := eq_blkB_of_zero (gU g) (hz 0 3 (Or.inr (by decide)) (by decide))
    (hz 0 4 (Or.inr (by decide)) (by decide)) (hz 1 3 (Or.inr (by decide)) (by decide))
    (hz 1 4 (Or.inr (by decide)) (by decide)) (hz 2 3 (Or.inr (by decide)) (by decide))
    (hz 2 4 (Or.inr (by decide)) (by decide)) (hz 3 0 (Or.inl (by decide)) (by decide))
    (hz 3 1 (Or.inl (by decide)) (by decide)) (hz 3 2 (Or.inl (by decide)) (by decide))
    (hz 3 4 (Or.inl (by decide)) (by decide)) (hz 4 0 (Or.inl (by decide)) (by decide))
    (hz 4 1 (Or.inl (by decide)) (by decide)) (hz 4 2 (Or.inl (by decide)) (by decide))
    (hz 4 3 (Or.inl (by decide)) (by decide))
  rw [h33, h44] at hblk
  exact mem_range_suBlock12_of_blkB hU hblk

theorem piSU_conj_rad5 {a : ↥(unitarySU 2 f K 5)} (ha : a ∈ piSU f K) {w : ↥(unitarySU 2 f K 5)}
    (hw : w ∈ rad5 f K) : a * w * a⁻¹ ∈ rad5 f K := by
  obtain ⟨d, -, -, hd01, hd⟩ := mem_piGL_iff.mp (Subgroup.mem_subgroupOf.mp ha)
  have h := diagU_conj_mem_radH (K := K) (i₀ := (0 : Fin 5)) (i₁ := 1) (i₂ := 2) (by decide)
    (by decide) (by decide) d hd01 (Subgroup.mem_subgroupOf.mp hw)
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hd]
  exact h

@[expose] def dvecR (t : Kˣ) : Fin 5 → Kˣ := ![t, t, (t⁻¹) ^ 2, 1, 1]

omit [CharP K 2] in
theorem diagU_dvecR_mem_torus {t : Kˣ} (ht : t ^ 5 = 1) :
    (diagU (dvecR t) : GL (Fin 5) K) ∈ torusSU 5 5 K := by
  refine mem_torusSU_iff.mpr ⟨dvecR t, fun i => ?_, ?_, rfl⟩
  · fin_cases i
    · simpa [dvecR] using ht
    · simpa [dvecR] using ht
    · simp [dvecR, inv_pow, pow_right_comm t 2 5, ht]
    · simp [dvecR]
    · simp [dvecR]
  · simp [Fin.prod_univ_five, dvecR]
    group

omit [CharP K 2] in
theorem diagU_dvecR_mem_piGL {t : Kˣ} (ht : t ^ 5 = 1) :
    (diagU (dvecR t) : GL (Fin 5) K) ∈ piGL K := by
  obtain ⟨d, hd1, hd2, hd⟩ := mem_torusSU_iff.mp (diagU_dvecR_mem_torus (K := K) ht)
  refine mem_piGL_iff.mpr ⟨d, hd1, hd2, ?_, hd⟩
  have := diagU_injective (hd.trans rfl : diagU d = diagU (dvecR t))
  rw [this]
  simp [dvecR]

theorem exists_not_commute (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) (h1 : t ≠ 1) :
    ∃ u ∈ rad5 f K, ∃ a ∈ piSU f K,
      projU K f u * projU K f a ≠ projU K f a * projU K f u := by
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  have h02 : (0 : Fin 5) ≠ 2 := by decide
  have h12 : (1 : Fin 5) ≠ 2 := by decide
  obtain ⟨α₀, hα₀⟩ := exists_trace_one hU
  have hbar1 : hU.bar 1 = 1 := map_one _
  have hu0 : mkRad h01 h02 h12 α₀ 1 1 ∈ unitarySU 2 f K 5 :=
    mkRad_mem_unitarySU hU h01 h02 h12 (by rw [hbar1, one_mul]; exact hα₀) (by rw [hbar1])
  let u : ↥(unitarySU 2 f K 5) := ⟨mkRad h01 h02 h12 α₀ 1 1, hu0⟩
  have hu : u ∈ rad5 f K := Subgroup.mem_subgroupOf.mpr (mkRad_mem h01 h02 h12 α₀ 1 1)
  have ha0 : (diagU (dvecR t) : GL (Fin 5) K) ∈ unitarySU 2 f K 5 :=
    torusSU_le_unitarySU hU h5 (diagU_dvecR_mem_torus ht)
  let a : ↥(unitarySU 2 f K 5) := ⟨diagU (dvecR t), ha0⟩
  have ha : a ∈ piSU f K := Subgroup.mem_subgroupOf.mpr (diagU_dvecR_mem_piGL ht)
  refine ⟨u, hu, a, ha, fun hcomm => ?_⟩
  have ht3 : t ^ 3 ≠ 1 := pow_three_ne_one_of_pow_five ht h1
  have hne : dvecR t 0 ≠ dvecR t 2 := by
    intro heq
    apply ht3
    have heq' : t = t⁻¹ ^ 2 := by simpa [dvecR] using heq
    calc t ^ 3 = t ^ 2 * t := by group
      _ = t ^ 2 * (t⁻¹ ^ 2) := by rw [← heq']
      _ = 1 := by group
  have hd01 : dvecR t 0 = dvecR t 1 := by simp [dvecR]
  have hconj : projU K f (a * u * a⁻¹) = projU K f u := by
    rw [map_mul, map_mul, map_inv, ← hcomm, mul_inv_cancel_right]
  have hz : u⁻¹ * (a * u * a⁻¹) ∈ scalarsU K f := by
    rw [← ker_projU, MonoidHom.mem_ker, map_mul, map_inv, hconj, inv_mul_cancel]
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
  have hmat : ((a * u * a⁻¹ : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) =
      (u : GL (Fin 5) K) * Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
    rw [hc]
    simp
  have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) = (c : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]
  have hu33 : ((u : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 3 3 = 1 := by
    show (1 + Nrad (0 : Fin 5) 1 2 α₀ 1 1) 3 3 = 1
    rw [Matrix.add_apply, Matrix.one_apply_eq,
      Nrad_apply_eq_zero (i := 3) (j := 3) (Or.inl (by decide)), add_zero]
  have hA33 : ((a * u * a⁻¹ : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val 3 3 = 1 := by
    show ((diagU (dvecR t) * mkRad h01 h02 h12 α₀ 1 1 * (diagU (dvecR t))⁻¹ : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K) 3 3 = 1
    rw [coe_diagU_conj_mkRad h01 h02 h12 (dvecR t) hd01, Matrix.add_apply, Matrix.one_apply_eq,
      Nrad_apply_eq_zero (i := 3) (j := 3) (Or.inl (by decide)), add_zero]
  have hc1 : c = 1 := by
    have e1 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 3 3) hmat
    simp only [Units.val_mul, hsc, Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul, hA33, hu33,
      mul_one] at e1
    exact Units.ext e1.symm
  rw [hc1, map_one, mul_one] at hmat
  exact diagU_conj_mkRad_ne h01 h02 h12 (dvecR t) hd01 hne α₀ hmat

end Rad

end CFSG.RankThree.PartOne.KFOUT3
