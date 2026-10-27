module

public import CFSG.RankThree.PartOne.KFOUT3.L12Rad
public import CFSG.RankThree.PartOne.KFOUT3.L12Frame

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.LocalCores

variable {f : ℕ} {K : Type} [Field K]

theorem projU_eq_iff {x y : ↥(unitarySU 2 f K 5)} :
    projU K f x = projU K f y ↔ x⁻¹ * y ∈ scalarsU K f := by
  rw [← ker_projU, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

theorem scalarsU_le_piSU (hU : UnitaryFieldData 2 f K) [Finite K] : scalarsU K f ≤ piSU f K := by
  intro w hw
  obtain ⟨d, hd1, hd2, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp
    (scalarsU_le_torus hU hw))
  obtain ⟨c, hc⟩ : (w : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K := Subgroup.mem_subgroupOf.mp hw
  have hdc : diagU d = Matrix.GeneralLinearGroup.scalar (Fin 5) c := hd.trans hc.symm
  have hd01 : d 0 = d 1 := by
    have e0 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 0) hdc
    have e1 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 1 1) hdc
    simp [diagU_val, Matrix.GeneralLinearGroup.scalar] at e0 e1
    exact Units.ext (e0.trans e1.symm)
  exact Subgroup.mem_subgroupOf.mpr (mem_piGL_iff.mpr ⟨d, hd1, hd2, hd01, hd⟩)

theorem diagU_dvecR_eq_blkB (a : Kˣ) :
    ((diagU (dvecR a) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blkB (Matrix.diagonal ![(a : K), (a : K), (((a⁻¹) ^ 2 : Kˣ) : K)]) 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkB, diagU_val, dvecR]

theorem diagU_dvecR_mem_range (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {a : Kˣ}
    (ha : a ^ 5 = 1) :
    (⟨diagU (dvecR a), torusSU_le_unitarySU hU h5 (diagU_dvecR_mem_torus ha)⟩ :
      ↥(unitarySU 2 f K 5)) ∈ (suBlock12 hU).range :=
  mem_range_suBlock12_of_blkB hU (diagU_dvecR_eq_blkB a)

theorem card_piSU_inf_range (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) : Nat.card ↥(piSU f K ⊓ (suBlock12 hU).range) = 5 := by
  have : NeZero 5 := ⟨by norm_num⟩
  have hcard : Nat.card (rootsOfUnity 5 K) = 5 := IsPrimitiveRoot.card_rootsOfUnity hζ
  let ν : rootsOfUnity 5 K → ↥(piSU f K ⊓ (suBlock12 hU).range) := fun a =>
    ⟨⟨diagU (dvecR (a : Kˣ)), torusSU_le_unitarySU hU h5
        (diagU_dvecR_mem_torus ((mem_rootsOfUnity 5 _).mp a.2))⟩,
      Subgroup.mem_subgroupOf.mpr (diagU_dvecR_mem_piGL ((mem_rootsOfUnity 5 _).mp a.2)),
      diagU_dvecR_mem_range hU h5 ((mem_rootsOfUnity 5 _).mp a.2)⟩
  have hν : Function.Bijective ν := by
    constructor
    · intro a b hab
      have e := congrArg (fun x : ↥(piSU f K ⊓ (suBlock12 hU).range) =>
        ((x : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val 0 0) hab
      simp [ν, diagU_val, dvecR] at e
      exact Subtype.ext (Units.ext e)
    · rintro ⟨x, hxpi, hxr⟩
      obtain ⟨d, hd1, hd2, hd01, hd⟩ := mem_piGL_iff.mp (Subgroup.mem_subgroupOf.mp hxpi)
      obtain ⟨A, hA⟩ := hxr
      have hxm : gU x = blkB ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 := by
        rw [← hA]
        rfl
      have e3 : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 3 3 = (d 3 : K) := by
        rw [← hd]
        simp [diagU_val]
      have e4 : ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) 4 4 = (d 4 : K) := by
        rw [← hd]
        simp [diagU_val]
      have h3' : d 3 = 1 := by
        apply Units.ext
        calc (d 3 : K) = gU x 3 3 := e3.symm
          _ = blkB ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 3 3 :=
            congrFun (congrFun hxm 3) 3
          _ = 1 := by simp [blkB]
      have h4' : d 4 = 1 := by
        apply Units.ext
        calc (d 4 : K) = gU x 4 4 := e4.symm
          _ = blkB ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 1 4 4 :=
            congrFun (congrFun hxm 4) 4
          _ = 1 := by simp [blkB]
      have hd2' : d 2 = ((d 0)⁻¹) ^ 2 := by
        have hp := hd2
        rw [Fin.prod_univ_five, ← hd01, h3', h4'] at hp
        simp only [mul_one] at hp
        rw [eq_inv_of_mul_eq_one_right hp]
        group
      refine ⟨⟨d 0, (mem_rootsOfUnity 5 _).mpr (hd1 0)⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Units.ext
      show ((diagU (dvecR (d 0)) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
      rw [← hd]
      congr 2
      funext i
      fin_cases i
      · rfl
      · exact hd01
      · exact hd2'.symm
      · exact h3'.symm
      · exact h4'.symm
  rw [← Nat.card_congr (Equiv.ofBijective ν hν), hcard]

theorem piSU_pow_five {a : ↥(unitarySU 2 f K 5)} (ha : a ∈ piSU f K) : a ^ 5 = 1 := by
  obtain ⟨d, hd1, -, -, hd⟩ := mem_piGL_iff.mp (Subgroup.mem_subgroupOf.mp ha)
  apply Subtype.ext
  show (a : GL (Fin 5) K) ^ 5 = 1
  rw [← hd, diagU_pow, show d ^ 5 = 1 from funext hd1, diagU_one]

theorem bB_mem_piSU (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ} (ht : t ^ 5 = 1) :
    bB hU h5 ht ∈ piSU f K := by
  obtain ⟨d, hd1, hd2, hd⟩ := mem_torusSU_iff.mp (diagU_dvecB_mem_torus (K := K) ht)
  have hdd : d = dvecB t := diagU_injective hd
  refine Subgroup.mem_subgroupOf.mpr (mem_piGL_iff.mpr ⟨d, hd1, hd2, ?_, hd⟩)
  rw [hdd]
  simp [dvecB]

theorem projU_bB_ne_one (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) (h1 : t ≠ 1) : projU K f (bB hU h5 ht) ≠ 1 := by
  intro h
  have hz : bB hU h5 ht ∈ scalarsU K f := by rw [← ker_projU]; exact h
  obtain ⟨c, hc⟩ : ((bB hU h5 ht : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) ∈
      StatedScalars (Fin 5) K := Subgroup.mem_subgroupOf.mp hz
  have e0 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 0 0) hc
  have e3 := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 3 3) hc
  simp [Matrix.GeneralLinearGroup.scalar, bB, diagU_val, dvecB] at e0 e3
  apply h1
  apply Units.ext
  rw [← e0, ← e3]

variable [CharP K 2]

theorem trace_dvecB_ne_zero {t : Kˣ} (ht : t ^ 5 = 1) (h1 : t ≠ 1) :
    Matrix.trace ((diagU (dvecB t) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  intro h0
  have htr : Matrix.trace ((diagU (dvecB t) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      (t : K) + t + t + 1 + (t : K) ^ 2 := by
    simp [Matrix.trace, Fin.sum_univ_five, diagU_val, dvecB]
  rw [htr] at h0
  have h3 : (t : K) ^ 2 + t + 1 = 0 := by linear_combination h0 - (t : K) * h2
  have h4 : (t : K) ^ 3 = 1 := by linear_combination ((t : K) - 1) * h3
  have h5 : t ^ 3 = 1 := Units.ext (by simpa using h4)
  exact pow_three_ne_one_of_pow_five ht h1 h5

variable [Finite K]

omit [Finite K] in
theorem centralizer_proj_eq (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {t : Kˣ}
    (ht : t ^ 5 = 1) (h1 : t ≠ 1) :
    Subgroup.centralizer ({projU K f (bB hU h5 ht)} : Set (StatedProj (unitarySU 2 f K 5))) =
      (Subgroup.centralizer ({bB hU h5 ht} : Set ↥(unitarySU 2 f K 5))).map (projU K f) := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, rfl⟩ := projU_surjective y
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    set b := bB hU h5 ht with hb
    have hconj : projU K f (g * b * g⁻¹) = projU K f b := by
      rw [map_mul, map_mul, map_inv, hy, mul_inv_cancel_right]
    have hz : b⁻¹ * (g * b * g⁻¹) ∈ scalarsU K f := projU_eq_iff.mp hconj.symm
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
    have hsc : ((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = (c : K) • (1 : Matrix (Fin 5) (Fin 5) K) := by
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.smul_one_eq_diagonal]
    have hmat : ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
        ((b : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          (((g : GL (Fin 5) K)⁻¹ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
        ((b : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((c : K) • 1) := by
      rw [← hsc, hc]
      simp
    have htr := Matrix.trace_units_conj (g : GL (Fin 5) K)
      ((b : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)
    rw [hmat, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul] at htr
    have hbtr : Matrix.trace ((b : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) ≠ 0 :=
      trace_dvecB_ne_zero ht h1
    have hc1 : c = 1 := by
      apply Units.ext
      have : ((c : K) - 1) * Matrix.trace ((b : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = 0 := by
        linear_combination htr
      rcases mul_eq_zero.mp this with h | h
      · simpa [sub_eq_zero] using h
      · exact absurd h hbtr
    have hg : g * b * g⁻¹ = b := by
      apply Subtype.ext
      apply Units.ext
      have : ((g * b * g⁻¹ : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) =
          (b : GL (Fin 5) K) * Matrix.GeneralLinearGroup.scalar (Fin 5) c := by
        rw [hc]
        simp
      rw [this, hc1, map_one, mul_one]
    calc g * b = (g * b * g⁻¹) * g := by group
      _ = b * g := by rw [hg]
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]

theorem perfectResidual_centralizer_proj (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {t : Kˣ} (ht : t ^ 5 = 1) (h1 : t ≠ 1) :
    inSubgroup perfectResidual
        (Subgroup.centralizer ({projU K f (bB hU h5 ht)} : Set (StatedProj (unitarySU 2 f K 5)))) =
      (suBlock12 hU).range.map (projU K f) := by
  rw [centralizer_proj_eq hU h5 ht h1, ← map_inSubgroup_perfectResidual,
    perfectResidual_centralizer_bB hU h5 ht h1]

omit [CharP K 2] [Finite K] in
theorem projU_injOn_range (hU : UnitaryFieldData 2 f K) {x y : ↥(unitarySU 2 f K 5)}
    (hx : x ∈ (suBlock12 hU).range) (hy : y ∈ (suBlock12 hU).range)
    (h : projU K f x = projU K f y) : x = y := by
  have hz : x⁻¹ * y ∈ scalarsU K f := projU_eq_iff.mp h
  have hr : x⁻¹ * y ∈ (suBlock12 hU).range :=
    (suBlock12 hU).range.mul_mem ((suBlock12 hU).range.inv_mem hx) hy
  obtain ⟨A, hA⟩ := hr
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hz
  have e := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) 3 3)
    (hc.trans (congrArg (fun z : ↥(unitarySU 2 f K 5) => (z : GL (Fin 5) K)) hA.symm))
  have hc1 : c = 1 := by
    apply Units.ext
    have e3 : ((Matrix.GeneralLinearGroup.scalar (Fin 5) c : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) 3 3 = c := by
      simp [Matrix.GeneralLinearGroup.scalar]
    have e4 : ((suBlock12 hU A : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K).val 3 3 = 1 := by
      rw [coe_suBlock12]
      simp [blkB]
    rw [e3, e4] at e
    simpa using e
  have : x⁻¹ * y = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [← hc, hc1, map_one]
    rfl
  exact inv_mul_eq_one.mp this

omit [CharP K 2] [Finite K] in
noncomputable def kerEquiv (hU : UnitaryFieldData 2 f K) :
    ↥((suBlock12 hU).range) ≃* ↥((suBlock12 hU).range.map (projU K f)) :=
  (MonoidHom.ofInjective (f := (projU K f).comp (suBlock12 hU).range.subtype) (fun x y hxy =>
    Subtype.ext (projU_injOn_range hU x.2 y.2 hxy))).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]))

omit [CharP K 2] in
theorem card_proj_inf (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {ζ : K}
    (hζ : IsPrimitiveRoot ζ 5) :
    Nat.card ↥((piSU f K).map (projU K f) ⊓ (suBlock12 hU).range.map (projU K f)) = 5 := by
  have hbij : Function.Bijective (fun x : ↥(piSU f K ⊓ (suBlock12 hU).range) =>
      (⟨projU K f (x : ↥(unitarySU 2 f K 5)), ⟨x, x.2.1, rfl⟩, ⟨x, x.2.2, rfl⟩⟩ :
        ↥((piSU f K).map (projU K f) ⊓ (suBlock12 hU).range.map (projU K f)))) := by
    constructor
    · intro x y hxy
      have := congrArg (fun z : ↥((piSU f K).map (projU K f) ⊓
        (suBlock12 hU).range.map (projU K f)) => (z : StatedProj (unitarySU 2 f K 5))) hxy
      exact Subtype.ext (projU_injOn_range hU x.2.2 y.2.2 this)
    · rintro ⟨y, ⟨a, ha, rfl⟩, ⟨k, hk, hky⟩⟩
      have hz : a⁻¹ * k ∈ scalarsU K f := projU_eq_iff.mp hky.symm
      have hkpi : k ∈ piSU f K := by
        have : k = a * (a⁻¹ * k) := by group
        rw [this]
        exact Subgroup.mul_mem _ ha (scalarsU_le_piSU hU hz)
      exact ⟨⟨k, hkpi, hk⟩, Subtype.ext hky⟩
  exact (Nat.card_congr (Equiv.ofBijective _ hbij).symm).trans (card_piSU_inf_range hU h5 hζ)

end CFSG.RankThree.PartOne.KFOUT3
