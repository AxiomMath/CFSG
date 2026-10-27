module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitz
public import CFSG.LieType.SeitzGeneration.OuterHeisFixedUnitary
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar
import CFSG.RankThree.PartTwo.KFacts.AutPSUDet

public section

namespace CFSG.RankThree.PartTwo.Sec19

open Matrix CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartOne.KFU

@[expose] def outerHeisExactFix (ℓ f : ℕ) (K : Type) [Field K] (ω α : K) :
    Set (unitarySU ℓ f K 3) :=
  {g | ∃ M ∈ outerHeisLines ω α, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M =
    M * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)}

@[expose] def UnitaryOuterHeisCoreExact : Prop :=
  ∀ (ℓ f : ℕ) (K : Type) [Field K], UnitaryFieldData ℓ f K → 3 ∣ ℓ ^ f + 1 → ℓ ^ f ≠ 2 →
    ∀ ω α : K, IsPrimitiveRoot ω 3 → α ^ (ℓ ^ f + 1) = 1 → (¬ ∃ μ : K, μ ^ 3 = α) →
      Subgroup.closure (outerHeisExactFix ℓ f K ω α) = ⊤

theorem mem_zpowers_of_card_nine {G : Type*} [Group G] [Finite G] (D R : Subgroup G)
    (hD : Nat.card D = 9) (hnR : ¬ D ≤ R) {c : G} (hcD : c ∈ D) (hcR : c ∈ R)
    (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) {x : G} (hxD : x ∈ D) (hxR : x ∈ R) :
    x ∈ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hzI : Subgroup.zpowers c ≤ D ⊓ R := Subgroup.zpowers_le.mpr ⟨hcD, hcR⟩
  have hzcard : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hord]
  have h3 : 3 ∣ Nat.card ((D ⊓ R : Subgroup G)) := hzcard ▸ Subgroup.card_dvd_of_le hzI
  have hdvd : Nat.card ((D ⊓ R : Subgroup G)) ∣ 9 := hD ▸ Subgroup.card_dvd_of_le (inf_le_left : D ⊓ R ≤ D)
  have hdvd' : Nat.card ((D ⊓ R : Subgroup G)) ∣ 3 ^ 2 := hdvd
  have hne9 : Nat.card ((D ⊓ R : Subgroup G)) ≠ 9 := by
    intro h9
    have hIeq : D ⊓ R = D :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : D ⊓ R ≤ D) (le_of_eq (by rw [hD, h9]))
    exact hnR (fun y hy => by
      have hyI : y ∈ (D ⊓ R : Subgroup G) := by rw [hIeq]; exact hy
      exact hyI.2)
  have hcard3 : Nat.card ((D ⊓ R : Subgroup G)) = 3 := by
    obtain ⟨m, hm, hmI⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd'
    interval_cases m
    · rw [hmI] at h3; norm_num at h3
    · rw [hmI]; norm_num
    · exact (hne9 (by rw [hmI]; norm_num)).elim
  have hIeq : Subgroup.zpowers c = D ⊓ R :=
    Subgroup.eq_of_le_of_card_ge hzI (le_of_eq (by rw [hzcard, hcard3]))
  have hxI : x ∈ D ⊓ R := ⟨hxD, hxR⟩
  rw [← hIeq] at hxI
  exact hxI

theorem comm_conj_matrix {K : Type} [Field K] (A Pm Pi N g : Matrix (Fin 3) (Fin 3) K)
    (hPP : Pm * Pi = 1) (hPiP : Pi * Pm = 1) (hAP : A * Pm = Pm * N) (hg : g * N = N * g) :
    A * (Pm * g * Pi) = Pm * g * Pi * A := by
  have hA : A = Pm * N * Pi := by
    calc A = A * (Pm * Pi) := by rw [hPP, Matrix.mul_one]
      _ = (A * Pm) * Pi := by rw [Matrix.mul_assoc]
      _ = Pm * N * Pi := by rw [hAP]
  have h1 : Pm * N * Pi * (Pm * g * Pi) = Pm * (N * g) * Pi := by
    calc Pm * N * Pi * (Pm * g * Pi) = Pm * N * (Pi * Pm) * g * Pi := by
          simp only [Matrix.mul_assoc]
      _ = Pm * (N * g) * Pi := by rw [hPiP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  have h2 : Pm * g * Pi * (Pm * N * Pi) = Pm * (g * N) * Pi := by
    calc Pm * g * Pi * (Pm * N * Pi) = Pm * g * (Pi * Pm) * N * Pi := by
          simp only [Matrix.mul_assoc]
      _ = Pm * (g * N) * Pi := by rw [hPiP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hA, h1, h2, hg]

theorem commute_of_card_nine {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (hD : Nat.card D = 9) {x y : G} (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card D = 3 ^ 2 := by rw [hD]; norm_num
  have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hc).is_comm.comm
    (⟨x, hx⟩ : D) ⟨y, hy⟩
  exact congrArg Subtype.val this

theorem finite_mulAut (G : Type*) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun φ : MulAut G => (φ : G → G))
    (fun _ _ hab => MulEquiv.ext fun x => congrFun hab x)

theorem not_mem_inner_of_card_nine {G : Type*} [Group G] [Finite G] (D : Subgroup (MulAut G))
    (hD : Nat.card D = 9) (hnR : ¬ D ≤ (MulAut.conj : G →* MulAut G).range)
    {s : G} (hs3 : s ^ 3 = 1) (hc1 : MulAut.conj s ≠ 1) (hcD : MulAut.conj s ∈ D)
    {e : MulAut G} (heD : e ∈ D) (hes : e s ≠ s) :
    e ∉ (MulAut.conj : G →* MulAut G).range := by
  haveI := finite_mulAut G
  intro heR
  have hc3 : (MulAut.conj s) ^ 3 = 1 := by rw [← map_pow, hs3, map_one]
  have hcR : MulAut.conj s ∈ (MulAut.conj : G →* MulAut G).range := ⟨s, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (mem_zpowers_of_card_nine D _ hD hnR hcD hcR hc1 hc3 heD heR)
  have hcomm : s ^ k * s = s * s ^ k := (Commute.zpow_left (Commute.refl s) k).eq
  apply hes
  rw [← hk, ← map_zpow, MulAut.conj_apply, hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem mul_ne_one_of_not_mem {G : Type*} [Group G] {R : Subgroup (MulAut G)} {e c : MulAut G}
    (hc : c ∈ R) (he : e ∉ R) : e * c ≠ 1 := by
  intro h1
  apply he
  rw [eq_inv_of_mul_eq_one_left h1]
  exact R.inv_mem hc

theorem suConj_fix_of_mul_eq {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (c : unitaryIsom3 h) (X : unitarySU p f K 3)
    (hX : (c : GL (Fin 3) K) * (X : GL (Fin 3) K) = (X : GL (Fin 3) K) * (c : GL (Fin 3) K)) :
    suConj h c X = X := by
  apply Subtype.ext
  rw [coe_suConj, Subgroup.coe_inv, hX, mul_assoc, mul_inv_cancel, mul_one]

theorem suConj_fix_of_matrix {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (c : unitaryIsom3 h) (X : unitarySU p f K 3)
    (hX : ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    suConj h c X = X :=
  suConj_fix_of_mul_eq c X (Units.ext (by simpa only [Units.val_mul] using hX))

theorem conj_eq_suConj {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (s : unitarySU p f K 3) :
    MulAut.conj s = suConj h ⟨(s : GL (Fin 3) K), unitarySU_le_unitaryIsom3 s.2⟩ := by
  refine MulEquiv.ext fun X => Subtype.ext ?_
  rw [coe_suConj, MulAut.conj_apply]
  rfl

theorem eq_sq_of_cube_roots {K : Type} [Field K] {lam x : K} (hL : lam ^ 3 = 1)
    (hl1 : lam ≠ 1) (hX : x ^ 3 = 1) (hx1 : x ≠ 1) (hxl : x ≠ lam) : x = lam ^ 2 := by
  have hA : lam ^ 2 + lam + 1 = 0 := by
    have h0 : (lam - 1) * (lam ^ 2 + lam + 1) = 0 := by linear_combination hL
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hl1)
  have h0 : (x - 1) * (x - lam) * (x - lam ^ 2) = 0 := by
    linear_combination hX - hL + (x - x ^ 2) * hA + x * hL
  rcases mul_eq_zero.mp h0 with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact absurd (sub_eq_zero.mp h2) hx1
    · exact absurd (sub_eq_zero.mp h2) hxl
  · exact sub_eq_zero.mp h1

theorem scalar_of_mem_center {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (hq : 2 < p ^ f) {z : unitarySU p f K 3} (hz : z ∈ Subgroup.center (unitarySU p f K 3)) :
    ∃ c : Kˣ, h.norm (c : K) = 1 ∧ c ^ 3 = 1 ∧
      (z : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) c := by
  rw [center_unitarySU_three (h := h) hq] at hz
  obtain ⟨c, hc, hc3, hzc⟩ := hz
  exact ⟨c, hc, hc3, hzc⟩

theorem conj_ne_one_of_fix {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {e : MulAut (unitarySU p f K 3)} (he3 : e ^ 3 = 1)
    {s : unitarySU p f K 3} (hs3 : s ^ 3 = 1) (hes : e s ≠ s) : MulAut.conj s ≠ 1 := by
  intro hc
  have hsc : s ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : s * g * s⁻¹ = g := congrArg (fun φ : MulAut (unitarySU p f K 3) => φ g) hc
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  have hec : e s ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hsc x]
  obtain ⟨c, _, hc3, hsC⟩ := scalar_of_mem_center (h := h) hq hsc
  obtain ⟨d, _, hd3, hdC⟩ := scalar_of_mem_center (h := h) hq hec
  have hcK : (c : K) ^ 3 = 1 := by simpa using congrArg Units.val hc3
  have hdK : (d : K) ^ 3 = 1 := by simpa using congrArg Units.val hd3
  have hcne : (c : K) ≠ 1 := by
    intro h1
    apply hes
    have hc' : c = 1 := Units.ext h1
    have hs1 : s = 1 := Subtype.ext (by simp [hsC, hc'])
    rw [hs1, map_one]
  have hdne : (d : K) ≠ 1 := by
    intro h1
    have hd' : d = 1 := Units.ext h1
    have he1 : e s = 1 := Subtype.ext (by simp [hdC, hd'])
    have hs1 : s = 1 := e.injective (he1.trans (map_one e).symm)
    exact hes (by rw [he1, hs1])
  have hxl : (d : K) ≠ (c : K) := by
    intro h1
    apply hes
    have hdc : d = c := Units.ext h1
    exact Subtype.ext (by rw [hdC, hsC, hdc])
  have hd2 : (d : K) = (c : K) ^ 2 := eq_sq_of_cube_roots hcK hcne hdK hdne hxl
  have hd' : d = c ^ 2 := Units.ext (by rw [hd2, Units.val_pow_eq_pow_val])
  have hes2 : e s = s ^ 2 := by
    apply Subtype.ext
    rw [hdC, Subgroup.coe_pow, hsC, ← map_pow, hd']
  have h1 : e (e s) = s := by
    rw [hes2, map_pow, hes2, ← pow_mul]
    rw [show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ, hs3, one_mul]
  have h2 : e (e (e s)) = s := by
    have h := DFunLike.congr_fun he3 s
    rw [pow_three, MulAut.mul_apply, MulAut.mul_apply] at h
    simpa using h
  rw [h1] at h2
  exact hes h2

theorem coe_scalar_fin3 {K : Type} [Field K] (c : Kˣ) :
    ((GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (c : K) • 1 := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem exists_heis_pair {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (hq : 2 < p ^ f) {e : MulAut (unitarySU p f K 3)} {s : unitarySU p f K 3}
    (hes : e s ≠ s) (hcomm : e * MulAut.conj s = MulAut.conj s * e)
    {a : unitaryIsom3 h} (ha : suConj h a = e) :
    ∃ ω : K, IsPrimitiveRoot ω 3 ∧
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ω • (((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm' : ∀ y : unitarySU p f K 3, e (s * y * s⁻¹) = s * e y * s⁻¹ := fun y =>
    congrArg (fun φ : MulAut (unitarySU p f K 3) => φ y) hcomm
  have hcz : ∀ y : unitarySU p f K 3, e s * y * (e s)⁻¹ = s * y * s⁻¹ := by
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    have h1 := hcomm' x
    rw [map_mul, map_mul, map_inv] at h1
    exact h1
  have hzc : ∀ y : unitarySU p f K 3, (s⁻¹ * e s) * y = y * (s⁻¹ * e s) := by
    intro y
    have h1 := hcz y
    calc (s⁻¹ * e s) * y = s⁻¹ * (e s * y * (e s)⁻¹) * e s := by group
      _ = s⁻¹ * (s * y * s⁻¹) * e s := by rw [h1]
      _ = y * (s⁻¹ * e s) := by group
  have hzmem : s⁻¹ * e s ∈ Subgroup.center (unitarySU p f K 3) :=
    Subgroup.mem_center_iff.mpr fun y => (hzc y).symm
  obtain ⟨c, _, hc3, hzC⟩ := scalar_of_mem_center (h := h) hq hzmem
  have hz1 : s⁻¹ * e s ≠ 1 := fun h1 => hes (inv_mul_eq_one.mp h1).symm
  have hc1 : (c : K) ≠ 1 := by
    intro h1
    apply hz1
    have hc' : c = 1 := Units.ext h1
    apply Subtype.ext
    rw [Subgroup.coe_one, hzC, hc', map_one]
  have hl3 : (c : K) ^ 3 = 1 := by simpa using congrArg Units.val hc3
  have hl0 : (c : K) ≠ 0 := Units.ne_zero c
  have hω3 : ((c : K)⁻¹) ^ 3 = 1 := by rw [inv_pow, hl3, inv_one]
  have hω1 : (c : K)⁻¹ ≠ 1 := by rwa [ne_eq, inv_eq_one]
  refine ⟨(c : K)⁻¹, IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime hω3 hω1), ?_⟩
  have hA : ((e s : unitarySU p f K 3) : GL (Fin 3) K) =
      (a : GL (Fin 3) K) * (s : GL (Fin 3) K) * (a : GL (Fin 3) K)⁻¹ := by
    subst ha
    rfl
  have hB : ((e s : unitarySU p f K 3) : GL (Fin 3) K) =
      (s : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [← hzC, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have hAS : (a : GL (Fin 3) K) * (s : GL (Fin 3) K) =
      (s : GL (Fin 3) K) * GeneralLinearGroup.scalar (Fin 3) c * (a : GL (Fin 3) K) := by
    rw [← hB, hA]
    group
  have hAm : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (c : K) •
      (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    have h1 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hAS
    simp only [Units.val_mul, coe_scalar_fin3, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one] at h1
    exact h1
  rw [hAm, smul_smul, inv_mul_cancel₀ hl0, one_smul]

theorem pow_succ_eq_one_of_norm {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {c : K} (hc : h.norm c = 1) : c ^ (p ^ f + 1) = 1 := by
  rw [UnitaryFieldData.norm, h.bar_apply] at hc
  rw [pow_succ, mul_comm]
  exact hc

theorem mem_primeFormUnitary_of_isometry {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) : A ∈ primeFormUnitary h (idGram K 3) := by
  rw [mem_primeFormUnitary, show idGram K 3 = 1 from rfl, Matrix.mul_one]
  exact mem_unitaryIsom3.mp hA

theorem bar_mul_eq_one_of_prim {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) {ω : K} (hω : IsPrimitiveRoot ω 3) : h.bar ω * ω = 1 := by
  obtain ⟨k, hk⟩ := hq3
  rw [h.bar_apply, ← pow_succ, hk, pow_mul, hω.pow_eq_one, one_pow]

theorem exists_heisC_one_su {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) :
    ∃ x : unitarySU ℓ f K 3, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisC 1 := by
  have hU := heisC_one_unitary (K := K) h
  exact ⟨⟨⟨heisC 1, ((heisC 1).map h.bar)ᵀ, mul_eq_one_comm.2 hU, hU⟩,
    (mem_unitarySU_iff h).2 ⟨det_heisC_one, hU⟩⟩, rfl⟩

theorem det_heisC_gen {K : Type} [Field K] (α : K) : (heisC α).det = α := by
  rw [heisC, Matrix.det_fin_three]
  simp

theorem scalar_of_commute_heis {K : Type} [Field K] {ω : K} (hω : IsPrimitiveRoot ω 3)
    {M : Matrix (Fin 3) (Fin 3) K} (hD : M * heisD ω = heisD ω * M)
    (hC : M * heisC (1 : K) = heisC (1 : K) * M) : ∃ α : K, M = α • 1 := by
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h2
    apply hω1
    linear_combination -ω * h2 + hω3
  have hd1 : ω - 1 ≠ 0 := sub_ne_zero.mpr hω1
  have hd2 : ω ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hω2
  have hd3 : ω ^ 2 - ω ≠ 0 := by
    have hfac : ω ^ 2 - ω = ω * (ω - 1) := by ring
    rw [hfac]
    exact mul_ne_zero hω0 hd1
  have hd4 : ω - ω ^ 2 ≠ 0 := fun h0 => hd3 (by linear_combination -h0)
  have hd5 : 1 - ω ^ 2 ≠ 0 := fun h0 => hd2 (by linear_combination -h0)
  have hd6 : 1 - ω ≠ 0 := fun h0 => hd1 (by linear_combination -h0)
  have hDe : ∀ i j : Fin 3, M i j * (![1, ω, ω ^ 2] : Fin 3 → K) j =
      (![1, ω, ω ^ 2] : Fin 3 → K) i * M i j := by
    intro i j
    have := congrFun (congrFun hD i) j
    simpa [heisD, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  have o01 : M 0 1 = 0 := by
    have h0 := hDe 0 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0
    have h1 : M 0 1 * (ω - 1) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_right hd1
  have o02 : M 0 2 = 0 := by
    have h0 := hDe 0 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0
    have h1 : M 0 2 * (ω ^ 2 - 1) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_right hd2
  have o10 : M 1 0 = 0 := by
    have h0 := hDe 1 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0
    have h1 : M 1 0 * (1 - ω) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_right hd6
  have o12 : M 1 2 = 0 := by
    have h0 := hDe 1 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0
    have h1 : M 1 2 * (ω ^ 2 - ω) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_right hd3
  have o20 : M 2 0 = 0 := by
    have h0 := hDe 2 0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0
    have h1 : M 2 0 * (1 - ω ^ 2) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_right hd5
  have o21 : M 2 1 = 0 := by
    have h0 := hDe 2 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at h0
    have h1 : M 2 1 * (ω - ω ^ 2) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp h1).resolve_right hd4
  have hc10 : M 1 1 = M 0 0 := by
    have := congrFun (congrFun hC 1) 0
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination this
  have hc21 : M 2 2 = M 1 1 := by
    have := congrFun (congrFun hC 2) 1
    simp [heisC, Matrix.mul_apply, Fin.sum_univ_three] at this
    linear_combination this
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply, o01, o02, o10, o12, o20, o21, hc10, hc21]

theorem eq_one_of_cube_pow {K : Type} [Field K] {x : K} {q : ℕ} (hq : q % 3 = 2) (hx3 : x ^ 3 = 1)
    (hxq : x ^ q = x) : x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx3
  have h2 : x ^ q = x ^ 2 := by
    obtain ⟨k, rfl⟩ : ∃ k, q = 3 * k + 2 := ⟨q / 3, by omega⟩
    rw [pow_add, pow_mul, hx3, one_pow, one_mul]
  have h3 : x * (x - 1) = 0 := by linear_combination hxq - h2
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h hx0
  · linear_combination h

theorem pow_succ_eq_one_of_cube {K : Type} [Field K] {q : ℕ} (hq3 : 3 ∣ q + 1)
    (hF : ∀ x : K, x ^ (q ^ 2) = x) {μ α : K} (hμ : μ ^ 3 = α) (hα : α ^ (q + 1) = 1) :
    μ ^ (q + 1) = 1 := by
  have hx3 : (μ ^ (q + 1)) ^ 3 = 1 := by
    rw [← pow_mul, show (q + 1) * 3 = 3 * (q + 1) by ring, pow_mul, hμ, hα]
  have hxq : (μ ^ (q + 1)) ^ q = μ ^ (q + 1) := by
    rw [← pow_mul, show (q + 1) * q = q ^ 2 + q by ring, pow_add, hF μ, pow_succ']
  exact eq_one_of_cube_pow (by omega) hx3 hxq

theorem pow_sq_card_eq {p f : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData p f K) (x : K) :
    x ^ ((p ^ f) ^ 2) = x := by
  haveI : Finite K := hU.finite
  haveI := Fintype.ofFinite K
  have hc : Fintype.card K = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hU.card, ← pow_mul, mul_comm]
  rw [← hc]
  exact FiniteField.pow_card x

theorem comm_cube_matrix {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {a : unitaryIsom3 h} (ha3 : suConj h a ^ 3 = 1) (X : unitarySU p f K 3) :
    (((a : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((a : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : suConj h (a ^ 3) = 1 := by rw [map_pow, ha3]
  have h2 : suConj h (a ^ 3) X = X := by rw [h1]; rfl
  have h3 := congrArg Subtype.val h2
  rw [coe_suConj] at h3
  simp only [Subgroup.coe_inv, Subgroup.coe_pow] at h3
  rw [mul_inv_eq_iff_eq_mul] at h3
  have h5 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h3
  simpa only [Units.val_mul] using h5

theorem exists_heisD_su {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hq3 : 3 ∣ ℓ ^ f + 1) {ω : K} (hω : IsPrimitiveRoot ω 3) :
    ∃ x : unitarySU ℓ f K 3, ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = heisD ω := by
  have hU := heisD_unitary h (bar_mul_eq_one_of_prim h hq3 hω)
  have hdet : (heisD ω).det = 1 := by rw [det_heisD, hω.pow_eq_one]
  exact ⟨⟨⟨heisD ω, ((heisD ω).map h.bar)ᵀ, mul_eq_one_comm.2 hU, hU⟩,
    (mem_unitarySU_iff h).2 ⟨hdet, hU⟩⟩, rfl⟩

theorem det_eq_of_mul_eq {K : Type} [Field K] {x P : Matrix (Fin 3) (Fin 3) K} {α : K}
    (hP : IsUnit P.det) (hxP : x * P = P * heisC α) : x.det = α := by
  have h1 := congrArg Matrix.det hxP
  rw [Matrix.det_mul, Matrix.det_mul, det_heisC_gen] at h1
  have h2 : (x.det - α) * P.det = 0 := by linear_combination h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hP.ne_zero)

theorem cube_scalar {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}
    (hq3 : 3 ∣ ℓ ^ f + 1) {ω : K} (hω : IsPrimitiveRoot ω 3)
    {a : unitaryIsom3 h} (ha3 : suConj h a ^ 3 = 1) :
    ∃ α : K, (((a : GL (Fin 3) K) ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = α • 1 := by
  obtain ⟨D, hD⟩ := exists_heisD_su h hq3 hω
  obtain ⟨C, hC⟩ := exists_heisC_one_su h
  have hD' := comm_cube_matrix ha3 D
  have hC' := comm_cube_matrix ha3 C
  rw [hD] at hD'
  rw [hC] at hC'
  exact scalar_of_commute_heis hω hD' hC'

theorem suConj_eq_one_of_scalar {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (u : unitaryIsom3 h) {c : K} (hu : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    suConj h u = 1 := by
  apply MulEquiv.ext
  intro X
  rw [MulAut.one_apply]
  apply suConj_fix_of_matrix
  rw [hu]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem suConj_mul_of_scalar {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (u a : unitaryIsom3 h) {c : K}
    (hu : ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) :
    suConj h (u * a) = suConj h a := by
  rw [map_mul, suConj_eq_one_of_scalar u hu, one_mul]

theorem suConj_mem_range_of_det_one {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (x : unitaryIsom3 h) (hdet : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) :
    suConj h x ∈ (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range := by
  have hx : (x : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
    (mem_unitarySU_iff h).2 ⟨hdet, mem_unitaryIsom3.mp x.2⟩
  rw [MonoidHom.mem_range]
  exact ⟨⟨(x : GL (Fin 3) K), hx⟩, conj_eq_suConj (h := h) ⟨(x : GL (Fin 3) K), hx⟩⟩

theorem comm_smul_of_comm {K : Type} [Field K] {g M : Matrix (Fin 3) (Fin 3) K} (c : K)
    (hgM : g * M = M * g) : g * (c • M) = (c • M) * g := by
  rw [Matrix.mul_smul, Matrix.smul_mul, hgM]

theorem suConj_mem_range_of_cube_det {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    (a : unitaryIsom3 h) {μ : K} (hμ : μ ^ (p ^ f + 1) = 1)
    (hdet : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = μ ^ 3) :
    suConj h a ∈ (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero _)] at hμ
    exact zero_ne_one hμ
  have hnorm : h.norm ((Units.mk0 μ⁻¹ (inv_ne_zero hμ0) : Kˣ) : K) = 1 := by
    rw [Units.val_mk0, UnitaryFieldData.norm, h.bar_apply]
    have hpow : μ⁻¹ * μ⁻¹ ^ (p ^ f) = (μ ^ (p ^ f + 1))⁻¹ := by
      rw [pow_succ, mul_inv, ← inv_pow]
      ring
    rw [hpow, hμ, inv_one]
  obtain ⟨u, hu⟩ : ∃ u : unitaryIsom3 h,
      ((u : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = μ⁻¹ • 1 :=
    ⟨⟨GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ⁻¹ (inv_ne_zero hμ0)),
      scalar_mem_unitaryIsom3_of_norm hnorm⟩, coe_scalar_fin3 _⟩
  have hsx : suConj h (u * a) = suConj h a := suConj_mul_of_scalar u a hu
  have hdetx : (((u * a : unitaryIsom3 h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [Subgroup.coe_mul, Units.val_mul, hu, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul,
      hdet, Fintype.card_fin, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hμ0)]
  have hmem := suConj_mem_range_of_det_one (u * a) hdetx
  rw [hsx] at hmem
  exact hmem

theorem diagonal_xi_eq_smul_heisD {K : Type} [Field K] (ξ ω : K) :
    (diagonal ![ξ, ξ * ω, ξ * ω ^ 2] : Matrix (Fin 3) (Fin 3) K) = ξ • heisD ω := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisD, Matrix.diagonal_apply]

theorem fixer_normal_forms {K : Type} [Field K] {A S P C D : Matrix (Fin 3) (Fin 3) K} {ξ : K}
    (hAP : A * P = P * C) (hSP : S * P = P * (ξ • D)) :
    A * S * P = P * (ξ • (C * D)) ∧ A * (S * S) * P = P * ((ξ * ξ) • (C * (D * D))) := by
  constructor
  · calc A * S * P = A * (S * P) := by rw [Matrix.mul_assoc]
      _ = A * (P * (ξ • D)) := by rw [hSP]
      _ = (A * P) * (ξ • D) := by rw [Matrix.mul_assoc]
      _ = (P * C) * (ξ • D) := by rw [hAP]
      _ = P * (ξ • (C * D)) := by rw [Matrix.mul_assoc, Matrix.mul_smul]
  · calc A * (S * S) * P = A * (S * (S * P)) := by simp only [Matrix.mul_assoc]
      _ = A * (S * (P * (ξ • D))) := by rw [hSP]
      _ = A * ((S * P) * (ξ • D)) := by simp only [Matrix.mul_assoc]
      _ = A * ((P * (ξ • D)) * (ξ • D)) := by rw [hSP]
      _ = (A * P) * ((ξ • D) * (ξ • D)) := by simp only [Matrix.mul_assoc]
      _ = (P * C) * ((ξ • D) * (ξ • D)) := by rw [hAP]
      _ = P * (C * ((ξ • D) * (ξ • D))) := by rw [Matrix.mul_assoc]
      _ = P * ((ξ * ξ) • (C * (D * D))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

theorem comm_conjSU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (P : primeFormUnitary h (idGram K 3)) {M N : Matrix (Fin 3) (Fin 3) K}
    (hMN : M * ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N)
    {g : unitarySU ℓ f K 3}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N =
      N * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    M * (((conjSU h P g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (((conjSU h P g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M := by
  have hPPi : ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((P : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : (((P : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcoe : (((conjSU h P g : unitarySU ℓ f K 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((P : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [coe_conjSU, Units.val_mul, Units.val_mul]
  rw [hcoe]
  exact comm_conj_matrix M _ _ N _ hPPi hPiP hMN hg

theorem conjSU_mem_fixSet {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}
    {D : Subgroup (MulAut (unitarySU p f K 3))} {c : unitaryIsom3 h}
    (hcD : suConj h c ∈ D) (hc1 : suConj h c ≠ 1)
    (P : primeFormUnitary h (idGram K 3)) {N : Matrix (Fin 3) (Fin 3) K}
    (hcP : ((c : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N)
    {g : unitarySU p f K 3}
    (hg : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * N =
      N * ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    conjSU h P g ∈ CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D := by
  show ∃ e ∈ D, e ≠ 1 ∧ e (conjSU h P g) = conjSU h P g
  exact ⟨suConj h c, hcD, hc1, suConj_fix_of_matrix c (conjSU h P g) (comm_conjSU h P hcP hg)⟩

theorem seitz199OuterUnitaryDiag_of_exact (h : UnitaryOuterHeisCoreExact) :
    Seitz199OuterUnitaryDiag := by
  unfold Seitz199OuterUnitaryDiag
  intro p f K _ hU hmod hq D hD3 hD9 hnR hsx hDsu
  obtain ⟨e, heD, s, hs3, hcsD, hes⟩ := hsx
  haveI : Finite K := hU.finite
  haveI : Finite (unitarySU p f K 3) :=
    Finite.of_injective
      (fun g : unitarySU p f K 3 => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      (fun x y hxy => Subtype.ext (Units.ext hxy))
  haveI : Finite (MulAut (unitarySU p f K 3)) := finite_mulAut (unitarySU p f K 3)
  have hq3 : 3 ∣ p ^ f + 1 := by omega
  have hqne : p ^ f ≠ 2 := by omega
  have he3 : e ^ 3 = 1 := hD3 e heD
  have hc1 : MulAut.conj s ≠ 1 := conj_ne_one_of_fix hU hq he3 hs3 hes
  have hnin : e ∉ (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range :=
    not_mem_inner_of_card_nine D hD9 hnR hs3 hc1 hcsD heD hes
  have hcomm : e * MulAut.conj s = MulAut.conj s * e := commute_of_card_nine D hD9 heD hcsD
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hDsu heD)
  obtain ⟨ω, hω, hsa⟩ := exists_heis_pair hU hq hes hcomm ha
  have ha3 : suConj hU a ^ 3 = 1 := by rw [ha]; exact he3
  obtain ⟨α, hα⟩ := cube_scalar hq3 hω ha3
  have hamem : (a : GL (Fin 3) K) ∈ primeFormUnitary hU (idGram K 3) :=
    mem_primeFormUnitary_of_isometry a.2
  obtain ⟨s', hs'⟩ : ∃ s' : unitaryIsom3 hU, ((s' : GL (Fin 3) K)) = (s : GL (Fin 3) K) :=
    ⟨⟨(s : GL (Fin 3) K), unitarySU_le_unitaryIsom3 s.2⟩, rfl⟩
  have hsmem : (s : GL (Fin 3) K) ∈ primeFormUnitary hU (idGram K 3) :=
    mem_primeFormUnitary_of_isometry (unitarySU_le_unitaryIsom3 s.2)
  have hsc : suConj hU s' = MulAut.conj s := by
    rw [conj_eq_suConj (h := hU) s]
    congr 1
    exact Subtype.ext hs'
  have hae1 : suConj hU a ≠ 1 := by
    rw [ha]
    exact fun h1 => hes (by simp [h1])
  have hcaD : suConj hU a ∈ D := by rw [ha]; exact heD
  have hsD : suConj hU s' ∈ D := by rw [hsc]; exact hcsD
  have hs1 : suConj hU s' ≠ 1 := by rw [hsc]; exact hc1
  have hsc2 : suConj hU (a * s') = e * MulAut.conj s := by rw [map_mul, ha, hsc]
  have hsc3 : suConj hU (a * (s' * s')) = e * (MulAut.conj s * MulAut.conj s) := by
    rw [map_mul, map_mul, ha, hsc]
  have hcc : MulAut.conj s * MulAut.conj s ∈
      (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range :=
    MonoidHom.mem_range.mpr ⟨s * s, map_mul _ s s⟩
  have hcs' : MulAut.conj s ∈
      (MulAut.conj : unitarySU p f K 3 →* MulAut (unitarySU p f K 3)).range :=
    MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hasD : suConj hU (a * s') ∈ D := by rw [hsc2]; exact D.mul_mem heD hcsD
  have has1 : suConj hU (a * s') ≠ 1 := by
    rw [hsc2]; exact mul_ne_one_of_not_mem hcs' hnin
  have hasSD : suConj hU (a * (s' * s')) ∈ D := by
    rw [hsc3]; exact D.mul_mem heD (D.mul_mem hcsD hcsD)
  have has2 : suConj hU (a * (s' * s')) ≠ 1 := by
    rw [hsc3]; exact mul_ne_one_of_not_mem hcc hnin
  have hy3 : ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hs3, Subgroup.coe_one, Units.val_one]
  have hx3 : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = α • 1 := by
    rw [← Units.val_pow_eq_pow_val]; exact hα
  obtain ⟨P, ξ, hP, -, hyP, hxP⟩ :=
    exists_unitary_heisenberg_basis_alpha hU hq3 hamem hsmem hω hsa hy3 hx3
  rw [diagonal_xi_eq_smul_heisD] at hyP
  have e1 : (((a * s' : unitaryIsom3 hU) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simp only [Subgroup.coe_mul, Units.val_mul, hs']
  have e2 : (((a * (s' * s') : unitaryIsom3 hU) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
    simp only [Subgroup.coe_mul, Units.val_mul, hs']
  obtain ⟨hASP, hASSP⟩ := fixer_normal_forms hxP hyP
  have hs'PN : ((s' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * (ξ • heisD ω) := by
    rw [hs']; exact hyP
  have hasPN : ((((a * s') : unitaryIsom3 hU) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) =
        (P : Matrix (Fin 3) (Fin 3) K) * (ξ • (heisC α * heisD ω)) := by
    rw [e1]; exact hASP
  have hasSPN : ((((a * (s' * s')) : unitaryIsom3 hU) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
        (P : Matrix (Fin 3) (Fin 3) K) * ((ξ * ξ) • (heisC α * (heisD ω * heisD ω))) := by
    rw [e2]; exact hASSP
  have hPdet : IsUnit (P : Matrix (Fin 3) (Fin 3) K).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit P)
  have hdetA : ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = α :=
    det_eq_of_mul_eq hPdet hxP
  have hαnorm : hU.norm α = 1 := by
    have h1 := norm_det_of_mem_unitaryIsom3 a.2
    rw [hdetA] at h1
    exact h1
  have hαN : α ^ (p ^ f + 1) = 1 := pow_succ_eq_one_of_norm hαnorm
  have hnc : ¬ ∃ μ : K, μ ^ 3 = α := by
    rintro ⟨μ, hμ⟩
    have hμN : μ ^ (p ^ f + 1) = 1 := pow_succ_eq_one_of_cube hq3 (pow_sq_card_eq hU) hμ hαN
    have hmem := suConj_mem_range_of_cube_det a hμN (by rw [hdetA, hμ])
    rw [ha] at hmem
    exact hnin hmem
  have hcore := h p f K hU hq3 hqne ω α hω hαN hnc
  have hfix : ∀ g ∈ outerHeisExactFix p f K ω α,
      conjSU hU ⟨P, hP⟩ g ∈ CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D := by
    rintro g ⟨M, hM, hgM⟩
    simp only [outerHeisLines, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact conjSU_mem_fixSet hcaD hae1 ⟨P, hP⟩ hxP hgM
    · exact conjSU_mem_fixSet hsD hs1 ⟨P, hP⟩ hs'PN (comm_smul_of_comm ξ hgM)
    · exact conjSU_mem_fixSet hasD has1 ⟨P, hP⟩ hasPN (comm_smul_of_comm ξ hgM)
    · rw [sq] at hgM
      exact conjSU_mem_fixSet hasSD has2 ⟨P, hP⟩ hasSPN (comm_smul_of_comm (ξ * ξ) hgM)
  exact eq_top_of_conj_closure hU ⟨P, hP⟩ hcore (fun g hg => Subgroup.subset_closure (hfix g hg))

