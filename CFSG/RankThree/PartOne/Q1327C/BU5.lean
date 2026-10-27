module

public import CFSG.RankThree.PartOne.Q1327C.BLift
public import CFSG.RankThree.PartOne.Q1327C.BDefs
public import CFSG.RankThree.PartOne.KF.UnitaryModel
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.Census CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K]
variable {G : Type} [Group G] [Finite G]

theorem pow_four_le_card_torusSU [Finite K] {p : ℕ} (hp : p.Prime) (hrK : p ∣ Nat.card Kˣ) :
    p ^ 4 ≤ Nat.card (torusSU p 5 K) := by
  classical
  let μ := rootsOfUnity p K
  have hμ : Nat.card μ = p := card_rootsOfUnity_of_dvd hp hrK
  let d : (Fin 4 → μ) → (Fin 5 → Kˣ) := fun t i =>
    if h : i.val < 4 then ((t ⟨i.val, h⟩ : μ) : Kˣ) else (∏ j : Fin 4, ((t j : μ) : Kˣ))⁻¹
  have hdp : ∀ t i, d t i ^ p = 1 := by
    intro t i
    by_cases h : i.val < 4
    · have hd : d t i = ((t ⟨i.val, h⟩ : μ) : Kˣ) := by simp [d, h]
      rw [hd]
      exact (mem_rootsOfUnity p _).1 (t ⟨i.val, h⟩).2
    · have hd : d t i = (∏ j : Fin 4, ((t j : μ) : Kˣ))⁻¹ := by simp [d, h]
      rw [hd, inv_pow, ← Finset.prod_pow]
      simp [fun j => (mem_rootsOfUnity p _).1 (t j).2]
  have hdprod : ∀ t, ∏ i, d t i = 1 := by
    intro t
    rw [Fin.prod_univ_castSucc]
    have h1 : ∀ j : Fin 4, d t (Fin.castSucc j) = ((t j : μ) : Kˣ) := fun j => by
      simp [d, j.2]
    have h2 : d t (Fin.last 4) = (∏ j : Fin 4, ((t j : μ) : Kˣ))⁻¹ := by
      simp [d]
    rw [h2]
    simp [h1]
  have hmem : ∀ t, (diagU (d t) : GL (Fin 5) K) ∈ torusSU p 5 K := fun t =>
    mem_torusSU_iff.2 ⟨d t, hdp t, hdprod t, rfl⟩
  let f : (Fin 4 → μ) → torusSU p 5 K := fun t => ⟨diagU (d t), hmem t⟩
  have hf : Function.Injective f := by
    intro s t hst
    have h1 : diagU (d s) = diagU (d t) := congrArg Subtype.val hst
    have h2 := diagU_injective h1
    funext j
    have := congrFun h2 (Fin.castSucc j)
    have hj : ∀ r : Fin 4 → μ, d r (Fin.castSucc j) = ((r j : μ) : Kˣ) := fun r => by
      simp [d, j.2]
    rw [hj, hj] at this
    exact Subtype.ext this
  have := Nat.card_le_card_of_injective f hf
  rwa [card_fun_rootsOfUnity hμ] at this

theorem false_of_u5_ne_five {p : ℕ} {X A₀ F : Subgroup G} (h : Q1327.T123Base p X A₀ F)
    (hne : p ≠ 5)
    (hm : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ (p ≠ 5 ∨ 25 ∣ 2 ^ f + 1) ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 5 2 f) : False := by
  classical
  obtain ⟨f, hf1, hpq, -, hcl⟩ := hm
  have hcl' := hcl
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl'
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hU : UnitaryFieldData 2 f K := unitaryFieldData_two hK hf1
  let Mg : Subgroup (GL (Fin 5) K) := StatedSU 5 (2 ^ f) K
  let ZM : Subgroup ↥Mg := (StatedScalars (Fin 5) K).subgroupOf Mg
  let π : ↥Mg →* StatedProj Mg := QuotientGroup.mk' ZM
  let πY : ↥Mg →* (↥X ⧸ Subgroup.center ↥X) := e.symm.toMonoidHom.comp π
  have hπY : Function.Surjective πY := e.symm.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerY : πY.ker = ZM := by
    ext x
    rw [MonoidHom.mem_ker]
    show e.symm (π x) = 1 ↔ x ∈ ZM
    rw [map_eq_one_iff e.symm e.symm.injective]
    exact QuotientGroup.eq_one_iff (N := ZM) x
  have hker : ¬ p ∣ Nat.card πY.ker := by
    rw [hkerY]
    have hcard := (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK
      (by norm_num : 1 ≤ 5)).2.2
    rw [show ZM = (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ f) K) from rfl, hcard]
    intro hd
    have h5 : p ∣ 5 := hd.trans (Nat.gcd_dvd_left 5 _)
    exact hne ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h5)
  obtain ⟨Ft, hFtel, hFtmap, hFtdis⟩ := exists_lift_elementary hp πY hπY hker (barF_elem h)
  have hFtexp : ∀ x ∈ Ft, x ^ p = 1 := fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := Ft) x hx
  have hFtcomm : ∀ x ∈ Ft, ∀ y ∈ Ft, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := Ft)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  obtain ⟨ψ, hψ⟩ := exists_diag_iso_le_of_iso hU hp hpq (MulEquiv.refl _) Ft hFtexp hFtcomm
  have hrK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    have hfac : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
      zify [Nat.one_le_pow 2 (2 ^ f) (by omega), h1]
      ring
    rw [hfac]
    exact Dvd.dvd.mul_right hpq _
  have hTle : torusSU p 5 K ≤ unitarySU 2 f K 5 := torusSU_le_unitarySU hU hpq
  let T5 : Subgroup ↥(unitarySU 2 f K 5) := (torusSU p 5 K).subgroupOf (unitarySU 2 f K 5)
  have hT5mem : ∀ g : ↥(unitarySU 2 f K 5), g ∈ T5 ↔ (g : GL (Fin 5) K) ∈ torusSU p 5 K :=
    fun g => Iff.rfl
  have hT5card : p ^ 4 ≤ Nat.card T5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]
    exact pow_four_le_card_torusSU hp hrK
  have hTcomm : ∀ x ∈ torusSU p 5 K, ∀ y ∈ torusSU p 5 K, x * y = y * x := by
    intro x hx y hy
    obtain ⟨d, -, -, rfl⟩ := mem_torusSU_iff.1 hx
    obtain ⟨d', -, -, rfl⟩ := mem_torusSU_iff.1 hy
    rw [diagU_mul, diagU_mul, mul_comm]
  have hTpow : ∀ x ∈ torusSU p 5 K, x ^ p = 1 := by
    intro x hx
    obtain ⟨d, hd, -, rfl⟩ := mem_torusSU_iff.1 hx
    rw [diagU_pow]
    have : d ^ p = 1 := funext fun i => hd i
    rw [this, diagU_one]
  have hT5el : IsElementaryAbelian p T5 := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply Subtype.ext
      exact hTcomm _ a.2 _ b.2
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact hTpow _ x.2
  let Eplus : Subgroup ↥Mg := T5.map ψ.toMonoidHom
  have hEel : IsElementaryAbelian p Eplus := by
    have := hT5el
    exact IsElementaryAbelian.map ψ.toMonoidHom
  have hFtE : Ft ≤ Eplus := by
    intro x hx
    exact ⟨ψ.symm x, (hT5mem _).2 (hψ _ (by simpa using hx)), by simp⟩
  have hEcard : p ^ 4 ≤ Nat.card Eplus := by
    rw [Subgroup.card_map_of_injective ψ.injective]
    exact hT5card
  let P' : Subgroup (↥X ⧸ Subgroup.center ↥X) := Eplus.map πY
  have hP'el : IsElementaryAbelian p P' := by
    have := hEel
    exact IsElementaryAbelian.map πY
  have hFP : bar X F ≤ P' := by
    rw [← hFtmap]
    exact Subgroup.map_mono hFtE
  have hP'card : Nat.card P' = Nat.card Eplus := by
    have hdis := N143.disjoint_ker_of_isPGroup πY hp (IsElementaryAbelian.isPGroup p Eplus) hker
    exact N143.card_map_of_disjoint_ker πY hdis
  have hA₀ : bar X A₀ ≤ bar X F := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h.A₀_le_F hx, rfl⟩
  have hC : P' ≤ Subgroup.centralizer ((bar X A₀ : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
      Set (↥X ⧸ Subgroup.center ↥X)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haP : a ∈ P' := hFP (hA₀ ha)
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := P')).comm ⟨a, haP⟩ ⟨y, hy⟩)
    simpa using this
  have hEq : P' = bar X F :=
    bar_maximal hp h.center_pPrime h.F_le h.F_elem h.A₀_le_F h.F_max hP'el hFP hC
  have h1 := barF_card h
  rw [← hEq, hP'card] at h1
  have : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.RankThree.PartOne.Q1327C
