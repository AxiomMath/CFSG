module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.UConjugatesGraph
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB4Divisible
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd-graph neighbours of `U`

The four conjugates of `U` that commute with `U` are the neighbours of the
base vertex in the 35-point commuting graph.  This module proves the
bijection with the four Sylow 3-subgroups containing `U`, the transitivity
of the `Ĥ`-action on the neighbour set, and the coclique property.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A conjugate of `U` distinct from `U` and commuting with `U`. -/
public abbrev lineNeighbor {G : Type u} [Group G] [Finite G] (c : CentralizerSetup G)
    (V : UConjugates c) : Prop :=
  V ≠ UConjugates.base c ∧ lineCommutes c (UConjugates.base c) V

public abbrev lineNeighborSet {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Type u :=
  {V : UConjugates c // lineNeighbor c V}

/-- The neighbour set of the base vertex in the 35-point commuting graph. -/
@[expose] public def lineNeighbors {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) : Set (UConjugates c) :=
  {V : UConjugates c | lineNeighbor c V}

@[simp] public theorem mem_lineNeighbors_iff
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (V : UConjugates c) :
    V ∈ lineNeighbors c ↔ lineNeighbor c V :=
  Iff.rfl

private lemma sylow3_comm_all
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) (P : Sylow 3 G) :
    ∀ x y : G, x ∈ (P : Subgroup G) → y ∈ (P : Subgroup G) → x * y = y * x := by
  classical
  have hP9 : Nat.card (P : Subgroup G) = 9 := firstCase_sylow3_card_nine c d P
  have hP9' : Nat.card (P : Subgroup G) = 3 ^ 2 := by simpa using hP9
  have : IsMulCommutative (P : Subgroup G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9'
  intro x y hx hy
  exact congrArg Subtype.val
    (((IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP9').is_comm).comm
      ⟨x, hx⟩ ⟨y, hy⟩)

private lemma conjugate_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (V : UConjugates c) :
    Nat.card (V : Subgroup G) = 3 := by
  rcases V with ⟨W, g, hW⟩
  have hcard : Nat.card (conjugateSubgroup c.U g) = Nat.card c.U := by
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective c.U (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv).symm
  have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
  simpa [hW] using hcard.trans (by rw [hU3])

/-- In a Sylow 3-subgroup containing `U`, there is a unique conjugate of
`U` distinct from `U`; it commutes with `U`. -/
private theorem exists_second_line
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) :
    ∃ V : UConjugates c,
      (V : Subgroup G) ≤ (R.1 : Subgroup G) ∧ V ≠ UConjugates.base c ∧
        lineCommutes c (UConjugates.base c) V ∧
        ∀ W : UConjugates c, (W : Subgroup G) ≤ (R.1 : Subgroup G) →
          W ≠ UConjugates.base c → W = V := by
  rcases firstCase_sylow3_UConjugates_inside_eq hmin c hfirst d R.1 with
    ⟨U1, U2, hU1neU2, hU1le, hU2le, hU1conj, hU2conj, honly⟩
  have hU1base : U1 = c.U ∨ U2 = c.U := by
    have hUconj : ∃ g : G, c.U = conjugateSubgroup c.U g := by
      refine ⟨1, ?_⟩
      rw [conjugateSubgroup]
      have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [h1]
      exact (Subgroup.map_id c.U).symm
    exact (honly c.U hUconj R.2).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  by_cases h : U1 = c.U
  · refine ⟨⟨U2, hU2conj⟩, ?_⟩
    constructor
    · exact hU2le
    constructor
    · intro hb
      have h2 : U2 = c.U := by
        simpa [UConjugates.base, h] using
          congrArg (fun V : UConjugates c => (V : Subgroup G)) hb
      exact hU1neU2 (h.trans h2.symm)
    constructor
    · intro v hv w hw
      exact sylow3_comm_all c d R.1 v w
        (R.2 (by simpa [UConjugates.base, h] using hv)) (hU2le hw)
    · intro W hWle hWne
      rcases honly (W : Subgroup G) W.2 hWle with hW1 | hW2
      · exfalso
        apply hWne
        apply Subtype.ext
        change (W : Subgroup G) = UConjugates.base c
        rw [hW1, h]
        rfl
      · apply Subtype.ext
        change (W : Subgroup G) = U2
        exact hW2
  · rcases hU1base with h1 | h2
    · exact False.elim (h h1)
    · refine ⟨⟨U1, hU1conj⟩, ?_⟩
      constructor
      · exact hU1le
      constructor
      · intro hb
        have h1 : U1 = c.U := by
          simpa [UConjugates.base, h2] using
            congrArg (fun V : UConjugates c => (V : Subgroup G)) hb
        exact h h1
      constructor
      · intro v hv w hw
        exact sylow3_comm_all c d R.1 v w
          (hU2le (by simpa [UConjugates.base, h2] using hv)) (hU1le hw)
      · intro W hWle hWne
        rcases honly (W : Subgroup G) W.2 hWle with hW1 | hW2
        · apply Subtype.ext
          change (W : Subgroup G) = U1
          exact hW1
        · exfalso
          apply hWne
          apply Subtype.ext
          change (W : Subgroup G) = UConjugates.base c
          rw [hW2, h2]
          rfl

/-- The second conjugate of `U` inside a Sylow 3-subgroup containing `U`. -/
noncomputable def secondLine
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) : UConjugates c :=
  Classical.choose (exists_second_line hmin c hfirst d R)

private lemma secondLine_spec
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) :
    (secondLine hmin c hfirst d R : Subgroup G) ≤ (R.1 : Subgroup G) ∧
      secondLine hmin c hfirst d R ≠ UConjugates.base c ∧
        lineCommutes c (UConjugates.base c) (secondLine hmin c hfirst d R) ∧
        ∀ W : UConjugates c, (W : Subgroup G) ≤ (R.1 : Subgroup G) →
          W ≠ UConjugates.base c → W = secondLine hmin c hfirst d R :=
  Classical.choose_spec (exists_second_line hmin c hfirst d R)

private lemma secondLine_ne_base
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) :
    secondLine hmin c hfirst d R ≠ UConjugates.base c :=
  (secondLine_spec hmin c hfirst d R).2.1

private lemma secondLine_commutes_base
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) :
    lineCommutes c (UConjugates.base c) (secondLine hmin c hfirst d R) :=
  (secondLine_spec hmin c hfirst d R).2.2.1

private lemma order_three_subgroups_disjoint_of_ne
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hne : A ≠ B) : Disjoint A B := by
  let : Fintype ↥A := Fintype.ofFinite _
  let : Fintype ↥B := Fintype.ofFinite _
  rw [disjoint_iff_inf_le]
  intro x hx
  by_contra hxne
  have hord : orderOf x = 3 := by
    have hd0 := Subgroup.orderOf_dvd_natCard A hx.1
    have hA' : Fintype.card ↥A = 3 := by simpa [Nat.card_eq_fintype_card] using hA
    have hd : orderOf x ∣ 3 := by simpa [hA'] using hd0
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact False.elim (hxne (orderOf_eq_one_iff.mp h1))
    · exact h3
  have hgenA : Subgroup.zpowers x = A := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact A.zpow_mem hx.1 n
    · rw [Nat.card_zpowers, hord, hA]
  have hgenB : Subgroup.zpowers x = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      exact B.zpow_mem hx.2 n
    · rw [Nat.card_zpowers, hord, hB]
  exact hne (hgenA.symm.trans hgenB)

private lemma order_three_subgroup_eq_zpowers
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (hA : Nat.card A = 3) {x : G} (hx : x ∈ A)
    (hxne : x ≠ 1) : A = Subgroup.zpowers x := by
  let : Fintype ↥A := Fintype.ofFinite _
  have hd0 := Subgroup.orderOf_dvd_natCard A hx
  have hA' : Fintype.card ↥A = 3 := by simpa [Nat.card_eq_fintype_card] using hA
  have hd : orderOf x ∣ 3 := by simpa [hA'] using hd0
  have hord : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact False.elim (hxne (orderOf_eq_one_iff.mp h1))
    · exact h3
  exact (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr hx)
    (by rw [Nat.card_zpowers, hord, hA])).symm

private lemma join_card_nine_of_commute
    {G : Type u} [Group G] [Finite G]
    (U V : Subgroup G) (hU3 : Nat.card U = 3) (hV3 : Nat.card V = 3)
    (hne : U ≠ V) (hcomm : V ≤ Subgroup.centralizer (U : Set G)) :
    Nat.card (U ⊔ V : Subgroup G) = 9 := by
  have hdisj : Disjoint U V := order_three_subgroups_disjoint_of_ne U V hU3 hV3 hne
  have hnorm : V ≤ Subgroup.normalizer (U : Set G) :=
    hcomm.trans (Subgroup.centralizer_le_normalizer (U : Set G))
  rw [card_sup_eq_mul_of_disjoint_of_le_normalizer U V hnorm hdisj]
  rw [hU3, hV3]

private lemma secondLine_injective
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Function.Injective (secondLine hmin c hfirst d) := by
  intro R S hV
  let U : Subgroup G := c.U
  let V : Subgroup G := (secondLine hmin c hfirst d R : Subgroup G)
  have hUR : U ≤ (R.1 : Subgroup G) := by simpa [U] using R.2
  have hUS : U ≤ (S.1 : Subgroup G) := by simpa [U] using S.2
  have hVR : V ≤ (R.1 : Subgroup G) := by
    simpa [V] using (secondLine_spec hmin c hfirst d R).1
  have hVS : V ≤ (S.1 : Subgroup G) := by
    simpa [V, hV] using (secondLine_spec hmin c hfirst d S).1
  have hU3 : Nat.card U = 3 := by simpa [U] using firstCase_U_card_three hmin c hfirst d
  have hV3 : Nat.card V = 3 := by
    simpa [V] using conjugate_card_three hmin c hfirst d (secondLine hmin c hfirst d R)
  have hVneU : V ≠ U := by
    intro h
    apply secondLine_ne_base hmin c hfirst d R
    apply Subtype.ext
    change (secondLine hmin c hfirst d R : Subgroup G) = c.U
    simpa [U, h]
  have hcomm : V ≤ Subgroup.centralizer (U : Set G) := by
    intro v hv u hu
    have hc : Commute u v :=
      secondLine_commutes_base hmin c hfirst d R u hu v hv
    exact hc.eq
  have hsup9 : Nat.card (U ⊔ V : Subgroup G) = 9 :=
    join_card_nine_of_commute U V hU3 hV3 hVneU.symm hcomm
  have hR9 : Nat.card (R.1 : Subgroup G) = 9 := firstCase_sylow3_card_nine c d R.1
  have hS9 : Nat.card (S.1 : Subgroup G) = 9 := firstCase_sylow3_card_nine c d S.1
  have hsup_le_R : U ⊔ V ≤ (R.1 : Subgroup G) := sup_le hUR hVR
  have hsup_le_S : U ⊔ V ≤ (S.1 : Subgroup G) := sup_le hUS hVS
  have hsupR : U ⊔ V = (R.1 : Subgroup G) :=
    (Subgroup.eq_of_le_of_card_ge hsup_le_R (by rw [hsup9, hR9]))
  have hsupS : U ⊔ V = (S.1 : Subgroup G) :=
    (Subgroup.eq_of_le_of_card_ge hsup_le_S (by rw [hsup9, hS9]))
  have hRsup : (R.1 : Subgroup G) = U ⊔ V := hsupR.symm
  have hSsup : (S.1 : Subgroup G) = U ⊔ V := hsupS.symm
  apply Subtype.ext
  apply Sylow.ext
  exact hRsup.trans hSsup.symm

private lemma hhat_normalizer_U
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) :
    Subgroup.normalizer (c.U : Set G) = c.Hhat := by
  have hklein : IsKleinFour (pCore 2 c.Hhat) :=
    firstCase_twoCore_isKleinFour hmin c hfirst
  have hO2 : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    have hfour : Nat.card (twoCoreOf c.Hhat) = 4 :=
      (firstCase_klein_V_klein c hklein).card_four
    omega
  exact theorem26_normalizer_U_eq_Hhat hmin c hO2 (lemma_2_2 hmin c).2

private lemma smul_base_fix_of_mem_hhat
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (h : c.Hhat) :
    (h : G) • UConjugates.base c = UConjugates.base c := by
  apply Subtype.ext
  rw [UConjugates.smul_def]
  change conjugateSubgroup c.U (h : G) = c.U
  have hN : (h : G) ∈ Subgroup.normalizer (c.U : Set G) := by
    rw [hhat_normalizer_U hmin c hfirst]
    exact h.2
  exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp hN)

private lemma smul_secondLine_le_smul_sylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (h : c.Hhat)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) :
    (((h : G) • secondLine hmin c hfirst d R : UConjugates c) : Subgroup G) ≤
      (((h : G) • R.1 : Sylow 3 G) : Subgroup G) := by
  rw [UConjugates.smul_def]
  change conjugateSubgroup (secondLine hmin c hfirst d R : Subgroup G) (h : G) ≤
    conjugateSubgroup (R.1 : Subgroup G) (h : G)
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨v, hv, rfl⟩
  refine Subgroup.mem_map.mpr ⟨(h : G)⁻¹ * ((h : G) * v * (h : G)⁻¹) * (h : G), ?_, ?_⟩
  · have hvR : v ∈ (R.1 : Subgroup G) :=
      (secondLine_spec hmin c hfirst d R).1 hv
    have heq : (h : G)⁻¹ * ((h : G) * v * (h : G)⁻¹) * (h : G) = v := by
      group
    rw [heq]
    exact hvR
  · simp [MulAut.conj_apply]
    group

private lemma secondLine_smul
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (h : c.Hhat)
    (R : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) :
    (h : G) • secondLine hmin c hfirst d R =
      secondLine hmin c hfirst d ⟨(h : G) • R.1, by
        change c.U ≤ conjugateSubgroup (R.1 : Subgroup G) (h : G)
        intro u hu
        refine Subgroup.mem_map.mpr ⟨(h : G)⁻¹ * u * (h : G), ?_, ?_⟩
        · have hN : (h : G) ∈ Subgroup.normalizer (c.U : Set G) := by
            rw [hhat_normalizer_U hmin c hfirst]
            exact h.2
          have hni : (h : G)⁻¹ ∈ Subgroup.normalizer (c.U : Set G) :=
            (Subgroup.normalizer (c.U : Set G)).inv_mem hN
          have hu' := (Subgroup.mem_normalizer_iff.mp hni u).1 hu
          simpa using (R.2 hu')
        · simp [MulAut.conj_apply]
          group⟩ := by
  let S : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)} :=
    ⟨(h : G) • R.1, by
      change c.U ≤ conjugateSubgroup (R.1 : Subgroup G) (h : G)
      intro u hu
      refine Subgroup.mem_map.mpr ⟨(h : G)⁻¹ * u * (h : G), ?_, ?_⟩
      · have hN : (h : G) ∈ Subgroup.normalizer (c.U : Set G) := by
          rw [hhat_normalizer_U hmin c hfirst]
          exact h.2
        have hni : (h : G)⁻¹ ∈ Subgroup.normalizer (c.U : Set G) :=
          (Subgroup.normalizer (c.U : Set G)).inv_mem hN
        have hu' := (Subgroup.mem_normalizer_iff.mp hni u).1 hu
        simpa using (R.2 hu')
      · simp [MulAut.conj_apply]
        group⟩
  apply (secondLine_spec hmin c hfirst d S).2.2.2
  · exact smul_secondLine_le_smul_sylow hmin c hfirst d h R
  · intro hb
    apply secondLine_ne_base hmin c hfirst d R
    have hfix : (h : G)⁻¹ • UConjugates.base c = UConjugates.base c := by
      exact smul_base_fix_of_mem_hhat hmin c hfirst
        ⟨(h : G)⁻¹, (c.Hhat.inv_mem h.2)⟩
    calc
      secondLine hmin c hfirst d R =
          (h : G)⁻¹ • ((h : G) • secondLine hmin c hfirst d R) := by
            rw [← mul_smul]
            simp
      _ = (h : G)⁻¹ • UConjugates.base c := by rw [hb]
      _ = UConjugates.base c := hfix

private lemma factorization_three_of_countData
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    (Nat.card G).factorization 3 = 2 := by
  rcases firstCase_index_card_of_countData c d with ⟨_, hGcard⟩
  rw [hGcard]
  rw [show (2 ^ 3 * 3 ^ 2 * 5 * 7 : ℕ) = 3 ^ 2 * (2 ^ 3 * 5 * 7) by ring]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_three.factorization_self]
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (2 ^ 3 * 5 * 7 : ℕ))

private def neighbor_sylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (V : lineNeighborSet c) : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)} := by
  let U : Subgroup G := c.U
  let W : Subgroup G := (V : UConjugates c)
  have hU3 : Nat.card U = 3 := by simpa [U] using firstCase_U_card_three hmin c hfirst d
  have hW3 : Nat.card W = 3 := by simpa [W] using conjugate_card_three hmin c hfirst d V.1
  have hVne : V.1 ≠ UConjugates.base c := V.2.1
  have hWneU : W ≠ U := by
    intro h
    apply hVne
    apply Subtype.ext
    dsimp [W] at h
    rw [h, UConjugates.base_val]
  have hcomm : W ≤ Subgroup.centralizer (U : Set G) := by
    intro w hw u hu
    exact (V.2.2 u hu w hw).eq
  have hsup9 : Nat.card (U ⊔ W : Subgroup G) = 9 :=
    join_card_nine_of_commute U W hU3 hW3 hWneU.symm hcomm
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card G).factorization 3 = 2 :=
    factorization_three_of_countData c d
  let R : Sylow 3 G := Sylow.ofCard (U ⊔ W : Subgroup G) (by
    rw [hsup9, hfac]
    norm_num)
  exact ⟨R, by
    rw [Sylow.coe_ofCard]
    exact le_sup_left⟩

private lemma secondLine_neighbor_sylow
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (V : lineNeighborSet c) :
    secondLine hmin c hfirst d (neighbor_sylow hmin c hfirst d V) = V.1 := by
  let S := neighbor_sylow hmin c hfirst d V
  exact ((secondLine_spec hmin c hfirst d S).2.2.2 V.1
    (by
      dsimp [S, neighbor_sylow]
      exact le_sup_right)
    V.2.1).symm

noncomputable def neighborEquiv
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    lineNeighborSet c ≃ {R : Sylow 3 G // c.U ≤ (R : Subgroup G)} :=
  { toFun := fun V => neighbor_sylow hmin c hfirst d V
    invFun := fun R =>
      ⟨secondLine hmin c hfirst d R, ⟨secondLine_ne_base hmin c hfirst d R,
        secondLine_commutes_base hmin c hfirst d R⟩⟩
    left_inv := by
      intro V
      apply Subtype.ext
      exact secondLine_neighbor_sylow hmin c hfirst d V
    right_inv := by
      intro R
      apply secondLine_injective hmin c hfirst d
      exact secondLine_neighbor_sylow hmin c hfirst d
        ⟨secondLine hmin c hfirst d R, ⟨secondLine_ne_base hmin c hfirst d R,
          secondLine_commutes_base hmin c hfirst d R⟩⟩ }

public theorem neighbor_card_eq_four
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c) :
    Nat.card (lineNeighborSet c) = 4 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU3 : Nat.card c.U = 3 := firstCase_U_card_three hmin c hfirst d
  have hUp : IsPGroup 3 c.U := by
    refine IsPGroup.of_card (n := 1) ?_
    simpa using hU3
  rcases IsPGroup.exists_le_sylow (p := 3) hUp with ⟨P, hPU⟩
  calc
    Nat.card (lineNeighborSet c) =
        Nat.card {R : Sylow 3 G // c.U ≤ (R : Subgroup G)} :=
          Nat.card_congr (neighborEquiv hmin c hfirst d)
    _ = 4 := firstCase_sylow3_containing_U_card hmin c hfirst d P hPU

public theorem neighbor_orbit_transitive
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (V W : lineNeighborSet c) :
    ∃ h : c.Hhat, (h : G) • V.1 = W.1 := by
  let RV := neighbor_sylow hmin c hfirst d V
  let RW := neighbor_sylow hmin c hfirst d W
  have hRW : RW.1 ∈ MulAction.orbit (↥c.Hhat) RV.1 := by
    rw [firstCase_hhat_sylow3_orbit_eq_containing hmin c hfirst d RV.1 RV.2]
    exact RW.2
  rcases hRW with ⟨h, hh⟩
  have hh' : (h : G) • RV.1 = RW.1 := by
    change (h : G) • RV.1 = RW.1 at hh
    exact hh
  refine ⟨h, ?_⟩
  calc
    (h : G) • V.1 = (h : G) • secondLine hmin c hfirst d RV := by
      rw [secondLine_neighbor_sylow hmin c hfirst d V]
    _ = secondLine hmin c hfirst d ⟨(h : G) • RV.1, by
        rw [hh']
        exact RW.2⟩ := secondLine_smul hmin c hfirst d h RV
    _ = W.1 := by
      have hsub : (⟨(h : G) • RV.1, by
          rw [hh']
          exact RW.2⟩ : {R : Sylow 3 G // c.U ≤ (R : Subgroup G)}) = RW := by
        apply Subtype.ext
        exact hh'
      rw [hsub, secondLine_neighbor_sylow hmin c hfirst d W]

public theorem neighbor_coclique
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (d : FirstCaseCountData c)
    (V W : lineNeighborSet c) (hVW : V.1 ≠ W.1) :
    ¬ lineCommutes c V.1 W.1 := by
  intro hcomm
  let U : Subgroup G := c.U
  let Vg : Subgroup G := (V : UConjugates c)
  let Wg : Subgroup G := (W : UConjugates c)
  let R : Subgroup G := U ⊔ Vg
  have hU3 : Nat.card U = 3 := by simpa [U] using firstCase_U_card_three hmin c hfirst d
  have hV3 : Nat.card Vg = 3 := by
    simpa [Vg] using conjugate_card_three hmin c hfirst d V.1
  have hW3 : Nat.card Wg = 3 := by
    simpa [Wg] using conjugate_card_three hmin c hfirst d W.1
  have hVneU : Vg ≠ U := by
    intro h
    apply V.2.1
    apply Subtype.ext
    dsimp [Vg] at h
    rw [h, UConjugates.base_val]
  have hWneU : Wg ≠ U := by
    intro h
    apply W.2.1
    apply Subtype.ext
    dsimp [Wg] at h
    rw [h, UConjugates.base_val]
  have hWneV : Wg ≠ Vg := by
    intro h
    apply hVW
    apply Subtype.ext
    dsimp [Vg, Wg] at h
    exact h.symm
  have hVcommU : Vg ≤ Subgroup.centralizer (U : Set G) := by
    intro v hv u hu
    exact (V.2.2 u hu v hv).eq
  have hWcommU : Wg ≤ Subgroup.centralizer (U : Set G) := by
    intro w hw u hu
    exact (W.2.2 u hu w hw).eq
  have hWcommV : Wg ≤ Subgroup.centralizer (Vg : Set G) := by
    intro w hw v hv
    exact (hcomm v hv w hw).eq
  have hR9 : Nat.card R = 9 := by
    dsimp [R]
    exact join_card_nine_of_commute U Vg hU3 hV3 hVneU.symm hVcommU
  have hWleC : Wg ≤ Subgroup.centralizer (R : Set G) := by
    dsimp [R]
    exact le_centralizer_sup_of_le_centralizers hWcommU hWcommV
  have hWnormR : Wg ≤ Subgroup.normalizer (R : Set G) :=
    hWleC.trans (Subgroup.centralizer_le_normalizer (R : Set G))
  have hdisj : Disjoint R Wg := by
    rw [disjoint_iff_inf_le]
    intro x hx
    by_contra hxne
    have hWgen : Wg = Subgroup.zpowers x :=
      order_three_subgroup_eq_zpowers Wg hW3 hx.2 hxne
    have hWleR : Wg ≤ R := by
      rw [hWgen]
      exact Subgroup.zpowers_le.mpr hx.1
    let S := neighbor_sylow hmin c hfirst d V
    have hWleS : (W : UConjugates c) ≤ (S.1 : Subgroup G) := by
      simpa [R, S, neighbor_sylow] using hWleR
    have hW' : W.1 = secondLine hmin c hfirst d S :=
      (secondLine_spec hmin c hfirst d S).2.2.2 W.1 hWleS W.2.1
    have hVeq : secondLine hmin c hfirst d S = V.1 :=
      secondLine_neighbor_sylow hmin c hfirst d V
    have hWV : W.1 = V.1 := hW'.trans hVeq
    exact hWneV (congrArg (fun X : UConjugates c => (X : Subgroup G)) hWV)
  have hRW9 : Nat.card ((R ⊔ Wg : Subgroup G) : Subgroup G) = 27 := by
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer R Wg hWnormR hdisj]
    rw [hR9, hW3]
  have h27dvd0 : Nat.card ((R ⊔ Wg : Subgroup G) : Subgroup G) ∣ Nat.card G := by
    have hle : (R ⊔ Wg : Subgroup G) ≤ ⊤ := le_top
    have hd := Subgroup.card_dvd_of_le hle
    rwa [show Nat.card (⊤ : Subgroup G) = Nat.card G by
      exact Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv] at hd
  have h27dvd : 27 ∣ Nat.card G := by
    rwa [hRW9] at h27dvd0
  rcases firstCase_index_card_of_countData c d with ⟨_, hGcard⟩
  rw [hGcard] at h27dvd
  norm_num at h27dvd

end CFSG.GorensteinWalter
