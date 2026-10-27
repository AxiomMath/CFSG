module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.theorem_13_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 13 6 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
public theorem CFSG.section13_exists_prime_order_subgroup_le_of_ne_bot
    {P : Subgroup G} (hPne : P ≠ ⊥) :
    ∃ p : Nat.Primes, ∃ R : Subgroup G, R ≤ P ∧ Nat.card R = p.val := by
  classical
  have hcard_ne_one : Nat.card P ≠ 1 := by
    intro hcard
    exact hPne ((Subgroup.eq_bot_iff_card (H := P)).2 hcard)
  obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd (n := Nat.card P) hcard_ne_one
  haveI : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card' (G := P) p hpdiv
  let R : Subgroup G := Subgroup.zpowers ((a : P) : G)
  have hR_le_P : R ≤ P := by
    exact Subgroup.zpowers_le.2 a.property
  let q : Nat.Primes := ⟨p, hpprime⟩
  have horderG : orderOf ((a : P) : G) = q.val := by
    simpa [q, Subgroup.orderOf_coe] using ha_order
  have hRcard : Nat.card R = q.val := by
    simp [R, Nat.card_zpowers, horderG]
  exact ⟨q, R, hR_le_P, hRcard⟩

private theorem CFSG.section13_msigma_centralizer_eq_E1_of_nontrivial_le_E1
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hPne : P ≠ ⊥) (hPE₁ : P ≤ E₁) :
    subgroupCentralizerIn (section10Msigma M) P =
      subgroupCentralizerIn (section10Msigma M) E₁ := by
  classical
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hE₁bot
    have hPbot : P = ⊥ := le_bot_iff.mp (by
      intro x hx
      simpa [hE₁bot] using hPE₁ hx)
    exact hPne hPbot
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := P) hPne with
    ⟨p, R, hRP, hRcard⟩
  have hRprime_E₁ : R ∈ section12PrimeOrderSubgroups E₁ := by
    simpa [section12PrimeOrderSubgroups] using
      ⟨hRP.trans hPE₁, ⟨p, hRcard⟩⟩
  have hacts :
      section13ActsPrimeManner E₁ (section10Msigma M) :=
    theorem_13_5 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₁ne
  apply le_antisymm
  · have hCP_le_CR :
        subgroupCentralizerIn (section10Msigma M) P ≤
          subgroupCentralizerIn (section10Msigma M) R := by
      intro x hx
      refine ⟨hx.1, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun r hr =>
        (Subgroup.mem_centralizer_iff.mp hx.2) r (hRP hr))
    exact hCP_le_CR.trans (hacts.2 R hRprime_E₁)
  · intro x hx
    refine ⟨hx.1, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hyP =>
      (Subgroup.mem_centralizer_iff.mp hx.2) y (hPE₁ hyP))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_centralizer_sup_eq_inf
    (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  ext x
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  change x ∈ Set.centralizer ((A : Set G) ∪ (B : Set G)) ↔
    x ∈ Set.centralizer (A : Set G) ∧ x ∈ Set.centralizer (B : Set G)
  simp [Set.centralizer_union]

private theorem CFSG.section13_E_le_E1_sup_derived_of_E2_eq_bot
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₂bot : E₂ = ⊥) :
    E ≤ E₁ ⊔ ambientDerivedSubgroup E := by
  classical
  have hEeq : E = E₁ ⊔ E₂ ⊔ E₃ :=
    (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hE₃D : E₃ ≤ ambientDerivedSubgroup E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  calc
    E ≤ E₁ ⊔ E₂ ⊔ E₃ := le_of_eq hEeq
    _ ≤ E₁ ⊔ ambientDerivedSubgroup E := by
      rw [hE₂bot]
      exact sup_le (by simp) (hE₃D.trans le_sup_right)

private theorem CFSG.section13_lemma_13_6_E1_core_of_E2_eq_bot
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₂bot : E₂ = ⊥)
    (hXE₁ : X ≤ subgroupCentralizerIn (section10Msigma M) E₁)
    (hXDerE : X ≤ subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E)) :
    X ≤ ambientDerivedSubgroup (section10Msigma M) := by
  classical
  have hXle_sigma : X ≤ section10Msigma M := fun x hx => (hXE₁ hx).1
  have hXcent_E1 : X ≤ Subgroup.centralizer (E₁ : Set G) := fun x hx => (hXE₁ hx).2
  have hXcent_D : X ≤ Subgroup.centralizer (ambientDerivedSubgroup E : Set G) :=
    fun x hx => (hXDerE hx).2
  have hXcent_sup :
      X ≤ Subgroup.centralizer ((E₁ ⊔ ambientDerivedSubgroup E : Subgroup G) : Set G) := by
    rw [section13_centralizer_sup_eq_inf]
    exact fun x hx => ⟨hXcent_E1 hx, hXcent_D hx⟩
  have hE_le : E ≤ E₁ ⊔ ambientDerivedSubgroup E :=
    section13_E_le_E1_sup_derived_of_E2_eq_bot
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hE₂bot
  have hXcent_E : X ≤ Subgroup.centralizer (E : Set G) := by
    intro x hx
    exact Subgroup.centralizer_le hE_le (hXcent_sup hx)
  have hX_CE : X ≤ subgroupCentralizerIn (section10Msigma M) E := by
    intro x hx
    exact ⟨hXle_sigma hx, hXcent_E hx⟩
  exact hX_CE.trans (lemma_12_17
    (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1

private theorem CFSG.section13_exists_tau2_rankTwo_of_E2_ne_bot
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₂ne : E₂ ≠ ⊥) :
    ∃ p : Nat.Primes, p ∈ section12Tau2Primes M ∧
      ∃ A : Subgroup G, A ∈ section12RankTwoElementaryAbelianIn p E := by
  classical
  have hcard_ne_one : Nat.card E₂ ≠ 1 := by
    intro hcard
    exact hE₂ne ((Subgroup.card_eq_one (H := E₂)).mp hcard)
  obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let q : Nat.Primes := ⟨p, hpprime⟩
  rcases hE with ⟨_hcomp, _hE12, _hE1, hE2, _hE3⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  have hcard_sub : Nat.card (E₂.subgroupOf E₁₂) = Nat.card E₂ := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := E₁₂) hE2E12).toEquiv
  have hpdiv_sub : q.val ∣ Nat.card (E₂.subgroupOf E₁₂) := by
    simpa [q, hcard_sub] using hpdiv
  have hqτ2 : q ∈ section12Tau2Primes M :=
    hHallE2.p_in_pi_of_p_dvd_card q hpdiv_sub
  rcases section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM
      ⟨_hcomp, _hE12, _hE1, ⟨hE2E12, hHallE2⟩, _hE3⟩ hqτ2 with
    ⟨A, hA⟩
  exact ⟨q, hqτ2, A, hA⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_rankTwo_of_EData
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    A ∈ section12RankTwoElementaryAbelianIn p M := by
  rcases hE with ⟨hcomp, _hE12, _hE1, _hE2, _hE3⟩
  exact ⟨hA.1.trans hcomp.2.1, hA.2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_coprime_card_E1_rankTwo_tau2
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    Nat.Coprime (Nat.card E₁) (Nat.card A) := by
  classical
  rcases hE with ⟨_hcomp, _hE12, hE1, _hE2, _hE3⟩
  rcases hE1 with ⟨hE1E12, hHallE1⟩
  rcases hA.2 with ⟨hAcard, _hAelem⟩
  have hp_coprime_E1 : Nat.Coprime p.val (Nat.card E₁) := by
    refine (p.property.coprime_iff_not_dvd).2 ?_
    intro hpdiv
    have hcard_sub : Nat.card (E₁.subgroupOf E₁₂) = Nat.card E₁ :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := E₁) (K := E₁₂) hE1E12).toEquiv
    have hpdiv_sub : p.val ∣ Nat.card (E₁.subgroupOf E₁₂) := by
      simpa [hcard_sub] using hpdiv
    have hpτ1 : p ∈ section12Tau1Primes M :=
      hHallE1.p_in_pi_of_p_dvd_card p hpdiv_sub
    have h1 : primeRank p.val M = 1 := hpτ1.2.2
    have h2 : primeRank p.val M = 2 := hp.2
    omega
  rw [hAcard, Nat.coprime_pow_right_iff (by norm_num : 0 < 2)]
  exact hp_coprime_E1.symm

private theorem CFSG.section13_fixed_rankTwo_le_centralizer_of_E1_centralized
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (_hpτ2 : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hXE₁ : X ≤ subgroupCentralizerIn (section10Msigma M) E₁) :
    subgroupCentralizerIn A E₁ ≤ Subgroup.centralizer (X : Set G) := by
  classical
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := E₁) hE₁ne with
    ⟨r, P, hPE₁, hPcard⟩
  have hP_E₁_prime : P ∈ section10PrimeOrderSubgroupsIn r E₁ := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPE₁, hPcard⟩
  have hrE₁ : r ∈ subgroupPrimeSet E₁ := by
    have hdivP : r.val ∣ Nat.card P := by rw [hPcard]
    exact hdivP.trans (Subgroup.card_dvd_of_le hPE₁)
  have hrτ1 : r ∈ section12Tau1Primes M :=
    section13_tau1_of_mem_E1_primeSet (G := G) (M := M) (E := E)
      (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE hrE₁
  rcases section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1 with
    ⟨hE₁E, _hHallE₁E⟩
  have hP_E : P ∈ section10PrimeOrderSubgroupsIn r E := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hPE₁.trans hE₁E, hPcard⟩
  have hX_CP : X ≤ subgroupCentralizerIn (section10Msigma M) P := by
    intro x hx
    refine ⟨(hXE₁ hx).1, ?_⟩
    exact Subgroup.centralizer_le (show (P : Set G) ⊆ (E₁ : Set G) from hPE₁)
      (hXE₁ hx).2
  rcases hA.2 with ⟨hAcard, hAelem⟩
  have hpE : p ∈ subgroupPrimeSet E := by
    have hp_dvd_A : p.val ∣ Nat.card A := by
      rw [hAcard]
      simp [pow_two]
    exact hp_dvd_A.trans (Subgroup.card_dvd_of_le hA.1)
  intro a ha
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  · let R : Subgroup G := Subgroup.zpowers a
    have hR_le_A : R ≤ A := Subgroup.zpowers_le.2 ha.1
    have hR_le_centE₁ : R ≤ Subgroup.centralizer (E₁ : Set G) :=
      Subgroup.zpowers_le.2 ha.2
    have hR_le_centP : R ≤ Subgroup.centralizer (P : Set G) :=
      hR_le_centE₁.trans
        (Subgroup.centralizer_le (show (P : Set G) ⊆ (E₁ : Set G) from hPE₁))
    have horder_dvd : orderOf a ∣ p.val := by
      letI : IsElementaryAbelian p.val A := hAelem
      exact orderOf_dvd_of_pow_eq_one
        (elemPow_eq_one_of_isElementaryAbelian (p := p.val) (A := A) a ha.1)
    have horder_ne_one : orderOf a ≠ 1 := by
      intro horder
      exact ha1 (orderOf_eq_one_iff.mp horder)
    have horder : orderOf a = p.val := by
      rcases p.property.eq_one_or_self_of_dvd (orderOf a) horder_dvd with h | h
      · exact False.elim (horder_ne_one h)
      · exact h
    have hRcard : Nat.card R = p.val := by
      simp [R, Nat.card_zpowers, horder]
    have hR_CEP : R ∈ section10PrimeOrderSubgroupsIn p (subgroupCentralizerIn E P) := by
      have hR_le_CEP : R ≤ subgroupCentralizerIn E P := by
        intro z hz
        exact ⟨hR_le_A.trans hA.1 hz, hR_le_centP hz⟩
      exact ⟨hR_le_CEP, hRcard⟩
    have hCP_CR :
        subgroupCentralizerIn (section10Msigma M) P ≤
          subgroupCentralizerIn (section10Msigma M) R :=
      theorem_13_4 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
        (p := r) (r := p) hM hE hrτ1 hP_E hpE hR_CEP
    have hX_cent_R : X ≤ Subgroup.centralizer (R : Set G) := fun x hx =>
      (hCP_CR (hX_CP hx)).2
    have hR_cent_X : R ≤ Subgroup.centralizer (X : Set G) :=
      (Subgroup.le_centralizer_iff (H := X) (K := R)).mp hX_cent_R
    exact hR_cent_X (Subgroup.mem_zpowers a)

private theorem CFSG.section13_rankTwo_le_fixed_sup_commutator_E1
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    A ≤ subgroupCentralizerIn A E₁ ⊔ ⁅A, E₁⁆ := by
  classical
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  rcases section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1 with
    ⟨hE₁E, _hHallE₁E⟩
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).1 hAnorm.2
  have hE₁_norm_A : E₁ ≤ Subgroup.normalizer (A : Set G) :=
    hE₁E.trans hE_norm_A
  haveI : Subgroup.Normalizes E₁ A := ⟨hE₁_norm_A⟩
  rcases hA.2 with ⟨hAcard, hAelem⟩
  have hsolvA : IsSolvable A := by
    letI : IsElementaryAbelian p.val A := hAelem
    have hAcomm := hAelem.toIsMulCommutative
    exact isSolvable_of_comm fun x y => hAcomm.is_comm.comm x y
  have hcop : Nat.Coprime (Nat.card E₁) (Nat.card A) :=
    section13_coprime_card_E1_rankTwo_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hE hp hA
  let Cfix : Subgroup A := fixedPointSubgroup (↥E₁) (↥A)
  let Ccomm : Subgroup A := commutatorAction (A := ↥E₁) (G := ↥A)
  have hsup : Cfix ⊔ Ccomm = ⊤ := by
    simpa [Cfix, Ccomm] using
      proposition_1_6_a (G := A) (A := E₁) hsolvA hcop
  have hfixed_eq :
      Cfix = (subgroupCentralizerIn A E₁).subgroupOf A := by
    simpa [Cfix] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn A E₁ hE₁_norm_A
  have hfixed_map : Cfix.map A.subtype = subgroupCentralizerIn A E₁ := by
    rw [hfixed_eq]
    exact Subgroup.map_subgroupOf_eq_of_le
      (H := subgroupCentralizerIn A E₁) (K := A)
      (show subgroupCentralizerIn A E₁ ≤ A from inf_le_left)
  have hcomm_map : Ccomm.map A.subtype = ⁅A, E₁⁆ := by
    simpa [Ccomm] using
      commutatorAction_subgroup_conj_map_eq_commutator A E₁ hE₁_norm_A
  have hsup_map :
      (Cfix ⊔ Ccomm).map A.subtype = subgroupCentralizerIn A E₁ ⊔ ⁅A, E₁⁆ := by
    rw [Subgroup.map_sup, hfixed_map, hcomm_map]
  intro a ha
  let aA : A := ⟨a, ha⟩
  have haJoin : aA ∈ Cfix ⊔ Ccomm := by
    simp [hsup]
  have haMap : a ∈ (Cfix ⊔ Ccomm).map A.subtype :=
    Subgroup.mem_map.mpr ⟨aA, haJoin, rfl⟩
  simpa [hsup_map] using haMap

private theorem CFSG.section13_lemma_13_6_rankTwo_centralizer
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hXE₁ : X ≤ subgroupCentralizerIn (section10Msigma M) E₁)
    (hXDerE : X ≤ subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E)) :
    X ≤ subgroupCentralizerIn (section10Msigma M) A := by
  classical
  have hA0_cent_X :
      subgroupCentralizerIn A E₁ ≤ Subgroup.centralizer (X : Set G) :=
    section13_fixed_rankTwo_le_centralizer_of_E1_centralized
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (X := X) (p := p)
      hM hE hE₁ne hp hA hXE₁
  rcases section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1 with
    ⟨hE₁E, _hHallE₁E⟩
  have hcomm_le_D : ⁅A, E₁⁆ ≤ ambientDerivedSubgroup E :=
    section13_commutator_le_ambientDerived_of_le hA.1 hE₁E
  have hX_cent_D : X ≤ Subgroup.centralizer (ambientDerivedSubgroup E : Set G) :=
    fun x hx => (hXDerE hx).2
  have hD_cent_X : ambientDerivedSubgroup E ≤ Subgroup.centralizer (X : Set G) :=
    (Subgroup.le_centralizer_iff (H := X) (K := ambientDerivedSubgroup E)).mp
      hX_cent_D
  have hcomm_cent_X : ⁅A, E₁⁆ ≤ Subgroup.centralizer (X : Set G) :=
    hcomm_le_D.trans hD_cent_X
  have hA_le_sup : A ≤ subgroupCentralizerIn A E₁ ⊔ ⁅A, E₁⁆ :=
    section13_rankTwo_le_fixed_sup_commutator_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hM hE hp hA
  have hA_cent_X : A ≤ Subgroup.centralizer (X : Set G) :=
    hA_le_sup.trans (sup_le hA0_cent_X hcomm_cent_X)
  have hX_cent_A : X ≤ Subgroup.centralizer (A : Set G) :=
    (Subgroup.le_centralizer_iff (H := A) (K := X)).mp hA_cent_X
  intro x hx
  exact ⟨(hXDerE hx).1, hX_cent_A hx⟩


public theorem CFSG.section13_exists_sylow_centralized_derivedE_of_not_beta
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hqβ : q ∉ section10BetaPrimes M) :
    ∃ S : Sylow q.val (section10Msigma M),
      section10AmbientSylowSubgroup (section10Msigma M) S ≤
        subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases lemma_12_19
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE with
    ⟨H, hHHallIn, hHcentD⟩
  rcases hHHallIn with ⟨hHσ, hHHall⟩
  let K : Subgroup G := section10Msigma M
  let Hsub : Subgroup K := H.subgroupOf K
  have hHHallK : IsHallSubgroup (section10BetaPrimes M)ᶜ Hsub := by
    simpa [Hsub, K] using hHHall
  have hqπ : q ∈ (section10BetaPrimes M)ᶜ := by
    simpa using hqβ
  let PH : Sylow q.val Hsub := default
  let PsubK : Subgroup K := (PH : Subgroup Hsub).map Hsub.subtype
  have hPsubKq : IsPGroup q.val PsubK := by
    exact IsPGroup.map (p := q.val) (H := (PH : Subgroup Hsub))
      PH.isPGroup' Hsub.subtype
  have hq_not_Hsub_index : ¬ q.val ∣ Hsub.index := by
    intro hq_dvd
    exact (hHHallK.p_in_pi_of_p_dvd_index q hq_dvd) hqπ
  have hPsubK_index :
      PsubK.index = (PH : Subgroup Hsub).index * Hsub.index := by
    simpa [PsubK] using
      (Subgroup.index_map_subtype (H := Hsub) (K := (PH : Subgroup Hsub)))
  have hq_not_PsubK_index : ¬ q.val ∣ PsubK.index := by
    intro hq_dvd
    have hq_prod : q.val ∣ (PH : Subgroup Hsub).index * Hsub.index := by
      simpa [hPsubK_index] using hq_dvd
    rcases q.property.dvd_or_dvd hq_prod with hq_PH | hq_H
    · exact PH.not_dvd_index hq_PH
    · exact hq_not_Hsub_index hq_H
  let S : Sylow q.val K := hPsubKq.toSylow hq_not_PsubK_index
  refine ⟨S, ?_⟩
  intro y hy
  have hyPsub : y ∈ PsubK.map K.subtype := by
    simpa [S, PsubK, K, section10AmbientSylowSubgroup] using hy
  rcases Subgroup.mem_map.mp hyPsub with ⟨yk, hykP, rfl⟩
  refine ⟨yk.property, ?_⟩
  have hyH : ((yk : K) : G) ∈ H := by
    rcases Subgroup.mem_map.mp hykP with ⟨yh, _hyhPH, hyh_eq⟩
    rw [← hyh_eq]
    exact yh.property
  exact hHcentD hyH


omit [IsMinCE G] in
private theorem CFSG.section13_isHallSubgroup_singleton_of_isPGroup_not_dvd_index
    {R : Type*} [Group R] [Finite R] {P : Subgroup R} {p : Nat.Primes}
    (hPp : IsPGroup p.val P) (hnot : ¬ p.val ∣ P.index) :
    IsHallSubgroup ({p} : Set Nat.Primes) P := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  refine isHallSubgroup_of (G := R) ({p} : Set Nat.Primes) P ?_ ?_
  · intro q hq
    rcases IsPGroup.iff_card.mp hPp with ⟨n, hn⟩
    have hq_dvd_p : q.val ∣ p.val :=
      q.property.dvd_of_dvd_pow (by simpa [hn] using hq)
    have hqp : q = p :=
      Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.property p.property).mp hq_dvd_p)
    simp [hqp]
  · intro q hq hqidx
    have hqp : q = p := by simpa using hq
    exact hnot (by simpa [hqp] using hqidx)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_card_conjBy (M : Subgroup G) (g : G) :
    Nat.card (M.conjBy g) = Nat.card M := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := M) (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_le_normalizer_ambientDerivedSubgroup
    {A K : Subgroup G} (hAK : A ≤ K) :
    A ≤ Subgroup.normalizer (ambientDerivedSubgroup K : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    let aK : K := ⟨a, hAK ha⟩
    have hconj : aK * y * aK⁻¹ ∈ derivedSubgroup K := by
      exact Subgroup.Normal.conj_mem inferInstance y hy aK
    change a * ((y : K) : G) * a⁻¹ ∈ ambientDerivedSubgroup K
    exact Subgroup.mem_map_of_mem K.subtype hconj
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    let aK : K := ⟨a, hAK ha⟩
    have hconj : aK⁻¹ * y * aK ∈ derivedSubgroup K := by
      simpa using (Subgroup.Normal.conj_mem inferInstance y hy aK⁻¹)
    refine Subgroup.mem_map.mpr ?_
    refine ⟨aK⁻¹ * y * aK, hconj, ?_⟩
    have hyx' : ((y : K) : G) = a * x * a⁻¹ := hyx
    calc
      ((aK⁻¹ * y * aK : K) : G) = a⁻¹ * ((y : K) : G) * a := by rfl
      _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [hyx']
      _ = x := by group

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_le_normalizer_of_le_centralizer
    {A X : Subgroup G} (hXcentA : X ≤ Subgroup.centralizer (A : Set G)) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hcomm : a * x = x * a :=
      Subgroup.mem_centralizer_iff.mp (hXcentA hx) a ha
    have hconj_eq : a * x * a⁻¹ = x := by
      calc
        a * x * a⁻¹ = (x * a) * a⁻¹ := by rw [hcomm]
        _ = x := by simp [mul_assoc]
    simpa [hconj_eq] using hx
  · intro hx
    have hcomm : a * (a * x * a⁻¹) = (a * x * a⁻¹) * a :=
      Subgroup.mem_centralizer_iff.mp (hXcentA hx) a ha
    have hconj_eq : a * x * a⁻¹ = x := by
      have h := congrArg (fun t : G => a⁻¹ * t) hcomm
      simpa [mul_assoc] using h
    simpa [hconj_eq] using hx

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_isInvariant_subgroupOf_of_le_normalizer
    {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (_hKH : K ≤ H) :
    haveI : Subgroup.Normalizes A H := ⟨hAH⟩
    IsInvariant (↥A) (↥H) (K.subgroupOf H) := by
  haveI : Subgroup.Normalizes A H := ⟨hAH⟩
  refine ⟨?_⟩
  intro a x
  change ((x : H) : G) ∈ K ↔ ((a : G) * ((x : H) : G) * (a : G)⁻¹) ∈ K
  exact Subgroup.mem_normalizer_iff.mp (hAK a.property) ((x : H) : G)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_primeOrderSubgroupsIn_conjBy_of_mem_centralizer
    {K E₁ X : Subgroup G} {q : Nat.Primes} {g : G}
    (hg : g ∈ subgroupCentralizerIn K E₁)
    (hX : X ∈ section10PrimeOrderSubgroupsIn q (subgroupCentralizerIn K E₁)) :
    X.conjBy g ∈ section10PrimeOrderSubgroupsIn q (subgroupCentralizerIn K E₁) := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXle, hXcard⟩
  refine ⟨?_, ?_⟩
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxCE : x ∈ subgroupCentralizerIn K E₁ := hXle hx
    refine ⟨?_, ?_⟩
    · change g * x * g⁻¹ ∈ K
      exact K.mul_mem (K.mul_mem hg.1 hxCE.1) (K.inv_mem hg.1)
    · change g * x * g⁻¹ ∈ Subgroup.centralizer (E₁ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hgcomm : e * g = g * e := Subgroup.mem_centralizer_iff.mp hg.2 e he
      have hxcomm : e * x = x * e := Subgroup.mem_centralizer_iff.mp hxCE.2 e he
      have hgcomm_inv : e * g⁻¹ = g⁻¹ * e := by
        have h := congrArg (fun t : G => g⁻¹ * t * g⁻¹) hgcomm
        simpa [mul_assoc] using h.symm
      calc
        e * (g * x * g⁻¹) = (e * g) * x * g⁻¹ := by simp [mul_assoc]
        _ = (g * e) * x * g⁻¹ := by rw [hgcomm]
        _ = g * (e * x) * g⁻¹ := by simp [mul_assoc]
        _ = g * (x * e) * g⁻¹ := by rw [hxcomm]
        _ = g * x * (e * g⁻¹) := by simp [mul_assoc]
        _ = g * x * (g⁻¹ * e) := by rw [hgcomm_inv]
        _ = (g * x * g⁻¹) * e := by simp [mul_assoc]
  · rw [section13_card_conjBy]
    exact hXcard

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_le_ambientDerivedSubgroup_of_conjBy_le
    {K X : Subgroup G} {g : G} (hgK : g ∈ K)
    (hXg : X.conjBy g ≤ ambientDerivedSubgroup K) :
    X ≤ ambientDerivedSubgroup K := by
  intro x hx
  have hxg : g * x * g⁻¹ ∈ X.conjBy g :=
    Subgroup.mem_map.mpr ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hxgD : g * x * g⁻¹ ∈ ambientDerivedSubgroup K := hXg hxg
  have hginv_norm : g⁻¹ ∈ Subgroup.normalizer (ambientDerivedSubgroup K : Set G) :=
    (Subgroup.normalizer (ambientDerivedSubgroup K : Set G)).inv_mem
      (section13_le_normalizer_ambientDerivedSubgroup (A := K) (K := K) le_rfl hgK)
  have hback : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ ambientDerivedSubgroup K :=
    (Subgroup.mem_normalizer_iff.mp hginv_norm (g * x * g⁻¹)).1 hxgD
  simpa [mul_assoc] using hback

private theorem CFSG.section13_lemma_13_6_conjugate_centralizes_derivedE
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (_hE₁ne : E₁ ≠ ⊥)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) E₁))
    (hSyl :
      ∃ S : Sylow q.val (section10Msigma M),
        section10AmbientSylowSubgroup (section10Msigma M) S ≤
          subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E)) :
    ∃ g : G,
      g ∈ subgroupCentralizerIn (section10Msigma M) E₁ ∧
        X.conjBy g ∈ section10PrimeOrderSubgroupsIn q
          (subgroupCentralizerIn (section10Msigma M) E₁) ∧
          X.conjBy g ≤
            subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E) := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let K : Subgroup G := section10Msigma M
  let D : Subgroup G := ambientDerivedSubgroup E
  let C : Subgroup G := subgroupCentralizerIn K D
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with
    ⟨hXleCE₁, hXcard⟩
  rcases section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1 with
    ⟨hE₁E, _hHallE₁E⟩
  have hE_le_M : E ≤ M := hE.1.2.1
  have hE₁_le_M : E₁ ≤ M := hE₁E.trans hE_le_M
  have hE₁_norm_K : E₁ ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using hE₁_le_M.trans section13_le_normalizer_msigma
  haveI : Subgroup.Normalizes E₁ K := ⟨hE₁_norm_K⟩
  have hK_le_M : K ≤ M := by
    intro x hx
    change x ∈ (section10MsigmaSubgroup M).map M.subtype at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hK_ne_top : K ≠ ⊤ := by
    intro hKtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hKtop] using hK_le_M
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hKsolv : IsSolvable K :=
    IsMinCE.proper_subgroups_solvable K (lt_top_iff_ne_top.2 hK_ne_top)
  have hKπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M) K := by
    intro s hs
    exact ((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_card s
      (by simpa [K] using hs)
  have hEπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E := by
    intro s hsE
    have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      natCard_subgroupOf_eq E M hE_le_M
    have hsEsub : s.val ∣ Nat.card (E.subgroupOf M) := by
      simpa [hcard, subgroupPrimeSet] using hsE
    exact (section12_msigma_complement_isHall_sigma_compl
      (G := G) hM hE.1).p_in_pi_of_p_dvd_card s hsEsub
  have hE₁πsub : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E₁ := by
    intro s hs
    exact hEπsub s (hs.trans (Subgroup.card_dvd_of_le hE₁E))
  have hdis :
      Disjoint (section10SigmaPrimes M)ᶜ (section10SigmaPrimes M) := by
    rw [Set.disjoint_left]
    intro p hpcomp hpσ
    exact hpcomp hpσ
  have hcop : Nat.Coprime (Nat.card E₁) (Nat.card K) :=
    section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) (π := (section10SigmaPrimes M)ᶜ)
      (ρ := section10SigmaPrimes M) (A := E₁) (B := K)
      hE₁πsub hKπsub hdis
  let Xsub : Subgroup K := X.subgroupOf K
  have hXleK : X ≤ K := hXleCE₁.trans inf_le_left
  have hXsubπ : IsPiSubgroup (G := K) ({q} : Set Nat.Primes) Xsub := by
    intro r hr
    have hcard : Nat.card Xsub = Nat.card X :=
      natCard_subgroupOf_eq X K hXleK
    have hrX : r.val ∣ Nat.card X := by
      simpa [Xsub, hcard, subgroupPrimeSet] using hr
    have hrq : r = q :=
      Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.property q.property).mp
        (by simpa [hXcard] using hrX))
    simp [hrq]
  have hE₁_norm_X : E₁ ≤ Subgroup.normalizer (X : Set G) :=
    section13_le_normalizer_of_le_centralizer (G := G)
      (hXleCE₁.trans inf_le_right)
  have hXsub_inv : IsInvariant (↥E₁) (↥K) Xsub :=
    section13_isInvariant_subgroupOf_of_le_normalizer
      (G := G) (A := E₁) (H := K) (K := X)
      hE₁_norm_K hE₁_norm_X hXleK
  rcases proposition_1_5_b (G := K) (A := E₁) hKsolv hcop
      ({q} : Set Nat.Primes) Xsub hXsubπ hXsub_inv with
    ⟨HX, hHXHall, hHXinv, hXsub_le_HX⟩
  have hE₁_norm_D : E₁ ≤ Subgroup.normalizer (D : Set G) :=
    section13_le_normalizer_ambientDerivedSubgroup (G := G) hE₁E
  have hE₁_norm_C : E₁ ≤ Subgroup.normalizer (C : Set G) := by
    have hE₁_norm_centD :
        E₁ ≤ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) :=
      hE₁_norm_D.trans (section13_normalizer_le_normalizer_centralizer (G := G) D)
    simpa [C, subgroupCentralizerIn] using
      section13_le_normalizer_inf
        (G := G) (A := E₁) (H := K)
        (K := Subgroup.centralizer (D : Set G)) hE₁_norm_K hE₁_norm_centD
  haveI : Subgroup.Normalizes E₁ C := ⟨hE₁_norm_C⟩
  have hC_le_K : C ≤ K := by
    simp [C, subgroupCentralizerIn]
  have hCπsub : IsPiSubgroup (G := G) (section10SigmaPrimes M) C :=
    IsPiSubgroup.of_le hC_le_K hKπsub
  have hCπ : IsPiGroup (section10SigmaPrimes M) C :=
    IsPiSubgroup.isPiGroup C hCπsub
  have hE₁π : IsPiGroup (section10SigmaPrimes M)ᶜ E₁ :=
    IsPiSubgroup.isPiGroup E₁ hE₁πsub
  have hC_ne_top : C ≠ ⊤ := by
    intro hCtop
    exact hK_ne_top (top_le_iff.mp (by simpa [hCtop] using hC_le_K))
  have hCsolv : IsSolvable C :=
    IsMinCE.proper_subgroups_solvable C (lt_top_iff_ne_top.2 hC_ne_top)
  have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := by
    ext
    rfl
  rcases exists_invariant_sylow_of_pi_complement_action
      (G := C) (A := E₁) (π := section10SigmaPrimes M) (p := q.val)
      hCπ hE₁π hCsolv (by rw [hq_eq]; exact hqσ) with
    ⟨TC, hTCinv⟩
  let Pamb : Subgroup G := section10AmbientSylowSubgroup C TC
  have hPamb_le_C : Pamb ≤ C := by
    simpa [Pamb] using section13_ambient_sylow_le_base (G := G) C TC
  have hPamb_le_K : Pamb ≤ K := hPamb_le_C.trans hC_le_K
  let HC : Subgroup K := Pamb.subgroupOf K
  have hPamb_norm : E₁ ≤ Subgroup.normalizer (Pamb : Set G) := by
    simpa [Pamb, section10AmbientSylowSubgroup] using
      section13_le_normalizer_map_of_isInvariant
        (G := G) (A := E₁) (H := C) (K := (TC : Subgroup C))
        hE₁_norm_C hTCinv
  have hHCinv : IsInvariant (↥E₁) (↥K) HC :=
    section13_isInvariant_subgroupOf_of_le_normalizer
      (G := G) (A := E₁) (H := K) (K := Pamb)
      hE₁_norm_K hPamb_norm hPamb_le_K
  have hPamb_q : IsPGroup q.val Pamb := by
    change IsPGroup q.val ((TC : Subgroup C).map C.subtype)
    exact IsPGroup.map (p := q.val) (H := (TC : Subgroup C))
      TC.isPGroup' C.subtype
  have hHCq : IsPGroup q.val HC :=
    hPamb_q.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Pamb) (K := K) hPamb_le_K).symm
  have hK_not_index : ¬ q.val ∣ K.index := by
    intro hqidx
    exact (((theorem_10_2_b (G := G) hM).1).p_in_pi_of_p_dvd_index q
      (by simpa [K] using hqidx)) hqσ
  have hC_not_index : ¬ q.val ∣ C.index := by
    rcases hSyl with ⟨SC, hSCcent⟩
    let SCamb : Subgroup G := section10AmbientSylowSubgroup K SC
    have hSCamb_not_index : ¬ q.val ∣ SCamb.index := by
      intro hqidx
      have hidx : SCamb.index = (SC : Subgroup K).index * K.index := by
        simpa [SCamb, section10AmbientSylowSubgroup] using
          (Subgroup.index_map_subtype (H := K) (K := (SC : Subgroup K)))
      have hprod : q.val ∣ (SC : Subgroup K).index * K.index := by
        simpa [hidx] using hqidx
      rcases q.property.dvd_or_dvd hprod with hSCidx | hKidx
      · exact SC.not_dvd_index hSCidx
      · exact hK_not_index hKidx
    intro hqCidx
    exact hSCamb_not_index
      (hqCidx.trans (Subgroup.index_dvd_of_le (by simpa [C, K, D] using hSCcent)))
  have hPamb_not_index : ¬ q.val ∣ Pamb.index := by
    intro hqidx
    have hidx : Pamb.index = (TC : Subgroup C).index * C.index := by
      simpa [Pamb, section10AmbientSylowSubgroup] using
        (Subgroup.index_map_subtype (H := C) (K := (TC : Subgroup C)))
    have hprod : q.val ∣ (TC : Subgroup C).index * C.index := by
      simpa [hidx] using hqidx
    rcases q.property.dvd_or_dvd hprod with hTCidx | hCidx
    · exact TC.not_dvd_index hTCidx
    · exact hC_not_index hCidx
  have hHC_not_index : ¬ q.val ∣ HC.index := by
    intro hqidx
    have hmapHC : HC.map K.subtype = Pamb := by
      simpa [HC] using
        (Subgroup.map_subgroupOf_eq_of_le (H := Pamb) (K := K) hPamb_le_K)
    have hidx : Pamb.index = HC.index * K.index := by
      simpa [hmapHC] using (Subgroup.index_map_subtype (H := K) (K := HC))
    exact hPamb_not_index (by
      rw [hidx]
      exact dvd_mul_of_dvd_left hqidx K.index)
  have hHCHall : IsHallSubgroup ({q} : Set Nat.Primes) HC :=
    section13_isHallSubgroup_singleton_of_isPGroup_not_dvd_index
      (R := K) hHCq hHC_not_index
  rcases proposition_1_5_c (G := K) (A := E₁) hKsolv hcop
      ({q} : Set Nat.Primes) HX HC hHXHall hHCHall hHXinv hHCinv with
    ⟨gK, hgfix, hHC_eq⟩
  have hfixed_eq :
      fixedPointSubgroup (↥E₁) (↥K) =
        (subgroupCentralizerIn K E₁).subgroupOf K := by
    simpa [K] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn K E₁ hE₁_norm_K
  have hgCE₁ : ((gK : K) : G) ∈ subgroupCentralizerIn K E₁ := by
    have hgsub : gK ∈ (subgroupCentralizerIn K E₁).subgroupOf K := by
      simpa [hfixed_eq] using hgfix
    exact hgsub
  refine ⟨(gK : K), by simpa [K] using hgCE₁, ?_, ?_⟩
  · exact
      section13_primeOrderSubgroupsIn_conjBy_of_mem_centralizer
        (G := G) (K := K) (E₁ := E₁) (X := X) (q := q)
        (g := (gK : K)) hgCE₁ (by simpa [K] using hX)
  · intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    let xK : K := ⟨x, hXleK hx⟩
    have hxXsub : xK ∈ Xsub := by
      simpa [Xsub, Subgroup.mem_subgroupOf, xK] using hx
    have hxHX : xK ∈ HX := hXsub_le_HX hxXsub
    have hxHC : (MulAut.conj gK) xK ∈ HC := by
      rw [hHC_eq]
      exact Subgroup.mem_map.mpr ⟨xK, hxHX, rfl⟩
    have hxPamb : (((MulAut.conj gK) xK : K) : G) ∈ Pamb := hxHC
    have hxC : (((MulAut.conj gK) xK : K) : G) ∈ C := hPamb_le_C hxPamb
    change ((gK : K) : G) * x * ((gK : K) : G)⁻¹ ∈
      subgroupCentralizerIn K D
    simpa [C, D, MulAut.conj_apply, xK, K] using hxC

private theorem CFSG.section13_lemma_13_6_centralizes_derivedE
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hqβ : q ∉ section10BetaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) E₁)) :
    ∃ g : G,
      g ∈ subgroupCentralizerIn (section10Msigma M) E₁ ∧
        X.conjBy g ∈ section10PrimeOrderSubgroupsIn q
          (subgroupCentralizerIn (section10Msigma M) E₁) ∧
          X.conjBy g ≤
            subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E) := by
  classical
  have hSyl :
      ∃ S : Sylow q.val (section10Msigma M),
        section10AmbientSylowSubgroup (section10Msigma M) S ≤
          subgroupCentralizerIn (section10Msigma M) (ambientDerivedSubgroup E) :=
    section13_exists_sylow_centralized_derivedE_of_not_beta
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE hqβ
  exact section13_lemma_13_6_conjugate_centralizes_derivedE
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (X := X) (q := q)
      hM hE hE₁ne hqσ hX hSyl

private theorem CFSG.section13_lemma_13_6_E1_core
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) E₁)) :
    q ∈ section10BetaPrimes M ∨ X ≤ ambientDerivedSubgroup (section10Msigma M) := by
  classical
  by_cases hqβ : q ∈ section10BetaPrimes M
  · exact Or.inl hqβ
  · right
    rcases
      section13_lemma_13_6_centralizes_derivedE
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (X := X) (q := q)
        hM hE hE₁ne hqσ hqβ hX with
      ⟨g, hgCE₁, hXg, hXgDerE⟩
    have hXgE₁ :
        X.conjBy g ≤ subgroupCentralizerIn (section10Msigma M) E₁ := by
      simpa [section10PrimeOrderSubgroupsIn] using hXg.1
    have hXgD : X.conjBy g ≤ ambientDerivedSubgroup (section10Msigma M) := by
      by_cases hE₂bot : E₂ = ⊥
      · exact
          section13_lemma_13_6_E1_core_of_E2_eq_bot
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) (X := X.conjBy g)
            hM hE hE₂bot hXgE₁ hXgDerE
      · rcases section13_exists_tau2_rankTwo_of_E2_ne_bot
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hE₂bot with
        ⟨p, hpτ2, A, hA⟩
        have hX_CA : X.conjBy g ≤ subgroupCentralizerIn (section10Msigma M) A :=
          section13_lemma_13_6_rankTwo_centralizer
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) (A := A) (X := X.conjBy g) (p := p)
            hM hE hE₁ne hpτ2 hA hXgE₁ hXgDerE
        have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
          section13_rankTwo_of_EData
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) hE hA
        have hCA_bot : subgroupCentralizerIn (section10Msigma M) A = ⊥ :=
          theorem_12_5_d (G := G) (M := M) (A := A) (p := p) hM hpτ2 hA_M
        exfalso
        have hXbot : X.conjBy g = ⊥ := by
          apply le_bot_iff.mp
          rw [← hCA_bot]
          exact hX_CA
        exact (section13_ne_bot_of_prime_order (G := G) (X := X.conjBy g) (q := q)
          (by simpa [section10PrimeOrderSubgroupsIn] using hXg.2)) hXbot
    exact
      section13_le_ambientDerivedSubgroup_of_conjBy_le
        (G := G) (K := section10Msigma M) (X := X) (g := g) hgCE₁.1 hXgD

private theorem CFSG.section13_lemma_13_6_cor12_14_hyp
    {M E E₁₂ E₁ E₂ E₃ P X : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hPne : P ≠ ⊥) (hPE₁ : P ≤ E₁)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) P)) :
    q ∈ section10BetaPrimes M ∨ X ≤ ambientDerivedSubgroup (section10Msigma M) := by
  have hCPeq :
      subgroupCentralizerIn (section10Msigma M) P =
        subgroupCentralizerIn (section10Msigma M) E₁ :=
    section13_msigma_centralizer_eq_E1_of_nontrivial_le_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) hM hE hPne hPE₁
  have hX_E₁ : X ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) E₁) := by
    simpa [hCPeq] using hX
  have hE₁ne : E₁ ≠ ⊥ := by
    intro hE₁bot
    have hPbot : P = ⊥ := le_bot_iff.mp (by
      intro x hx
      simpa [hE₁bot] using hPE₁ hx)
    exact hPne hPbot
  exact
    section13_lemma_13_6_E1_core
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (X := X) (q := q)
      hM hE hE₁ne hqσ hX_E₁

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_centralizer_singleton_le_centralizer_zpowers
    (a : G) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
  have hcomm : Commute a x :=
    (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
  simpa using (hcomm.zpow_left n).eq

public theorem CFSG.section13_nonregular_exists_prime_order_centralizing
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hnotRegular : ¬ section13ActsRegularlyOn E₁ E₃) :
    ∃ p r : Nat.Primes, ∃ P R : Subgroup G,
      P ∈ section10PrimeOrderSubgroupsIn p E₁ ∧
        R ∈ section10PrimeOrderSubgroupsIn r E₃ ∧
          R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P) := by
  classical
  rcases hE with ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases hE₃ with ⟨hE₃E, hHallE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with
    ⟨hE₁E, _hHallE₁E⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE₁₂, hE₁, hE₂, ⟨hE₃E, hHallE₃⟩⟩
  have hE₃norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hEdata).2
  have hE₁_norm_E₃ : E₁ ≤ Subgroup.normalizer (E₃ : Set G) := by
    have hE_norm_E₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃norm.1).1 hE₃norm.2
    exact hE₁E.trans hE_norm_E₃
  have hnot_all :
      ¬ ∀ a : G, a ∈ E₁ → a ≠ 1 → elementCentralizerIn E₃ a = ⊥ := by
    intro hregular
    exact hnotRegular ⟨hE₁_norm_E₃, hregular⟩
  push Not at hnot_all
  rcases hnot_all with ⟨a, haE₁, hane, hCent_ne_bot⟩
  have hzp_ne_bot : Subgroup.zpowers a ≠ (⊥ : Subgroup G) := by
    intro hzp_bot
    have ha_bot : a ∈ (⊥ : Subgroup G) := by
      simpa [hzp_bot] using (Subgroup.mem_zpowers a)
    exact hane (Subgroup.mem_bot.mp ha_bot)
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := Subgroup.zpowers a) hzp_ne_bot with
    ⟨p, P, hP_zp, hPcard⟩
  let C : Subgroup G := elementCentralizerIn E₃ a
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := C) (by simpa [C] using hCent_ne_bot) with
    ⟨r, R, hR_C, hRcard⟩
  have hzp_le_E₁ : Subgroup.zpowers a ≤ E₁ := Subgroup.zpowers_le.2 haE₁
  have hP_E₁ : P ∈ section10PrimeOrderSubgroupsIn p E₁ := by
    simpa [section10PrimeOrderSubgroupsIn] using
      ⟨hP_zp.trans hzp_le_E₁, hPcard⟩
  have hR_E₃_le : R ≤ E₃ := by
    intro x hx
    exact (show x ∈ C from hR_C hx).1
  have hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃ := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hR_E₃_le, hRcard⟩
  have hR_cent_zp : R ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
    intro x hx
    exact section13_centralizer_singleton_le_centralizer_zpowers (G := G) a
      ((show x ∈ C from hR_C hx).2)
  have hR_cent_P : R ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hR_cent_zp hx)) y (hP_zp hy)
  have hR_CEP : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P) := by
    have hR_le_CEP : R ≤ subgroupCentralizerIn E P := by
      intro x hx
      exact ⟨hE₃E (hR_E₃_le hx), hR_cent_P hx⟩
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hR_le_CEP, hRcard⟩
  exact ⟨p, r, P, R, hP_E₁, hR_E₃, hR_CEP⟩

omit [IsMinCE G] in
public theorem CFSG.section13_centralizer_ne_bot_of_prime_manner_not_regular
    {A H : Subgroup G}
    (hprime : section13ActsPrimeManner A H)
    (hnotRegular : ¬ section13ActsRegularlyOn A H) :
    subgroupCentralizerIn H A ≠ ⊥ := by
  classical
  have hnot_all :
      ¬ ∀ a : G, a ∈ A → a ≠ 1 → elementCentralizerIn H a = ⊥ := by
    intro hregular
    exact hnotRegular ⟨hprime.1, hregular⟩
  push Not at hnot_all
  rcases hnot_all with ⟨a, haA, hane, hCa_ne⟩
  have hzp_ne : Subgroup.zpowers a ≠ (⊥ : Subgroup G) := by
    intro hzp
    have ha_bot : a ∈ (⊥ : Subgroup G) := by
      simpa [hzp] using Subgroup.mem_zpowers a
    exact hane (Subgroup.mem_bot.mp ha_bot)
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := Subgroup.zpowers a) hzp_ne with
    ⟨r, R, hR_zp, hRcard⟩
  let C : Subgroup G := elementCentralizerIn H a
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := C) (by simpa [C] using hCa_ne) with
    ⟨q, X, hX_C, hXcard⟩
  have hR_A : R ∈ section12PrimeOrderSubgroups A := by
    have hR_le_A : R ≤ A := hR_zp.trans (Subgroup.zpowers_le.2 haA)
    simpa [section12PrimeOrderSubgroups] using ⟨hR_le_A, ⟨r, hRcard⟩⟩
  have hX_le_CHR : X ≤ subgroupCentralizerIn H R := by
    intro x hx
    have hxC : x ∈ C := hX_C hx
    refine ⟨hxC.1, ?_⟩
    have hx_cent_zp :
        x ∈ Subgroup.centralizer (Subgroup.zpowers a : Set G) :=
      section13_centralizer_singleton_le_centralizer_zpowers (G := G) a hxC.2
    change x ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff] at hx_cent_zp ⊢
    intro y hy
    exact hx_cent_zp y (hR_zp hy)
  have hX_le_CHA : X ≤ subgroupCentralizerIn H A :=
    hX_le_CHR.trans (hprime.2 R hR_A)
  intro hbot
  have hXbot : X ≤ (⊥ : Subgroup G) := by
    simpa [hbot] using hX_le_CHA
  have hXne : X ≠ ⊥ := by
    intro hXeq
    have hcard_one : Nat.card X = 1 := by
      rw [hXeq]
      simp
    have hq_one : q.val = 1 := by omega
    exact q.property.ne_one hq_one
  exact hXne (le_bot_iff.mp hXbot)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_lemma_13_7_centralizer_le_join_of_left_factor
    {M E₁ E₃ P R X : Subgroup G} {p r : Nat.Primes}
    (hE₁_prime : section13ActsPrimeManner E₁ (section10Msigma M))
    (hE₃_prime : section13ActsPrimeManner E₃ (section10Msigma M))
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hCP_eq_CR :
      subgroupCentralizerIn (section10Msigma M) P =
        subgroupCentralizerIn (section10Msigma M) R)
    (hX : X ∈ section12PrimeOrderSubgroups E₁) :
    subgroupCentralizerIn (section10Msigma M) X ≤
      subgroupCentralizerIn (section10Msigma M) (E₁ ⊔ E₃) := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR_E₃) with
    ⟨hR_E₃_le, hRcard⟩
  have hPprime : P ∈ section12PrimeOrderSubgroups E₁ := by
    simpa [section12PrimeOrderSubgroups] using ⟨hP_E₁, ⟨p, hPcard⟩⟩
  have hRprime : R ∈ section12PrimeOrderSubgroups E₃ := by
    simpa [section12PrimeOrderSubgroups] using ⟨hR_E₃_le, ⟨r, hRcard⟩⟩
  have hCX_E₁ :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) E₁ :=
    hE₁_prime.2 X hX
  have hCE₁_CP :
      subgroupCentralizerIn (section10Msigma M) E₁ ≤
        subgroupCentralizerIn (section10Msigma M) P := by
    intro y hy
    exact ⟨hy.1, Subgroup.centralizer_le
      (show (P : Set G) ⊆ (E₁ : Set G) from hP_E₁) hy.2⟩
  have hCX_CP :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) P :=
    hCX_E₁.trans hCE₁_CP
  have hCX_CR :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) R := by
    simpa [hCP_eq_CR] using hCX_CP
  have hCR_E₃ :
      subgroupCentralizerIn (section10Msigma M) R ≤
        subgroupCentralizerIn (section10Msigma M) E₃ :=
    hE₃_prime.2 R hRprime
  have hCX_E₃ :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) E₃ :=
    hCX_CR.trans hCR_E₃
  intro y hy
  refine ⟨hy.1, ?_⟩
  rw [section13_centralizer_sup_eq_inf]
  exact ⟨(hCX_E₁ hy).2, (hCX_E₃ hy).2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_lemma_13_7_centralizer_le_join_of_right_factor
    {M E₁ E₃ P R X : Subgroup G} {p r : Nat.Primes}
    (hE₁_prime : section13ActsPrimeManner E₁ (section10Msigma M))
    (hE₃_prime : section13ActsPrimeManner E₃ (section10Msigma M))
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hCP_eq_CR :
      subgroupCentralizerIn (section10Msigma M) P =
        subgroupCentralizerIn (section10Msigma M) R)
    (hX : X ∈ section12PrimeOrderSubgroups E₃) :
    subgroupCentralizerIn (section10Msigma M) X ≤
      subgroupCentralizerIn (section10Msigma M) (E₁ ⊔ E₃) := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR_E₃) with
    ⟨hR_E₃_le, hRcard⟩
  have hPprime : P ∈ section12PrimeOrderSubgroups E₁ := by
    simpa [section12PrimeOrderSubgroups] using ⟨hP_E₁, ⟨p, hPcard⟩⟩
  have hCX_E₃ :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) E₃ :=
    hE₃_prime.2 X hX
  have hCE₃_CR :
      subgroupCentralizerIn (section10Msigma M) E₃ ≤
        subgroupCentralizerIn (section10Msigma M) R := by
    intro y hy
    exact ⟨hy.1, Subgroup.centralizer_le
      (show (R : Set G) ⊆ (E₃ : Set G) from hR_E₃_le) hy.2⟩
  have hCX_CR :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) R :=
    hCX_E₃.trans hCE₃_CR
  have hCX_CP :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) P := by
    simpa [hCP_eq_CR] using hCX_CR
  have hCP_E₁ :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) E₁ :=
    hE₁_prime.2 P hPprime
  have hCX_E₁ :
      subgroupCentralizerIn (section10Msigma M) X ≤
        subgroupCentralizerIn (section10Msigma M) E₁ :=
    hCX_CP.trans hCP_E₁
  intro y hy
  refine ⟨hy.1, ?_⟩
  rw [section13_centralizer_sup_eq_inf]
  exact ⟨(hCX_E₁ hy).2, (hCX_E₃ hy).2⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_lemma_13_7_centralizer_le_join_of_conj
    {M E₁ E₃ X : Subgroup G} {g : G}
    (hJ_norm :
      E₁ ⊔ E₃ ≤ Subgroup.normalizer (section10Msigma M : Set G))
    (hgJ : g ∈ E₁ ⊔ E₃)
    (hbound :
      subgroupCentralizerIn (section10Msigma M) (X.conjBy g) ≤
        subgroupCentralizerIn (section10Msigma M) (E₁ ⊔ E₃)) :
    subgroupCentralizerIn (section10Msigma M) X ≤
      subgroupCentralizerIn (section10Msigma M) (E₁ ⊔ E₃) := by
  classical
  let J : Subgroup G := E₁ ⊔ E₃
  intro y hy
  have hgyH : g * y * g⁻¹ ∈ section10Msigma M := by
    exact (Subgroup.mem_normalizer_iff.mp (hJ_norm hgJ) y).1 hy.1
  have hgy_cent_Xg :
      g * y * g⁻¹ ∈ Subgroup.centralizer (X.conjBy g : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, rfl⟩
    change (g * x * g⁻¹) * (g * y * g⁻¹) =
      (g * y * g⁻¹) * (g * x * g⁻¹)
    have hycomm : x * y = y * x :=
      Subgroup.mem_centralizer_iff.mp hy.2 x hx
    calc
      (g * x * g⁻¹) * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
      _ = g * (y * x) * g⁻¹ := by rw [hycomm]
      _ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
  have hgy :
      g * y * g⁻¹ ∈ subgroupCentralizerIn (section10Msigma M) (X.conjBy g) :=
    ⟨hgyH, hgy_cent_Xg⟩
  have hgyJ := hbound hgy
  refine ⟨hy.1, ?_⟩
  change y ∈ Subgroup.centralizer (J : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hgzJ : g * z * g⁻¹ ∈ J := by
    exact J.mul_mem (J.mul_mem (by simpa [J] using hgJ) (by simpa [J] using hz))
      (J.inv_mem (by simpa [J] using hgJ))
  have hcomm :
      (g * z * g⁻¹) * (g * y * g⁻¹) =
        (g * y * g⁻¹) * (g * z * g⁻¹) :=
    Subgroup.mem_centralizer_iff.mp hgyJ.2 (g * z * g⁻¹) hgzJ
  have h := congrArg (fun t : G => g⁻¹ * t * g) hcomm
  simpa [mul_assoc] using h

public theorem CFSG.section13_lemma_13_7_prime_conj_le_E1_or_E3
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hX : X ∈ section12PrimeOrderSubgroups (E₁ ⊔ E₃)) :
    ∃ g : G, g ∈ E₁ ⊔ E₃ ∧ (X.conjBy g ≤ E₁ ∨ X.conjBy g ≤ E₃) := by
  classical
  let J : Subgroup G := E₁ ⊔ E₃
  rcases hE with ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases hE₃ with ⟨hE₃E, hHallE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with
    ⟨hE₁E, hHallE₁E⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE₁₂, hE₁, hE₂, ⟨hE₃E, hHallE₃⟩⟩
  have hJ_E : J ≤ E := by
    simpa [J] using (sup_le hE₁E hE₃E)
  rcases (by simpa [section12PrimeOrderSubgroups, J] using hX) with
    ⟨hX_le_J, q, hXcard⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hX_le_E : X ≤ E := hX_le_J.trans hJ_E
  have hE₃norm : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hEdata).2
  have hE_norm_E₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃norm.1).1 hE₃norm.2
  have hE₁_norm_E₃ : E₁ ≤ Subgroup.normalizer (E₃ : Set G) :=
    hE₁E.trans hE_norm_E₃
  have hE₁π :
      IsPiSubgroup (G := G)
        (section12Tau1Primes M ∪ section12Tau3Primes M) E₁ := by
    intro s hs
    have hcard : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      natCard_subgroupOf_eq E₁ E hE₁E
    exact Or.inl (hHallE₁E.p_in_pi_of_p_dvd_card s
      (by simpa [hcard, subgroupPrimeSet] using hs))
  have hE₃π :
      IsPiSubgroup (G := G)
        (section12Tau1Primes M ∪ section12Tau3Primes M) E₃ := by
    intro s hs
    have hcard : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
      natCard_subgroupOf_eq E₃ E hE₃E
    exact Or.inr (hHallE₃.p_in_pi_of_p_dvd_card s
      (by simpa [hcard, subgroupPrimeSet] using hs))
  have hJπ :
      IsPiSubgroup (G := G)
        (section12Tau1Primes M ∪ section12Tau3Primes M) J := by
    simpa [J] using
      section13_isPiSubgroup_sup_of_le_normalizer
        (G := G) (π := section12Tau1Primes M ∪ section12Tau3Primes M)
        (H := E₁) (K := E₃) hE₁π hE₃π hE₁_norm_E₃
  have hqτ13 : q ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
    have hqX : q.val ∣ Nat.card X := by rw [hXcard]
    exact hJπ q (hqX.trans (Subgroup.card_dvd_of_le hX_le_J))
  rcases hqτ13 with hqτ1 | hqτ3
  · have hJ_le_M : J ≤ M := hJ_E.trans hcomp.2.1
    have hJ_ne_top : J ≠ ⊤ := by
      intro hJtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hJtop] using hJ_le_M
      exact hM.1 (top_le_iff.mp htop_le_M)
    have hJsolv : IsSolvable J :=
      IsMinCE.proper_subgroups_solvable J (lt_top_iff_ne_top.2 hJ_ne_top)
    let XJ : Subgroup J := X.subgroupOf J
    have hXJπ : IsPiSubgroup (G := J) (section12Tau1Primes M) XJ := by
      intro s hs
      have hcard : Nat.card XJ = Nat.card X :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := J) hX_le_J).toEquiv
      have hsX : s.val ∣ Nat.card X := by
        simpa [hcard] using hs
      have hsq : s.val ∣ q.val := by
        simpa [hXcard] using hsX
      have hs_eq_q : s = q :=
        Subtype.ext ((Nat.prime_dvd_prime_iff_eq s.property q.property).mp hsq)
      simpa [hs_eq_q] using hqτ1
    letI : MulDistribMulAction Unit J := {
      smul := fun _ x => x
      one_smul := fun x => rfl
      mul_smul := fun _ _ x => rfl
      smul_mul := fun _ x y => rfl
      smul_one := fun _ => rfl }
    have hXJinv : IsInvariant Unit J XJ := by
      refine ⟨?_⟩
      intro a x
      simp
    rcases exists_isHallSubgroup_isInvariant_of_isPiSubgroup
        (G := J) (A := Unit) hJsolv (by simp)
        (section12Tau1Primes M) XJ hXJπ hXJinv with
      ⟨K, hKHall, _hKinv, hXK⟩
    have hE₁_le_J : E₁ ≤ J := by
      simp [J]
    have hE₁HallJ :
        IsHallSubgroup (section12Tau1Primes M) (E₁.subgroupOf J) := by
      refine isHallSubgroup_of (G := J) (section12Tau1Primes M)
        (E₁.subgroupOf J) ?_ ?_
      · intro s hs
        have hcardJ : Nat.card (E₁.subgroupOf J) = Nat.card E₁ :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := E₁) (K := J) hE₁_le_J).toEquiv
        have hcardE : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (H := E₁) (K := E) hE₁E).toEquiv
        exact hHallE₁E.p_in_pi_of_p_dvd_card s (by simpa [hcardE, hcardJ] using hs)
      · intro s hsτ hsidx
        have hsrelJ : s.val ∣ E₁.relIndex J := by
          simpa [Subgroup.relIndex] using hsidx
        have hrelmul : E₁.relIndex J * J.relIndex E = E₁.relIndex E :=
          Subgroup.relIndex_mul_relIndex E₁ J E hE₁_le_J hJ_E
        have hsrelE : s.val ∣ E₁.relIndex E := by
          rw [← hrelmul]
          exact dvd_mul_of_dvd_left hsrelJ _
        exact (hHallE₁E.p_in_pi_of_p_dvd_index s
          (by simpa [Subgroup.relIndex] using hsrelE)) hsτ
    rcases exists_conj_eq_of_isHallSubgroup_of_solvable
        (G := J) hJsolv (H₁ := K) (H₂ := E₁.subgroupOf J)
        hKHall hE₁HallJ with
      ⟨gJ, hconj⟩
    refine ⟨(gJ : J), gJ.property, Or.inl ?_⟩
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    let xJ : J := ⟨x, hX_le_J hx⟩
    have hxXJ : xJ ∈ XJ := by
      simpa [XJ, Subgroup.mem_subgroupOf, xJ] using hx
    have hxK : xJ ∈ K := hXK hxXJ
    have hxmap : (MulAut.conj gJ) xJ ∈ K.map (MulAut.conj gJ).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨xJ, hxK, rfl⟩
    have hxE₁J : (MulAut.conj gJ) xJ ∈ E₁.subgroupOf J := by
      rw [hconj]
      exact hxmap
    change ((gJ : G) * x * (gJ : G)⁻¹) ∈ E₁
    change (((MulAut.conj gJ) xJ : J) : G) ∈ E₁ at hxE₁J
    simpa [MulAut.conj_apply, xJ] using hxE₁J
  · let XE : Subgroup E := X.subgroupOf E
    have hXEp : IsPGroup q.val XE := by
      have hcard : Nat.card XE = Nat.card X :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := E) hX_le_E).toEquiv
      refine IsPGroup.of_card (p := q.val) (G := XE) (n := 1) ?_
      simpa [pow_one, hcard] using hXcard
    haveI : (E₃.subgroupOf E).Normal := hE₃norm.2
    have hXE_le_E₃ : XE ≤ E₃.subgroupOf E :=
      section13_pSubgroup_le_normal_hall_of_prime_mem
        (R := E) (π := section12Tau3Primes M) (H := E₃.subgroupOf E)
        (A := XE) (p := q) hHallE₃ hqτ3 hXEp
    have hX_le_E₃ : X ≤ E₃ := by
      intro x hx
      let xE : E := ⟨x, hX_le_E hx⟩
      have hxXE : xE ∈ XE := by
        simpa [XE, Subgroup.mem_subgroupOf, xE] using hx
      exact hXE_le_E₃ hxXE
    refine ⟨1, by simp, Or.inr ?_⟩
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hX_le_E₃ hx

private theorem CFSG.section13_lemma_13_7_prime_centralizer_le_join_of_equal_centralizers
    {M E E₁₂ E₁ E₂ E₃ P R X : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁_prime : section13ActsPrimeManner E₁ (section10Msigma M))
    (hE₃_prime : section13ActsPrimeManner E₃ (section10Msigma M))
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hCP_eq_CR :
      subgroupCentralizerIn (section10Msigma M) P =
        subgroupCentralizerIn (section10Msigma M) R)
    (hX : X ∈ section12PrimeOrderSubgroups (E₁ ⊔ E₃)) :
    subgroupCentralizerIn (section10Msigma M) X ≤
      subgroupCentralizerIn (section10Msigma M) (E₁ ⊔ E₃) := by
  classical
  have hJ_norm :
      E₁ ⊔ E₃ ≤ Subgroup.normalizer (section10Msigma M : Set G) :=
    sup_le hE₁_prime.1 hE₃_prime.1
  rcases section13_lemma_13_7_prime_conj_le_E1_or_E3
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (X := X) hM hE hX with
    ⟨g, hgJ, hXg_factor⟩
  have hXg_bound :
      subgroupCentralizerIn (section10Msigma M) (X.conjBy g) ≤
        subgroupCentralizerIn (section10Msigma M) (E₁ ⊔ E₃) := by
    rcases (by simpa [section12PrimeOrderSubgroups] using hX) with
      ⟨_hX_le_join, q, hXcard⟩
    have hXgcard : Nat.card (X.conjBy g) = q.val := by
      rw [section13_card_conjBy, hXcard]
    rcases hXg_factor with hXgE₁ | hXgE₃
    · have hXg_prime : X.conjBy g ∈ section12PrimeOrderSubgroups E₁ := by
        simpa [section12PrimeOrderSubgroups] using ⟨hXgE₁, ⟨q, hXgcard⟩⟩
      exact
        section13_lemma_13_7_centralizer_le_join_of_left_factor
          (G := G) (M := M) (E₁ := E₁) (E₃ := E₃) (P := P)
          (R := R) (X := X.conjBy g) (p := p) (r := r)
          hE₁_prime hE₃_prime hP hR_E₃ hCP_eq_CR hXg_prime
    · have hXg_prime : X.conjBy g ∈ section12PrimeOrderSubgroups E₃ := by
        simpa [section12PrimeOrderSubgroups] using ⟨hXgE₃, ⟨q, hXgcard⟩⟩
      exact
        section13_lemma_13_7_centralizer_le_join_of_right_factor
          (G := G) (M := M) (E₁ := E₁) (E₃ := E₃) (P := P)
          (R := R) (X := X.conjBy g) (p := p) (r := r)
          hE₁_prime hE₃_prime hP hR_E₃ hCP_eq_CR hXg_prime
  exact
    section13_lemma_13_7_centralizer_le_join_of_conj
      (G := G) (M := M) (E₁ := E₁) (E₃ := E₃) (X := X)
      (g := g) hJ_norm hgJ hXg_bound

private theorem CFSG.section13_lemma_13_7_of_equal_centralizers
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁_prime : section13ActsPrimeManner E₁ (section10Msigma M))
    (hE₃_prime : section13ActsPrimeManner E₃ (section10Msigma M))
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hCP_eq_CR :
      subgroupCentralizerIn (section10Msigma M) P =
        subgroupCentralizerIn (section10Msigma M) R) :
    section13ActsPrimeManner (E₁ ⊔ E₃) (section10Msigma M) := by
  refine ⟨sup_le hE₁_prime.1 hE₃_prime.1, ?_⟩
  intro X hX
  exact
    section13_lemma_13_7_prime_centralizer_le_join_of_equal_centralizers
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (X := X)
      (p := p) (r := r) hM hE hE₁_prime hE₃_prime hP hR_E₃
      hCP_eq_CR hX

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_lemma_13_7_CR_ne_bot_of_proper
    {M P R : Subgroup G}
    (hCP_le_CR :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) R)
    (hCP_ne_CR :
      subgroupCentralizerIn (section10Msigma M) P ≠
        subgroupCentralizerIn (section10Msigma M) R) :
    subgroupCentralizerIn (section10Msigma M) R ≠ ⊥ := by
  intro hCRbot
  exact hCP_ne_CR <| le_antisymm hCP_le_CR <| by
    rw [hCRbot]
    exact bot_le

private theorem CFSG.section13_lemma_13_7_tau2_empty_of_proper
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hCP_le_CR :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) R)
    (hCP_ne_CR :
      subgroupCentralizerIn (section10Msigma M) P ≠
        subgroupCentralizerIn (section10Msigma M) R) :
    section12Tau2Primes M = ∅ := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR_E₃) with
    ⟨hR_le_E₃, hRcard⟩
  have hCR_ne :
      subgroupCentralizerIn (section10Msigma M) R ≠ ⊥ :=
    section13_lemma_13_7_CR_ne_bot_of_proper
      (G := G) (M := M) (P := P) (R := R) hCP_le_CR hCP_ne_CR
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hCR_ne with ⟨y, hyne⟩
  have hyCR : (y : G) ∈ subgroupCentralizerIn (section10Msigma M) R := y.property
  have hyneG : (y : G) ≠ 1 := by
    intro hy
    exact hyne (Subtype.ext hy)
  have hR_ne : R ≠ ⊥ :=
    section13_ne_bot_of_prime_order (G := G) (X := R) (q := r) hRcard
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hR_ne with ⟨z, hzne⟩
  have hzE₃ : (z : G) ∈ E₃ := hR_le_E₃ z.property
  have hzneG : (z : G) ≠ 1 := by
    intro hz
    exact hzne (Subtype.ext hz)
  ext q
  constructor
  · intro hqτ2
    rcases section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) hM hE hqτ2 with
      ⟨A, hA⟩
    have hCz_bot :
        elementCentralizerIn (section10Msigma M) (z : G) = ⊥ :=
      corollary_12_6_d
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
        hM hE hqτ2 hA (z : G) hzE₃ hzneG
    have hyCz : (y : G) ∈ elementCentralizerIn (section10Msigma M) (z : G) := by
      refine ⟨hyCR.1, ?_⟩
      change (y : G) ∈ Subgroup.centralizer ({(z : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst t
      exact Subgroup.mem_centralizer_iff.mp hyCR.2 (z : G) z.property
    have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
      simpa [hCz_bot] using hyCz
    exact False.elim <| hyneG (by simpa using hybot)
  · intro hqempty
    cases hqempty

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_E2_eq_bot_of_tau2_empty
    {M E₁₂ E₂ : Subgroup G}
    (hE₂ : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂)
    (hτ2empty : section12Tau2Primes M = ∅) :
    E₂ = ⊥ := by
  classical
  rcases hE₂ with ⟨hE₂E₁₂, hHallE₂⟩
  apply Subgroup.card_eq_one.mp
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  intro q hqprime hqdiv
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hcard_sub : Nat.card (E₂.subgroupOf E₁₂) = Nat.card E₂ :=
    natCard_subgroupOf_eq E₂ E₁₂ hE₂E₁₂
  have hqdiv_sub : q'.val ∣ Nat.card (E₂.subgroupOf E₁₂) := by
    simpa [q', hcard_sub] using hqdiv
  have hqτ2 : q' ∈ section12Tau2Primes M :=
    hHallE₂.p_in_pi_of_p_dvd_card q' hqdiv_sub
  simp [hτ2empty] at hqτ2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_coprime_index_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    Nat.Coprime N.index E.index := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqN hqE
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hq_notπ : q' ∉ π := hN.p_in_pi_of_p_dvd_index q' hqN
  have hq_notπc : q' ∉ πᶜ := hE.p_in_pi_of_p_dvd_index q' hqE
  exact hq_notπ (by
    by_contra hnot
    exact hq_notπc hnot)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_card_eq_index_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    Nat.card E = N.index := by
  have hcopEN : Nat.Coprime (Nat.card E) (Nat.card N) :=
    (section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) (π := πᶜ) (ρ := π) (A := E) (B := N)
      (fun q hq => hE.p_in_pi_of_p_dvd_card q hq)
      (fun q hq => hN.p_in_pi_of_p_dvd_card q hq)
      (by
        rw [Set.disjoint_left]
        intro q hqπc hqπ
        exact hqπc hqπ))
  have hE_dvd_Nidx : Nat.card E ∣ N.index := by
    have hdiv : Nat.card E ∣ Nat.card G := Subgroup.card_subgroup_dvd_card E
    have hdiv' : Nat.card E ∣ N.index * Nat.card N := by
      simpa [Subgroup.index_mul_card (H := N)] using hdiv
    exact hcopEN.dvd_of_dvd_mul_right hdiv'
  have hcopIdx : Nat.Coprime N.index E.index :=
    section13_coprime_index_of_isHall_compl hN hE
  have hNidx_dvd_E : N.index ∣ Nat.card E := by
    have hdiv : N.index ∣ Nat.card G := Subgroup.index_dvd_card (H := N)
    have hdiv' : N.index ∣ Nat.card E * E.index := by
      simpa [Subgroup.index_mul_card (H := E), mul_comm] using hdiv
    exact hcopIdx.dvd_of_dvd_mul_right hdiv'
  exact Nat.dvd_antisymm hE_dvd_Nidx hNidx_dvd_E

omit [IsMinCE G] in
private theorem CFSG.section13_isComplement_of_isHall_compl
    {π : Set Nat.Primes} {N E : Subgroup G}
    (hN : IsHallSubgroup π N) (hE : IsHallSubgroup πᶜ E) :
    N.IsComplement' E := by
  have hcardE : Nat.card E = N.index :=
    section13_card_eq_index_of_isHall_compl hN hE
  have hcard_mul : Nat.card N * Nat.card E = Nat.card G := by
    rw [hcardE, mul_comm]
    exact Subgroup.index_mul_card (H := N)
  exact Subgroup.isComplement'_of_coprime hcard_mul
    (section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) (π := π) (ρ := πᶜ) (A := N) (B := E)
      (fun q hq => hN.p_in_pi_of_p_dvd_card q hq)
      (fun q hq => hE.p_in_pi_of_p_dvd_card q hq)
      (by
        rw [Set.disjoint_left]
        intro q hqπ hqπc
        exact hqπc hqπ))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_section12HallSubgroupIn_map_subtype
    {π : Set Nat.Primes} {H : Subgroup G} {K : Subgroup H}
    (hK : IsHallSubgroup π K) :
    section12HallSubgroupIn π (K.map H.subtype) H := by
  have hKH : K.map H.subtype ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  refine ⟨hKH, ?_⟩
  have hsub_eq : (K.map H.subtype).subgroupOf H = K := by
    ext x
    constructor
    · intro hx
      change ((x : H) : G) ∈ K.map H.subtype at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hy
    · intro hx
      change ((x : H) : G) ∈ K.map H.subtype
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  simpa [hsub_eq] using hK

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_isPiSubgroup_subgroupOf
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hKπ : IsPiSubgroup (G := G) π K) (hKH : K ≤ H) :
    IsPiSubgroup (G := H) π (K.subgroupOf H) := by
  intro p hp
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    natCard_subgroupOf_eq K H hKH
  exact hKπ p (by rwa [hcard] at hp)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_complementToMsigma_of_local_complement
    {M : Subgroup G} {E : Subgroup M}
    (hcomp : (section10MsigmaSubgroup M).IsComplement' E) :
    section12ComplementToMsigma M (E.map M.subtype) := by
  classical
  have hσmap :
      (section10MsigmaSubgroup M).map M.subtype = section10Msigma M := by
    simp [section10Msigma]
  have htop_map : (⊤ : Subgroup M).map M.subtype = M := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by simp, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [← hσmap] at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  · calc
      M = (⊤ : Subgroup M).map M.subtype := htop_map.symm
      _ = (section10MsigmaSubgroup M ⊔ E).map M.subtype := by
        rw [hcomp.sup_eq_top]
      _ = section10Msigma M ⊔ E.map M.subtype := by
        rw [Subgroup.map_sup, hσmap]
  · rw [Subgroup.disjoint_def]
    intro x hxσ hxE
    rw [← hσmap] at hxσ
    rcases Subgroup.mem_map.mp hxσ with ⟨y, hyσ, hyx⟩
    rcases Subgroup.mem_map.mp hxE with ⟨z, hzE, hzx⟩
    have hyz : y = z := Subtype.ext (hyx.trans hzx.symm)
    have hyE : y ∈ E := by
      simpa [hyz] using hzE
    have hybot : y ∈ (⊥ : Subgroup M) := by
      have hinf : section10MsigmaSubgroup M ⊓ E = ⊥ :=
        hcomp.disjoint.eq_bot
      have hyinf : y ∈ section10MsigmaSubgroup M ⊓ E := ⟨hyσ, hyE⟩
      simpa [hinf] using hyinf
    have hyone : y = 1 := by
      simpa using hybot
    calc
      x = (y : M) := hyx.symm
      _ = 1 := by simpa using congrArg (fun t : M => (t : G)) hyone

public theorem CFSG.section13_exists_EData_containing_tau1_piSubgroup
    {M A : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hAM : A ≤ M)
    (hAπ : IsPiSubgroup (G := G) (section12Tau1Primes M) A) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧ A ≤ E₁ := by
  classical
  let A_M : Subgroup M := A.subgroupOf M
  have hAπ_M : IsPiSubgroup (G := M) (section12Tau1Primes M) A_M :=
    section13_isPiSubgroup_subgroupOf hAπ hAM
  have hAσc_M : IsPiSubgroup (G := M) (section10SigmaPrimes M)ᶜ A_M := by
    intro q hqA
    exact (hAπ_M q hqA).1
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hAinv_M : IsInvariant Unit M A_M := by
    refine ⟨?_⟩
    intro _ x
    simp
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcopM : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Eloc, hElocHall, _hElocInv, hA_Eloc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcopM (section10SigmaPrimes M)ᶜ
      A_M hAσc_M hAinv_M
  have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b (G := G) hM).2
  let E : Subgroup G := Eloc.map M.subtype
  have hEcomp : section12ComplementToMsigma M E :=
    section13_complementToMsigma_of_local_complement
      (G := G) (M := M) (E := Eloc)
      (section13_isComplement_of_isHall_compl hσHall hElocHall)
  have hA_E : A ≤ E := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hAM hx⟩, hA_Eloc (by simpa [A_M, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hsolvE : IsSolvable E := by
    have hEproper : E ≠ ⊤ := by
      intro hEtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hEtop] using hEcomp.2.1
      exact hM.1 (top_le_iff.mp htop_le_M)
    exact IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
  letI : MulDistribMulAction Unit E := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let A_E : Subgroup E := A.subgroupOf E
  have hAπ12_E :
      IsPiSubgroup (G := E)
        (section12Tau1Primes M ∪ section12Tau2Primes M) A_E := by
    exact section13_isPiSubgroup_subgroupOf
      (fun q hqA => Or.inl (hAπ q hqA)) hA_E
  have hAinv_E : IsInvariant Unit E A_E := by
    refine ⟨?_⟩
    intro _ x
    simp
  have hcopE : Nat.Coprime (Nat.card Unit) (Nat.card E) := by simp
  obtain ⟨E₁₂loc, hE₁₂Hall, _hE₁₂Inv, hA_E₁₂loc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau1Primes M ∪ section12Tau2Primes M)
      A_E hAπ12_E hAinv_E
  let E₁₂ : Subgroup G := E₁₂loc.map E.subtype
  have hE₁₂HallIn :
      section12HallSubgroupIn
        (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E) (K := E₁₂loc) hE₁₂Hall
  have hA_E₁₂ : A ≤ E₁₂ := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hA_E hx⟩,
        hA_E₁₂loc (by simpa [A_E, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hsolvE₁₂ : IsSolvable E₁₂ := by
    have hE₁₂_le_M : E₁₂ ≤ M := hE₁₂HallIn.1.trans hEcomp.2.1
    have hE₁₂proper : E₁₂ ≠ ⊤ := by
      intro htop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [htop] using hE₁₂_le_M
      exact hM.1 (top_le_iff.mp htop_le_M)
    exact IsMinCE.proper_subgroups_solvable E₁₂ (lt_top_iff_ne_top.2 hE₁₂proper)
  letI : MulDistribMulAction Unit E₁₂ := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  let A_E₁₂ : Subgroup E₁₂ := A.subgroupOf E₁₂
  have hAπ_E₁₂ : IsPiSubgroup (G := E₁₂) (section12Tau1Primes M) A_E₁₂ :=
    section13_isPiSubgroup_subgroupOf hAπ hA_E₁₂
  have hAinv_E₁₂ : IsInvariant Unit E₁₂ A_E₁₂ := by
    refine ⟨?_⟩
    intro _ x
    simp
  have hcopE₁₂ : Nat.Coprime (Nat.card Unit) (Nat.card E₁₂) := by simp
  obtain ⟨E₁loc, hE₁Hall, _hE₁Inv, hA_E₁loc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau1Primes M) A_E₁₂ hAπ_E₁₂ hAinv_E₁₂
  let E₁ : Subgroup G := E₁loc.map E₁₂.subtype
  have hE₁HallIn : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E₁₂) (K := E₁loc) hE₁Hall
  have hA_E₁ : A ≤ E₁ := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hA_E₁₂ hx⟩,
        hA_E₁loc (by simpa [A_E₁₂, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hbotτ2 : IsPiSubgroup (G := E₁₂) (section12Tau2Primes M) (⊥ : Subgroup E₁₂) := by
    intro q hq
    exact False.elim (q.property.not_dvd_one (by simpa using hq))
  have hbotInv_E₁₂ : IsInvariant Unit E₁₂ (⊥ : Subgroup E₁₂) := by
    refine ⟨?_⟩
    intro _ x
    simp
  obtain ⟨E₂loc, hE₂Hall, _hE₂Inv, _hbot_E₂loc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau2Primes M) (⊥ : Subgroup E₁₂) hbotτ2 hbotInv_E₁₂
  let E₂ : Subgroup G := E₂loc.map E₁₂.subtype
  have hE₂HallIn : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂ :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E₁₂) (K := E₂loc) hE₂Hall
  have hbotτ3 : IsPiSubgroup (G := E) (section12Tau3Primes M) (⊥ : Subgroup E) := by
    intro q hq
    exact False.elim (q.property.not_dvd_one (by simpa using hq))
  have hbotInv_E : IsInvariant Unit E (⊥ : Subgroup E) := by
    refine ⟨?_⟩
    intro _ x
    simp
  obtain ⟨E₃loc, hE₃Hall, _hE₃Inv, _hbot_E₃loc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau3Primes M) (⊥ : Subgroup E) hbotτ3 hbotInv_E
  let E₃ : Subgroup G := E₃loc.map E.subtype
  have hE₃HallIn : section12HallSubgroupIn (section12Tau3Primes M) E₃ E :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E) (K := E₃loc) hE₃Hall
  exact ⟨E, E₁₂, E₁, E₂, E₃,
    ⟨hEcomp, hE₁₂HallIn, hE₁HallIn, hE₂HallIn, hE₃HallIn⟩, hA_E₁⟩

public theorem CFSG.section13_exists_EData_containing_sigma_compl_piSubgroup
    {M A : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hAM : A ≤ M)
    (hAπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A) :
    ∃ E E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ ∧ A ≤ E := by
  classical
  let A_M : Subgroup M := A.subgroupOf M
  have hAπ_M : IsPiSubgroup (G := M) (section10SigmaPrimes M)ᶜ A_M :=
    section13_isPiSubgroup_subgroupOf hAπ hAM
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hAinv_M : IsInvariant Unit M A_M := by
    refine ⟨?_⟩
    intro _ x
    simp
  have hsolvM : IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.mpr hM.1)
  have hcopM : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  obtain ⟨Eloc, hElocHall, _hElocInv, hA_Eloc⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := M) (A := Unit) hsolvM hcopM (section10SigmaPrimes M)ᶜ
      A_M hAπ_M hAinv_M
  have hσHall : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) :=
    (theorem_10_2_b (G := G) hM).2
  let E : Subgroup G := Eloc.map M.subtype
  have hEcomp : section12ComplementToMsigma M E :=
    section13_complementToMsigma_of_local_complement
      (G := G) (M := M) (E := Eloc)
      (section13_isComplement_of_isHall_compl hσHall hElocHall)
  have hA_E : A ≤ E := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hAM hx⟩, hA_Eloc (by simpa [A_M, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hsolvE : IsSolvable E := by
    have hEproper : E ≠ ⊤ := by
      intro hEtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hEtop] using hEcomp.2.1
      exact hM.1 (top_le_iff.mp htop_le_M)
    exact IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
  letI : MulDistribMulAction Unit E := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcopE : Nat.Coprime (Nat.card Unit) (Nat.card E) := by simp
  obtain ⟨E₁₂loc, hE₁₂Hall, _hE₁₂Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau1Primes M ∪ section12Tau2Primes M)
  let E₁₂ : Subgroup G := E₁₂loc.map E.subtype
  have hE₁₂HallIn :
      section12HallSubgroupIn
        (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E) (K := E₁₂loc) hE₁₂Hall
  have hsolvE₁₂ : IsSolvable E₁₂ := by
    have hE₁₂_le_M : E₁₂ ≤ M := hE₁₂HallIn.1.trans hEcomp.2.1
    have hE₁₂proper : E₁₂ ≠ ⊤ := by
      intro htop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [htop] using hE₁₂_le_M
      exact hM.1 (top_le_iff.mp htop_le_M)
    exact IsMinCE.proper_subgroups_solvable E₁₂ (lt_top_iff_ne_top.2 hE₁₂proper)
  letI : MulDistribMulAction Unit E₁₂ := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcopE₁₂ : Nat.Coprime (Nat.card Unit) (Nat.card E₁₂) := by simp
  obtain ⟨E₁loc, hE₁Hall, _hE₁Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau1Primes M)
  let E₁ : Subgroup G := E₁loc.map E₁₂.subtype
  have hE₁HallIn : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E₁₂) (K := E₁loc) hE₁Hall
  obtain ⟨E₂loc, hE₂Hall, _hE₂Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E₁₂) (A := Unit) hsolvE₁₂ hcopE₁₂
      (section12Tau2Primes M)
  let E₂ : Subgroup G := E₂loc.map E₁₂.subtype
  have hE₂HallIn : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂ :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E₁₂) (K := E₂loc) hE₂Hall
  obtain ⟨E₃loc, hE₃Hall, _hE₃Inv⟩ :=
    exists_isHallSubgroup_isInvariant
      (G := E) (A := Unit) hsolvE hcopE
      (section12Tau3Primes M)
  let E₃ : Subgroup G := E₃loc.map E.subtype
  have hE₃HallIn : section12HallSubgroupIn (section12Tau3Primes M) E₃ E :=
    section13_section12HallSubgroupIn_map_subtype
      (G := G) (H := E) (K := E₃loc) hE₃Hall
  exact ⟨E, E₁₂, E₁, E₂, E₃,
    ⟨hEcomp, hE₁₂HallIn, hE₁HallIn, hE₂HallIn, hE₃HallIn⟩, hA_E⟩

omit [IsMinCE G] in
private theorem CFSG.section13_subgroupCentralizerIn_actor_eq_bot_of_prime_manner
    {H A K : Subgroup G}
    (hA_prime : section13ActsPrimeManner A H)
    (hK_le_H : K ≤ H)
    (hcomm : ⁅K, A⁆ ≠ ⊥) :
    subgroupCentralizerIn A K = ⊥ := by
  classical
  by_contra hCne
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := subgroupCentralizerIn A K) hCne with
    ⟨q, X, hXleC, hXcard⟩
  have hXprimeA : X ∈ section12PrimeOrderSubgroups A := by
    have hXA : X ≤ A := hXleC.trans inf_le_left
    simpa [section12PrimeOrderSubgroups] using ⟨hXA, ⟨q, hXcard⟩⟩
  have hX_cent_K : X ≤ Subgroup.centralizer (K : Set G) :=
    hXleC.trans inf_le_right
  have hK_cent_X : K ≤ Subgroup.centralizer (X : Set G) :=
    (Subgroup.le_centralizer_iff (H := X) (K := K)).mp hX_cent_K
  have hK_le_CX : K ≤ subgroupCentralizerIn H X := by
    intro x hx
    exact ⟨hK_le_H hx, hK_cent_X hx⟩
  have hK_le_CA : K ≤ subgroupCentralizerIn H A :=
    hK_le_CX.trans (hA_prime.2 X hXprimeA)
  have hK_cent_A : K ≤ Subgroup.centralizer (A : Set G) :=
    fun x hx => (hK_le_CA hx).2
  exact hcomm ((Subgroup.commutator_eq_bot_iff_le_centralizer).2 hK_cent_A)

private theorem CFSG.section13_lemma_13_7_proper_centralizer_absurd
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hR_CEP : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P))
    (hCP_le_CR :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) R)
    (hCP_ne_CR :
      subgroupCentralizerIn (section10Msigma M) P ≠
        subgroupCentralizerIn (section10Msigma M) R) :
    False := by
  classical
  have hτ2empty : section12Tau2Primes M = ∅ :=
    section13_lemma_13_7_tau2_empty_of_proper
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (r := r)
      hM hE hR_E₃ hCP_le_CR hCP_ne_CR
  have hE₂bot : E₂ = ⊥ :=
    section13_E2_eq_bot_of_tau2_empty
      (G := G) (M := M) (E₁₂ := E₁₂) (E₂ := E₂) hE.2.2.2.1 hτ2empty
  have hE_eq : E = E₁ ⊔ E₃ := by
    have hEfull : E = E₁ ⊔ E₂ ⊔ E₃ :=
      (lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
    calc
      E = E₁ ⊔ E₂ ⊔ E₃ := hEfull
      _ = E₁ ⊔ E₃ := by
        rw [hE₂bot]
        simp
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR_E₃) with
    ⟨hR_E₃_le, hRcard⟩
  have hE₁E : E₁ ≤ E :=
    (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  have hE₃E : E₃ ≤ E := hE.2.2.2.2.1
  have hP_E : P ≤ E := hP_E₁.trans hE₁E
  have hP_M : P ≤ M := hP_E.trans hE.1.2.1
  have hR_E : R ≤ E := hR_E₃_le.trans hE₃E
  have hR_M : R ≤ M := hR_E.trans hE.1.2.1
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hRp : IsPGroup r.val R := by
    refine IsPGroup.of_card (p := r.val) (G := R) (n := 1) ?_
    simpa [pow_one] using hRcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hR_ne : R ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hRcard
  have hpτ1 : p ∈ section12Tau1Primes M :=
    section13_tau1_of_prime_order_le_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hE hP
  have hrτ3 : r ∈ section12Tau3Primes M :=
    section13_tau3_of_prime_order_le_E3
      (G := G) (M := M) (E := E) (E₃ := E₃) (X := R) (q := r)
      hE.2.2.2.2 hR_E₃_le hRcard
  have hE₁_prime : section13ActsPrimeManner E₁ (section10Msigma M) :=
    theorem_13_5 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₁ne
  let CR : Subgroup G := subgroupCentralizerIn (section10Msigma M) R
  have hCR_not_centP : ¬ CR ≤ Subgroup.centralizer (P : Set G) := by
    intro hCR_centP
    have hCR_le_CP :
        CR ≤ subgroupCentralizerIn (section10Msigma M) P := by
      intro x hx
      exact ⟨hx.1, hCR_centP hx⟩
    exact hCP_ne_CR (le_antisymm hCP_le_CR hCR_le_CP)
  have hCRP_ne : ⁅CR, P⁆ ≠ ⊥ := by
    intro hcomm
    exact hCR_not_centP
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm)
  have hE₃cyc : IsCyclic E₃ := (lemma_12_1_d hM hE).2
  have hE₃norm : section10NormalIn E₃ E := (lemma_12_1_b hM hE).2
  have hE_le_normR : E ≤ Subgroup.normalizer (R : Set G) :=
    section13_le_normalizer_of_le_cyclic_normal
      (G := G) hR_E₃_le hE₃cyc hE₃norm
  have hnormR_ne_top : Subgroup.normalizer (R : Set G) ≠ ⊤ :=
    section13_normalizer_ne_top_of_ne_bot_le_maximal hM hR_M hR_ne
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hnormR_ne_top with
    ⟨Mstar, hMstar⟩
  have hE_le_Mstar : E ≤ Mstar := hE_le_normR.trans hMstar.2
  have hE₁_le_Mstar : E₁ ≤ Mstar := hE₁E.trans hE_le_Mstar
  have hP_le_Mstar : P ≤ Mstar := hP_E.trans hE_le_Mstar
  have hR_le_Mstar : R ≤ Mstar :=
    Subgroup.le_normalizer.trans hMstar.2
  let K : Subgroup G := section10Msigma M ⊓ Mstar
  have hCR_le_K : CR ≤ K := by
    intro x hx
    exact ⟨hx.1, hMstar.2 ((centralizer_le_normalizer R) hx.2)⟩
  have hP_le_E₁ : P ≤ E₁ := hP_E₁
  have hCRP_le_KE₁ : ⁅CR, P⁆ ≤ ⁅K, E₁⁆ :=
    Subgroup.commutator_mono hCR_le_K hP_le_E₁
  have hKE₁_ne : ⁅K, E₁⁆ ≠ ⊥ := by
    intro hKE₁
    exact hCRP_ne (le_bot_iff.mp (by
      rw [← hKE₁]
      exact hCRP_le_KE₁))
  have hCE₁K_bot : subgroupCentralizerIn E₁ K = ⊥ :=
    section13_subgroupCentralizerIn_actor_eq_bot_of_prime_manner
      (G := G) (H := section10Msigma M) (A := E₁) (K := K)
      hE₁_prime inf_le_left hKE₁_ne
  have hbig :
      ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := by
    intro hbigbot
    apply hKE₁_ne
    apply le_bot_iff.mp
    rw [← hbigbot]
    have hE₁_le_Minf : E₁ ≤ M ⊓ Mstar := by
      intro x hx
      exact ⟨hE₁E.trans hE.1.2.1 hx, hE₁_le_Mstar hx⟩
    exact Subgroup.commutator_mono le_rfl hE₁_le_Minf
  have hrσstar : r ∈ section10SigmaPrimes Mstar :=
    (corollary_13_2_c (G := G) hM hE (Or.inr hrτ3)
      hRp hR_ne hR_M hMstar hbig).1
  have hE₁πstar : IsPiSubgroup (G := G) (section12Tau1Primes Mstar) E₁ := by
    intro q hqE₁
    by_contra hqτ1star
    haveI : Fact q.val.Prime := ⟨q.property⟩
    let S : Sylow q.val E₁ := default
    have hSne : (S : Subgroup E₁) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := E₁) S hqE₁
    rcases section13_exists_prime_order_subgroup_le_ambient_sylow
        (G := G) (A := E₁) S hSne with
      ⟨X, hX_le_S, hXcard⟩
    have hX_E₁ : X ≤ E₁ :=
      hX_le_S.trans (section13_ambient_sylow_le_base (G := G) E₁ S)
    have hXq : IsPGroup q.val X := by
      refine IsPGroup.of_card (p := q.val) (G := X) (n := 1) ?_
      simpa [pow_one] using hXcard
    have hXne : X ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hXcard
    have hX_inf : X ≤ E ⊓ Mstar := by
      intro x hx
      exact ⟨hX_E₁.trans hE₁E hx, hX_E₁.trans hE₁_le_Mstar hx⟩
    have hXπc : IsPiSubgroup (G := G) (section12Tau1Primes Mstar)ᶜ X :=
      section13_isPiSubgroup_compl_of_isPGroup_not_mem hqτ1star hXq
    have hX_cent_K : X ≤ Subgroup.centralizer (K : Set G) := by
      simpa [K] using
        corollary_13_2_b (G := G) hM hE (Or.inr hrτ3)
          hRp hR_ne hR_M hMstar X hX_inf hXπc
    have hX_le_CE₁K : X ≤ subgroupCentralizerIn E₁ K := by
      intro x hx
      exact ⟨hX_E₁ hx, hX_cent_K hx⟩
    have hXbot : X = ⊥ := by
      apply le_bot_iff.mp
      rw [← hCE₁K_bot]
      exact hX_le_CE₁K
    exact hXne hXbot
  rcases section13_exists_EData_containing_tau1_piSubgroup
      (G := G) (M := Mstar) (A := E₁) hMstar.1 hE₁_le_Mstar hE₁πstar with
    ⟨Estar, E₁₂star, E₁star, E₂star, E₃star, hEstar, hE₁_le_E₁star⟩
  have hE₁star_ne : E₁star ≠ ⊥ := by
    intro hbot
    have hE₁bot : E₁ = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      simpa [hbot] using hE₁_le_E₁star hx
    exact hE₁ne hE₁bot
  have hE₁star_prime :
      section13ActsPrimeManner E₁star (section10Msigma Mstar) :=
    theorem_13_5 (G := G) (M := Mstar) (E := Estar) (E₁₂ := E₁₂star)
      (E₁ := E₁star) (E₂ := E₂star) (E₃ := E₃star)
      hMstar.1 hEstar hE₁star_ne
  have hRsub_p : IsPGroup r.val (R.subgroupOf Mstar) :=
    hRp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := R) (K := Mstar) hR_le_Mstar).symm
  have hRsub_le_sigma :
      R.subgroupOf Mstar ≤ section10MsigmaSubgroup Mstar :=
    section13_pSubgroup_le_normal_hall_of_prime_mem
      (R := Mstar) (π := section10SigmaPrimes Mstar)
      (H := section10MsigmaSubgroup Mstar) (A := R.subgroupOf Mstar)
      ((theorem_10_2_b (G := G) hMstar.1).2) hrσstar hRsub_p
  have hR_le_msigma_star : R ≤ section10Msigma Mstar := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hR_le_Mstar hx⟩,
        hRsub_le_sigma (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hR_cent_P : R ≤ Subgroup.centralizer (P : Set G) :=
    (by
      rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR_CEP) with
        ⟨hR_CEP_le, _hRcard'⟩
      exact hR_CEP_le.trans inf_le_right)
  have hPprime_E₁star : P ∈ section12PrimeOrderSubgroups E₁star := by
    simpa [section12PrimeOrderSubgroups] using
      ⟨hP_E₁.trans hE₁_le_E₁star, ⟨p, hPcard⟩⟩
  have hR_le_CstarP : R ≤ subgroupCentralizerIn (section10Msigma Mstar) P := by
    intro x hx
    exact ⟨hR_le_msigma_star hx, hR_cent_P hx⟩
  have hR_le_CstarE₁ :
      R ≤ subgroupCentralizerIn (section10Msigma Mstar) E₁star :=
    hR_le_CstarP.trans (hE₁star_prime.2 P hPprime_E₁star)
  have hR_cent_E₁ : R ≤ Subgroup.centralizer (E₁ : Set G) := by
    intro x hx
    exact Subgroup.centralizer_le
      (show (E₁ : Set G) ⊆ (E₁star : Set G) from hE₁_le_E₁star)
      (hR_le_CstarE₁ hx).2
  have hR_cent_E₃ : R ≤ Subgroup.centralizer (E₃ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    haveI : IsCyclic E₃ := hE₃cyc
    exact setLike_mul_comm (s := E₃)
      hy (hR_E₃_le hx)
  have hR_cent_E : R ≤ Subgroup.centralizer (E : Set G) := by
    intro x hx
    have hx_join : x ∈ Subgroup.centralizer ((E₁ ⊔ E₃ : Subgroup G) : Set G) := by
      rw [section13_centralizer_sup_eq_inf]
      exact ⟨hR_cent_E₁ hx, hR_cent_E₃ hx⟩
    simpa [hE_eq] using hx_join
  have hR_le_CE₃E : R ≤ subgroupCentralizerIn E₃ E := by
    intro x hx
    exact ⟨hR_E₃_le hx, hR_cent_E hx⟩
  have hRbot : R = ⊥ := by
    apply le_bot_iff.mp
    rw [← lemma_12_1_f (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE]
    exact hR_le_CE₃E
  exact hR_ne hRbot

public theorem CFSG.section13_lemma_13_7_core
    {M E E₁₂ E₁ E₂ E₃ P R : Subgroup G} {p r : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hE₁ne : E₁ ≠ ⊥)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hR_E₃ : R ∈ section10PrimeOrderSubgroupsIn r E₃)
    (hR_CEP : R ∈ section10PrimeOrderSubgroupsIn r (subgroupCentralizerIn E P)) :
    section13ActsPrimeManner (E₁ ⊔ E₃) (section10Msigma M) := by
  classical
  rcases hE with ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases section12_E1_hall_in_E (G := G) hE₁₂ hE₁ with
    ⟨hE₁E, _hHallE₁E⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE₁₂, hE₁, hE₂, hE₃⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hR_CEP) with
    ⟨hR_CEP_le, hRcard⟩
  have hP_E : P ∈ section10PrimeOrderSubgroupsIn p E := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hP_E₁.trans hE₁E, hPcard⟩
  have hpτ1 : p ∈ section12Tau1Primes M :=
    section13_tau1_of_prime_order_le_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hEdata hP
  have hrE : r ∈ subgroupPrimeSet E := by
    have hrR : r.val ∣ Nat.card R := by
      rw [hRcard]
    have hR_le_E : R ≤ E := hR_CEP_le.trans inf_le_left
    exact hrR.trans (Subgroup.card_dvd_of_le hR_le_E)
  have hCP_le_CR :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) R :=
    theorem_13_4 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (R := R)
      (p := p) (r := r) hM hEdata hpτ1 hP_E hrE hR_CEP
  have hE₁_prime :
      section13ActsPrimeManner E₁ (section10Msigma M) :=
    theorem_13_5 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hEdata hE₁ne
  have hE₃_prime :
      section13ActsPrimeManner E₃ (section10Msigma M) :=
    corollary_13_3_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hEdata
  by_cases hCP_eq_CR :
      subgroupCentralizerIn (section10Msigma M) P =
        subgroupCentralizerIn (section10Msigma M) R
  · exact
      section13_lemma_13_7_of_equal_centralizers
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (p := p) (r := r)
        hM hEdata hE₁_prime hE₃_prime hP hR_E₃ hCP_eq_CR
  · exact False.elim <|
      section13_lemma_13_7_proper_centralizer_absurd
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (R := R) (p := p) (r := r)
        hM hEdata hE₁ne hP hR_E₃ hR_CEP hCP_le_CR hCP_eq_CR

/-- Lemma 13.6: for `1 < P ≤ E₁`, `q ∈ σ(M)`,
`X ∈ 𝓔_q^1(C_{M_σ}(P))`, and `S ∈ Syl_q(M_σ)`, both
`𝓜(C_G(X))` and `𝓜(S)` equal `{M}`. -/
public theorem CFSG.lemma_13_6
    {M E E₁₂ E₁ E₂ E₃ P X : Subgroup G} {q : Nat.Primes}
    (S : Sylow q.val (section10Msigma M))
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hPne : P ≠ ⊥) (hPE₁ : P ≤ E₁)
    (hqσ : q ∈ section10SigmaPrimes M)
    (hX : X ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) P)) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      section9MaximalSubgroupsContaining
        (section10AmbientSylowSubgroup (section10Msigma M) S) = {M} := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXleCP, hXcard⟩
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hX_M : X ∈ section10PrimeOrderSubgroupsIn q M := by
    have hX_le_Msigma : X ≤ section10Msigma M := hXleCP.trans inf_le_left
    simpa [section10PrimeOrderSubgroupsIn] using
      ⟨hX_le_Msigma.trans hMsigma_le_M, hXcard⟩
  exact corollary_12_14 (G := G) (M := M) (X := X) (p := q) S
    hM hqσ hX_M
    (section13_lemma_13_6_cor12_14_hyp
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (X := X) (q := q)
      hM hE hPne hPE₁ hqσ hX)

end Section13
