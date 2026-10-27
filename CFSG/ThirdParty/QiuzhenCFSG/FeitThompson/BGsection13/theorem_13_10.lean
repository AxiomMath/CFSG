module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.theorem_13_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 13 10 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
/-- Core source step for Theorem 13.10(a,c): the noncentral action of `P ≤ E₁`
on `E₃` gives nontrivial `M_α` fixed points. -/
private theorem CFSG.section13_theorem_13_10_exists_regular_tau3_sylow
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hPnotCentE₃ : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    ∃ q : Nat.Primes, ∃ Q : Subgroup G,
      q ∈ section12Tau3Primes M ∧
        section12SylowSubgroupIn q Q M ∧
          Q ≤ E₃ ∧
            P ≤ Subgroup.normalizer (Q : Set G) ∧
              subgroupCentralizerIn Q P = ⊥ ∧
                Q ≠ ⊥ ∧ IsPGroup q.val Q := by
  classical
  rcases hE with ⟨hcomp, hE12, hE1, hE2, hE3Hall⟩
  rcases hE3Hall with ⟨hE3E, hHallE₃⟩
  have hEdata : section12EData M E E₁₂ E₁ E₂ E₃ :=
    ⟨hcomp, hE12, hE1, hE2, ⟨hE3E, hHallE₃⟩⟩
  have hE3cyc : IsCyclic E₃ := (lemma_12_1_d hM hEdata).2
  have hE3norm : section10NormalIn E₃ E := (lemma_12_1_b hM hEdata).2
  have hE_le_N3 : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    section13_le_normalizer_of_le_cyclic_normal
      (G := G) (E := E) (E₃ := E₃) (X := E₃) le_rfl hE3cyc hE3norm
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  have hE₁_le_E : E₁ ≤ E := (section12_E1_hall_in_E (G := G) hE12 hE1).1
  have hpτ1 : p ∈ section12Tau1Primes M :=
    section13_tau1_of_prime_order_le_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) hEdata hP
  have hP_le_E : P ≤ E := hP_E₁.trans hE₁_le_E
  have hnoncent_exists :
      ∃ q : Nat.Primes, q ∈ subgroupPrimeSet E₃ ∧
        ∃ S : Sylow q.val E₃,
          ¬ P ≤ Subgroup.centralizer (section10AmbientSylowSubgroup E₃ S : Set G) := by
    by_contra hnone
    have hcent_all : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet E₃ →
        ∀ S : Sylow q.val E₃,
          P ≤ Subgroup.centralizer (section10AmbientSylowSubgroup E₃ S : Set G) := by
      intro q hqE3 S
      by_contra hnot
      exact hnone ⟨q, hqE3, ⟨S, hnot⟩⟩
    have hSylowCent : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet E₃ →
        ∃ S : Sylow q.val E₃,
          (section10AmbientSylowSubgroup E₃ S : Subgroup G) ≤
            Subgroup.centralizer (P : Set G) := by
      intro q hqE3
      let S : Sylow q.val E₃ := Classical.choice (Sylow.nonempty (p := q.val) (G := E₃))
      refine ⟨S, ?_⟩
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      have hyCentQ :
          y ∈ Subgroup.centralizer (section10AmbientSylowSubgroup E₃ S : Set G) :=
        hcent_all q hqE3 S hyP
      exact (Subgroup.mem_centralizer_iff.mp hyCentQ x hx).symm
    have hE₃_le_centP : E₃ ≤ Subgroup.centralizer (P : Set G) :=
      section13_le_centralizer_of_exists_sylow_images
        (G := G) (K := P) (X := E₃) hSylowCent
    have hP_cent_E₃ : P ≤ Subgroup.centralizer (E₃ : Set G) :=
      (Subgroup.le_centralizer_iff (H := E₃) (K := P)).mp hE₃_le_centP
    exact hPnotCentE₃ hP_cent_E₃
  rcases hnoncent_exists with ⟨q, hqE₃, S, hnotCent⟩
  have hqτ3 : q ∈ section12Tau3Primes M := by
    have hcardE3sub : Nat.card (E₃.subgroupOf E) = Nat.card E₃ := by
      exact natCard_subgroupOf_eq E₃ E hE3E
    exact hHallE₃.p_in_pi_of_p_dvd_card q (by
      simpa [hcardE3sub, subgroupPrimeSet] using hqE₃)
  have hQbot : (section10AmbientSylowSubgroup E₃ S : Subgroup G) ≠ ⊥ := by
    intro hbot
    haveI : Fact q.val.Prime := ⟨q.property⟩
    have hSbot : (S : Subgroup E₃) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (S : Subgroup E₃)) (f := E₃.subtype) E₃.subtype_injective).mp
        (by simpa [section10AmbientSylowSubgroup] using hbot)
    exact (Sylow.ne_bot_of_dvd_card (G := E₃) S (by
      simpa [subgroupPrimeSet] using hqE₃)) hSbot
  have hQ_E3 : (section10AmbientSylowSubgroup E₃ S : Subgroup G) ≤ E₃ :=
    section13_ambient_sylow_le_base (G := G) E₃ S
  have hQcyc : IsCyclic (section10AmbientSylowSubgroup E₃ S) := by
    letI : IsCyclic E₃ := hE3cyc
    exact Subgroup.isCyclic_of_le hQ_E3
  have hQq : IsPGroup q.val (section10AmbientSylowSubgroup E₃ S : Subgroup G) := by
    change IsPGroup q.val ((S : Subgroup E₃).map E₃.subtype)
    exact IsPGroup.map (p := q.val) (H := (S : Subgroup E₃))
      S.isPGroup' E₃.subtype
  have hE3_sylow_E :
      ∃ T : Sylow q.val E,
        section10AmbientSylowSubgroup E T = section10AmbientSylowSubgroup E₃ S := by
    exact section13_E3_sylow_as_E_sylow (G := G) (M := M) (E := E) (E₃ := E₃)
      ⟨hE3E, hHallE₃⟩ hqτ3 S
  rcases hE3_sylow_E with ⟨T, hTEq⟩
  have hQM : section12SylowSubgroupIn q (section10AmbientSylowSubgroup E₃ S) M := by
    have hTM : section12SylowSubgroupIn q (section10AmbientSylowSubgroup E T) M :=
      section13_E_sylowSubgroupIn_M_of_sigma_compl
        (G := G) (M := M) (E := E) (q := q) hM hcomp hqτ3.1 T
    simpa [hTEq] using hTM
  have hPnormQ :
      P ≤ Subgroup.normalizer
        ((section10AmbientSylowSubgroup E₃ S : Subgroup G) : Set G) := by
    exact hP_le_E.trans (section13_le_normalizer_of_le_cyclic_normal
      (G := G) (E := E) (E₃ := E₃)
      (X := section10AmbientSylowSubgroup E₃ S) hQ_E3 hE3cyc hE3norm)
  have hPp : IsPGroup p.val P :=
    section13_primeOrderSubgroupsIn_isPGroup (G := G) hP
  have hPπ : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) P :=
    section8_isPiSubgroup_singleton_of_isPGroup hPp
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)
      (section10AmbientSylowSubgroup E₃ S) :=
    section8_isPiSubgroup_singleton_of_isPGroup hQq
  have hdis_pq : Disjoint ({p} : Set Nat.Primes) ({q} : Set Nat.Primes) := by
    rw [Set.disjoint_left]
    intro r hrp hrq
    have hrp_eq : r = p := by simpa using hrp
    have hrq_eq : r = q := by simpa using hrq
    have hqp : q = p := hrq_eq.symm.trans hrp_eq
    exact hpτ1.2.1 (by simpa [hqp] using hqτ3.2.1)
  have hcop : Nat.Coprime (Nat.card (section10AmbientSylowSubgroup E₃ S))
      (Nat.card P) :=
    section13_coprime_card_of_isPiSubgroup_disjoint_primes
      (G := G) hQπ hPπ hdis_pq.symm
  have hCQ : subgroupCentralizerIn (section10AmbientSylowSubgroup E₃ S) P = ⊥ :=
    section13_subgroupCentralizerIn_eq_bot_of_cyclic_pgroup_noncentral
      (G := G) (P := P)
      (Q := section10AmbientSylowSubgroup E₃ S) (q := q) hQq hQcyc hPnormQ hcop hnotCent
  exact ⟨q, section10AmbientSylowSubgroup E₃ S, hqτ3, hQM, hQ_E3, hPnormQ, hCQ, hQbot, hQq⟩


private theorem CFSG.section13_theorem_13_10_initial_lemma_13_8_side
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hPnotCentE₃ : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    ∃ Mstar Q : Subgroup G, ∃ q : Nat.Primes,
      Mstar ∈ section9MaximalSubgroups G ∧
        section12NotConjugate Mstar M ∧
          q ∈ section12Tau3Primes M ∧
            p ∈ section12Tau1Primes M ∧
              P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar) ∧
                section12SylowSubgroupIn q Q (M ⊓ Mstar) ∧
                  Q ≤ E₃ ∧
                    P ≤ Subgroup.normalizer (Q : Set G) ∧
                      subgroupCentralizerIn Q P = ⊥ ∧
                        subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥ ∧
                          Subgroup.normalizer (Q : Set G) ≤ Mstar := by
  classical
  rcases section13_theorem_13_10_exists_regular_tau3_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (p := p)
      hM hE hP hPnotCentE₃ with
    ⟨q, Q, hqτ3, hQ_M, hQ_E₃, hPnormQ, hCQ, hQne, hQq⟩
  have hpτ1 : p ∈ section12Tau1Primes M :=
    section13_tau1_of_prime_order_le_E1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) hE hP
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  have hE₁_le_E : E₁ ≤ E :=
    (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  have hP_M : P ≤ M := hP_E₁.trans (hE₁_le_E.trans hE.1.2.1)
  have hQ_le_M : Q ≤ M := section13_sylowSubgroupIn_le (G := G) hQ_M
  have hNproper : Subgroup.normalizer (Q : Set G) ≠ ⊤ :=
    section13_normalizer_ne_top_of_ne_bot_le_maximal hM hQ_le_M hQne
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hNproper with
    ⟨Mstar, hMstar⟩
  have hnotconj : section12NotConjugate Mstar M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := Mstar)
      (X := Q) (p := q) hM hQq hQne hQ_le_M hMstar
      (Or.inr (Or.inr hqτ3))
  have hP_Mstar : P ≤ Mstar := hPnormQ.trans hMstar.2
  have hPinf : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar) := by
    simpa [section10PrimeOrderSubgroupsIn] using
      ⟨⟨hP_M, hP_Mstar⟩, hPcard⟩
  have hP_M_prime : P ∈ section10PrimeOrderSubgroupsIn p M :=
    section13_primeOrderSubgroupsIn_mono (G := G) hPinf inf_le_left
  have hQ_le_Mstar : Q ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
  have hQ_le_inf : Q ≤ M ⊓ Mstar := le_inf hQ_le_M hQ_le_Mstar
  have hQinf : section12SylowSubgroupIn q Q (M ⊓ Mstar) :=
    section13_sylowSubgroupIn_of_overgroup_sylow_with_pgroups_le
      (G := G) (C := M) (L := M ⊓ Mstar) (Q := Q) (q := q)
      hQ_M hQ_le_inf (by
        intro Y hYle _hYq
        exact hYle.trans inf_le_left)
  have hqP : q ∈ section10PPrimeSet p :=
    section13_pPrimeSet_of_fixedpoint_free_sylow
      (G := G) (P := P) (Q := Q) (H := M ⊓ Mstar)
      hPinf hQq hQne hPnormQ hCQ
  have hnotUnique :
      section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} :=
    section13_notUnique_of_crossed_normalizer
      (G := G) (M := M) (Mstar := Mstar) (Q := Q)
      hMstar.1 hnotconj hMstar.2
  have h18 :=
    lemma_12_18_b (G := G) (M := M) (P := P) (Q := Q)
      (p := p) (q := q) hM hpτ1 hP_M_prime hqP hQ_le_M hQne hQq
      hPnormQ hCQ hnotUnique hQ_M
  exact ⟨Mstar, Q, q, hMstar.1, hnotconj, hqτ3, hpτ1, hPinf, hQinf,
    hQ_E₃, hPnormQ, hCQ, h18.2.2.2.2, hMstar.2⟩

private theorem CFSG.section13_theorem_13_10_nonregular_centralizer_prime
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    ∃ qstar : Nat.Primes,
      qstar ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) E₃) ∧
        qstar ∈ section10SigmaPrimes M := by
  classical
  have hprime :
      section13ActsPrimeManner E₃ (section10Msigma M) :=
    corollary_13_3_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hCne : subgroupCentralizerIn (section10Msigma M) E₃ ≠ ⊥ :=
    section13_centralizer_ne_bot_of_prime_manner_not_regular
      (G := G) hprime hnotRegular
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := subgroupCentralizerIn (section10Msigma M) E₃) hCne with
    ⟨qstar, X, hXleC, hXcard⟩
  have hqC : qstar ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) E₃) := by
    have hqX : qstar.val ∣ Nat.card X := by rw [hXcard]
    exact hqX.trans (Subgroup.card_dvd_of_le hXleC)
  exact ⟨qstar, hqC, section13_sigma_of_mem_centralizer_msigma (G := G) hM hqC⟩

private theorem CFSG.section13_theorem_13_10_beta_Qstar_data
    {M Mstar E E₁₂ E₁ E₂ E₃ P Q : Subgroup G} {p q qstar : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar_max : Mstar ∈ section9MaximalSubgroups G)
    (hqτ3 : q ∈ section12Tau3Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (_hPinf : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQinf : section12SylowSubgroupIn q Q (M ⊓ Mstar))
    (hQ_E₃ : Q ≤ E₃)
    (hCαPQ : subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hqstarC_E₃ : qstar ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) E₃))
    (hqstarσ : qstar ∈ section10SigmaPrimes M)
    (hqstarβ : qstar ∈ section10BetaPrimes M) :
    ∃ Qstar : Subgroup G,
      section12SylowSubgroupIn qstar Qstar (M ⊓ Mstar) ∧
        P ≤ Subgroup.normalizer (Qstar : Set G) ∧
          subgroupCentralizerIn Qstar P = ⊥ ∧
            Subgroup.normalizer (Qstar : Set G) ≤ M := by
  classical
  haveI : Fact qstar.val.Prime := ⟨qstar.property⟩
  let C : Subgroup G := subgroupCentralizerIn (section10Msigma M) Q
  have hC_E₃_le_C_Q :
      subgroupCentralizerIn (section10Msigma M) E₃ ≤ C := by
    intro x hx
    exact ⟨hx.1, Subgroup.centralizer_le hQ_E₃ hx.2⟩
  have hqstarC : qstar ∈ subgroupPrimeSet C :=
    section8_subgroupPrimeSet_mono hC_E₃_le_C_Q hqstarC_E₃
  have hE₃cyc : IsCyclic E₃ := (lemma_12_1_d hM hE).2
  have hE₃norm : section10NormalIn E₃ E := (lemma_12_1_b hM hE).2
  have hE_norm_Q : E ≤ Subgroup.normalizer (Q : Set G) :=
    section13_le_normalizer_of_le_cyclic_normal
      (G := G) (E := E) (E₃ := E₃) (X := Q) hQ_E₃ hE₃cyc hE₃norm
  rcases section13_exists_E_invariant_msigma_centralizer_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q) (q := qstar)
      hM hE hE_norm_Q (by simpa [C] using hqstarC) with
    ⟨hEC, S, hSinv⟩
  let Qstar : Subgroup G := section10AmbientSylowSubgroup C S
  have hE₁_le_E : E₁ ≤ E :=
    (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, _hPcard⟩
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) := by
    simpa [C] using hEC.1
  have hE_norm_Qstar : E ≤ Subgroup.normalizer (Qstar : Set G) := by
    change E ≤ Subgroup.normalizer ((S : Subgroup C).map C.subtype : Set G)
    exact section13_le_normalizer_map_of_isInvariant
      (G := G) (A := E) (H := C) (K := (S : Subgroup C))
      hE_norm_C hSinv
  have hPnormQstar : P ≤ Subgroup.normalizer (Qstar : Set G) :=
    hP_E₁.trans (hE₁_le_E.trans hE_norm_Qstar)
  have hQstar_le_C : Qstar ≤ C :=
    section13_ambient_sylow_le_base (G := G) C S
  have hQstar_le_msigma : Qstar ≤ section10Msigma M := by
    intro x hx
    exact (show x ∈ C from hQstar_le_C hx).1
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQstar_le_M : Qstar ≤ M := hQstar_le_msigma.trans hMsigma_le_M
  have hQstar_cent_Q : Qstar ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    exact (show x ∈ C from hQstar_le_C hx).2
  have hQstar_le_Mstar : Qstar ≤ Mstar := by
    intro x hx
    exact hNQ (centralizer_le_normalizer Q (hQstar_cent_Q hx))
  have hQstar_le_inf : Qstar ≤ M ⊓ Mstar := le_inf hQstar_le_M hQstar_le_Mstar
  have hQstarq : IsPGroup qstar.val Qstar := by
    change IsPGroup qstar.val ((S : Subgroup C).map C.subtype)
    exact IsPGroup.map (p := qstar.val) (H := (S : Subgroup C))
      S.isPGroup' C.subtype
  have hS_ne : (S : Subgroup C) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := C) S (by
      simpa [C, subgroupPrimeSet] using hqstarC)
  have hQstar_ne : Qstar ≠ ⊥ := by
    intro hbot
    have hSbot : (S : Subgroup C) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (S : Subgroup C)) (f := C.subtype) C.subtype_injective).mp
        (by simpa [Qstar, section10AmbientSylowSubgroup] using hbot)
    exact hS_ne hSbot
  have hQp : IsPGroup q.val Q := section13_sylowSubgroupIn_isPGroup (G := G) hQinf
  have hQne : Q ≠ ⊥ :=
    section13_ne_bot_of_normalizer_le_maximal (G := G) hMstar_max hNQ
  have hQ_le_inf : Q ≤ M ⊓ Mstar := section13_sylowSubgroupIn_le (G := G) hQinf
  have hQ_le_M : Q ≤ M := hQ_le_inf.trans inf_le_left
  have hMstar_cont :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
    ⟨hMstar_max, hNQ⟩
  have hQ_cent_inf :
      Q ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) :=
    corollary_13_2_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (P := Q) (Mstar := Mstar) (p := q)
      hM hE (Or.inr hqτ3) hQp hQne hQ_le_M hMstar_cont
      Q hQ_le_inf hQp
  have hInf_cent_Q :
      section10Msigma M ⊓ Mstar ≤ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff
      (H := section10Msigma M ⊓ Mstar) (K := Q)).mpr hQ_cent_inf
  have hL_p_le_C : ∀ Y : Subgroup G, Y ≤ M ⊓ Mstar → IsPGroup qstar.val Y → Y ≤ C := by
    intro Y hYle hYq
    have hY_le_M : Y ≤ M := hYle.trans inf_le_left
    have hYsub_p : IsPGroup qstar.val (Y.subgroupOf M) :=
      hYq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Y) (K := M) hY_le_M).symm
    have hYsub_le_sigma :
        Y.subgroupOf M ≤ section10MsigmaSubgroup M :=
      section13_pSubgroup_le_normal_hall_of_prime_mem
        (R := M) (π := section10SigmaPrimes M)
        (H := section10MsigmaSubgroup M) (A := Y.subgroupOf M)
        (p := qstar) (theorem_10_2_b (G := G) hM).2 hqstarσ hYsub_p
    have hY_le_msigma : Y ≤ section10Msigma M := by
      intro y hy
      have hySub : (⟨y, hY_le_M hy⟩ : M) ∈ Y.subgroupOf M := by
        simpa [Subgroup.mem_subgroupOf] using hy
      exact Subgroup.mem_map.mpr
        ⟨⟨y, hY_le_M hy⟩,
          hYsub_le_sigma hySub,
          rfl⟩
    intro y hy
    exact ⟨hY_le_msigma hy, hInf_cent_Q ⟨hY_le_msigma hy, (hYle hy).2⟩⟩
  have hQstar_C : section12SylowSubgroupIn qstar Qstar C := by
    exact ⟨S, rfl⟩
  have hQstarInf : section12SylowSubgroupIn qstar Qstar (M ⊓ Mstar) :=
    section13_sylowSubgroupIn_of_overgroup_sylow_with_pgroups_le
      (G := G) (C := C) (L := M ⊓ Mstar) (Q := Qstar) (q := qstar)
      hQstar_C hQstar_le_inf hL_p_le_C
  have hQstarπβ : IsPiSubgroup (G := G) (section10BetaPrimes M) Qstar := by
    intro s hs
    have hs_single : s ∈ ({qstar} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hQstarq s hs
    have hs_eq : s = qstar := by simpa using hs_single
    simpa [hs_eq] using hqstarβ
  let Sg : Sylow qstar.val G := Classical.choice (Sylow.nonempty (p := qstar.val) (G := G))
  have hNQstarM : Subgroup.normalizer (Qstar : Set G) ≤ M :=
    proposition_10_14_d (G := G) (p := qstar) hqstarβ.2 Sg
      (M := M) (Y := Qstar) hM hQstar_le_M hQstar_ne hQstarπβ
  have hQstar_sub_p : IsPGroup qstar.val (Qstar.subgroupOf M) :=
    hQstarq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Qstar) (K := M) hQstar_le_M).symm
  have hQstar_sub_le_beta :
      Qstar.subgroupOf M ≤ section10MbetaSubgroup M :=
    section13_pSubgroup_le_normal_hall_of_prime_mem
      (R := M) (π := section10BetaPrimes M)
      (H := section10MbetaSubgroup M) (A := Qstar.subgroupOf M)
      (p := qstar) (lemma_10_8_a (G := G) hM).2 hqstarβ hQstar_sub_p
  have hQstar_le_mbeta : Qstar ≤ section10Mbeta M := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hQstar_le_M hx⟩,
        by
          exact hQstar_sub_le_beta (by simpa [Subgroup.mem_subgroupOf] using hx),
        rfl⟩
  have hQstar_le_malpha : Qstar ≤ section10Malpha M :=
    hQstar_le_mbeta.trans (section13_mbeta_le_malpha (G := G) M)
  have hCQstar_le_CαP :
      subgroupCentralizerIn Qstar P ≤ subgroupCentralizerIn (section10Malpha M) P := by
    intro x hx
    exact ⟨hQstar_le_malpha hx.1, hx.2⟩
  have hCQstar_cent_Q :
      subgroupCentralizerIn Qstar P ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    exact hQstar_cent_Q hx.1
  have hCQstar_le_CαPQ :
      subgroupCentralizerIn Qstar P ≤
        subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) :=
    section13_subgroupCentralizerIn_sup_of_le_centralizer
      (G := G) (A := section10Malpha M) (R := P) (Q := Q)
      (C := subgroupCentralizerIn Qstar P) hCQstar_le_CαP hCQstar_cent_Q
  have hCQstar : subgroupCentralizerIn Qstar P = ⊥ :=
    le_bot_iff.mp (by simpa [hCαPQ] using hCQstar_le_CαPQ)
  exact ⟨Qstar, hQstarInf, hPnormQstar, hCQstar, hNQstarM⟩

private theorem CFSG.section13_theorem_13_10_not_beta_Qstar_data
    {M Mstar E E₁₂ E₁ E₂ E₃ P Q : Subgroup G} {p q qstar : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hnotconj : section12NotConjugate Mstar M)
    (hqτ3 : q ∈ section12Tau3Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (_hPinf : P ∈ section10PrimeOrderSubgroupsIn p (M ⊓ Mstar))
    (hQinf : section12SylowSubgroupIn q Q (M ⊓ Mstar))
    (hQ_E₃ : Q ≤ E₃)
    (_hPnormQ : P ≤ Subgroup.normalizer (Q : Set G))
    (_hCQ : subgroupCentralizerIn Q P = ⊥)
    (_hCαPQ : subgroupCentralizerIn (section10Malpha M) (P ⊔ Q) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hqstarC_E₃ : qstar ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) E₃))
    (hqstarσ : qstar ∈ section10SigmaPrimes M)
    (hqstar_notβ : qstar ∉ section10BetaPrimes M) :
    ∃ Qstar : Subgroup G,
      section12SylowSubgroupIn qstar Qstar (M ⊓ Mstar) ∧
        P ≤ Subgroup.normalizer (Qstar : Set G) ∧
          subgroupCentralizerIn Qstar P = ⊥ ∧
            Subgroup.normalizer (Qstar : Set G) ≤ M := by
  classical
  haveI : Fact qstar.val.Prime := ⟨qstar.property⟩
  let C : Subgroup G := subgroupCentralizerIn (section10Msigma M) Q
  let K : Subgroup G := section10Msigma M
  have hC_E₃_le_C_Q :
      subgroupCentralizerIn (section10Msigma M) E₃ ≤ C := by
    intro x hx
    exact ⟨hx.1, Subgroup.centralizer_le hQ_E₃ hx.2⟩
  have hqstarC : qstar ∈ subgroupPrimeSet C :=
    section8_subgroupPrimeSet_mono hC_E₃_le_C_Q hqstarC_E₃
  have hE₃cyc : IsCyclic E₃ := (lemma_12_1_d hM hE).2
  have hE₃norm : section10NormalIn E₃ E := (lemma_12_1_b hM hE).2
  have hE_norm_Q : E ≤ Subgroup.normalizer (Q : Set G) :=
    section13_le_normalizer_of_le_cyclic_normal
      (G := G) (E := E) (E₃ := E₃) (X := Q) hQ_E₃ hE₃cyc hE₃norm
  rcases section13_exists_E_invariant_msigma_centralizer_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (Q := Q) (q := qstar)
      hM hE hE_norm_Q (by simpa [C] using hqstarC) with
    ⟨hEC, S, hSinv⟩
  let Qstar : Subgroup G := section10AmbientSylowSubgroup C S
  have hE₁_le_E : E₁ ≤ E :=
    (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) := by
    simpa [C] using hEC.1
  have hE_norm_Qstar : E ≤ Subgroup.normalizer (Qstar : Set G) := by
    change E ≤ Subgroup.normalizer ((S : Subgroup C).map C.subtype : Set G)
    exact section13_le_normalizer_map_of_isInvariant
      (G := G) (A := E) (H := C) (K := (S : Subgroup C))
      hE_norm_C hSinv
  have hPnormQstar : P ≤ Subgroup.normalizer (Qstar : Set G) :=
    hP_E₁.trans (hE₁_le_E.trans hE_norm_Qstar)
  have hQstar_le_C : Qstar ≤ C :=
    section13_ambient_sylow_le_base (G := G) C S
  have hQstar_le_msigma : Qstar ≤ section10Msigma M := by
    intro x hx
    exact (show x ∈ C from hQstar_le_C hx).1
  have hMsigma_le_M : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQstar_le_M : Qstar ≤ M := hQstar_le_msigma.trans hMsigma_le_M
  have hQstar_cent_Q : Qstar ≤ Subgroup.centralizer (Q : Set G) := by
    intro x hx
    exact (show x ∈ C from hQstar_le_C hx).2
  have hQstar_le_Mstar : Qstar ≤ Mstar := by
    intro x hx
    exact hNQ (centralizer_le_normalizer Q (hQstar_cent_Q hx))
  have hQstar_le_inf : Qstar ≤ M ⊓ Mstar := le_inf hQstar_le_M hQstar_le_Mstar
  have hQstarq : IsPGroup qstar.val Qstar := by
    change IsPGroup qstar.val ((S : Subgroup C).map C.subtype)
    exact IsPGroup.map (p := qstar.val) (H := (S : Subgroup C))
      S.isPGroup' C.subtype
  have hS_ne : (S : Subgroup C) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := C) S (by
      simpa [C, subgroupPrimeSet] using hqstarC)
  have hQstar_ne : Qstar ≠ ⊥ := by
    intro hbot
    have hSbot : (S : Subgroup C) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (S : Subgroup C)) (f := C.subtype) C.subtype_injective).mp
        (by simpa [Qstar, section10AmbientSylowSubgroup] using hbot)
    exact hS_ne hSbot
  have hQp : IsPGroup q.val Q := section13_sylowSubgroupIn_isPGroup (G := G) hQinf
  have hQne : Q ≠ ⊥ :=
    section13_ne_bot_of_normalizer_le_maximal (G := G) hMstar hNQ
  have hQ_le_inf : Q ≤ M ⊓ Mstar := section13_sylowSubgroupIn_le (G := G) hQinf
  have hQ_le_M : Q ≤ M := hQ_le_inf.trans inf_le_left
  have hMstar_cont :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
    ⟨hMstar, hNQ⟩
  have hQ_cent_inf :
      Q ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) :=
    corollary_13_2_a
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (P := Q) (Mstar := Mstar) (p := q)
      hM hE (Or.inr hqτ3) hQp hQne hQ_le_M hMstar_cont
      Q hQ_le_inf hQp
  have hInf_cent_Q :
      section10Msigma M ⊓ Mstar ≤ Subgroup.centralizer (Q : Set G) :=
    (Subgroup.le_centralizer_iff
      (H := section10Msigma M ⊓ Mstar) (K := Q)).mpr hQ_cent_inf
  have hL_p_le_C : ∀ Y : Subgroup G, Y ≤ M ⊓ Mstar → IsPGroup qstar.val Y → Y ≤ C := by
    intro Y hYle hYq
    have hY_le_M : Y ≤ M := hYle.trans inf_le_left
    have hYsub_p : IsPGroup qstar.val (Y.subgroupOf M) :=
      hYq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := Y) (K := M) hY_le_M).symm
    have hYsub_le_sigma :
        Y.subgroupOf M ≤ section10MsigmaSubgroup M :=
      section13_pSubgroup_le_normal_hall_of_prime_mem
        (R := M) (π := section10SigmaPrimes M)
        (H := section10MsigmaSubgroup M) (A := Y.subgroupOf M)
        (p := qstar) (theorem_10_2_b (G := G) hM).2 hqstarσ hYsub_p
    have hY_le_msigma : Y ≤ section10Msigma M := by
      intro y hy
      have hySub : (⟨y, hY_le_M hy⟩ : M) ∈ Y.subgroupOf M := by
        simpa [Subgroup.mem_subgroupOf] using hy
      exact Subgroup.mem_map.mpr
        ⟨⟨y, hY_le_M hy⟩,
          hYsub_le_sigma hySub,
          rfl⟩
    intro y hy
    exact ⟨hY_le_msigma hy, hInf_cent_Q ⟨hY_le_msigma hy, (hYle hy).2⟩⟩
  have hQstar_C : section12SylowSubgroupIn qstar Qstar C := by
    exact ⟨S, rfl⟩
  have hQstarInf : section12SylowSubgroupIn qstar Qstar (M ⊓ Mstar) :=
    section13_sylowSubgroupIn_of_overgroup_sylow_with_pgroups_le
      (G := G) (C := C) (L := M ⊓ Mstar) (Q := Qstar) (q := qstar)
      hQstar_C hQstar_le_inf hL_p_le_C
  have hC_le_K : C ≤ K := by
    intro x hx
    exact hx.1
  let Csub : Subgroup K := C.subgroupOf K
  let eC : C ≃* Csub :=
    (Subgroup.subgroupOfEquivOfLe (H := C) (K := K) hC_le_K).symm
  let Ssub : Sylow qstar.val Csub :=
    S.mapSurjective (f := eC.toMonoidHom) eC.surjective
  rcases section13_exists_sylow_centralized_derivedE_of_not_beta
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (q := qstar)
      hM hE hqstar_notβ with
    ⟨T, hTcentD⟩
  have hE₃D : E₃ ≤ ambientDerivedSubgroup E := (lemma_12_1_b hM hE).1
  have hT_le_C : section10AmbientSylowSubgroup K T ≤ C := by
    intro x hx
    have hxD : x ∈ subgroupCentralizerIn K (ambientDerivedSubgroup E) := hTcentD hx
    exact ⟨hxD.1, Subgroup.centralizer_le (hQ_E₃.trans hE₃D) hxD.2⟩
  have hT_le_Csub : (T : Subgroup K) ≤ Csub := by
    intro x hx
    have hxamb : (x : G) ∈ section10AmbientSylowSubgroup K T :=
      Subgroup.mem_map_of_mem K.subtype hx
    have hxC : (x : G) ∈ C := hT_le_C hxamb
    simpa [Csub, Subgroup.mem_subgroupOf] using hxC
  rcases section13_sylowSubgroupIn_of_subgroup_sylow_with_ambient_sylow_le
      (G := G) (K := K) (C := Csub) (q := qstar) Ssub ⟨T, hT_le_Csub⟩ with
    ⟨Tstar, hTstar⟩
  have hTstar_ambient :
      section10AmbientSylowSubgroup K Tstar = Qstar := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hyT, rfl⟩
      have hyMap : y ∈ (Ssub : Subgroup Csub).map Csub.subtype := by
        simpa [hTstar] using hyT
      rcases Subgroup.mem_map.mp hyMap with ⟨z, hzSsub, rfl⟩
      have hzSmap : z ∈ (S : Subgroup C).map eC.toMonoidHom := by
        simpa [Ssub] using hzSsub
      rcases Subgroup.mem_map.mp hzSmap with ⟨w, hwS, hwz⟩
      have hxQ : ((w : C) : G) ∈ Qstar := by
        exact Subgroup.mem_map.mpr ⟨w, hwS, rfl⟩
      change ((z : K) : G) ∈ Qstar
      rw [← hwz]
      simpa [Csub, eC, Subgroup.subgroupOfEquivOfLe] using hxQ
    · intro hx
      change x ∈ (S : Subgroup C).map C.subtype at hx
      rcases Subgroup.mem_map.mp hx with ⟨w, hwS, hwx⟩
      let z : Csub := eC w
      have hzSsub : z ∈ (Ssub : Subgroup Csub) := by
        have hzSmap : z ∈ (S : Subgroup C).map eC.toMonoidHom :=
          Subgroup.mem_map.mpr ⟨w, hwS, rfl⟩
        simpa [Ssub] using hzSmap
      have hzMap : (z : K) ∈ (Ssub : Subgroup Csub).map Csub.subtype :=
        Subgroup.mem_map.mpr ⟨z, hzSsub, rfl⟩
      have hzT : (z : K) ∈ (Tstar : Subgroup K) := by
        simpa [hTstar] using hzMap
      exact Subgroup.mem_map.mpr ⟨(z : K), hzT, by
        rw [← hwx]
        simp [z, eC, Csub, Subgroup.subgroupOfEquivOfLe]⟩
  have hQstarMsigma : section12SylowSubgroupIn qstar Qstar K :=
    ⟨Tstar, hTstar_ambient⟩
  have hQstarM : section12SylowSubgroupIn qstar Qstar M := by
    have hTM : section12SylowSubgroupIn qstar
        (section10AmbientSylowSubgroup (section10Msigma M) Tstar) M :=
      section13_msigma_sylowSubgroupIn_maximal (G := G) hM hqstarσ Tstar
    simpa [K, hTstar_ambient] using hTM
  have hNQstarM : Subgroup.normalizer (Qstar : Set G) ≤ M :=
    section13_normalizer_sylowSubgroupIn_le_of_sigma (G := G) hM hqstarσ hQstarM
  have hCQstar : subgroupCentralizerIn Qstar P = ⊥ := by
    by_contra hCne
    rcases section13_exists_prime_order_subgroup_le_of_ne_bot
        (G := G) (P := subgroupCentralizerIn Qstar P) hCne with
      ⟨r, X, hXleCQP, hXcard⟩
    have hXqstar : IsPGroup qstar.val X :=
      section13_isPGroup_of_le_pSubgroup (G := G) hQstarq
        (hXleCQP.trans inf_le_left)
    have hr_eq : r = qstar := by
      have hr_dvd_X : r.val ∣ Nat.card X := by
        rw [hXcard]
      have hr_mem : r ∈ ({qstar} : Set Nat.Primes) :=
        section8_isPiSubgroup_singleton_of_isPGroup hXqstar r hr_dvd_X
      simpa using hr_mem
    have hXcard_qstar : Nat.card X = qstar.val := by
      simpa [hr_eq] using hXcard
    have hX_le_CP : X ≤ subgroupCentralizerIn (section10Msigma M) P := by
      intro x hx
      exact ⟨hQstar_le_msigma ((hXleCQP hx).1), (hXleCQP hx).2⟩
    have hXprime :
        X ∈ section10PrimeOrderSubgroupsIn qstar
          (subgroupCentralizerIn (section10Msigma M) P) := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hX_le_CP, hXcard_qstar⟩
    have huniq :
        section9MaximalSubgroupsContaining
          (section10AmbientSylowSubgroup (section10Msigma M) Tstar) = {M} :=
      (lemma_13_6 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (X := X)
        (q := qstar) Tstar hM hE hPne hP_E₁ hqstarσ hXprime).2
    have hMstar_mem :
        Mstar ∈ section9MaximalSubgroupsContaining
          (section10AmbientSylowSubgroup (section10Msigma M) Tstar) := by
      exact ⟨hMstar, by simpa [hTstar_ambient, K] using hQstar_le_Mstar⟩
    have hMstar_eq_M : Mstar = M := by
      simpa [huniq] using hMstar_mem
    exact hnotconj 1 (by
      simpa [hMstar_eq_M] using section8_conjBy_one (G := G) Mstar)
  exact ⟨Qstar, hQstarInf, hPnormQstar, hCQstar, hNQstarM⟩

/-- Core source step for Theorem 13.10(b): nonregularity of the `E₃` action
on `M_σ` contradicts Lemma 13.8. -/
private theorem CFSG.section13_theorem_13_10_b_absurd
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hPnotCentE₃ : ¬ P ≤ Subgroup.centralizer (E₃ : Set G))
    (hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M)) :
    False := by
  classical
  rcases section13_theorem_13_10_initial_lemma_13_8_side
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (p := p)
      hM hE hP hPnotCentE₃ with
    ⟨Mstar, Q, q, hMstar, hnotconj, hqτ3, hpτ1, hPinf, hQinf,
      hQ_E₃, hPnormQ, hCQ, hCαPQ, hNQ⟩
  rcases section13_theorem_13_10_nonregular_centralizer_prime
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hnotRegular with
    ⟨qstar, hqstarC_E₃, hqstarσ⟩
  have hQstar_data :
      ∃ Qstar : Subgroup G,
        section12SylowSubgroupIn qstar Qstar (M ⊓ Mstar) ∧
          P ≤ Subgroup.normalizer (Qstar : Set G) ∧
            subgroupCentralizerIn Qstar P = ⊥ ∧
              Subgroup.normalizer (Qstar : Set G) ≤ M := by
    by_cases hqstarβ : qstar ∈ section10BetaPrimes M
    · exact
        section13_theorem_13_10_beta_Qstar_data
          (G := G) (M := M) (Mstar := Mstar) (E := E)
          (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
          (P := P) (Q := Q) (p := p) (q := q) (qstar := qstar)
          hM hE hMstar hqτ3 hP hPinf hQinf hQ_E₃ hCαPQ hNQ
          hqstarC_E₃ hqstarσ hqstarβ
    · exact
        section13_theorem_13_10_not_beta_Qstar_data
          (G := G) (M := M) (Mstar := Mstar) (E := E)
          (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
          (P := P) (Q := Q) (p := p) (q := q) (qstar := qstar)
          hM hE hMstar hnotconj hqτ3 hP hPinf hQinf hQ_E₃
          hPnormQ hCQ hCαPQ hNQ hqstarC_E₃ hqstarσ hqstarβ
  rcases hQstar_data with
    ⟨Qstar, hQstarInf, hPnormQstar, hCQstar, hNQstar⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hP_E₁, hPcard⟩
  have hE₁_le_E : E₁ ≤ E :=
    (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  have hpE : p ∈ subgroupPrimeSet E := by
    have hpP : p.val ∣ Nat.card P := by rw [hPcard]
    exact hpP.trans (Subgroup.card_dvd_of_le (hP_E₁.trans hE₁_le_E))
  have hP_le_inf : P ≤ M ⊓ Mstar := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hPinf) with
      ⟨hP_le, _hcard⟩
    intro x hx
    exact ⟨hP_le.1 hx, hP_le.2 hx⟩
  have hP_le_Mstar : P ≤ Mstar := hP_le_inf.trans inf_le_right
  have hpMstar : p ∈ subgroupPrimeSet Mstar := by
    have hpP : p.val ∣ Nat.card P := by rw [hPcard]
    exact hpP.trans (Subgroup.card_dvd_of_le hP_le_Mstar)
  have hPp : IsPGroup p.val P :=
    section13_primeOrderSubgroupsIn_isPGroup (G := G) hPinf
  have hQstarq : IsPGroup qstar.val Qstar :=
    section13_sylowSubgroupIn_isPGroup (G := G) hQstarInf
  have hQstar_ne : Qstar ≠ ⊥ :=
    section13_ne_bot_of_normalizer_le_maximal (G := G) hM hNQstar
  have hQstar_le_inf : Qstar ≤ M ⊓ Mstar :=
    section13_sylowSubgroupIn_le (G := G) hQstarInf
  have hQstar_le_M : Qstar ≤ M := hQstar_le_inf.trans inf_le_left
  have hQstar_le_Mstar : Qstar ≤ Mstar := hQstar_le_inf.trans inf_le_right
  have hQstar_sub_p : IsPGroup qstar.val (Qstar.subgroupOf M) :=
    hQstarq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Qstar) (K := M) hQstar_le_M).symm
  have hQstar_sub_le_sigma :
      Qstar.subgroupOf M ≤ section10MsigmaSubgroup M :=
    section13_pSubgroup_le_normal_hall_of_prime_mem
      (R := M) (π := section10SigmaPrimes M)
      (H := section10MsigmaSubgroup M) (A := Qstar.subgroupOf M)
      (p := qstar) (theorem_10_2_b (G := G) hM).2 hqstarσ hQstar_sub_p
  have hQstar_le_msigma : Qstar ≤ section10Msigma M := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hQstar_le_M hx⟩,
        hQstar_sub_le_sigma (by simpa [Subgroup.mem_subgroupOf] using hx),
        rfl⟩
  let K : Subgroup G := section10Msigma M ⊓ Mstar
  let L : Subgroup G := M ⊓ Mstar
  have hQstar_le_K : Qstar ≤ K := by
    intro x hx
    exact ⟨hQstar_le_msigma hx, hQstar_le_Mstar hx⟩
  have hcommQP : ⁅Qstar, P⁆ = Qstar :=
    section13_commutator_eq_left_of_fixedpoint_free_pgroup
      (G := G) (P := P) (Q := Qstar) (H := M ⊓ Mstar)
      (p := p) (q := qstar) hPinf hQstarq hQstar_ne hPnormQstar hCQstar
  have hcomm_le : ⁅Qstar, P⁆ ≤ ⁅K, L⁆ :=
    Subgroup.commutator_mono hQstar_le_K hP_le_inf
  have hQstar_le_comm : Qstar ≤ ⁅K, L⁆ := by
    rw [← hcommQP]
    exact hcomm_le
  have hcomm_ne :
      ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := by
    intro hbot
    have hQbot : Qstar ≤ (⊥ : Subgroup G) := by
      simpa [K, L, hbot] using hQstar_le_comm
    exact hQstar_ne (le_bot_iff.mp hQbot)
  have hpτ1star : p ∈ section12Tau1Primes Mstar := by
    by_contra hp_notτ1star
    have hP_cent_K :
        P ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) :=
      lemma_13_1_a
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
        (Mstar := Mstar) (p := p)
        hM hE hMstar hpE hpMstar hp_notτ1star hcomm_ne hnotconj
        P hP_le_inf hPp
    have hK_cent_P :
        section10Msigma M ⊓ Mstar ≤ Subgroup.centralizer (P : Set G) :=
      (Subgroup.le_centralizer_iff
        (H := P) (K := section10Msigma M ⊓ Mstar)).mp hP_cent_K
    have hQstar_le_C : Qstar ≤ subgroupCentralizerIn Qstar P := by
      intro x hx
      exact ⟨hx, hK_cent_P (hQstar_le_K hx)⟩
    have hQbot : Qstar ≤ (⊥ : Subgroup G) := by
      simpa [hCQstar] using hQstar_le_C
    exact hQstar_ne (le_bot_iff.mp hQbot)
  exact
    lemma_13_8
      (G := G) (M := M) (Mstar := Mstar) (P := P) (Q := Q)
      (Qstar := Qstar) (p := p) (q := q) (qstar := qstar)
      hM hMstar hnotconj hpτ1 hpτ1star hPinf hQinf hQstarInf
      hPnormQ hPnormQstar hCQ hCQstar hNQ hNQstar


/-- Theorem 13.10(b): if some `P ∈ 𝓔_p^1(E₁)` does not centralize
`E₃`, then `E₃` acts regularly on `M_σ`. -/
public theorem CFSG.theorem_13_10_b
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E₁)
    (hPnotCentE₃ : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    section13ActsRegularlyOn E₃ (section10Msigma M) := by
  classical
  by_contra hnotRegular
  exact False.elim <|
    section13_theorem_13_10_b_absurd
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (p := p)
      hM hE hP hPnotCentE₃ hnotRegular


end Section13
