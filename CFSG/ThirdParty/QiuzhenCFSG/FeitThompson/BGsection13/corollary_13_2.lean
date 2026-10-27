module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.lemma_13_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 13 2 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section13_prime_mem_E_of_tau13
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M) :
    p ∈ subgroupPrimeSet E := by
  exact section12_prime_mem_E_of_mem_tau13 hM hE hpτ13

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section13_centralizes_of_commutator_eq_bot
    {A B P : Subgroup G} (hcomm : ⁅A, B⁆ = ⊥) (hPB : P ≤ B) :
    P ≤ Subgroup.centralizer (A : Set G) := by
  have hB_le_centA : B ≤ Subgroup.centralizer (A : Set G) := by
    have hA_le_centB :
        A ≤ Subgroup.centralizer (B : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := A) (H₂ := B)).mp hcomm
    exact (Subgroup.le_centralizer_iff (H := A) (K := B)).mp hA_le_centB
  exact hPB.trans hB_le_centA

omit [IsMinCE G] in
private theorem CFSG.section13_le_centralizer_of_sylow_images
    {K X : Subgroup G}
    (hSylowCent : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet X →
      ∀ S : Sylow q.val X,
        (S : Subgroup X).map X.subtype ≤ Subgroup.centralizer (K : Set G)) :
    X ≤ Subgroup.centralizer (K : Set G) := by
  classical
  let C : Subgroup X := (Subgroup.centralizer (K : Set G)).comap X.subtype
  have htop_le_C : (⊤ : Subgroup X) ≤ C := by
    rw [← Sylow.iSup_sylow_eq_top (G := X)]
    refine iSup_le ?_
    intro r
    refine iSup_le ?_
    intro hr
    have hrprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr
    let q : Nat.Primes := ⟨r, hrprime⟩
    let _ : Fact q.val.Prime := ⟨q.property⟩
    let S : Sylow q.val X := default
    change (S : Subgroup X) ≤ C
    intro y hyS
    change ((y : X) : G) ∈ Subgroup.centralizer (K : Set G)
    have hy_map : ((y : X) : G) ∈ ((S : Subgroup X).map X.subtype : Subgroup G) :=
      Subgroup.mem_map_of_mem X.subtype hyS
    exact hSylowCent q
      (by
        change q.val ∣ Nat.card X
        exact Nat.dvd_of_mem_primeFactors hr) S hy_map
  intro x hxX
  let xX : X := ⟨x, hxX⟩
  have hxC : xX ∈ C := htop_le_C (show xX ∈ (⊤ : Subgroup X) by simp)
  change ((xX : X) : G) ∈ Subgroup.centralizer (K : Set G) at hxC
  exact hxC

omit [IsMinCE G] in
private theorem CFSG.section13_eq_top_of_exists_sylow_le
    {X : Type*} [Group X] [Finite X] (H : Subgroup X)
    (hSyl :
      ∀ p : ℕ, p ∈ (Nat.card X).primeFactors → ∀ [Fact p.Prime],
        ∃ P : Sylow p X, (P : Subgroup X) ≤ H) :
    H = ⊤ := by
  rw [← Subgroup.card_eq_iff_eq_top]
  apply Nat.eq_of_factorization_eq Nat.card_pos.ne' Nat.card_pos.ne'
  intro p
  by_cases hp : p.Prime
  · let _ : Fact p.Prime := ⟨hp⟩
    by_cases hd : p ∈ (Nat.card X).primeFactors
    · obtain ⟨P, hPle⟩ := hSyl p hd
      refine le_antisymm
        (Nat.factorization_le_factorization_of_dvd_right
          (Subgroup.card_subgroup_dvd_card H) Nat.card_pos.ne' Nat.card_pos.ne') ?_
      rw [← pow_le_pow_iff_right₀ hp.one_lt, ← Sylow.card_eq_multiplicity P]
      have hc : Nat.card P = Nat.card (P.subgroupOf H) :=
        (natCard_subgroupOf_eq _ _ hPle).symm
      have hpP : IsPGroup p (P.subgroupOf H) := by
        refine IsPGroup.of_card (n := (Nat.card X).factorization p) ?_
        rw [← hc, ← Sylow.card_eq_multiplicity P]
      rcases IsPGroup.exists_le_sylow hpP with ⟨P', hP'⟩
      rw [← Sylow.card_eq_multiplicity P', hc]
      exact Subgroup.card_le_of_le hP'
    · have hnpX : ¬ p ∣ Nat.card X := by
        intro hpX
        exact hd ((Nat.mem_primeFactors).2 ⟨hp, hpX, Nat.card_pos.ne'⟩)
      have hnpH : ¬ p ∣ Nat.card H := by
        intro hpH
        exact hnpX (dvd_trans hpH (Subgroup.card_subgroup_dvd_card H))
      simp [Nat.factorization_eq_zero_of_not_dvd hnpX,
        Nat.factorization_eq_zero_of_not_dvd hnpH]
  · simp [Nat.factorization_eq_zero_of_not_prime (n := Nat.card X) (p := p) hp,
      Nat.factorization_eq_zero_of_not_prime (n := Nat.card H) (p := p) hp]

omit [IsMinCE G] in
public theorem CFSG.section13_le_centralizer_of_exists_sylow_images
    {K X : Subgroup G}
    (hSylowCent : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet X →
      ∃ S : Sylow q.val X,
        (S : Subgroup X).map X.subtype ≤ Subgroup.centralizer (K : Set G)) :
    X ≤ Subgroup.centralizer (K : Set G) := by
  classical
  let C : Subgroup X := (Subgroup.centralizer (K : Set G)).comap X.subtype
  have hC_top : C = ⊤ := by
    apply section13_eq_top_of_exists_sylow_le C
    intro p hpX hpFact
    let q : Nat.Primes := ⟨p, hpFact.out⟩
    let _ : Fact q.val.Prime := ⟨q.property⟩
    have hqX : q ∈ subgroupPrimeSet X := by
      change q.val ∣ Nat.card X
      exact Nat.dvd_of_mem_primeFactors hpX
    obtain ⟨S, hScent⟩ := hSylowCent q hqX
    refine ⟨S, ?_⟩
    change (S : Subgroup X) ≤ C
    intro y hyS
    change ((y : X) : G) ∈ Subgroup.centralizer (K : Set G)
    have hy_map : ((y : X) : G) ∈ ((S : Subgroup X).map X.subtype : Subgroup G) :=
      Subgroup.mem_map_of_mem X.subtype hyS
    exact hScent hy_map
  intro x hxX
  let xX : X := ⟨x, hxX⟩
  have hxC : xX ∈ C := by
    rw [hC_top]
    simp
  change ((xX : X) : G) ∈ Subgroup.centralizer (K : Set G) at hxC
  exact hxC

omit [IsMinCE G] in
private theorem CFSG.section13_primeRank_le_card
    {R : Type*} [Group R] [Finite R] (q : ℕ) :
    primeRank q R ≤ Nat.card R := by
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := q) (G := R), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
    exact hnB.trans <|
      (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)

omit [IsMinCE G] in
private theorem CFSG.section13_generatorRank_le_groupRank_of_subgroup
    {q : ℕ} (hq : Nat.Prime q) {A K : Subgroup G}
    (hAK : A ≤ K) (hAp : IsPGroup q A) (hAcomm : IsMulCommutative A) :
    generatorRank A ≤ groupRank K := by
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup q A' :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    let _ : IsMulCommutative A := hAcomm
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hqrankK : generatorRank A ≤ primeRank q K := by
    rw [primeRank]
    refine le_csSup ?_ ?_
    · refine ⟨Nat.card K, ?_⟩
      intro n hn
      rcases hn with ⟨B, _hBp, _hBcomm, hnB⟩
      exact hnB.trans <|
        (section8_generatorRank_le_natCard B).trans (Subgroup.card_le_card_group B)
    · exact ⟨A', hA'p, hA'comm, by simp [hgen_eq]⟩
  rw [groupRank]
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card K, ?_⟩
    intro n hn
    rcases hn with ⟨r, _hr, hnr⟩
    exact hnr.trans (section13_primeRank_le_card (R := K) r)
  · exact ⟨q, hq, hqrankK⟩

private theorem CFSG.section13_primeRank_le_groupRank_sylow
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes} (S : Sylow p.val R) :
    primeRank p.val R ≤ groupRank (S : Subgroup R) := by
  classical
  let _ : Fact p.val.Prime := ⟨p.property⟩
  rw [primeRank]
  refine csSup_le ?_ ?_
  · exact ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := R), inferInstance, Nat.zero_le _⟩
  · intro n hn
    rcases hn with ⟨A, hAp, hAcomm, hnA⟩
    obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := R) (p := p.val) hAp
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq R Q S
    let Aconj : Subgroup R := A.map (MulAut.conj g).toMonoidHom
    have hAconj_le_S : Aconj ≤ (S : Subgroup R) := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨a, haA, rfl⟩
      have haQ : a ∈ (Q : Subgroup R) := hAQ haA
      have hmem : (MulAut.conj g) a ∈ ((g • Q : Sylow p.val R) : Subgroup R) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Q : Subgroup R) haQ
      simpa [hg] using hmem
    have hAconj_p : IsPGroup p.val Aconj := by
      exact hAp.of_equiv
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    have hAconj_comm : IsMulCommutative Aconj := by
      let _ : IsMulCommutative A := hAcomm
      simpa [Aconj] using
        (Subgroup.map_isMulCommutative (f := (MulAut.conj g).toMonoidHom) (H := A))
    have hgen_eq : generatorRank A = generatorRank Aconj := by
      rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
      exact Group.rank_congr
        (Subgroup.equivMapOfInjective (f := (MulAut.conj g).toMonoidHom) A
          (EquivLike.injective (MulAut.conj g)))
    exact hnA.trans <| by
      rw [hgen_eq]
      exact section13_generatorRank_le_groupRank_of_subgroup
        (G := R) (q := p.val) p.property hAconj_le_S hAconj_p hAconj_comm

public theorem CFSG.section13_normalizer_ne_top_of_ne_bot_le_maximal
    {X M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hXM : X ≤ M) (hXne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≠ ⊤ := by
  intro hnorm_top
  have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  let _ : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hXnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal X) with hXbot | hXtop
  · exact hXne hXbot
  · have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hXtop] using hXM
    exact hM.1 (top_le_iff.mp htop_le_M)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_ambient_sylow_is_cyclic {p : Nat.Primes}
    {E : Subgroup G} (P : Sylow p.val E)
    (hPcyc : IsCyclic (P : Subgroup E)) :
    IsCyclic (section10AmbientSylowSubgroup E P) := by
  let e : (P : Subgroup E) ≃* section10AmbientSylowSubgroup E P :=
    Subgroup.equivMapOfInjective (f := E.subtype) (P : Subgroup E) E.subtype_injective
  exact e.isCyclic.mp hPcyc

public theorem CFSG.section13_prime_mem_tau13_of_cyclic_sylow_E
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (P : Sylow p.val E) (hPne : (P : Subgroup E) ≠ ⊥)
    (hPcyc : IsCyclic (P : Subgroup E)) :
    p ∈ section12Tau1Primes M ∪ section12Tau3Primes M := by
  classical
  have hpE : p ∈ subgroupPrimeSet E :=
    section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
      (A := E) (B := (P : Subgroup E)) P.isPGroup' hPne
  have hpτ :
      p ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪
        section12Tau3Primes M :=
    section12_prime_mem_tau_union_of_mem_E hM hE.1 hpE
  have hp_notτ2 : p ∉ section12Tau2Primes M := by
    intro hpτ2
    have hrank_ge : 2 ≤ primeRank p.val E :=
      section12_primeRank_E_ge_two_of_tau2 hM hE.1 hpτ2
    let _ : IsCyclic (P : Subgroup E) := hPcyc
    have hrank_le : primeRank p.val E ≤ 1 :=
      (section13_primeRank_le_groupRank_sylow (R := E) P).trans
        (groupRank_le_one_of_isCyclic (P : Subgroup E))
    omega
  rcases hpτ with hpτ12 | hpτ3
  · rcases hpτ12 with hpτ1 | hpτ2
    · exact Or.inl hpτ1
    · exact False.elim (hp_notτ2 hpτ2)
  · exact Or.inr hpτ3

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_isPGroup_of_le_pSubgroup
    {A X : Subgroup G} {p : Nat.Primes}
    (hAp : IsPGroup p.val A) (hXA : X ≤ A) :
    IsPGroup p.val X := by
  have hXsub_p : IsPGroup p.val (X.subgroupOf A) :=
    hAp.to_subgroup (X.subgroupOf A)
  let e : X.subgroupOf A ≃* X := Subgroup.subgroupOfEquivOfLe hXA
  exact hXsub_p.of_equiv e

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_ne_bot_of_prime_order
    {X : Subgroup G} {q : Nat.Primes} (hXcard : Nat.card X = q.val) :
    X ≠ ⊥ := by
  intro hXbot
  have hcard_one : Nat.card X = 1 := by
    rw [hXbot]
    simp
  have hq_one : q.val = 1 := by omega
  exact q.property.ne_one hq_one

omit [IsMinCE G] in
public theorem CFSG.section13_ambient_sylow_le_normalizer_of_le_cyclic
    {A X : Subgroup G} (hXA : X ≤ A) (hAcyc : IsCyclic A) :
    A ≤ Subgroup.normalizer (X : Set G) := by
  classical
  let _ : IsCyclic A := hAcyc
  have hXchar : (X.subgroupOf A).Characteristic :=
    section12_subgroup_characteristic_of_cyclic (X.subgroupOf A)
  let _ : (X.subgroupOf A).Characteristic := hXchar
  have hnormA_le_normXmap :
      Subgroup.normalizer (A : Set G) ≤
        Subgroup.normalizer ((X.subgroupOf A).map A.subtype : Set G) :=
    section8_normalizer_map_subtype_le_of_characteristic
      (H := A) (K := X.subgroupOf A)
  have hXmap : (X.subgroupOf A).map A.subtype = X :=
    Subgroup.map_subgroupOf_eq_of_le hXA
  simpa [hXmap] using Subgroup.le_normalizer.trans hnormA_le_normXmap

/-- Corollary 13.2(a): for `p ∈ τ₁(M) ∪ τ₃(M)` and nonidentity
`p`-subgroup `P ≤ M`, every `p`-subgroup of `M ∩ M*` centralizes
`M_σ ∩ M*` when `M* ∈ 𝓜(N_G(P))`. -/
public theorem CFSG.corollary_13_2_a
    {M E E₁₂ E₁ E₂ E₃ P Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hPp : IsPGroup p.val P) (hPne : P ≠ ⊥) (hPM : P ≤ M)
      (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
        (Subgroup.normalizer (P : Set G))) :
      ∀ X : Subgroup G, X ≤ M ⊓ Mstar → IsPGroup p.val X →
        X ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) := by
    classical
    intro X hXinf hXp
    by_cases hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ = ⊥
    · exact section13_centralizes_of_commutator_eq_bot hcomm hXinf
    · have hp_alt :
          p ∈ section10SigmaPrimes Mstar ∪ section12Tau2Primes Mstar :=
        lemma_12_2_a (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
          hM hPp hPne hPM hMstar
      have hnotconj : section12NotConjugate Mstar M :=
        lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
          hM hPp hPne hPM hMstar (Or.inr hpτ13)
      have hP_Mstar : P ≤ Mstar :=
        Subgroup.le_normalizer.trans hMstar.2
      have hpτ2star_not : p ∉ section12Tau2Primes Mstar := by
        intro hpτ2star
        have hpE : p ∈ subgroupPrimeSet E :=
          section13_prime_mem_E_of_tau13 hM hE hpτ13
        have hpMstar : p ∈ subgroupPrimeSet Mstar :=
          section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
            (A := Mstar) (B := P.subgroupOf Mstar)
            (hBp := hPp.of_equiv
              (Subgroup.subgroupOfEquivOfLe (H := P) (K := Mstar) hP_Mstar).symm)
            (hB_ne_bot := by
              intro hbot
              exact hPne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hP_Mstar))
        have hpτ1star : p ∉ section12Tau1Primes Mstar := by
          intro hpτ1star
          rcases hp_alt with hpσstar | hpτ2star'
          · rcases (by simpa [section12Tau1Primes] using hpτ1star) with
              ⟨hp_notσ, _hpD, _hrank⟩
            exact hp_notσ hpσstar
          · rcases (by simpa [section12Tau1Primes] using hpτ1star) with
              ⟨_hp_notσ, _hpD, hrank1⟩
            rcases (by simpa [section12Tau2Primes] using hpτ2star') with
              ⟨_hp_notσ', hrank2⟩
            omega
        exact lemma_13_1_b (G := G) hM hE hMstar.1 hpE hpMstar hpτ1star hcomm
          hnotconj hpτ2star
      have hpσstar : p ∈ section10SigmaPrimes Mstar := by
        rcases hp_alt with hpσstar | hpτ2star
        · exact hpσstar
        · exact False.elim (hpτ2star_not hpτ2star)
      have hpE : p ∈ subgroupPrimeSet E :=
        section13_prime_mem_E_of_tau13 hM hE hpτ13
      have hpMstar : p ∈ subgroupPrimeSet Mstar := hpσstar.1
      have hpτ1star : p ∉ section12Tau1Primes Mstar := by
        intro hpτ1star
        rcases (by simpa [section12Tau1Primes] using hpτ1star) with
          ⟨hp_notσ, _hpD, _hrank⟩
        exact hp_notσ hpσstar
      exact lemma_13_1_a (G := G) hM hE hMstar.1 hpE hpMstar hpτ1star hcomm hnotconj
        X hXinf hXp

/-- Corollary 13.2(b): every `τ₁(M*)'`-subgroup of `E ∩ M*` centralizes
`M_σ ∩ M*` under the hypotheses of Corollary 13.2. -/
public theorem CFSG.corollary_13_2_b
    {M E E₁₂ E₁ E₂ E₃ P Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hPp : IsPGroup p.val P) (hPne : P ≠ ⊥) (hPM : P ≤ M)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G))) :
    ∀ X : Subgroup G, X ≤ E ⊓ Mstar →
      IsPiSubgroup (section12Tau1Primes Mstar)ᶜ X →
        X ≤ Subgroup.centralizer (section10Msigma M ⊓ Mstar : Set G) := by
  classical
  intro X hXinf hXπc
  have hE_le_M : E ≤ M := hE.1.2.1
  have hX_le_E : X ≤ E := hXinf.trans inf_le_left
  have hX_le_Mstar : X ≤ Mstar := hXinf.trans inf_le_right
  have hX_le_M : X ≤ M := hX_le_E.trans hE_le_M
  have hX_le_Minf : X ≤ M ⊓ Mstar := le_inf hX_le_M hX_le_Mstar
  by_cases hcomm_eq : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ = ⊥
  · exact section13_centralizes_of_commutator_eq_bot hcomm_eq hX_le_Minf
  · have hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥ := hcomm_eq
    have hnotconj : section12NotConjugate Mstar M :=
      lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
        hM hPp hPne hPM hMstar (Or.inr hpτ13)
    refine
      section13_le_centralizer_of_sylow_images
        (G := G) (K := section10Msigma M ⊓ Mstar) (X := X) ?_
    intro q hqX S
    let Q : Subgroup G := (S : Subgroup X).map X.subtype
    have hQ_le_X : Q ≤ X := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨s, _hs, rfl⟩
      exact s.property
    have hQ_le_inf : Q ≤ M ⊓ Mstar :=
      hQ_le_X.trans hX_le_Minf
    have hQp : IsPGroup q.val Q := by
      simpa [Q] using
        IsPGroup.map (p := q.val) (H := (S : Subgroup X)) S.isPGroup' X.subtype
    have hqE : q ∈ subgroupPrimeSet E :=
      section8_subgroupPrimeSet_mono hX_le_E hqX
    have hqMstar : q ∈ subgroupPrimeSet Mstar :=
      section8_subgroupPrimeSet_mono hX_le_Mstar hqX
    have hqτ1star : q ∉ section12Tau1Primes Mstar := by
      simpa using hXπc q hqX
    exact
      lemma_13_1_a (G := G) hM hE hMstar.1 hqE hqMstar hqτ1star
        hcomm hnotconj Q hQ_le_inf hQp

/-- Corollary 13.2(c): if `[M_σ ∩ M*, M ∩ M*] ≠ 1`, then
`p ∈ σ(M*)`, and if also `p ∈ τ₁(M)`, then `p ∈ β(M*)`. -/
public theorem CFSG.corollary_13_2_c
    {M E E₁₂ E₁ E₂ E₃ P Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hPp : IsPGroup p.val P) (hPne : P ≠ ⊥) (hPM : P ≤ M)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining
      (Subgroup.normalizer (P : Set G)))
    (hcomm : ⁅section10Msigma M ⊓ Mstar, M ⊓ Mstar⁆ ≠ ⊥) :
    p ∈ section10SigmaPrimes Mstar ∧
      (p ∈ section12Tau1Primes M → p ∈ section10BetaPrimes Mstar) := by
  classical
  have hp_alt :
      p ∈ section10SigmaPrimes Mstar ∪ section12Tau2Primes Mstar :=
    lemma_12_2_a (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
      hM hPp hPne hPM hMstar
  have hnotconj : section12NotConjugate Mstar M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
      hM hPp hPne hPM hMstar (Or.inr hpτ13)
  have hP_Mstar : P ≤ Mstar :=
    Subgroup.le_normalizer.trans hMstar.2
  have hpMstar : p ∈ subgroupPrimeSet Mstar :=
    section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
      (A := Mstar) (B := P.subgroupOf Mstar)
      (hBp := hPp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := P) (K := Mstar) hP_Mstar).symm)
      (hB_ne_bot := by
        intro hbot
        exact hPne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hP_Mstar))
  have hpE : p ∈ subgroupPrimeSet E :=
    section13_prime_mem_E_of_tau13 hM hE hpτ13
  have hpτ2star_not : p ∉ section12Tau2Primes Mstar := by
    intro hpτ2star
    have hpτ1star : p ∉ section12Tau1Primes Mstar := by
      intro hpτ1star
      rcases hp_alt with hpσstar | hpτ2star'
      · rcases (by simpa [section12Tau1Primes] using hpτ1star) with
          ⟨hp_notσ, _hpD, _hrank⟩
        exact hp_notσ hpσstar
      · rcases (by simpa [section12Tau1Primes] using hpτ1star) with
          ⟨_hp_notσ, _hpD, hrank1⟩
        rcases (by simpa [section12Tau2Primes] using hpτ2star') with
          ⟨_hp_notσ', hrank2⟩
        omega
    exact lemma_13_1_b (G := G) hM hE hMstar.1 hpE hpMstar hpτ1star hcomm
      hnotconj hpτ2star
  have hpσstar : p ∈ section10SigmaPrimes Mstar := by
    rcases hp_alt with hpσstar | hpτ2star
    · exact hpσstar
    · exact False.elim (hpτ2star_not hpτ2star)
  refine ⟨hpσstar, ?_⟩
  intro hpτ1
  have hpτ1star : p ∉ section12Tau1Primes Mstar := by
    intro hpτ1star
    rcases (by simpa [section12Tau1Primes] using hpτ1star) with
      ⟨hp_notσ, _hpD, _hrank⟩
    exact hp_notσ hpσstar
  have hpβG : p ∈ section12BetaPrimesOfGroup G :=
    lemma_13_1_c (G := G) hM hE hMstar.1 hpE hpMstar hpτ1star hcomm hnotconj hpτ1
  exact section10_betaPrimes_of_idealPrime_of_sigma (G := G) hMstar.1
    (by simpa [section12BetaPrimesOfGroup] using hpβG) hpσstar

end Section13
