module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.corollary_13_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 13 12 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
private theorem CFSG.section13_lemma_13_12_not_le_centralizer_of_msigma_fixed
    {M E E₁₂ E₁ E₂ E₃ P A : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hqτ2 : q ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn q E)
    (hCPne : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) :
    ¬ P ≤ subgroupCentralizerIn E A := by
  classical
  intro hPcentA
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPπ : IsPiSubgroup (G := G) (section12Tau1Primes M) P := by
    intro r hrP
    have hr_single : r ∈ ({p} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hPp r hrP
    have hrp : r = p := by simpa using hr_single
    simpa [hrp] using hpτ1
  let Psub : Subgroup E := P.subgroupOf E
  have hPπE : IsPiSubgroup (G := E) (section12Tau1Primes M) Psub := by
    simpa [Psub] using section13_isPiSubgroup_subgroupOf (G := G) hPπ hPE
  rcases section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1 with
    ⟨hE₁E, hHallE₁E⟩
  have hEproper : E ≠ ⊤ := by
    intro hEtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hEtop] using hE.1.2.1
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hsolvE : IsSolvable E :=
    IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
  letI : MulDistribMulAction Unit E := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hPinv : IsInvariant Unit E Psub := by
    refine ⟨?_⟩
    intro _ x
    simp
  obtain ⟨H, hHHall, _hHinv, hPsub_le_H⟩ :=
    exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E) (A := Unit) hsolvE (by simp)
      (section12Tau1Primes M) Psub hPπE hPinv
  obtain ⟨gE, hgEq⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := E) hsolvE (π := section12Tau1Primes M)
      (H₁ := H) (H₂ := E₁.subgroupOf E) hHHall hHallE₁E
  let g : G := gE
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM hE hqτ2 hA).1
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnorm.1).1 hAnorm.2
  have hPg_le_CE₁A : P.conjBy g ≤ subgroupCentralizerIn E₁ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, huP, hux⟩
    have hx_eq : x = g * u * g⁻¹ := by
      simpa [g, MulAut.conj_apply] using hux.symm
    refine ⟨?_, ?_⟩
    · let uE : E := ⟨u, hPE huP⟩
      have huPsub : uE ∈ Psub := by
        simpa [Psub, uE, Subgroup.mem_subgroupOf] using huP
      have hconj_H :
          (MulAut.conj gE).toMonoidHom uE ∈
            H.map (MulAut.conj gE).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨uE, hPsub_le_H huPsub, rfl⟩
      have hconj_E₁ :
          (MulAut.conj gE).toMonoidHom uE ∈ E₁.subgroupOf E := by
        rw [hgEq]
        exact hconj_H
      have hval_E₁ :
          (((MulAut.conj gE).toMonoidHom uE : E) : G) ∈ E₁ := by
        simpa [Subgroup.mem_subgroupOf] using hconj_E₁
      change g * u * g⁻¹ ∈ E₁ at hval_E₁
      simpa [hx_eq] using hval_E₁
    · change x ∈ Subgroup.centralizer (A : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hgE : g ∈ E := gE.property
      have hg_inv_normA : g⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
        hE_norm_A (E.inv_mem hgE)
      have hga : g⁻¹ * a * g ∈ A := by
        simpa [g] using
          (Subgroup.mem_normalizer_iff.mp hg_inv_normA a).1 ha
      have hu_cent_A : u ∈ Subgroup.centralizer (A : Set G) :=
        (hPcentA huP).2
      have hcomm : u * (g⁻¹ * a * g) = (g⁻¹ * a * g) * u :=
        (Subgroup.mem_centralizer_iff.mp hu_cent_A (g⁻¹ * a * g) hga).symm
      calc
        a * x = a * (g * u * g⁻¹) := by rw [hx_eq]
        _ = g * ((g⁻¹ * a * g) * u) * g⁻¹ := by group
        _ = g * (u * (g⁻¹ * a * g)) * g⁻¹ := by rw [← hcomm]
        _ = (g * u * g⁻¹) * a := by group
        _ = x * a := by rw [hx_eq]
  have hPg_card : Nat.card (P.conjBy g) = p.val := by
    rw [section13_card_conjBy (G := G) P g, hPcard]
  have hPg_ne : P.conjBy g ≠ ⊥ :=
    section13_ne_bot_of_prime_order (G := G) (X := P.conjBy g) (q := p) hPg_card
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hPg_ne with ⟨x, hxne⟩
  have hxPg : (x : G) ∈ P.conjBy g := x.property
  have hxneG : (x : G) ≠ 1 := by
    intro hx1
    exact hxne (Subtype.ext hx1)
  have hg_norm_sigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section13_le_normalizer_msigma (G := G) (M := M) (hE.1.2.1 gE.property)
  have hCPg_ne :
      subgroupCentralizerIn (section10Msigma M) (P.conjBy g) ≠ ⊥ :=
    section11_subgroupCentralizerIn_conjBy_self_ne_bot_of_mem_normalizer
      (G := G) (R := section10Msigma M) (X := P) (g := g)
      hg_norm_sigma hCPne
  have hxCE₁A : (x : G) ∈ subgroupCentralizerIn E₁ A :=
    hPg_le_CE₁A hxPg
  have hElemBot :
      elementCentralizerIn (section10Msigma M) (x : G) = ⊥ :=
    corollary_12_6_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM hE hqτ2 hA (x : G) hxCE₁A hxneG
  have hCPg_le_elem :
      subgroupCentralizerIn (section10Msigma M) (P.conjBy g) ≤
        elementCentralizerIn (section10Msigma M) (x : G) := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    change y ∈ Subgroup.centralizer ({(x : G)} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact Subgroup.mem_centralizer_iff.mp hy.2 (x : G) hxPg
  exact hCPg_ne (le_bot_iff.mp (by
    rw [← hElemBot]
    exact hCPg_le_elem))

omit [IsMinCE G] in
private theorem CFSG.section13_lemma_13_12_fixed_rankTwo_centralizer_prime
    {E P A : Subgroup G} {p q : Nat.Primes}
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hA : A ∈ section12RankTwoElementaryAbelianIn q E)
    (hPnotCentA : ¬ P ≤ subgroupCentralizerIn E A)
    (hCAP : subgroupCentralizerIn A P ≠ ⊥) :
    subgroupCentralizerIn A P ∈ section10PrimeOrderSubgroupsIn q A := by
  classical
  let Y : Subgroup G := subgroupCentralizerIn A P
  have hY_le_A : Y ≤ A := by
    intro y hy
    exact hy.1
  have hcardY_dvd : Nat.card Y ∣ q.val ^ 2 := by
    rcases hA.2 with ⟨hAcard, _hAelem⟩
    exact (Subgroup.card_dvd_of_le hY_le_A).trans (by rw [hAcard])
  have hcardY_pos : 0 < Nat.card Y := Nat.card_pos
  have hcardY_mem : Nat.card Y ∈ (q.val ^ 2).divisors :=
    Nat.mem_divisors.mpr ⟨hcardY_dvd, pow_ne_zero 2 q.2.ne_zero⟩
  have hcard_cases :
      Nat.card Y = q.val ^ 2 ∨ Nat.card Y = q.val ∨ Nat.card Y = 1 := by
    have hdivs := Nat.Prime.divisors_sq q.2
    simpa [hdivs] using hcardY_mem
  have hcardY_ne_one : Nat.card Y ≠ 1 := by
    intro hcard
    have hYbot : Y = ⊥ := (Subgroup.card_eq_one (H := Y)).1 hcard
    exact hCAP (by simpa [Y] using hYbot)
  have hcardY_ne_qsq : Nat.card Y ≠ q.val ^ 2 := by
    intro hcard
    rcases hA.2 with ⟨hAcard, _hAelem⟩
    have hY_eq_A : Y = A :=
      Subgroup.eq_of_le_of_card_ge hY_le_A (by rw [hcard, hAcard])
    apply hPnotCentA
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with ⟨hPE, _hPcard⟩
    intro x hx
    refine ⟨hPE hx, ?_⟩
    change x ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haY : a ∈ Y := by
      rw [hY_eq_A]
      exact ha
    exact (Subgroup.mem_centralizer_iff.mp haY.2 x hx).symm
  have hYcard : Nat.card Y = q.val := by
    rcases hcard_cases with hq2 | hq_or_one
    · exact False.elim (hcardY_ne_qsq hq2)
    · rcases hq_or_one with hq | hone
      · exact hq
      · exact False.elim (hcardY_ne_one hone)
  simpa [Y, section10PrimeOrderSubgroupsIn] using ⟨hY_le_A, hYcard⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section13_lemma_13_12_quotient_prime_of_not_le_centralizer
    {E P A : Subgroup G} {p : Nat.Primes}
    (hCnorm : section10NormalIn (subgroupCentralizerIn E A) E)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hPnotCentA : ¬ P ≤ subgroupCentralizerIn E A) :
    p ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E := by
  classical
  let K : Subgroup G := subgroupCentralizerIn E A
  have hKnormal : section10NormalIn K E := by
    simpa [K] using hCnorm
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  refine ⟨hKnormal.1, ?_⟩
  let Ksub : Subgroup E := K.subgroupOf E
  let Psub : Subgroup E := P.subgroupOf E
  haveI : Ksub.Normal := by
    simpa [Ksub] using hKnormal.2
  let qE : E →* E ⧸ Ksub := QuotientGroup.mk' Ksub
  have hPsub_card : Nat.card Psub = p.val := by
    simpa [Psub] using (natCard_subgroupOf_eq P E hPE).trans hPcard
  have hPmap_ne_bot : Psub.map qE ≠ ⊥ := by
    intro hbot
    apply hPnotCentA
    intro x hxP
    have hxSub : (⟨x, hPE hxP⟩ : E) ∈ Psub := by
      simpa [Psub, Subgroup.mem_subgroupOf] using hxP
    have hle : Psub ≤ qE.ker := by
      simpa using (Subgroup.map_eq_bot_iff (H := Psub) (f := qE)).mp hbot
    have hxker : (⟨x, hPE hxP⟩ : E) ∈ qE.ker := hle hxSub
    have hxKsub : (⟨x, hPE hxP⟩ : E) ∈ Ksub := by
      simpa [qE, Ksub] using hxker
    simpa [K, Ksub, Subgroup.mem_subgroupOf] using hxKsub
  have hmap_dvd_p : Nat.card (Psub.map qE) ∣ p.val := by
    have hmap_dvd : Nat.card (Psub.map qE) ∣ Nat.card Psub :=
      Subgroup.card_map_dvd (H := Psub) qE
    simpa [hPsub_card] using hmap_dvd
  have hmap_card_ne_one : Nat.card (Psub.map qE) ≠ 1 := by
    intro hcard
    exact hPmap_ne_bot ((Subgroup.card_eq_one (H := Psub.map qE)).1 hcard)
  have hmap_eq_p : Nat.card (Psub.map qE) = p.val := by
    rcases (Nat.dvd_prime p.2).mp hmap_dvd_p with hmap_one | hmap_p
    · exact False.elim (hmap_card_ne_one hmap_one)
    · exact hmap_p
  have hp_dvd_quot : p.val ∣ Nat.card (E ⧸ Ksub) := by
    rw [← hmap_eq_p]
    exact Subgroup.card_subgroup_dvd_card (Psub.map qE)
  simpa [Ksub, K, Subgroup.index_eq_card] using hp_dvd_quot

private theorem CFSG.section13_lemma_13_12_contradiction_of_msigma_fixed
    {M E E₁₂ E₁ E₂ E₃ P A : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hqτ2 : q ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn q E)
    (hCAP : subgroupCentralizerIn A P ≠ ⊥)
    (hCPne : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) :
    False := by
  classical
  let Y : Subgroup G := subgroupCentralizerIn A P
  have hPnotCentA :
      ¬ P ≤ subgroupCentralizerIn E A :=
    section13_lemma_13_12_not_le_centralizer_of_msigma_fixed
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (A := A) (p := p) (q := q)
      hM hE hpτ1 hP hqτ2 hA hCPne
  have hYprimeA :
      Y ∈ section10PrimeOrderSubgroupsIn q A := by
    simpa [Y] using
      section13_lemma_13_12_fixed_rankTwo_centralizer_prime
        (G := G) (E := E) (P := P) (A := A) (p := p) (q := q)
        hP hA hPnotCentA hCAP
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hYprimeA) with
    ⟨hYA, hYcard⟩
  have hY_CEP :
      Y ∈ section10PrimeOrderSubgroupsIn q (subgroupCentralizerIn E P) := by
    refine ⟨?_, hYcard⟩
    intro y hy
    have hyY : y ∈ subgroupCentralizerIn A P := by simpa [Y] using hy
    exact ⟨hA.1 hyY.1, hyY.2⟩
  have hqE : q ∈ subgroupPrimeSet E := by
    rcases hA.2 with ⟨hAcard, _hAelem⟩
    have hqA : q.val ∣ Nat.card A := by
      rw [hAcard]
      exact dvd_pow_self q.val (by decide : 2 ≠ 0)
    exact hqA.trans (Subgroup.card_dvd_of_le hA.1)
  have hCP_le_CY :
      subgroupCentralizerIn (section10Msigma M) P ≤
        subgroupCentralizerIn (section10Msigma M) Y :=
    theorem_13_4 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (P := P) (R := Y)
      (p := p) (r := q) hM hE hpτ1 hP hqE hY_CEP
  have hCYne : subgroupCentralizerIn (section10Msigma M) Y ≠ ⊥ := by
    intro hCYbot
    apply hCPne
    exact le_bot_iff.mp (by
      rw [← hCYbot]
      exact hCP_le_CY)
  have hMaxCY_M :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) = {M} :=
    corollary_12_6_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM hE hqτ2 hA Y hYprimeA hCYne
  have hnotNormA_le_M :
      ¬ Subgroup.normalizer (A : Set G) ≤ M :=
    (corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM hE hqτ2 hA).2.2
  have hA_le_M : A ≤ M := hA.1.trans hE.1.2.1
  have hAne : A ≠ ⊥ := by
    rcases hA.2 with ⟨hAcard, _hAelem⟩
    intro hbot
    have hcard_bot : Nat.card A = 1 := by
      rw [hbot]
      simp
    have hq_sq_eq_one : q.val ^ 2 = 1 := by
      rw [← hAcard, hcard_bot]
    have hq_le_sq : q.val ≤ q.val ^ 2 :=
      le_self_pow q.2.one_lt.le (by decide : 2 ≠ 0)
    exact (ne_of_gt (q.2.one_lt.trans_le hq_le_sq)) hq_sq_eq_one
  have hNormA_proper : Subgroup.normalizer (A : Set G) ≠ ⊤ :=
    section13_normalizer_ne_top_of_ne_bot_le_maximal hM hA_le_M hAne
  obtain ⟨Mstar, hMstar⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) hNormA_proper
  have hMstar_ne_M : Mstar ≠ M := by
    intro hEq
    exact hnotNormA_le_M (by simpa [hEq] using hMstar.2)
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM hE hqτ2 hA).1
  have hE_norm_A : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
  have hE_le_Mstar : E ≤ Mstar := hE_norm_A.trans hMstar.2
  have hA_le_Mstar₀ : A ≤ Mstar := hA.1.trans hE_le_Mstar
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn q Mstar :=
    ⟨hA_le_Mstar₀, hA.2⟩
  have hqσstar : q ∈ section10SigmaPrimes Mstar :=
    ((lemma_12_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mstar)
      (p := q) hM hE hqτ2 hA hMstar) hqτ2).1
  have hA_le_Mstarσ : A ≤ section10Msigma Mstar := by
    have hAsub_p : IsPGroup q.val (A.subgroupOf Mstar) := by
      rcases hA.2 with ⟨_hAcard, hAelem⟩
      haveI : IsElementaryAbelian q.val A := hAelem
      have hAp : IsPGroup q.val A := IsElementaryAbelian.isPGroup q.val A
      exact hAp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := A) (K := Mstar) hA_le_Mstar₀).symm
    have hAsub_le_sigma :
        A.subgroupOf Mstar ≤ section10MsigmaSubgroup Mstar :=
      section13_pSubgroup_le_normal_hall_of_prime_mem
        (R := Mstar) (π := section10SigmaPrimes Mstar)
        (H := section10MsigmaSubgroup Mstar) (A := A.subgroupOf Mstar)
        (p := q) (theorem_10_2_b (G := G) hMstar.1).2 hqσstar hAsub_p
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hA_le_Mstar₀ hx⟩,
        hAsub_le_sigma (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hY_le_CstarP : Y ≤ subgroupCentralizerIn (section10Msigma Mstar) P := by
    intro y hy
    have hyY : y ∈ subgroupCentralizerIn A P := by simpa [Y] using hy
    exact ⟨hA_le_Mstarσ hyY.1, hyY.2⟩
  have hYne : Y ≠ ⊥ :=
    section13_ne_bot_of_prime_order (G := G) (X := Y) (q := q) hYcard
  have hCstarP_ne :
      subgroupCentralizerIn (section10Msigma Mstar) P ≠ ⊥ := by
    intro hbot
    exact hYne (le_bot_iff.mp (by
      rw [← hbot]
      exact hY_le_CstarP))
  have hCnormE : section10NormalIn (subgroupCentralizerIn E A) E :=
    (corollary_12_10_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
      hM hE hqτ2 hA).2.1
  have hpQuot :
      p ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E :=
    section13_lemma_13_12_quotient_prime_of_not_le_centralizer
      (G := G) (E := E) (P := P) (A := A) (p := p)
      hCnormE hP hPnotCentA
  have hpτstar :
      p ∈ section12Tau1Primes Mstar ∪ section12Tau2Primes Mstar :=
    lemma_12_11_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mstar)
      (p := q) hM hE hqτ2 hA hMstar hpQuot
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  rcases hpτstar with hpτ1star | hpτ2star
  · have hPπτ1star : IsPiSubgroup (G := G) (section12Tau1Primes Mstar) P := by
      intro r hrP
      have hr_single : r ∈ ({p} : Set Nat.Primes) :=
        section8_isPiSubgroup_singleton_of_isPGroup hPp r hrP
      have hrp : r = p := by simpa using hr_single
      simpa [hrp] using hpτ1star
    have hP_le_Mstar : P ≤ Mstar := hPE.trans hE_le_Mstar
    obtain ⟨Estar, E₁₂star, E₁star, E₂star, E₃star, hEstar, hP_le_E₁star⟩ :=
      section13_exists_EData_containing_tau1_piSubgroup
        (G := G) (M := Mstar) (A := P) hMstar.1 hP_le_Mstar hPπτ1star
    have hPne : P ≠ ⊥ := by
      have hP_E₁star : P ∈ section10PrimeOrderSubgroupsIn p E₁star := by
        simpa [section10PrimeOrderSubgroupsIn] using ⟨hP_le_E₁star, hPcard⟩
      exact section13_ne_bot_of_prime_order (G := G) (X := P) (q := p) hPcard
    have hY_CstarP_prime :
        Y ∈ section10PrimeOrderSubgroupsIn q
          (subgroupCentralizerIn (section10Msigma Mstar) P) := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hY_le_CstarP, hYcard⟩
    let S : Sylow q.val (section10Msigma Mstar) :=
      Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma Mstar))
    have hMaxCY_Mstar :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) =
          {Mstar} :=
      (lemma_13_6 (G := G) (M := Mstar) (E := Estar) (E₁₂ := E₁₂star)
        (E₁ := E₁star) (E₂ := E₂star) (E₃ := E₃star)
        (P := P) (X := Y) (q := q) S
        hMstar.1 hEstar hPne hP_le_E₁star hqσstar hY_CstarP_prime).1
    have hMstar_mem_CY :
        Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (Y : Set G)) := by
      simp [hMaxCY_Mstar]
    have hMstar_eq_M : Mstar = M := by
      have : Mstar ∈ ({M} : Set (Subgroup G)) := by
        simpa [hMaxCY_M] using hMstar_mem_CY
      simpa using this
    exact hMstar_ne_M hMstar_eq_M
  · have hp_notσstar : p ∉ section10SigmaPrimes Mstar := by
      simpa [section12Tau2Primes] using hpτ2star.1
    have hPπσcstar : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ P :=
      section13_isPiSubgroup_compl_of_isPGroup_not_mem
        (G := G) hp_notσstar hPp
    have hP_le_Mstar : P ≤ Mstar := hPE.trans hE_le_Mstar
    obtain ⟨Estar, E₁₂star, E₁star, E₂star, E₃star, hEstar, hP_le_Estar⟩ :=
      section13_exists_EData_containing_sigma_compl_piSubgroup
        (G := G) (M := Mstar) (A := P) hMstar.1 hP_le_Mstar hPπσcstar
    have hP_Estar : P ∈ section10PrimeOrderSubgroupsIn p Estar := by
      simpa [section10PrimeOrderSubgroupsIn] using ⟨hP_le_Estar, hPcard⟩
    obtain ⟨B, hB⟩ :=
      section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := Mstar) (E := Estar) (E₁₂ := E₁₂star)
        (E₁ := E₁star) (E₂ := E₂star) (E₃ := E₃star)
        hMstar.1 hEstar hpτ2star
    have hP_B : P ∈ section10PrimeOrderSubgroupsIn p B := by
      have hEq :=
        (corollary_12_6_a (G := G) (M := Mstar) (E := Estar)
          (E₁₂ := E₁₂star) (E₁ := E₁star) (E₂ := E₂star)
          (E₃ := E₃star) (A := B) (p := p)
          hMstar.1 hEstar hpτ2star hB).2
      simpa [hEq] using hP_Estar
    have hMaxCP_Mstar :
        section9MaximalSubgroupsContaining (Subgroup.centralizer (P : Set G)) =
          {Mstar} :=
      corollary_12_6_c (G := G) (M := Mstar) (E := Estar)
        (E₁₂ := E₁₂star) (E₁ := E₁star) (E₂ := E₂star)
        (E₃ := E₃star) (A := B) (p := p)
        hMstar.1 hEstar hpτ2star hB P hP_B hCstarP_ne
    have hMstar_mem_CP :
        Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (P : Set G)) := by
      simp [hMaxCP_Mstar]
    have hCP_le_inf :
        subgroupCentralizerIn (section10Msigma M) P ≤ section10Msigma M ⊓ Mstar := by
      intro x hx
      exact ⟨hx.1, hMstar_mem_CP.2 hx.2⟩
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn q M :=
      section13_rankTwo_of_EData hE hA
    have hA_le_Mstar : A ≤ Mstar := hA.1.trans hE_le_Mstar
    have hMsigma_inf :
        section10Msigma M ⊓ Mstar = ⊥ :=
      theorem_12_5_e (G := G) (M := M) (A := A) (p := q)
        hM hqτ2 hA_M Mstar ⟨hMstar.1, hA_le_Mstar⟩ hMstar_ne_M
    apply hCPne
    exact le_bot_iff.mp (by
      rw [← hMsigma_inf]
      exact hCP_le_inf)

/-- Lemma 13.12: if `p ∈ τ₁(M)`, `P ∈ 𝓔_p^1(E)`, `q ∈ τ₂(M)`,
`A ∈ 𝓔_q^2(E)`, and `C_A(P) ≠ 1`, then `C_{M_σ}(P) = 1`. -/
public theorem CFSG.lemma_13_12
    {M E E₁₂ E₁ E₂ E₃ P A : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hqτ2 : q ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn q E)
    (hCAP : subgroupCentralizerIn A P ≠ ⊥) :
    subgroupCentralizerIn (section10Msigma M) P = ⊥ := by
  by_contra hCPne
  exact
    section13_lemma_13_12_contradiction_of_msigma_fixed
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (A := A) (p := p) (q := q)
      hM hE hpτ1 hP hqτ2 hA hCAP hCPne

end Section13
