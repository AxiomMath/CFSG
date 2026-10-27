module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection13.lemma_13_12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Data.Finset.NatDivisors
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Lemma 13 13 from BG Section 13 -/

section Section13

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
private theorem CFSG.section13_primeRank_at_least_two_of_rankTwo
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    2 ≤ primeRank p.val M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hAM : A ≤ M := hA.1
  rcases hA.2 with ⟨hAcard, hAelem⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAcomm : IsMulCommutative A := inferInstance
  let A' : Subgroup M := A.subgroupOf M
  have hA'p : IsPGroup p.val A' :=
    (IsElementaryAbelian.isPGroup p.val A).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM).symm
  have hA'comm : IsMulCommutative A' := by
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := M)
  have hgenA : 2 ≤ generatorRank A := by
    letI : CommGroup A := IsMulCommutative.instCommGroup
    have hcard_dvd : Nat.card A ∣ p.val ^ Group.rank A := by
      simpa using card_dvd_exponent_pow_rank' (G := A) (n := p.val) (fun a =>
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (show Monoid.exponent A ∣ p.val by
            simpa using IsElementaryAbelian.exponent_dvd_p p.val A) a)
    rw [hAcard] at hcard_dvd
    have hle_rank : 2 ≤ Group.rank A := by
      exact (Nat.pow_dvd_pow_iff_le_right p.2.one_lt).mp hcard_dvd
    simpa [generatorRank_eq_group_rank] using hle_rank
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM)
  have hgenA' : 2 ≤ generatorRank A' := by
    simpa [hgen_eq] using hgenA
  exact hgenA'.trans
    (section13_generatorRank_le_primeRank_of_subgroup (R := M) (q := p.val)
      (A := A') hA'p hA'comm)

private theorem CFSG.section13_lemma_13_13_centralizer_prime_le_M_of_tau1
    {M E E₁₂ E₁ E₂ E₃ P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ1 : p ∈ section12Tau1Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) P)) :
    Subgroup.centralizer (Q : Set G) ≤ M := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hQ) with
    ⟨hQleCP, hQcard⟩
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
    ⟨_hE₁E, hHallE₁E⟩
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
  have hPg_le_E₁ : P.conjBy g ≤ E₁ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, huP, hux⟩
    have hx_eq : x = g * u * g⁻¹ := by
      simpa [g, MulAut.conj_apply] using hux.symm
    let uE : E := ⟨u, hPE huP⟩
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
  have hg_norm_sigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section13_le_normalizer_msigma (G := G) (M := M) (hE.1.2.1 gE.property)
  have hQg_le_CPg :
      Q.conjBy g ≤ subgroupCentralizerIn (section10Msigma M) (P.conjBy g) := by
    intro y hy
    have hCeq :
        subgroupCentralizerIn (section10Msigma M) (P.conjBy g) =
          (subgroupCentralizerIn (section10Msigma M) P).conjBy g :=
      section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer
        (G := G) (R := section10Msigma M) (X := P) (g := g) hg_norm_sigma
    rw [hCeq]
    exact Subgroup.map_mono hQleCP hy
  have hQg_card : Nat.card (Q.conjBy g) = q.val := by
    rw [section13_card_conjBy (G := G) Q g, hQcard]
  have hQg_prime :
      Q.conjBy g ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) (P.conjBy g)) := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hQg_le_CPg, hQg_card⟩
  have hqCP : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P) := by
    have hqQ : q.val ∣ Nat.card Q := by rw [hQcard]
    exact hqQ.trans (Subgroup.card_dvd_of_le hQleCP)
  have hqσM : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM hqCP
  let S : Sylow q.val (section10Msigma M) :=
    Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma M))
  have hPg_card : Nat.card (P.conjBy g) = p.val := by
    rw [section13_card_conjBy (G := G) P g, hPcard]
  have hPg_ne : P.conjBy g ≠ ⊥ :=
    section13_ne_bot_of_prime_order (G := G) hPg_card
  have hMaxQg :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Q.conjBy g : Set G)) =
        {M} :=
    (lemma_13_6 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (P := P.conjBy g) (X := Q.conjBy g) (q := q) S
      hM hE hPg_ne hPg_le_E₁ hqσM hQg_prime).1
  have hCentQg_le_M : Subgroup.centralizer (Q.conjBy g : Set G) ≤ M := by
    have hM_mem :
        M ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer (Q.conjBy g : Set G)) := by
      simp [hMaxQg]
    exact hM_mem.2
  intro c hc
  have hgcg_cent : g * c * g⁻¹ ∈ Subgroup.centralizer (Q.conjBy g : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hzQ, hzy⟩
    have hy_eq : y = g * z * g⁻¹ := by
      simpa [g, MulAut.conj_apply] using hzy.symm
    have hzc : z * c = c * z :=
      Subgroup.mem_centralizer_iff.mp hc z hzQ
    calc
      y * (g * c * g⁻¹) = (g * z * g⁻¹) * (g * c * g⁻¹) := by rw [hy_eq]
      _ = g * (z * c) * g⁻¹ := by group
      _ = g * (c * z) * g⁻¹ := by rw [hzc]
      _ = (g * c * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * c * g⁻¹) * y := by rw [hy_eq]
  have hgcg_M : g * c * g⁻¹ ∈ M := hCentQg_le_M hgcg_cent
  have hgM : g ∈ M := hE.1.2.1 gE.property
  have hcM : g⁻¹ * (g * c * g⁻¹) * g ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hgM) hgcg_M) hgM
  simpa [mul_assoc] using hcM

private theorem CFSG.section13_lemma_13_13_centralizer_prime_le_M_of_tau3
    {M E E₁₂ E₁ E₂ E₃ P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ3 : p ∈ section12Tau3Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) P)) :
    Subgroup.centralizer (Q : Set G) ≤ M := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hQ) with
    ⟨hQleCP, hQcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPπ : IsPiSubgroup (G := G) (section12Tau3Primes M) P := by
    intro r hrP
    have hr_single : r ∈ ({p} : Set Nat.Primes) :=
      section8_isPiSubgroup_singleton_of_isPGroup hPp r hrP
    have hrp : r = p := by simpa using hr_single
    simpa [hrp] using hpτ3
  let Psub : Subgroup E := P.subgroupOf E
  have hPπE : IsPiSubgroup (G := E) (section12Tau3Primes M) Psub := by
    simpa [Psub] using section13_isPiSubgroup_subgroupOf (G := G) hPπ hPE
  rcases hE.2.2.2.2 with ⟨hE₃E, hHallE₃E⟩
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
      (section12Tau3Primes M) Psub hPπE hPinv
  obtain ⟨gE, hgEq⟩ :=
    exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := E) hsolvE (π := section12Tau3Primes M)
      (H₁ := H) (H₂ := E₃.subgroupOf E) hHHall hHallE₃E
  let g : G := gE
  have hPg_le_E₃ : P.conjBy g ≤ E₃ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, huP, hux⟩
    have hx_eq : x = g * u * g⁻¹ := by
      simpa [g, MulAut.conj_apply] using hux.symm
    let uE : E := ⟨u, hPE huP⟩
    have huPsub : uE ∈ Psub := by
      simpa [Psub, uE, Subgroup.mem_subgroupOf] using huP
    have hconj_H :
        (MulAut.conj gE).toMonoidHom uE ∈
          H.map (MulAut.conj gE).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨uE, hPsub_le_H huPsub, rfl⟩
    have hconj_E₃ :
        (MulAut.conj gE).toMonoidHom uE ∈ E₃.subgroupOf E := by
      rw [hgEq]
      exact hconj_H
    have hval_E₃ :
        (((MulAut.conj gE).toMonoidHom uE : E) : G) ∈ E₃ := by
      simpa [Subgroup.mem_subgroupOf] using hconj_E₃
    change g * u * g⁻¹ ∈ E₃ at hval_E₃
    simpa [hx_eq] using hval_E₃
  have hg_norm_sigma : g ∈ Subgroup.normalizer (section10Msigma M : Set G) :=
    section13_le_normalizer_msigma (G := G) (M := M) (hE.1.2.1 gE.property)
  have hQg_le_CPg :
      Q.conjBy g ≤ subgroupCentralizerIn (section10Msigma M) (P.conjBy g) := by
    intro y hy
    have hCeq :
        subgroupCentralizerIn (section10Msigma M) (P.conjBy g) =
          (subgroupCentralizerIn (section10Msigma M) P).conjBy g :=
      section11_subgroupCentralizerIn_conjBy_eq_self_of_mem_normalizer
        (G := G) (R := section10Msigma M) (X := P) (g := g) hg_norm_sigma
    rw [hCeq]
    exact Subgroup.map_mono hQleCP hy
  have hQg_card : Nat.card (Q.conjBy g) = q.val := by
    rw [section13_card_conjBy (G := G) Q g, hQcard]
  have hQg_prime_CPg :
      Q.conjBy g ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) (P.conjBy g)) := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hQg_le_CPg, hQg_card⟩
  have hqCP : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P) := by
    have hqQ : q.val ∣ Nat.card Q := by rw [hQcard]
    exact hqQ.trans (Subgroup.card_dvd_of_le hQleCP)
  have hqσM : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM hqCP
  have hPg_card : Nat.card (P.conjBy g) = p.val := by
    rw [section13_card_conjBy (G := G) P g, hPcard]
  have hPg_ne : P.conjBy g ≠ ⊥ :=
    section13_ne_bot_of_prime_order (G := G) hPg_card
  have hQg_ne : Q.conjBy g ≠ ⊥ :=
    section13_ne_bot_of_prime_order (G := G) hQg_card
  have hE₃ne : E₃ ≠ ⊥ := by
    intro hE₃bot
    exact hPg_ne (le_bot_iff.mp (by
      rw [← hE₃bot]
      exact hPg_le_E₃))
  have hnotRegular : ¬ section13ActsRegularlyOn E₃ (section10Msigma M) := by
    intro hregular
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hPg_ne with ⟨x, hxne⟩
    have hxPg : (x : G) ∈ P.conjBy g := x.property
    have hxE₃ : (x : G) ∈ E₃ := hPg_le_E₃ hxPg
    have hxneG : (x : G) ≠ 1 := by
      intro hx1
      exact hxne (Subtype.ext hx1)
    have hElemBot :
        elementCentralizerIn (section10Msigma M) (x : G) = ⊥ :=
      hregular.2 (x : G) hxE₃ hxneG
    have hQg_le_elem :
        Q.conjBy g ≤ elementCentralizerIn (section10Msigma M) (x : G) := by
      intro y hy
      have hyC : y ∈ subgroupCentralizerIn (section10Msigma M) (P.conjBy g) :=
        hQg_le_CPg hy
      refine ⟨hyC.1, ?_⟩
      change y ∈ Subgroup.centralizer ({(x : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact Subgroup.mem_centralizer_iff.mp hyC.2 (x : G) hxPg
    exact hQg_ne (le_bot_iff.mp (by
      rw [← hElemBot]
      exact hQg_le_elem))
  have hE₁ne : E₁ ≠ ⊥ :=
    corollary_13_11_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hPrimeE :
      section13ActsPrimeManner E (section10Msigma M) :=
    corollary_13_11_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hE₃ne hnotRegular
  have hPg_prime_E : P.conjBy g ∈ section12PrimeOrderSubgroups E := by
    refine ⟨hPg_le_E₃.trans hE₃E, ?_⟩
    exact ⟨p, hPg_card⟩
  have hCPg_le_CE :
      subgroupCentralizerIn (section10Msigma M) (P.conjBy g) ≤
        subgroupCentralizerIn (section10Msigma M) E :=
    hPrimeE.2 (P.conjBy g) hPg_prime_E
  have hQg_le_CE :
      Q.conjBy g ≤ subgroupCentralizerIn (section10Msigma M) E :=
    hQg_le_CPg.trans hCPg_le_CE
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := E₁) hE₁ne with
    ⟨r, R, hR_le_E₁, hRcard⟩
  have hRne : R ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hRcard
  have hE₁E : E₁ ≤ E := (section12_E1_hall_in_E (G := G) hE.2.1 hE.2.2.1).1
  have hQg_prime_CR :
      Q.conjBy g ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) R) := by
    refine ⟨?_, hQg_card⟩
    intro y hy
    have hyCE : y ∈ subgroupCentralizerIn (section10Msigma M) E :=
      hQg_le_CE hy
    refine ⟨hyCE.1, ?_⟩
    change y ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact Subgroup.mem_centralizer_iff.mp hyCE.2 z (hE₁E (hR_le_E₁ hz))
  let S : Sylow q.val (section10Msigma M) :=
    Classical.choice (Sylow.nonempty (p := q.val) (G := section10Msigma M))
  have hMaxQg :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (Q.conjBy g : Set G)) =
        {M} :=
    (lemma_13_6 (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃)
      (P := R) (X := Q.conjBy g) (q := q) S
      hM hE hRne hR_le_E₁ hqσM hQg_prime_CR).1
  have hCentQg_le_M : Subgroup.centralizer (Q.conjBy g : Set G) ≤ M := by
    have hM_mem :
        M ∈ section9MaximalSubgroupsContaining
          (Subgroup.centralizer (Q.conjBy g : Set G)) := by
      simp [hMaxQg]
    exact hM_mem.2
  intro c hc
  have hgcg_cent : g * c * g⁻¹ ∈ Subgroup.centralizer (Q.conjBy g : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hzQ, hzy⟩
    have hy_eq : y = g * z * g⁻¹ := by
      simpa [g, MulAut.conj_apply] using hzy.symm
    have hzc : z * c = c * z :=
      Subgroup.mem_centralizer_iff.mp hc z hzQ
    calc
      y * (g * c * g⁻¹) = (g * z * g⁻¹) * (g * c * g⁻¹) := by rw [hy_eq]
      _ = g * (z * c) * g⁻¹ := by group
      _ = g * (c * z) * g⁻¹ := by rw [hzc]
      _ = (g * c * g⁻¹) * (g * z * g⁻¹) := by group
      _ = (g * c * g⁻¹) * y := by rw [hy_eq]
  have hgcg_M : g * c * g⁻¹ ∈ M := hCentQg_le_M hgcg_cent
  have hgM : g ∈ M := hE.1.2.1 gE.property
  have hcM : g⁻¹ * (g * c * g⁻¹) * g ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hgM) hgcg_M) hgM
  simpa [mul_assoc] using hcM

private theorem CFSG.section13_lemma_13_13_centralizer_prime_le_M
    {M E E₁₂ E₁ E₂ E₃ P Q : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q
      (subgroupCentralizerIn (section10Msigma M) P)) :
    Subgroup.centralizer (Q : Set G) ≤ M := by
  rcases hpτ13 with hpτ1 | hpτ3
  · exact section13_lemma_13_13_centralizer_prime_le_M_of_tau1
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (Q := Q) (p := p) (q := q)
      hM hE hpτ1 hP hQ
  · exact section13_lemma_13_13_centralizer_prime_le_M_of_tau3
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (Q := Q) (p := p) (q := q)
      hM hE hpτ3 hP hQ

private theorem CFSG.section13_lemma_13_13_tau2_branch_absurd
    {M E E₁₂ E₁ E₂ E₃ P Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (P : Set G)))
    (hpτ2star : p ∈ section12Tau2Primes Mstar) :
    False := by
  classical
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hPM : P ≤ M := hPE.trans hE.1.2.1
  have hnotconj : section12NotConjugate Mstar M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := P) (p := p)
      hM hPp hPne hPM hMstar (Or.inr hpτ13)
  rcases section13_exists_prime_order_subgroup_le_of_ne_bot
      (G := G) (P := subgroupCentralizerIn (section10Msigma M) P) hCP with
    ⟨q, Q, hQleCP, hQcard⟩
  have hQprimeCP :
      Q ∈ section10PrimeOrderSubgroupsIn q
        (subgroupCentralizerIn (section10Msigma M) P) := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨hQleCP, hQcard⟩
  have hqCP : q ∈ subgroupPrimeSet (subgroupCentralizerIn (section10Msigma M) P) := by
    have hqQ : q.val ∣ Nat.card Q := by rw [hQcard]
    exact hqQ.trans (Subgroup.card_dvd_of_le hQleCP)
  have hqσM : q ∈ section10SigmaPrimes M :=
    section13_sigma_of_mem_centralizer_msigma (G := G) hM hqCP
  have hq_notσstar : q ∉ section10SigmaPrimes Mstar := by
    intro hqσstar
    exact (Set.disjoint_left.mp
      (theorem_13_9 (G := G) hM hMstar.1 hnotconj) hqσM) hqσstar
  have hQq : IsPGroup q.val Q := by
    refine IsPGroup.of_card (p := q.val) (G := Q) (n := 1) ?_
    simpa [pow_one] using hQcard
  have hP_le_Mstar : P ≤ Mstar := Subgroup.le_normalizer.trans hMstar.2
  have hQ_le_Mstar : Q ≤ Mstar := by
    intro x hx
    exact hMstar.2 ((centralizer_le_normalizer P) ((hQleCP hx).2))
  have hp_notσstar : p ∉ section10SigmaPrimes Mstar := by
    simpa [section12Tau2Primes] using hpτ2star.1
  have hPπσcstar : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ P :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem
      (G := G) hp_notσstar hPp
  have hQπσcstar : IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ Q :=
    section13_isPiSubgroup_compl_of_isPGroup_not_mem
      (G := G) hq_notσstar hQq
  have hP_norm_Q : P ≤ Subgroup.normalizer (Q : Set G) := by
    intro x hx
    apply centralizer_le_normalizer Q
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp ((hQleCP hy).2) x hx).symm
  have hPQπσcstar :
      IsPiSubgroup (G := G) (section10SigmaPrimes Mstar)ᶜ (P ⊔ Q) :=
    section13_isPiSubgroup_sup_of_le_normalizer
      (G := G) hPπσcstar hQπσcstar hP_norm_Q
  have hPQ_le_Mstar : P ⊔ Q ≤ Mstar := sup_le hP_le_Mstar hQ_le_Mstar
  obtain ⟨Estar, E₁₂star, E₁star, E₂star, E₃star, hEstar, hPQ_le_Estar⟩ :=
    section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := Mstar) (A := P ⊔ Q) hMstar.1 hPQ_le_Mstar hPQπσcstar
  have hP_Estar : P ∈ section10PrimeOrderSubgroupsIn p Estar := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨le_sup_left.trans hPQ_le_Estar, hPcard⟩
  have hQ_Estar : Q ∈ section10PrimeOrderSubgroupsIn q Estar := by
    simpa [section10PrimeOrderSubgroupsIn] using ⟨le_sup_right.trans hPQ_le_Estar, hQcard⟩
  obtain ⟨A, hA⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := Mstar) (E := Estar) (E₁₂ := E₁₂star)
      (E₁ := E₁star) (E₂ := E₂star) (E₃ := E₃star)
      hMstar.1 hEstar hpτ2star
  have hP_A : P ∈ section10PrimeOrderSubgroupsIn p A := by
    have hEq :=
      (corollary_12_6_a (G := G) (M := Mstar) (E := Estar)
        (E₁₂ := E₁₂star) (E₁ := E₁star) (E₂ := E₂star)
        (E₃ := E₃star) (A := A) (p := p)
        hMstar.1 hEstar hpτ2star hA).2
    simpa [hEq] using hP_Estar
  have hP_le_A : P ≤ A := hP_A.1
  have hCGQ_le_M : Subgroup.centralizer (Q : Set G) ≤ M :=
    section13_lemma_13_13_centralizer_prime_le_M
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (P := P) (Q := Q) (p := p) (q := q)
      hM hE hpτ13 hP hQprimeCP
  have hprankM : primeRank p.val M = 1 := by
    rcases hpτ13 with hpτ1 | hpτ3
    · simpa [section12Tau1Primes] using hpτ1.2.2
    · simpa [section12Tau3Primes] using hpτ3.2.2
  have hA_not_le_CEQ : ¬ A ≤ subgroupCentralizerIn Estar Q := by
    intro hA_CEQ
    have hA_le_M : A ≤ M := by
      intro a ha
      exact hCGQ_le_M (hA_CEQ ha).2
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
      ⟨hA_le_M, hA.2⟩
    have hge2 : 2 ≤ primeRank p.val M :=
      section13_primeRank_at_least_two_of_rankTwo (G := G) hA_M
    omega
  have hQ_not_le_CEA : ¬ Q ≤ subgroupCentralizerIn Estar A := by
    intro hQ_CEA
    apply hA_not_le_CEQ
    intro a ha
    refine ⟨hA.1 ha, ?_⟩
    change a ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hQ_CEA hy).2 a ha).symm
  have hCnormEstar : section10NormalIn (subgroupCentralizerIn Estar A) Estar :=
    (corollary_12_10_c (G := G) (M := Mstar) (E := Estar)
      (E₁₂ := E₁₂star) (E₁ := E₁star) (E₂ := E₂star)
      (E₃ := E₃star) (A := A) (p := p)
      hMstar.1 hEstar hpτ2star hA).2.1
  have hqQuot :
      q ∈ section12QuotientPrimeSet (subgroupCentralizerIn Estar A) Estar :=
    section13_lemma_13_12_quotient_prime_of_not_le_centralizer
      (G := G) (E := Estar) (P := Q) (A := A) (p := q)
      hCnormEstar hQ_Estar hQ_not_le_CEA
  have hqτ1star : q ∈ section12Tau1Primes Mstar :=
    ((corollary_12_10_c (G := G) (M := Mstar) (E := Estar)
      (E₁₂ := E₁₂star) (E₁ := E₁star) (E₂ := E₂star)
      (E₃ := E₃star) (A := A) (p := p)
      hMstar.1 hEstar hpτ2star hA).2.2) hqQuot
  have hCAQne : subgroupCentralizerIn A Q ≠ ⊥ := by
    intro hbot
    have hP_le_bot : P ≤ ⊥ := by
      rw [← hbot]
      intro x hx
      refine ⟨hP_le_A hx, ?_⟩
      change x ∈ Subgroup.centralizer (Q : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp ((hQleCP hy).2) x hx).symm
    exact hPne (le_bot_iff.mp hP_le_bot)
  have hCMstarσQ :
      subgroupCentralizerIn (section10Msigma Mstar) Q = ⊥ :=
    lemma_13_12 (G := G) (M := Mstar) (E := Estar) (E₁₂ := E₁₂star)
      (E₁ := E₁star) (E₂ := E₂star) (E₃ := E₃star)
      (P := Q) (A := A) (p := q) (q := p)
      hMstar.1 hEstar hqτ1star hQ_Estar hpτ2star hA hCAQne
  have hcomm_ne : ⁅A, Q⁆ ≠ ⊥ := by
    intro hcomm_bot
    apply hA_not_le_CEQ
    intro a ha
    refine ⟨hA.1 ha, ?_⟩
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot) ha
  rcases corollary_12_9_c (G := G) (M := Mstar) (E := Estar)
      (E₁₂ := E₁₂star) (E₁ := E₁star) (E₂ := E₂star)
      (E₃ := E₃star) (A := A) (Q := Q) (p := p) (q := q)
      hMstar.1 hEstar hpτ2star hA hqτ1star hQ_Estar hCMstarσQ hcomm_ne with
    ⟨hCAQprime, hnotCentCAQ_le_Mstar⟩
  have hP_le_CAQ : P ≤ subgroupCentralizerIn A Q := by
    intro x hx
    refine ⟨hP_le_A hx, ?_⟩
    change x ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp ((hQleCP hy).2) x hx).symm
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hCAQprime) with
    ⟨_hCAQ_le_A, hCAQcard⟩
  have hP_eq_CAQ : P = subgroupCentralizerIn A Q :=
    Subgroup.eq_of_le_of_card_ge hP_le_CAQ (by rw [hPcard, hCAQcard])
  have hCentCAQ_le_Mstar :
      Subgroup.centralizer (subgroupCentralizerIn A Q : Set G) ≤ Mstar := by
    have hCentP_le_Mstar : Subgroup.centralizer (P : Set G) ≤ Mstar :=
      (centralizer_le_normalizer P).trans hMstar.2
    simpa [← hP_eq_CAQ] using hCentP_le_Mstar
  exact hnotCentCAQ_le_Mstar hCentCAQ_le_Mstar

/-- Lemma 13.13: if `p ∈ τ₁(M) ∪ τ₃(M)`, `P ∈ 𝓔_p^1(E)`, and
`C_{M_σ}(P) ≠ 1`, then every maximal subgroup containing `N_G(P)` has
`p ∈ σ`. -/
public theorem CFSG.lemma_13_13
    {M E E₁₂ E₁ E₂ E₃ P : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hpτ13 : p ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hP : P ∈ section10PrimeOrderSubgroupsIn p E)
    (hCP : subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) :
    ∀ Mstar : Subgroup G,
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (P : Set G)) →
        p ∈ section10SigmaPrimes Mstar := by
  classical
  intro Mstar hMstar
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hP) with
    ⟨hPE, hPcard⟩
  have hPp : IsPGroup p.val P := by
    refine IsPGroup.of_card (p := p.val) (G := P) (n := 1) ?_
    simpa [pow_one] using hPcard
  have hPne : P ≠ ⊥ := section13_ne_bot_of_prime_order (G := G) hPcard
  have hPM : P ≤ M := hPE.trans hE.1.2.1
  rcases lemma_12_2_a (G := G) (M := M) (Mstar := Mstar) (X := P)
      (p := p) hM hPp hPne hPM hMstar with
    hpσstar | hpτ2star
  · exact hpσstar
  · exact False.elim
      (section13_lemma_13_13_tau2_branch_absurd
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (P := P) (Mstar := Mstar) (p := p)
        hM hE hpτ13 hP hCP hMstar hpτ2star)

end Section13
