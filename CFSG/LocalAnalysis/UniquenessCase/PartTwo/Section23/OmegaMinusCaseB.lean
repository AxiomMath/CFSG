module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusStructure
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ComponentShapes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProductComponents
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121B
public import CFSG.HardMathSupport.Solomon.Coordinator.WeakBalance
public import CFSG.GroupTheory.PRankLeOneOfSylowLe
public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.GH74.BNPair.Lemma3013
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusQ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem n_eq_four_of_caseB (c : Ctx23L D Ch) (h52 : S23_5_2Omega D Ch)
    (h1930 : H1930 D) (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) : c.n = 4 := by
  have h := (h52 h1930 c hOm).2
  rw [hB'.1] at h
  omega

private theorem odd_card_B0_of_caseB (c : Ctx23L D Ch) (h52 : S23_5_2Omega D Ch)
    (h1930 : H1930 D) (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) : Odd (Nat.card c.B0) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2dvd : 2 ∣ Nat.card c.B0 := even_iff_two_dvd.mp heven
  have h2pi : 2 ∈ piSet c.B0 := ⟨Nat.prime_two, h2dvd⟩
  rw [c.hpi, c.n_eq_four_of_caseB h52 h1930 hOm hB'] at h2pi
  norm_num [etaSet] at h2pi

private theorem card_B0_dvd_bar2 (c : Ctx23L D Ch) (h52 : S23_5_2Omega D Ch)
    (h1930 : H1930 D) (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) : Nat.card c.B0 ∣ Nat.card (Bar2 c.L) := by
  have hodd : Odd (Nat.card c.B0) := c.odd_card_B0_of_caseB h52 h1930 hOm hB'
  have hB0leL : c.B0 ≤ c.L := c.hB0.1.trans c.hL0L
  have hdvdL : Nat.card c.B0 ∣ Nat.card ↥c.L := Subgroup.card_dvd_of_le hB0leL
  have hcardL : Nat.card ↥c.L =
      Nat.card (Bar2 c.L) * Nat.card ↥(CFSG.pCore 2 ↥c.L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥c.L)
  have hcop : Nat.Coprime (Nat.card c.B0) (Nat.card ↥(CFSG.pCore 2 ↥c.L)) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).exists_card_eq
    rw [hk]
    exact hodd.coprime_two_right.pow_right k
  refine hcop.dvd_of_dvd_mul_right ?_
  rw [← hcardL]
  exact hdvdL

private theorem card_bar2_eq_4080 (c : Ctx23L D Ch) (hOm : IsOmegaMinus (Bar2 c.L) 4
    (CFSG.Open.pRank 2 D.Z)) (hB' : S23_23OmegaCaseB c) :
    Nat.card (Bar2 c.L) = 4080 := by
  have hOm2 : IsOmegaMinus (Bar2 c.L) 4 2 := by
    simpa only [hB'.1] using hOm
  have hL2 : IsL2 (Bar2 c.L) 4 :=
    isL2_two_mul_of_isOmegaMinus_four (m := 2) (by norm_num) hOm2
  rw [hL2.card_eq_lieOrd (by norm_num : 2 ≠ 0)]
  rw [CFSG.EvenSmallLie.CatalogOrders.lieOrd,
    CFSG.RankThree.PartOne.KFU.ordA_one_two_pow (by norm_num : 1 ≤ 4)]
  norm_num

private theorem prime_dvd_card_B0_of_caseB (c : Ctx23L D Ch) (h52 : S23_5_2Omega D Ch)
    (h1930 : H1930 D) (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ Nat.card c.B0) :
    p = 3 ∨ p = 5 := by
  have hpPi : p ∈ piSet c.B0 := ⟨hp, hpdvd⟩
  rw [c.hpi, c.n_eq_four_of_caseB h52 h1930 hOm hB'] at hpPi
  have hpd : p ∣ 2 ^ 4 - 1 := hpPi.2
  rw [show 2 ^ 4 - 1 = 3 * 5 by norm_num] at hpd
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h)

private theorem card_B0_eq_fifteen (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch)
    (h52 : S23_5_2Omega D Ch) (h53 : S23_5_3 D Ch)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) : Nat.card c.B0 = 15 := by
  have hcardB0dvd : Nat.card c.B0 ∣ Nat.card (Bar2 c.L) :=
    c.card_B0_dvd_bar2 h52 h1930 hOm hB'
  have hcard4080 : Nat.card (Bar2 c.L) = 4080 := c.card_bar2_eq_4080 hOm hB'
  have h3pi : 3 ∈ piSet c.B0 := by
    rw [c.hpi, c.n_eq_four_of_caseB h52 h1930 hOm hB']
    norm_num [etaSet]
  have h5pi : 5 ∈ piSet c.B0 := by
    rw [c.hpi, c.n_eq_four_of_caseB h52 h1930 hOm hB']
    norm_num [etaSet]
  have hdvd4080 : Nat.card c.B0 ∣ 4080 := by
    rwa [hcard4080] at hcardB0dvd
  have hdvd255 : Nat.card c.B0 ∣ 255 := by
    have hcop16 : Nat.Coprime (Nat.card c.B0) (2 ^ 4) :=
      (c.odd_card_B0_of_caseB h52 h1930 hOm hB').coprime_two_right.pow_right 4
    refine hcop16.dvd_of_dvd_mul_right ?_
    simpa [show 255 * 2 ^ 4 = 4080 by norm_num] using hdvd4080
  have h17not : ¬ (17 : ℕ) ∣ Nat.card c.B0 := by
    intro h17
    rcases c.prime_dvd_card_B0_of_caseB h52 h1930 hOm hB'
      (by norm_num : Nat.Prime 17) h17 with h | h <;> norm_num at h
  have hdvd15 : Nat.card c.B0 ∣ 15 := by
    have hcop17 : Nat.Coprime (Nat.card c.B0) 17 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 17)).2 h17not).symm
    refine hcop17.dvd_of_dvd_mul_right ?_
    simpa [show 15 * 17 = 255 by norm_num] using hdvd255
  have h15dvd : 15 ∣ Nat.card c.B0 := by
    have h := Nat.lcm_dvd h3pi.2 h5pi.2
    norm_num at h
    exact h
  exact (Nat.dvd_antisymm h15dvd hdvd15).symm

private theorem kernel_B0_normalizerHom {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hBN : c.B0 ≤ Subgroup.normalizer (D.Z : Set G))
    (f : ↥c.B0 →* MulAut ↥D.Z)
    (hf : f = (Subgroup.normalizerMonoidHom (D.Z : Subgroup G)).comp
      (Subgroup.inclusion hBN)) :
    f.ker = (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.B0 := by
  subst f
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hx' := congrArg Subtype.val
      (congrArg (fun g : MulAut ↥D.Z => g ⟨z, hz⟩) hx)
    simp only [MonoidHom.comp_apply, Subgroup.coe_inclusion, MulAut.one_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at hx'
    have h1 : z * (x : G) = ((x : G) * z * (x : G)⁻¹) * (x : G) := by rw [hx']
    calc z * (x : G) = ((x : G) * z * (x : G)⁻¹) * (x : G) := h1
      _ = (x : G) * z := by group
  · rintro ⟨-, hxcent⟩
    refine MulEquiv.ext fun z => ?_
    simp only [MonoidHom.comp_apply, MulAut.one_apply]
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion]
    have hcomm := Subgroup.mem_centralizer_iff.mp hxcent (z : G) z.2
    calc (x : G) * (z : G) * (x : G)⁻¹ = (z : G) * (x : G) * (x : G)⁻¹ := by
          rw [hcomm]
      _ = (z : G) := by group

private theorem card_B5_mul_range {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hcardB0 : Nat.card c.B0 = 15) (f : ↥c.B0 →* MulAut ↥D.Z)
    (hker : f.ker = (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf c.B0)
    (hAut : Nat.card (MulAut ↥D.Z) = 6) :
    Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) * Nat.card ↥f.range = 15 ∧
      Nat.card ↥f.range ∣ 3 := by
  have hker_card : Nat.card ↥f.ker =
      Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmul : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) *
      Nat.card ↥f.range = 15 := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hker_card, hcardB0] at h
    exact h
  have hrange_dvd6 : Nat.card ↥f.range ∣ 6 := by
    rw [← hAut]
    exact Subgroup.card_subgroup_dvd_card _
  have hrange_dvd15 : Nat.card ↥f.range ∣ 15 := by
    have h := Subgroup.card_range_dvd f
    rwa [hcardB0] at h
  have hrange_dvd3 : Nat.card ↥f.range ∣ 3 := by
    have h := Nat.dvd_gcd hrange_dvd6 hrange_dvd15
    rw [show Nat.gcd 6 15 = 3 by norm_num] at h
    simpa using h
  exact ⟨hmul, hrange_dvd3⟩

private theorem card_B5_eq_five_of_range {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h53 : S23_5_3 D Ch)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) (f : ↥c.B0 →* MulAut ↥D.Z)
    (hmul : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) *
      Nat.card ↥f.range = 15)
    (hrange_dvd3 : Nat.card ↥f.range ∣ 3) :
    Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5 := by
  have hrange_le3 : Nat.card ↥f.range ≤ 3 := Nat.le_of_dvd (by norm_num) hrange_dvd3
  have hrange_pos : 0 < Nat.card ↥f.range := Nat.card_pos
  have hrange_ne2 : Nat.card ↥f.range ≠ 2 := by
    intro h2
    rw [h2] at hrange_dvd3
    norm_num at hrange_dvd3
  have hrange_cases : Nat.card ↥f.range = 1 ∨ Nat.card ↥f.range = 3 := by omega
  rcases hrange_cases with h1 | h3
  · rw [h1, mul_one] at hmul
    have h3dvd : 3 ∣ Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) := by
      rw [hmul]
      norm_num
    have h3mem : 3 ∈ piSet (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) :=
      ⟨Nat.prime_three, h3dvd⟩
    have hcases := h53 h1930 c.withB0 c.hpi
    rcases hcases with hbot | ⟨-, hpi5⟩
    · have hbot' : c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) = ⊥ := by
        simpa [Ctx23L.withB0] using hbot
      rw [hbot'] at hmul
      norm_num at hmul
    · have hpi5' : piSet (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) =
          {p | p.Prime ∧ p ∣ 2 ^ (CFSG.Open.pRank 2 D.Z) + 1} := by
        simpa [Ctx23L.withB0] using hpi5
      rw [hpi5', hB'.1] at h3mem
      norm_num at h3mem
  · rw [h3] at hmul
    omega

theorem card_B0_of_caseB (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch)
    (h52 : S23_5_2Omega D Ch) (h53 : S23_5_3 D Ch)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hB' : S23_23OmegaCaseB c) :
    Nat.card c.B0 = 15 ∧
      Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5 := by
  have hcardB0 : Nat.card c.B0 = 15 :=
    card_B0_eq_fifteen c h1930 h4 h52 h53 hOm hB'
  refine ⟨hcardB0, ?_⟩
  have hZel : IsElemAbelian 2 D.Z := c.isElemAbelian_Z h4 h1930
  have hZcard : Nat.card D.Z = 4 := by
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZel, hB'.1]
    norm_num
  have hBN : c.B0 ≤ Subgroup.normalizer (D.Z : Set G) := by
    rw [← (h4 h1930 c).1]
    exact c.hBM.trans (h4 h1930 c).2.2
  letI : CommGroup ↥D.Z :=
    { (inferInstance : Group ↥D.Z) with mul_comm := fun a b => hZel.1.is_comm.comm a b }
  have hZsq : ∀ z : ↥D.Z, z ^ 2 = 1 := fun z => Subtype.ext (hZel.2 z z.2)
  have hAut : Nat.card (MulAut ↥D.Z) = 6 :=
    CFSG.CGT.PushingUpLit.CGT6.card_mulAut_of_card_four hZsq hZcard
  let f : ↥c.B0 →* MulAut ↥D.Z :=
    (Subgroup.normalizerMonoidHom (D.Z : Subgroup G)).comp (Subgroup.inclusion hBN)
  have hker := kernel_B0_normalizerHom c hBN f rfl
  obtain ⟨hmul, hrange⟩ := card_B5_mul_range c hcardB0 f hker hAut
  exact card_B5_eq_five_of_range c h1930 h53 hOm hB' f hmul hrange

private theorem B5_permutes_T {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hB5leB0 : c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) ≤ c.B0)
    (hperm : Permutes c.B0 D.T) :
    Permutes (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) D.T := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  have hB5leB0' : B5 ≤ c.B0 := hB5leB0
  have hB5centZ : B5 ≤ Subgroup.centralizer (D.Z : Set G) := inf_le_right
  have hTcentZ : D.T ≤ Subgroup.centralizer (D.Z : Set G) :=
    le_centralizer_omegaOneCenterIn D.T
  have hZmul : ∀ {a b : G}, a ∈ Subgroup.centralizer (D.Z : Set G) →
      b ∈ Subgroup.centralizer (D.Z : Set G) →
      a * b ∈ Subgroup.centralizer (D.Z : Set G) :=
    fun ha hb => (Subgroup.centralizer (D.Z : Set G)).mul_mem ha hb
  unfold Permutes
  apply Set.ext
  intro x
  constructor
  · rintro ⟨b, hb, t, ht, rfl⟩
    have hmem : b * t ∈ (c.B0 : Set G) * (D.T : Set G) :=
      ⟨b, hB5leB0' hb, t, ht, rfl⟩
    rw [hperm] at hmem
    obtain ⟨t', ht', b', hb', hbt⟩ := hmem
    have hxZ : b * t ∈ Subgroup.centralizer (D.Z : Set G) :=
      hZmul (hB5centZ hb) (hTcentZ ht)
    have hb'Z : b' ∈ Subgroup.centralizer (D.Z : Set G) := by
      have hb'eq : b' = t'⁻¹ * (b * t) := by rw [← hbt]; group
      rw [hb'eq]
      exact hZmul ((Subgroup.centralizer (D.Z : Set G)).inv_mem (hTcentZ ht')) hxZ
    exact ⟨t', ht', b', ⟨hb', hb'Z⟩, hbt⟩
  · rintro ⟨t, ht, b, hb, rfl⟩
    have hmem : t * b ∈ (D.T : Set G) * (c.B0 : Set G) :=
      ⟨t, ht, b, hB5leB0' hb, rfl⟩
    rw [← hperm] at hmem
    obtain ⟨b', hb', t', ht', hbt⟩ := hmem
    have hxZ : t * b ∈ Subgroup.centralizer (D.Z : Set G) :=
      hZmul (hTcentZ ht) (hB5centZ hb)
    have hb'Z : b' ∈ Subgroup.centralizer (D.Z : Set G) := by
      have hb'eq : b' = (t * b) * t'⁻¹ := by rw [← hbt]; group
      rw [hb'eq]
      exact hZmul hxZ ((Subgroup.centralizer (D.Z : Set G)).inv_mem (hTcentZ ht'))
    exact ⟨b', ⟨hb', hb'Z⟩, t', ht', hbt⟩

private theorem B5_isMulCommutative {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hB0comm : IsMulCommutative ↥c.B0) :
    IsMulCommutative ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  apply Subtype.ext
  exact congrArg (fun x : ↥c.B0 => (x : G))
    (hB0comm.is_comm.comm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩)

private theorem B5_mem_calB {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5)
    (hB0le : c.B0 ≤ c.L0)
    (hperm : Permutes c.B0 D.T) (hinv : InvertedOutside D.M c.L0 c.B0) :
    (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ∈ calB D.T D.M c.L0 := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  have hB5leB0 : B5 ≤ c.B0 := inf_le_left
  have hB5leL0 : B5 ≤ c.L0 := hB5leB0.trans hB0le
  have hB5cyc : IsCyclic ↥B5 := isCyclic_of_prime_card (p := 5) h5
  have hB5sq : Squarefree (Nat.card ↥B5) := by
    rw [h5]
    exact Nat.prime_five.squarefree
  have hB5odd : Odd (Nat.card ↥B5) := by rw [h5]; norm_num
  have hpermB5 : Permutes B5 D.T := B5_permutes_T c inf_le_left hperm
  have hinvB5 : InvertedOutside D.M c.L0 B5 := by
    obtain ⟨t, htL, htM, ht2, htinv⟩ := hinv
    exact ⟨t, htL, htM, ht2, fun x hx => htinv x (hB5leB0 hx)⟩
  exact ⟨hB5leL0, hB5cyc, hB5sq, hB5odd, hpermB5, hinvB5⟩

theorem B5_mem_calB1 (c : Ctx23L D Ch)
    (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5) :
    (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ∈ calB1 D.T D.M c.L0 := by
  obtain ⟨hB0le, hB0comm, B, C, hBcal, hCcomm, hCodd, hCsyl, hB0eq, hperm, hinv, -⟩ := c.hB0
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  have hB5comm : IsMulCommutative ↥B5 := B5_isMulCommutative c hB0comm
  have hB5calB : B5 ∈ calB D.T D.M c.L0 := B5_mem_calB c h5 hB0le hperm hinv
  have hpermB5 : Permutes B5 D.T := hB5calB.2.2.2.2.1
  have hinvB5 : InvertedOutside D.M c.L0 B5 := hB5calB.2.2.2.2.2
  have hbotcomm : IsMulCommutative ↥(⊥ : Subgroup G) := inferInstance
  have hbotodd : Odd (Nat.card ↥(⊥ : Subgroup G)) := by simp
  have hbotsyl : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(⊥ : Subgroup G) →
      ∃ P : Sylow p (⊥ : Subgroup G), Nat.card P = p ^ 2 ∧ ¬ IsCyclic ↥P := by
    intro p hp hpd
    exact absurd (by simpa using hpd) hp.ne_one
  have hAeq : B5 = B5 ⊔ (⊥ : Subgroup G) := by rw [sup_bot_eq]
  have hIrr : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(⊥ : Subgroup G) →
      IrrOn (D.T ⊓ Subgroup.normalizer (B5 : Set G)) (CFSG.Open.pCoreOf p B5) := by
    intro p hp hpd
    exact absurd (by simpa using hpd) hp.ne_one
  exact ⟨hB5calB.1, hB5comm, B5, ⊥, hB5calB, hbotcomm, hbotodd, hbotsyl, hAeq,
    hpermB5, hinvB5, hIrr⟩

theorem five_not_mem_sig (c : Ctx23L D Ch) (h1930 : H1930 D) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5) :
    (5 : ℕ) ∉ D.sig := by
  intro h5sig
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  have hB5cal : B5 ∈ calB1 D.T D.M c.L0 := c.B5_mem_calB1 h5
  have hB5ne : B5 ≠ ⊥ := by
    have h5' : Nat.card ↥B5 = 5 := h5
    intro hbot
    rw [hbot] at h5'
    norm_num at h5'
  have hB5M : B5 ≤ D.M := inf_le_left.trans c.hBM
  have hB5p : IsPGroup 5 ↥B5 := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [h5]
    norm_num
  have h5sig1 : 5 ∈ D.sig1 := by
    rw [← h6 h1930 c]
    exact h5sig
  have hB5U : B5 ∈ uniqueSet D.M :=
    mem_uniqueSet_of_isStronglyPEmbedded Nat.prime_five (hsp 5 h5sig1) hB5M hB5ne hB5p
  have hN : Subgroup.normalizer (B5 : Set G) ≤ D.M :=
    normalizer_le_of_mem_uniqueSet D.maxLocal hB5U
  let c5 : Ctx23L D Ch := c.withB B5 hB5cal inf_le_left
  exact (s21_2 D Ch h1930 c5.toCtx23.toCtx21 B5 le_rfl) hN

private theorem mem_of_square_mem_of_pow_five {X : Type} [Group X] {F : Subgroup X} {x : X}
    (h2 : x ^ 2 ∈ F) (h5 : x ^ 5 = 1) : x ∈ F := by
  have hcalc : x = (x ^ 2) ^ 3 := by
    rw [← pow_mul]
    calc x = x ^ 6 := by
          rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ, h5, one_mul]
      _ = x ^ (2 * 3) := by norm_num
  rw [hcalc]
  exact F.pow_mem h2 3

private theorem bar_commutator_eq_square {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (b t : G) (hbB5 : b ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G))
    (hbM : b ∈ D.M) (htT : t ∈ D.T) (htinv : t * b * t⁻¹ = b⁻¹) :
    ⁅uc22p21cPi D.M ⟨b, hbM⟩, uc22p21cPi D.M ⟨t, D.sylowM.le htT⟩⁆ =
      (uc22p21cPi D.M ⟨b, hbM⟩) ^ 2 := by
  let bM : ↥D.M := ⟨b, hbM⟩
  let tM : ↥D.M := ⟨t, D.sylowM.le htT⟩
  let π : ↥D.M →* Bar2 D.M := uc22p21cPi D.M
  have hbar : π tM * π bM * (π tM)⁻¹ = (π bM)⁻¹ := by
    have hEq : tM * bM * tM⁻¹ = bM⁻¹ := Subtype.ext htinv
    calc π tM * π bM * (π tM)⁻¹ = π (tM * bM * tM⁻¹) := by
          simp only [π, map_mul, map_inv]
      _ = π bM⁻¹ := by rw [hEq]
      _ = (π bM)⁻¹ := map_inv π bM
  have hbar_inv : π tM * (π bM)⁻¹ * (π tM)⁻¹ = π bM := by
    calc π tM * (π bM)⁻¹ * (π tM)⁻¹
        = (π tM * π bM * (π tM)⁻¹)⁻¹ := by group
      _ = ((π bM)⁻¹)⁻¹ := by rw [hbar]
      _ = π bM := by rw [inv_inv]
  rw [commutatorElement_def]
  change π bM * π tM * (π bM)⁻¹ * (π tM)⁻¹ = (π bM) ^ 2
  calc π bM * π tM * (π bM)⁻¹ * (π tM)⁻¹
      = π bM * (π tM * (π bM)⁻¹ * (π tM)⁻¹) := by group
    _ = π bM * π bM := by rw [hbar_inv]
    _ = (π bM) ^ 2 := by rw [pow_two]

theorem barImage_B5_le_centralizer_fitting (c : Ctx23L D Ch)
    (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5)
    (ht : ∃ t ∈ D.T, ∀ b ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G),
      t * b * t⁻¹ = b⁻¹)
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M))) :
    barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)) := by
  classical
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  let F : Subgroup (Bar2 D.M) := CFSG.fittingSubgroup (Bar2 D.M)
  obtain ⟨t, htT, htinv⟩ := ht
  let c0 : Ctx23L D Ch := c.withB0
  rintro x hx
  obtain ⟨m, hmB5, rfl⟩ := uc22p21c_mem_barImage.1 hx
  let b : G := (m : G)
  have hbB5 : b ∈ B5 := hmB5
  have hbB0 : b ∈ c.B0 := (Subgroup.mem_inf.mp hbB5).1
  have hbM : b ∈ D.M := c.hBM hbB0
  have hb5 : b ^ 5 = 1 := by
    have hdvd : orderOf b ∣ 5 := by
      rw [← h5]
      exact Subgroup.orderOf_dvd_natCard B5 hbB5
    exact orderOf_dvd_iff_pow_eq_one.mp (by simpa using hdvd)
  let bM : ↥D.M := ⟨b, hbM⟩
  let tM : ↥D.M := ⟨t, D.sylowM.le htT⟩
  let π : ↥D.M →* Bar2 D.M := uc22p21cPi D.M
  have hbbar : π bM = uc22p21cPi D.M ⟨b, hbM⟩ := rfl
  have hcomm := c0.commutator_bar_mem_centralizer_of_isCyclic (b := b) (t := t)
    (by show b ∈ c0.B; exact hbB0) htT inferInstance hcyc
  have hcomm_eq := bar_commutator_eq_square c b t hbB5 hbM htT (htinv b hbB5)
  have hb2C : (π bM) ^ 2 ∈ Subgroup.centralizer (F : Set (Bar2 D.M)) := by
    rw [← hcomm_eq]
    exact hcomm
  have hbpow : (π bM) ^ 5 = 1 := by
    rw [← map_pow, show bM ^ 5 = 1 from Subtype.ext (by simpa using hb5), map_one]
  have hbC : π bM ∈ Subgroup.centralizer (F : Set (Bar2 D.M)) :=
    mem_of_square_mem_of_pow_five hb2C hbpow
  simpa [F, B5, b, hbbar] using hbC

private theorem B0_inf_centralizer_V_eq_bot (c : Ctx23L D Ch)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    c.B0 ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ := by
  have hodd : Odd (Nat.card c.B0) := by
    have h := uc22p22f_odd_card_B c.withB0.toCtx23.toCtx21
    simpa [Ctx23L.withB0] using h
  rw [eq_bot_iff]
  intro x hx
  have hxB0 : x ∈ c.B0 := (Subgroup.mem_inf.mp hx).1
  have hxV : x ∈ Subgroup.centralizer (c.V : Set G) := (Subgroup.mem_inf.mp hx).2
  have hxL : x ∈ c.L := c.hB0.1.trans c.hL0L hxB0
  have hxO : x ∈ CFSG.Open.pCoreOf 2 c.L :=
    hCLV (Subgroup.mem_inf.mpr ⟨hxL, hxV⟩)
  have hx' : x ∈ c.B0 ⊓ CFSG.Open.pCoreOf 2 c.L := ⟨hxB0, hxO⟩
  have hbot : c.B0 ⊓ CFSG.Open.pCoreOf 2 c.L = ⊥ :=
    uc22p2214_inf_eq_bot_of_odd hodd
      ((CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype)
  rw [hbot] at hx'
  exact Subgroup.mem_bot.mp hx'

private theorem phiL_conj_eq {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (t : ↥D.T) (b : ↥c.L) :
    (c.phiL hV ⟨(t : G) * (b : G) * (t : G)⁻¹, c.conj_mem t b⟩ :
        MulAut (c.W hV)) =
      c.phiT hV t * c.phiL hV b * (c.phiT hV t)⁻¹ := by
  calc (c.phiL hV ⟨(t : G) * (b : G) * (t : G)⁻¹, c.conj_mem t b⟩ :
        MulAut (c.W hV))
      = MulAut.conj (c.phiT hV t) (c.phiL hV b) :=
        (c.phiT_conj_phiL hV t b).symm
    _ = c.phiT hV t * c.phiL hV b * (c.phiT hV t)⁻¹ := by
        rw [MulAut.conj_apply]

private theorem card_map_phiL_B0 {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) :
    Nat.card ↥(((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype) =
      Nat.card c.B0 := by
  have hinjB0 : c.B0 ⊓ Subgroup.centralizer (c.V : Set G) = ⊥ :=
    c.B0_inf_centralizer_V_eq_bot hCLV
  have hK : ∀ x ∈ c.B0.subgroupOf c.L, c.phiL hV x = 1 → x = 1 := by
    intro x hx h1
    have hxB0 : (x : G) ∈ c.B0 := Subgroup.mem_subgroupOf.mp hx
    have hxV : (x : G) ∈ Subgroup.centralizer (c.V : Set G) :=
      (c.phiL_eq_one_iff hV x).1 h1
    have hxbot : (x : G) ∈ c.B0 ⊓ Subgroup.centralizer (c.V : Set G) := ⟨hxB0, hxV⟩
    rw [hinjB0] at hxbot
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  calc Nat.card ↥(((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype)
      = Nat.card ↥((c.B0.subgroupOf c.L).map (c.phiL hV)) :=
        Subgroup.card_map_of_injective (f := (c.H hV).subtype)
          (c.H hV).subtype_injective
    _ = Nat.card ↥(c.B0.subgroupOf c.L) :=
        (Nat.card_congr (c.equivMapPhiL hV (c.B0.subgroupOf c.L) hK).toEquiv).symm
    _ = Nat.card c.B0 := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (c.hB0.1.trans c.hL0L)).toEquiv

private theorem fixV_map_eq_of_mem_map_phiL_B0 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hA : KTab23a)
    (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    {b : MulAut (c.W hV)}
    (hb : b ∈ ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype) :
    (CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
        (c.H hV).subtype)).map b.toMonoidHom =
      CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
        (c.H hV).subtype) := by
  obtain ⟨a, ha, hba⟩ := Subgroup.mem_map.mp hb
  obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
  let xL : ↥c.L := x
  have hxa' : c.phiL hV xL = a := by simpa [xL] using hxa
  have hxB0 : (x : G) ∈ c.B0 := Subgroup.mem_subgroupOf.mp hx
  have hxM : (x : G) ∈ D.M := c.hBM hxB0
  have hstabx := (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 xL).2 hxM
  rw [MulAction.mem_stabilizer_iff] at hstabx
  have hmap : (c.Ztil hV).map (c.phiL hV xL : MulAut (c.W hV)).toMonoidHom =
      c.Ztil hV := by
    apply Subgroup.ext
    have hset : (c.phiL hV xL : MulAut (c.W hV)) '' (c.Ztil hV :
        Set (c.W hV)) = (c.Ztil hV : Set (c.W hV)) := by
      change ((c.phiL hV xL) • (c.Ztil hV : Set (c.W hV))) =
        (c.Ztil hV : Set (c.W hV))
      exact hstabx
    exact Set.ext_iff.mp hset
  have hb_eq : (b : MulAut (c.W hV)) = (c.phiL hV xL : MulAut (c.W hV)) := by
    calc (b : MulAut (c.W hV)) = (a : MulAut (c.W hV)) := hba.symm
      _ = (c.phiL hV xL : MulAut (c.W hV)) := (congrArg Subtype.val hxa').symm
  rw [c.fixV_sylowStar_eq_Ztil hV hA hnat h4 h1930, hb_eq, hmap]

private theorem exists_QV_mul_B0_of_conj_mem {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (t : ↥D.T) (bL : ↥c.L)
    (hbB0 : (bL : G) ∈ c.B0)
    (hconjmem : c.phiT hV t * c.phiL hV bL * (c.phiT hV t)⁻¹ ∈
      ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype) :
    ∃ q ∈ c.QV, ∃ b' ∈ c.B0, (t : G) * (bL : G) * (t : G)⁻¹ = q * b' := by
  obtain ⟨a, ha, hha⟩ := Subgroup.mem_map.mp hconjmem
  obtain ⟨yL, hyL, hya⟩ := Subgroup.mem_map.mp ha
  let yL' : ↥c.L := yL
  have hya' : c.phiL hV yL' = a := by simpa [yL'] using hya
  have hyB0 : (yL : G) ∈ c.B0 := Subgroup.mem_subgroupOf.mp hyL
  have hconj : c.phiL hV ⟨(t : G) * (bL : G) * (t : G)⁻¹, c.conj_mem t bL⟩ =
      c.phiL hV yL' := by
    apply Subtype.ext
    calc (c.phiL hV ⟨(t : G) * (bL : G) * (t : G)⁻¹, c.conj_mem t bL⟩ :
        MulAut (c.W hV))
        = c.phiT hV t * c.phiL hV bL * (c.phiT hV t)⁻¹ :=
          phiL_conj_eq c hV t bL
      _ = (c.phiL hV yL' : MulAut (c.W hV)) :=
          hha.symm.trans (congrArg Subtype.val hya').symm
  let z : G := ((t : G) * (bL : G) * (t : G)⁻¹) * (yL : G)⁻¹
  have hzL : z ∈ c.L := c.L.mul_mem (c.conj_mem t bL) (c.L.inv_mem yL'.2)
  have hzphi : c.phiL hV ⟨z, hzL⟩ = 1 := by
    have hz_eq : (⟨z, hzL⟩ : ↥c.L) =
        (⟨(t : G) * (bL : G) * (t : G)⁻¹, c.conj_mem t bL⟩ : ↥c.L) * (yL' : ↥c.L)⁻¹ :=
      Subtype.ext rfl
    rw [hz_eq, map_mul, map_inv, hconj]
    group
  have hzC : z ∈ Subgroup.centralizer (c.V : Set G) :=
    (c.phiL_eq_one_iff hV ⟨z, hzL⟩).1 hzphi
  have hzQV : z ∈ c.QV :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hzL, hzC⟩
  refine ⟨z, hzQV, yL', hyB0, ?_⟩
  show (t : G) * (bL : G) * (t : G)⁻¹ = z * (yL' : G)
  rw [show z = ((t : G) * (bL : G) * (t : G)⁻¹) * (yL' : G)⁻¹ from rfl]
  group

private theorem phiL_conj_eq_inv_of {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) (t : ↥D.T) (bL : ↥c.L)
    (tstar : MulAut (c.W hV)) (htstar : tstar = c.phiT hV t)
    (hinv : tstar * c.phiL hV bL * tstar⁻¹ = (c.phiL hV bL)⁻¹) :
    (c.phiL hV ⟨(t : G) * (bL : G) * (t : G)⁻¹, c.conj_mem t bL⟩ :
        MulAut (c.W hV)) =
      c.phiL hV ⟨(bL : G)⁻¹, c.L.inv_mem bL.2⟩ := by
  rw [phiL_conj_eq c hV t bL, ← htstar, hinv, ← map_inv]
  congr 1

private theorem exists_conj_B0_le_sup_of_mem_first {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (t : ↥D.T)
    (hconj : ∀ b ∈ ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype,
      c.phiT hV t * b * (c.phiT hV t)⁻¹ ∈
        ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype) :
    ∀ b ∈ c.B0, ∃ q ∈ c.QV, ∃ b' ∈ c.B0, (t : G) * b * (t : G)⁻¹ = q * b' := by
  intro b hb
  have hbL : b ∈ c.L := c.hB0.1.trans c.hL0L hb
  let bL : ↥c.L := ⟨b, hbL⟩
  have hbstarH : c.phiL hV bL ∈ (c.B0.subgroupOf c.L).map (c.phiL hV) :=
    Subgroup.mem_map.mpr ⟨bL, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hbstarB : (c.phiL hV bL : MulAut (c.W hV)) ∈
      ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype :=
    Subgroup.mem_map.mpr ⟨_, hbstarH, rfl⟩
  exact exists_QV_mul_B0_of_conj_mem c hV t bL hb (hconj _ hbstarB)

private theorem phiL_conj_eq_inv_on_B5 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hA : KTab23a)
    (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (t : ↥D.T) (tstar : MulAut (c.W hV)) (htstar : c.phiT hV t = tstar)
    (hinvert : ∀ b ∈ ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype,
      (∀ w ∈ CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
          (c.H hV).subtype), b w = w) →
        tstar * b * tstar⁻¹ = b⁻¹) :
    ∀ b : ↥c.L, (b : G) ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) →
      (c.phiL hV ⟨(t : G) * (b : G) * (t : G)⁻¹, c.conj_mem t b⟩ :
          MulAut (c.W hV)) =
        c.phiL hV ⟨(b : G)⁻¹, c.L.inv_mem b.2⟩ := by
  intro b hbB5
  have hbB0 : (b : G) ∈ c.B0 := (Subgroup.mem_inf.mp hbB5).1
  have hbZ : (b : G) ∈ Subgroup.centralizer (D.Z : Set G) :=
    (Subgroup.mem_inf.mp hbB5).2
  let bL : ↥c.L := b
  have hbstarH : c.phiL hV bL ∈ (c.B0.subgroupOf c.L).map (c.phiL hV) :=
    Subgroup.mem_map.mpr ⟨bL, Subgroup.mem_subgroupOf.mpr hbB0, rfl⟩
  have hbstarB : (c.phiL hV bL : MulAut (c.W hV)) ∈
      ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype :=
    Subgroup.mem_map.mpr ⟨_, hbstarH, rfl⟩
  have hfixb : ∀ w ∈ CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
      (c.H hV).subtype), (c.phiL hV bL : MulAut (c.W hV)) w = w := by
    rw [c.fixV_sylowStar_eq_Ztil hV hA hnat h4 h1930]
    have hmem := (c.phiL_mem_fixingSubgroup_Ztil_iff hV bL).2 hbZ
    rw [fixingSubgroupOf, mem_fixingSubgroup_iff] at hmem
    exact hmem
  have hinv := hinvert _ hbstarB hfixb
  exact phiL_conj_eq_inv_of c hV t b tstar htstar.symm hinv

private theorem exists_conj_B0_le_sup_of_mem (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hKC : KOmC) (hTH : ¬ c.Tstar hV ≤ c.H hV) :
    ∃ t : ↥D.T,
      (∀ b ∈ c.B0, ∃ q ∈ c.QV, ∃ b' ∈ c.B0,
        (t : G) * b * (t : G)⁻¹ = q * b') ∧
      (∀ b : ↥c.L, (b : G) ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) →
        c.phiL hV ⟨(t : G) * (b : G) * (t : G)⁻¹, c.conj_mem t b⟩ =
          c.phiL hV ⟨(b : G)⁻¹, c.L.inv_mem b.2⟩) := by
  classical
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) :=
    Or.inr (Or.inl ⟨isOmegaMinus_of_natOmegaMinus_four hNat, hNat⟩)
  have hframe := c.omegaMinusFrame_of hV hA h4 h1930 hn2 hNat
  let B : Subgroup (MulAut (c.W hV)) :=
    ((c.B0.subgroupOf c.L).map (c.phiL hV)).map (c.H hV).subtype
  have hoddB0 : Odd (Nat.card c.B0) := by
    have h := uc22p22f_odd_card_B c.withB0.toCtx23.toCtx21
    simpa [Ctx23L.withB0] using h
  have hBodd : Odd (Nat.card ↥B) := by
    rw [show Nat.card ↥B = Nat.card c.B0 from card_map_phiL_B0 c hV hCLV]
    exact hoddB0
  have hstab : ∀ b ∈ B, (CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map
      (c.H hV).subtype)).map (b : MulAut (c.W hV)).toMonoidHom =
      CFSG.Quasithin.fixV ((c.sylowStar hV : Subgroup ↥(c.H hV)).map (c.H hV).subtype) :=
    fun b hb => fixV_map_eq_of_mem_map_phiL_B0 c hV hA h4 h1930 hnat hb
  obtain ⟨tstar, htstar, hnorm, hinvert⟩ :=
    hKC (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) (c.sylowStar hV) (c.Tstar hV)
      hframe hTH B (Subgroup.map_subtype_le _) hBodd hstab
  obtain ⟨t₁, ht₁⟩ := MonoidHom.mem_range.1 htstar
  refine ⟨t₁, ?_, ?_⟩
  · refine exists_conj_B0_le_sup_of_mem_first c hV t₁ ?_
    intro b hb
    rw [ht₁]
    exact hnorm _ hb
  · intro b hbB5
    apply Subtype.ext
    exact phiL_conj_eq_inv_on_B5 c hV hA h4 h1930 hnat t₁ tstar ht₁ hinvert b hbB5

private theorem disjoint_subgroupOf_of_inf_eq_bot {G : Type*} [Group G]
    {A B N : Subgroup G} (h : A ⊓ B = ⊥) :
    Disjoint (A.subgroupOf N) (B.subgroupOf N) := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  apply Subtype.ext
  have hx : (x : G) ∈ A ⊓ B := ⟨hxA, hxB⟩
  rw [h, Subgroup.mem_bot] at hx
  exact hx

private theorem conj_B0_le_normalizer_QV {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hB0normQV : c.B0 ≤ Subgroup.normalizer (c.QV : Set G)) {t : G}
    (hle : ∀ b ∈ c.B0, ∃ q ∈ c.QV, ∃ b' ∈ c.B0, t * b * t⁻¹ = q * b') :
    c.B0.map (MulAut.conj t).toMonoidHom ≤ Subgroup.normalizer (c.QV : Set G) := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  obtain ⟨q, hq, b', hb', heq⟩ := hle b hb
  change t * b * t⁻¹ ∈ Subgroup.normalizer (c.QV : Set G)
  rw [heq]
  exact (Subgroup.normalizer (c.QV : Set G)).mul_mem
    ((Subgroup.le_normalizer) hq) (hB0normQV hb')

private theorem sup_conj_B0_eq {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L) {t : G}
    (hle : ∀ b ∈ c.B0, ∃ q ∈ c.QV, ∃ b' ∈ c.B0, t * b * t⁻¹ = q * b') :
    (c.B0.map (MulAut.conj t).toMonoidHom ≤ c.B0 ⊔ c.QV) ∧
      (c.B0.map (MulAut.conj t).toMonoidHom ≤ Subgroup.normalizer (c.QV : Set G)) ∧
      (c.QV ⊔ c.B0.map (MulAut.conj t).toMonoidHom = c.B0 ⊔ c.QV) := by
  let N : Subgroup G := c.B0 ⊔ c.QV
  let Y : Subgroup G := c.B0.map (MulAut.conj t).toMonoidHom
  have hB0normQV : c.B0 ≤ Subgroup.normalizer (c.QV : Set G) :=
    (c.hB0.1.trans c.hL0L).trans (le_sup_left.trans c.le_normalizer_QV)
  have hYleN : Y ≤ N := by
    rintro y ⟨b, hb, rfl⟩
    obtain ⟨q, hq, b', hb', heq⟩ := hle b hb
    change t * b * t⁻¹ ∈ N
    rw [heq]
    exact N.mul_mem (Subgroup.mem_sup_right hq) (Subgroup.mem_sup_left hb')
  have hYnormQV : Y ≤ Subgroup.normalizer (c.QV : Set G) :=
    conj_B0_le_normalizer_QV c hB0normQV hle
  have hQV2G : IsPGroup 2 c.QV := D.sylowM.isPGroup.to_le (c.QV_le_T hCLV)
  have hoddB0 : Odd (Nat.card c.B0) := by
    have h := uc22p22f_odd_card_B c.withB0.toCtx23.toCtx21
    simpa [Ctx23L.withB0] using h
  have hoddY : Odd (Nat.card Y) := by
    rw [show Nat.card Y = Nat.card c.B0 from
      Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact hoddB0
  have hdisjB0 : c.QV ⊓ c.B0 = ⊥ := by
    rw [inf_comm]
    exact uc22p2214_inf_eq_bot_of_odd hoddB0 hQV2G
  have hdisjY : c.QV ⊓ Y = ⊥ := by
    rw [inf_comm]
    exact uc22p2214_inf_eq_bot_of_odd (B := Y) (T := c.QV) hoddY hQV2G
  have hcardN : Nat.card ↥N = Nat.card c.QV * Nat.card c.B0 := by
    rw [show N = c.QV ⊔ c.B0 from by
      rw [show N = c.B0 ⊔ c.QV from rfl, sup_comm]]
    exact CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      c.QV c.B0 hB0normQV (by rw [disjoint_iff]; exact hdisjB0)
  have hcardY : Nat.card ↥(c.QV ⊔ Y) = Nat.card c.QV * Nat.card c.B0 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      c.QV Y hYnormQV (by rw [disjoint_iff]; exact hdisjY)]
    congr 1
    change Nat.card (c.B0.map (MulAut.conj t).toMonoidHom) = Nat.card c.B0
    exact Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
      (MulAut.conj t).injective
  have hQVY : c.QV ⊔ Y = N := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le le_sup_right hYleN) ?_
    rw [hcardN, hcardY]
  exact ⟨hYleN, hYnormQV, hQVY⟩

private theorem map_conj_eq_of_subgroupOf {G : Type*} [Group G] {Y B N : Subgroup G}
    {e : ↥N} (hYN : Y ≤ N) (hBN : B ≤ N)
    (heq : (Y.subgroupOf N).map (MulAut.conj e).toMonoidHom = B.subgroupOf N) :
    Y.map (MulAut.conj ((e : ↥N) : G)).toMonoidHom = B := by
  have hleft : ((Y.subgroupOf N).map (MulAut.conj e).toMonoidHom).map N.subtype =
      Y.map (MulAut.conj ((e : ↥N) : G)).toMonoidHom := by
    rw [Subgroup.map_map]
    have hcomp : N.subtype.comp (MulAut.conj e).toMonoidHom =
        (MulAut.conj ((e : ↥N) : G)).toMonoidHom.comp N.subtype := by
      ext y
      rfl
    rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hYN]
  have hmap := congrArg (Subgroup.map N.subtype) heq
  rw [hleft, Subgroup.map_subgroupOf_eq_of_le hBN] at hmap
  exact hmap

private theorem exists_conj_B0_of_le_sup (c : Ctx23L D Ch)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    {t : G} (hle : ∀ b ∈ c.B0, ∃ q ∈ c.QV, ∃ b' ∈ c.B0,
      t * b * t⁻¹ = q * b') :
    ∃ x ∈ c.QV,
      (c.B0.map (MulAut.conj t).toMonoidHom).map
        (MulAut.conj x).toMonoidHom = c.B0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup G := c.B0 ⊔ c.QV
  let Y : Subgroup G := c.B0.map (MulAut.conj t).toMonoidHom
  have hB0leN : c.B0 ≤ N := le_sup_left
  have hQVleN : c.QV ≤ N := le_sup_right
  have hB0normQV : c.B0 ≤ Subgroup.normalizer (c.QV : Set G) :=
    (c.hB0.1.trans c.hL0L).trans (le_sup_left.trans c.le_normalizer_QV)
  have hNnormQV : N ≤ Subgroup.normalizer (c.QV : Set G) :=
    sup_le hB0normQV (Subgroup.le_normalizer)
  haveI hQVnormalN : (c.QV.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQVleN).2 hNnormQV
  obtain ⟨hYleN, -, hQVY⟩ := sup_conj_B0_eq c hCLV hle
  have hQV2G : IsPGroup 2 c.QV :=
    D.sylowM.isPGroup.to_le (c.QV_le_T hCLV)
  have hoddB0 : Odd (Nat.card c.B0) := by
    have h := uc22p22f_odd_card_B c.withB0.toCtx23.toCtx21
    simpa [Ctx23L.withB0] using h
  have hoddY : Odd (Nat.card Y) := by
    rw [show Nat.card Y = Nat.card c.B0 from
      Subgroup.card_map_of_injective (MulAut.conj t).injective]
    exact hoddB0
  have hdisjB0 : c.QV ⊓ c.B0 = ⊥ := by
    rw [inf_comm]
    exact uc22p2214_inf_eq_bot_of_odd hoddB0 hQV2G
  have hdisjY : c.QV ⊓ Y = ⊥ := by
    rw [inf_comm]
    exact uc22p2214_inf_eq_bot_of_odd (B := Y) (T := c.QV) hoddY hQV2G
  have hsupB0 : c.QV.subgroupOf N ⊔ c.B0.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQVleN hB0leN,
      show c.QV ⊔ c.B0 = N from by rw [sup_comm], Subgroup.subgroupOf_self]
  have hsupY : c.QV.subgroupOf N ⊔ Y.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQVleN hYleN, hQVY, Subgroup.subgroupOf_self]
  have hdisjB0N : Disjoint (c.QV.subgroupOf N) (c.B0.subgroupOf N) :=
    disjoint_subgroupOf_of_inf_eq_bot hdisjB0
  have hdisjYN : Disjoint (c.QV.subgroupOf N) (Y.subgroupOf N) :=
    disjoint_subgroupOf_of_inf_eq_bot hdisjY
  have hnot2 : ¬ 2 ∣ Nat.card ↥(c.B0.subgroupOf N) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB0leN).toEquiv]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hoddB0) (even_iff_two_dvd.mpr h2)
  have hQV2N : IsPGroup 2 ↥(c.QV.subgroupOf N) :=
    hQV2G.of_equiv (Subgroup.subgroupOfEquivOfLe hQVleN).symm
  obtain ⟨e, he, heq⟩ :=
      CFSG.GH74.BNPair.exists_conj_of_complements (p := 2)
        hQV2N hnot2 hdisjB0N hdisjYN (by rw [hsupY, hsupB0])
  refine ⟨(e : G), Subgroup.mem_subgroupOf.mp he, ?_⟩
  exact map_conj_eq_of_subgroupOf hYleN hB0leN heq

private theorem inverts_of_phiTt_and_invPhi {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    {t : G} (htT : t ∈ D.T) (t₁ : ↥D.T) (b : G)
    (hbB5 : b ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G))
    (hbB0 : b ∈ c.B0) (hbL : b ∈ c.L) (haB0 : t * b * t⁻¹ ∈ c.B0)
    (hphiTt : c.phiT hV ⟨t, htT⟩ = c.phiT hV t₁)
    (hinvPhi : ∀ bL : ↥c.L, (bL : G) ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) →
      c.phiL hV ⟨(t₁ : G) * (bL : G) * (t₁ : G)⁻¹, c.conj_mem t₁ bL⟩ =
        c.phiL hV ⟨(bL : G)⁻¹, c.L.inv_mem bL.2⟩) :
    t * b * t⁻¹ = b⁻¹ := by
  have haL : t * b * t⁻¹ ∈ c.L := c.hB0.1.trans c.hL0L haB0
  let aL : ↥c.L := ⟨t * b * t⁻¹, haL⟩
  let bL : ↥c.L := ⟨b, hbL⟩
  have hphiLa : c.phiL hV aL =
      c.phiL hV ⟨(t₁ : G) * b * (t₁ : G)⁻¹, c.conj_mem t₁ bL⟩ := by
    apply Subtype.ext
    calc (c.phiL hV aL : MulAut (c.W hV))
        = MulAut.conj (c.phiT hV ⟨t, htT⟩) (c.phiL hV bL) :=
          (c.phiT_conj_phiL hV ⟨t, htT⟩ bL).symm
      _ = MulAut.conj (c.phiT hV t₁) (c.phiL hV bL) := by rw [hphiTt]
      _ = (c.phiL hV ⟨(t₁ : G) * b * (t₁ : G)⁻¹, c.conj_mem t₁ bL⟩ :
            MulAut (c.W hV)) := c.phiT_conj_phiL hV t₁ bL
  have hphiLb : c.phiL hV aL = (c.phiL hV bL)⁻¹ := by
    rw [hphiLa, hinvPhi bL hbB5]
    have hb : (⟨(b : G)⁻¹, c.L.inv_mem hbL⟩ : ↥c.L) = (bL)⁻¹ := Subtype.ext rfl
    rw [hb, map_inv]
  have hphi_ab : c.phiL hV ⟨(t * b * t⁻¹) * b,
      c.L.mul_mem haL bL.2⟩ = 1 := by
    have hsub : (⟨(t * b * t⁻¹) * b, c.L.mul_mem haL bL.2⟩ : ↥c.L) = aL * bL :=
      Subtype.ext rfl
    rw [hsub, map_mul, hphiLb]
    group
  have hinj : c.withB0.B ⊓ Subgroup.centralizer (c.withB0.V : Set G) = ⊥ := by
    change c.B0 ⊓ Subgroup.centralizer (c.V : Set G) = ⊥
    exact c.B0_inf_centralizer_V_eq_bot hCLV
  have h_abB0 : (t * b * t⁻¹) * b ∈ c.withB0.B :=
    c.B0.mul_mem haB0 hbB0
  have h1 := c.withB0.phiL_eq_one_of_mem_of_le_B hV hinj
    (K := c.withB0.B.subgroupOf c.withB0.L) le_rfl
    (x := ⟨(t * b * t⁻¹) * b, c.withB0.L.mul_mem haL bL.2⟩)
    (Subgroup.mem_subgroupOf.mpr h_abB0) hphi_ab
  exact mul_eq_one_iff_eq_inv.mp (congrArg Subtype.val h1)

theorem exists_inverting_t_of_caseB (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hKC : KOmC) (hTH : ¬ c.Tstar hV ≤ c.H hV) :
    ∃ t ∈ D.T, ∀ b ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G),
      t * b * t⁻¹ = b⁻¹ := by
  classical
  obtain ⟨t₁, hle, hinvPhi⟩ :=
    c.exists_conj_B0_le_sup_of_mem hV hA h4 h1930 hn2 hNat hCLV hKC hTH
  obtain ⟨x, hxQV, hconjY⟩ := c.exists_conj_B0_of_le_sup hCLV hle
  have hxT : x ∈ D.T := c.QV_le_T hCLV hxQV
  have hxV : x ∈ Subgroup.centralizer (c.V : Set G) := (Subgroup.mem_inf.mp hxQV).2
  have hphiTx : c.phiT hV ⟨x, hxT⟩ = 1 :=
    (c.phiT_eq_one_iff hV ⟨x, hxT⟩).2 hxV
  let t : G := x * (t₁ : G)
  have htT : t ∈ D.T := D.T.mul_mem hxT t₁.2
  refine ⟨t, htT, ?_⟩
  intro b hbB5
  have hbB0 : b ∈ c.B0 := (Subgroup.mem_inf.mp hbB5).1
  have hbL : b ∈ c.L := c.hB0.1.trans c.hL0L hbB0
  let bL : ↥c.L := ⟨b, hbL⟩
  have hbstarH : c.phiL hV bL ∈ (c.B0.subgroupOf c.L).map (c.phiL hV) :=
    Subgroup.mem_map.mpr ⟨bL, Subgroup.mem_subgroupOf.mpr hbB0, rfl⟩
  have hmemY : (t₁ : G) * b * (t₁ : G)⁻¹ ∈
      c.B0.map (MulAut.conj (t₁ : G)).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨b, hbB0, MulAut.conj_apply (t₁ : G) b⟩
  have hmemX : x * ((t₁ : G) * b * (t₁ : G)⁻¹) * x⁻¹ ∈
      (c.B0.map (MulAut.conj (t₁ : G)).toMonoidHom).map
        (MulAut.conj x).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨_, hmemY, (MulAut.conj_apply x _).symm⟩
  rw [hconjY] at hmemX
  have haeq : t * b * t⁻¹ = x * ((t₁ : G) * b * (t₁ : G)⁻¹) * x⁻¹ := by
    show (x * (t₁ : G)) * b * (x * (t₁ : G))⁻¹ = _
    group
  have haB0 : t * b * t⁻¹ ∈ c.B0 := by rwa [haeq]
  have haL : t * b * t⁻¹ ∈ c.L := c.hB0.1.trans c.hL0L haB0
  have hphiTt : c.phiT hV ⟨t, htT⟩ = c.phiT hV t₁ := by
    have ht_eq : (⟨t, htT⟩ : ↥D.T) = ⟨x, hxT⟩ * t₁ := Subtype.ext rfl
    rw [ht_eq, map_mul, hphiTx, one_mul]
  exact inverts_of_phiTt_and_invPhi c hV hCLV htT t₁ b hbB5 hbB0 hbL haB0 hphiTt hinvPhi

private theorem isCyclic_fitting_commutator_of_cyclic (D : Data G)
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M))) :
    IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))) := by
  let Fbar : Subgroup (Bar2 D.M) := CFSG.fittingSubgroup (Bar2 D.M)
  haveI : IsCyclic ↥Fbar := hcyc
  have hC : (CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))).map
      (commutator (Bar2 D.M)).subtype = commutator (Bar2 D.M) ⊓ Fbar :=
    CFSG.LocalCores.fitting_normal_intersection (commutator (Bar2 D.M))
  have hcycNF : IsCyclic ↥(commutator (Bar2 D.M) ⊓ Fbar) :=
    Subgroup.isCyclic_of_le inf_le_right
  refine (MulEquiv.isCyclic (Subgroup.equivMapOfInjective
    (CFSG.fittingSubgroup ↥(commutator (Bar2 D.M)))
    (commutator (Bar2 D.M)).subtype (commutator (Bar2 D.M)).subtype_injective)).mpr ?_
  rw [hC]
  exact hcycNF

private theorem commutator_B5_le_pCore {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (hB7 : barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)))
    {P : Subgroup G} (hPM : P ≤ D.M)
    (hPbarF : barImage D.M P ≤ CFSG.fittingSubgroup (Bar2 D.M)) :
    ⁅(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)), P⁆ ≤ CFSG.Open.pCoreOf 2 D.M := by
  rw [Subgroup.commutator_le]
  intro b hb x hx
  have hbB0 : b ∈ c.B0 := (Subgroup.mem_inf.mp hb).1
  have hbM : b ∈ D.M := c.hBM hbB0
  have hxM : x ∈ D.M := hPM hx
  have hbBar : uc22p21cPi D.M ⟨b, hbM⟩ ∈
      barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) :=
    uc22p21c_mem_barImage.2
      ⟨⟨b, hbM⟩, Subgroup.mem_inf.mpr ⟨hbB0, (Subgroup.mem_inf.mp hb).2⟩, rfl⟩
  have hxBar : uc22p21cPi D.M ⟨x, hxM⟩ ∈ barImage D.M P :=
    uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx, rfl⟩
  have hcent := hB7 hbBar
  have hcommM : b * x * b⁻¹ * x⁻¹ ∈ D.M := by
    exact mul_mem (mul_mem (mul_mem hbM hxM) (D.M.inv_mem hbM)) (D.M.inv_mem hxM)
  have hcomm : uc22p21cPi D.M ⟨⁅b, x⁆, by
      simpa [commutatorElement_def] using hcommM⟩ = 1 := by
    change uc22p21cPi D.M ⁅(⟨b, hbM⟩ : ↥D.M), (⟨x, hxM⟩ : ↥D.M)⁆ = 1
    rw [map_commutatorElement, commutatorElement_def]
    have hc := Subgroup.mem_centralizer_iff.mp hcent (uc22p21cPi D.M ⟨x, hxM⟩)
      (hPbarF hxBar)
    rw [← hc]
    group
  exact (CFSG.mem_openPCoreOf_iff ⟨⁅b, x⁆, by
      simpa [commutatorElement_def] using hcommM⟩).2
    ((QuotientGroup.eq_one_iff _).1 hcomm)

private theorem B5_normalizes_sup_pCore_forward {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch)
    (hB7 : barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)))
    {P : Subgroup G} (hPM : P ≤ D.M)
    (hPbarF : barImage D.M P ≤ CFSG.fittingSubgroup (Bar2 D.M)) :
    ∀ b ∈ c.B0 ⊓ Subgroup.centralizer (D.Z : Set G),
      ∀ x ∈ (P ⊔ CFSG.Open.pCoreOf 2 D.M : Subgroup G),
        b * x * b⁻¹ ∈ (P ⊔ CFSG.Open.pCoreOf 2 D.M : Subgroup G) := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  let O : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  have hY : (P ⊔ O : Subgroup G) = barPreimage D.M (barImage D.M P) :=
    (barPreimage_barImage_eq_sup_pCore hPM).symm
  have hcentral : barImage D.M B5 ≤
      Subgroup.centralizer (barImage D.M P : Set (Bar2 D.M)) :=
    hB7.trans (Subgroup.centralizer_le hPbarF)
  intro b hb x hx
  have hbM : b ∈ D.M := c.hBM (Subgroup.mem_inf.mp hb).1
  rw [hY] at hx ⊢
  obtain ⟨hxM, hxbar⟩ := uc22p21c_mem_barPreimage.1 hx
  have hbBar : uc22p21cPi D.M ⟨b, hbM⟩ ∈ barImage D.M B5 :=
    uc22p21c_mem_barImage.2
      ⟨⟨b, hbM⟩, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hb).1,
        (Subgroup.mem_inf.mp hb).2⟩, rfl⟩
  have hmemM : b * x * b⁻¹ ∈ D.M :=
    mul_mem (mul_mem hbM hxM) (D.M.inv_mem hbM)
  refine uc22p21c_mem_barPreimage.2 ⟨hmemM, ?_⟩
  have hmap : uc22p21cPi D.M ⟨b * x * b⁻¹, hmemM⟩ =
      uc22p21cPi D.M ⟨b, hbM⟩ * uc22p21cPi D.M ⟨x, hxM⟩ *
        (uc22p21cPi D.M ⟨b, hbM⟩)⁻¹ := by
    rw [show (⟨b * x * b⁻¹, hmemM⟩ : ↥D.M) =
      (⟨b, hbM⟩ : ↥D.M) * ⟨x, hxM⟩ * (⟨b, hbM⟩ : ↥D.M)⁻¹ from Subtype.ext rfl,
      map_mul, map_mul, map_inv]
  have hc := Subgroup.mem_centralizer_iff.mp (hcentral hbBar)
    (uc22p21cPi D.M ⟨x, hxM⟩) hxbar
  have hcancel : uc22p21cPi D.M ⟨b, hbM⟩ * uc22p21cPi D.M ⟨x, hxM⟩ *
      (uc22p21cPi D.M ⟨b, hbM⟩)⁻¹ = uc22p21cPi D.M ⟨x, hxM⟩ := by
    rw [← hc]
    group
  rw [hmap, hcancel]
  exact hxbar

private theorem B5_le_normalizer_sup_pCore {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch)
    (hB7 : barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)))
    {P : Subgroup G} (hPM : P ≤ D.M)
    (hPbarF : barImage D.M P ≤ CFSG.fittingSubgroup (Bar2 D.M)) :
    c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) ≤
      Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  have hforward := B5_normalizes_sup_pCore_forward c hB7 hPM hPbarF
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward b hb x
  · intro hx
    have hb' : b⁻¹ ∈ B5 := B5.inv_mem hb
    have h := hforward b⁻¹ hb' (b * x * b⁻¹) hx
    convert h using 2 <;> group

private theorem sylow_barImage_le_fitting {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h1930 : H1930 D) (h2123 : S21_23 D Ch)
    (hcycN : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))))
    {p : ℕ} (hp : p.Prime) (hpSig : p ∈ D.sig) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M))) :
    barImage D.M P ≤ CFSG.fittingSubgroup (Bar2 D.M) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hPp : IsPGroup p ↥P := hP.isPGroup
  have hPbarP : IsPGroup p ↥(barImage D.M P) :=
    (hPp.comap_subtype (K := D.M)).map (uc22p21cPi D.M)
  have hPbarN : (barImage D.M P).Normal :=
    (h2123 h1930 c.toCtx23.toCtx21 p hpSig P hP hcycN).2.2.2.1
  exact (le_sSup ⟨hPbarN, hPbarP⟩ :
    barImage D.M P ≤ CFSG.pCore p (Bar2 D.M)).trans (CFSG.pCore_le_fitting _ p)

private theorem five_not_dvd_card_sylow_and_pCore {D : Data G} {p : ℕ} (hp : p.Prime)
    (hpSig : p ∈ D.sig) (h5σ : (5 : ℕ) ∉ D.sig) {P : Subgroup G} (hPp : IsPGroup p P) :
    ¬ (5 : ℕ) ∣ Nat.card ↥P ∧
      ¬ (5 : ℕ) ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 D.M) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp5 : p ≠ 5 := fun h => h5σ (h ▸ hpSig)
  constructor
  · obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    intro hd
    have h5dvd : (5 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).1 h5dvd).symm
  · have hO2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 D.M) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).map D.M.subtype
    obtain ⟨k, hk⟩ := hO2.exists_card_eq
    rw [hk]
    intro hd
    have h5dvd : (5 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hd
    norm_num at h5dvd

private theorem exists_sylow_sup_pCore_normalized_by_B5 {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5)
    (h5σ : (5 : ℕ) ∉ D.sig) (h1930 : H1930 D) (h2123 : S21_23 D Ch)
    (hcycN : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))))
    (hB7 : barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)))
    {p : ℕ} (hp : p.Prime) (hpSig : p ∈ D.sig) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M))) :
    ∃ P' : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P' (P ⊔ CFSG.Open.pCoreOf 2 D.M) ∧
        c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) ≤
          Subgroup.normalizer (P' : Set G) := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  let O : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPleR : P ≤ barPreimage D.M (centE D.M) := hP.le
  have hPM : P ≤ D.M := hPleR.trans (uc22p21c_barPreimage_le D.M (centE D.M))
  have hPbarF : barImage D.M P ≤ CFSG.fittingSubgroup (Bar2 D.M) :=
    sylow_barImage_le_fitting c h1930 h2123 hcycN hp hpSig hP
  have hp2 : p ≠ 2 := (D.sig_prime p hpSig).2
  have h5p : IsPGroup 5 ↥B5 := by
    refine IsPGroup.of_card (n := 1) ?_
    have h5' : Nat.card ↥B5 = 5 := h5
    simpa using h5'
  have hB5NY : B5 ≤ Subgroup.normalizer ((P ⊔ O : Subgroup G) : Set G) :=
    B5_le_normalizer_sup_pCore c hB7 hPM hPbarF
  obtain ⟨h5P, h5O⟩ := five_not_dvd_card_sylow_and_pCore (D := D) hp hpSig h5σ hP.isPGroup
  have hPnormO : P ≤ Subgroup.normalizer (O : Set G) :=
    hPM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hnot5Y : ¬ (5 : ℕ) ∣ Nat.card ↥(P ⊔ O : Subgroup G) :=
    CFSG.HardMathSupport.Solomon.Coordinator.not_dvd_card_sup_of_le_normalizer
      Nat.prime_five hPnormO h5P h5O
  exact CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime Nat.prime_five hp
    h5p hB5NY hnot5Y

private theorem sylow_sup_pCore_isSylow_and_centralizes {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5)
    (h1930 : H1930 D) (h2123 : S21_23 D Ch)
    (hcycN : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))))
    (hB7 : barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)))
    {p : ℕ} (hp : p.Prime) (hpSig : p ∈ D.sig) {P P' : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)))
    (hP'Y : CFSG.ABGLocalTools.IsSylowOf p P' (P ⊔ CFSG.Open.pCoreOf 2 D.M))
    (hB5NP' : c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) ≤
      Subgroup.normalizer (P' : Set G)) :
    CFSG.ABGLocalTools.IsSylowOf p P' (barPreimage D.M (centE D.M)) ∧
      P' ≤ Subgroup.normalizer
        (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G) : Subgroup G) := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  let O : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  let R : Subgroup G := barPreimage D.M (centE D.M)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 : p ≠ 2 := (D.sig_prime p hpSig).2
  have hOleR : O ≤ R := pCoreOf_le_barPreimage D.M (centE D.M)
  have hPleR : P ≤ R := hP.le
  have hP'leR : P' ≤ R := hP'Y.le.trans (sup_le hPleR hOleR)
  have hPM : P ≤ D.M := hPleR.trans (uc22p21c_barPreimage_le D.M (centE D.M))
  have hP'leM : P' ≤ D.M := hP'leR.trans (uc22p21c_barPreimage_le D.M (centE D.M))
  have hY : (P ⊔ O : Subgroup G) = barPreimage D.M (barImage D.M P) :=
    (barPreimage_barImage_eq_sup_pCore hPM).symm
  have hP'barP : barImage D.M P' ≤ barImage D.M P := by
    calc barImage D.M P' ≤ barImage D.M (P ⊔ O) := barImage_mono hP'Y.le
      _ = barImage D.M P := by rw [hY, barImage_barPreimage]
  have hP'barF : barImage D.M P' ≤ CFSG.fittingSubgroup (Bar2 D.M) :=
    hP'barP.trans (sylow_barImage_le_fitting c h1930 h2123 hcycN hp hpSig hP)
  have hcommO : ⁅B5, P'⁆ ≤ O :=
    commutator_B5_le_pCore c hB7 hP'leM hP'barF
  have hcommP' : ⁅B5, P'⁆ ≤ P' :=
    (Subgroup.le_normalizer_iff_commutator_le_right.mp hB5NP')
  have hP'odd : Odd (Nat.card ↥P') := by
    obtain ⟨k, hk⟩ := hP'Y.isPGroup.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hO2 : IsPGroup 2 ↥O :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).map D.M.subtype
  have hdisj : P' ⊓ O = ⊥ :=
    uc22p2214_inf_eq_bot_of_odd (B := P') (T := O) hP'odd hO2
  have hcommBot : ⁅B5, P'⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← hdisj]
    exact le_inf hcommP' hcommO
  have hP'centB5 : P' ≤ Subgroup.centralizer (B5 : Set G) := by
    have hcomm' : ⁅P', B5⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hcommBot
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomm'
  have hP'N : P' ≤ Subgroup.normalizer (B5 : Set G) :=
    hP'centB5.trans (Subgroup.centralizer_le_normalizer (B5 : Set G))
  have hPY : CFSG.ABGLocalTools.IsSylowOf p P (P ⊔ O) :=
    hP.of_le le_sup_left (sup_le hPleR hOleR)
  have hcardP' : Nat.card ↥P' = Nat.card ↥P :=
    (hP'Y.card_eq).trans (hPY.card_eq).symm
  have hP'R : CFSG.ABGLocalTools.IsSylowOf p P' R := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hP'leR ?_
    exact hcardP'.trans hP.card_eq
  exact ⟨hP'R, hP'N⟩

private theorem pRank_barPreimage_le_one_of_sylow_cyclic {D : Data G} {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P
      (barPreimage D.M (centE D.M)) → IsCyclic ↥P) :
    CFSG.Open.pRank p (barPreimage D.M (centE D.M)) ≤ 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p
    (barPreimage D.M (centE D.M))
  exact CFSG.pRank_le_one_of_isSylowOf_le hp hP.le hP le_rfl
    (CFSG.SectionRank.pRank_le_one_of_isCyclic hp (h P hP))

theorem hyp2120_ctx5 (hJ : J1NotSp4SU3) (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h8 : S23_8 D Ch) (h2123 : S21_23 D Ch)
    (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5)
    (h5σ : (5 : ℕ) ∉ D.sig)
    (hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)))
    (hB7 : barImage D.M (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M))) :
    Hyp2120 D (c.withB (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G))
      (c.B5_mem_calB1 h5) inf_le_left).toCtx23.toCtx21 := by
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  let c5 : Ctx23L D Ch := c.withB B5 (c.B5_mem_calB1 h5) inf_le_left
  have hcycN : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))) :=
    isCyclic_fitting_commutator_of_cyclic D hcyc
  have h1 : ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
    (uc22p21c_commutator_bar_eq_bot_iff D.M).2
      (uc22p21c_commutator_perfectResidual_fitting_eq_bot hcycN)
  refine ⟨h1, ?_, ?_, ?_⟩
  · exact hyp2120_two_of_s23_8 hJ D Ch h8 h1930 c
  · intro p hp
    haveI : Fact (Nat.Prime p) := ⟨(D.sig_prime p hp).1⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p
      (barPreimage D.M (centE D.M))
    obtain ⟨P', hP'Y, hB5NP'⟩ :=
      exists_sylow_sup_pCore_normalized_by_B5 c h5 h5σ h1930 h2123 hcycN hB7
        (D.sig_prime p hp).1 hp (P := P) hP
    obtain ⟨hP'R, hP'N⟩ :=
      sylow_sup_pCore_isSylow_and_centralizes c h5 h1930 h2123 hcycN hB7
        (D.sig_prime p hp).1 hp (P := P) (P' := P') hP hP'Y hB5NP'
    exact ⟨P', hP'R, by
      change P' ≤ Subgroup.normalizer (B5 : Set G)
      exact hP'N⟩
  · intro p hp hrank
    have hcycP : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P
        (barPreimage D.M (centE D.M)) → IsCyclic ↥P := by
      intro P hP
      exact (h2123 h1930 c5.toCtx23.toCtx21 p hp P hP hcycN).2.2.2.2
    have hle := pRank_barPreimage_le_one_of_sylow_cyclic (D := D)
      (D.sig_prime p hp).1 hcycP
    omega

private theorem T_subset_mul_centralizer_of_Tstar_le_H {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h : c.Tstar hV ≤ c.H hV) :
    (D.T : Set G) ⊆ (c.L : Set G) * (Subgroup.centralizer (c.V : Set G) : Set G) := by
  intro t htT
  have htstar : c.phiT hV ⟨t, htT⟩ ∈ c.Tstar hV := ⟨⟨t, htT⟩, rfl⟩
  obtain ⟨x, hxL, hxact⟩ := h htstar
  let xL : ↥c.L := ⟨x.1, Subgroup.mem_subgroupOf.mp hxL⟩
  have hact : (c.phiL hV xL : MulAut (c.W hV)) = c.phiT hV ⟨t, htT⟩ := by
    change actTil (⊥ : Subgroup G) c.V hV ⟨(xL : G), c.L_le_stabTil xL.2⟩ =
      c.phiT hV ⟨t, htT⟩
    simpa [xL] using hxact
  refine ⟨xL, xL.2, (xL : G)⁻¹ * t, ?_, by group⟩
  change (xL : G)⁻¹ * t ∈ Subgroup.centralizer (c.V : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hmk := congrArg (fun g : MulAut (c.W hV) =>
    g (mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩))) hact
  rw [c.phiL_apply_mkTil hV xL] at hmk
  change mkTil (⊥ : Subgroup G) c.V hV
      (actStab (⊥ : Subgroup G) c.V hV ⟨xL, c.L_le_stabTil xL.2⟩
        (IntMod.mk hV ⟨v, hv⟩)) =
    actTil (⊥ : Subgroup G) c.V hV ⟨t, c.T_le_stabTil htT⟩
      (mkTil (⊥ : Subgroup G) c.V hV (IntMod.mk hV ⟨v, hv⟩)) at hmk
  rw [actTil_mk, mkTil_eq_iff, Subgroup.mem_bot, actStab_apply_val,
    actStab_apply_val] at hmk
  have hval : (xL : G) * v * (xL : G)⁻¹ = t * v * t⁻¹ :=
    mul_inv_eq_one.mp hmk
  have htv : t * v = (xL : G) * v * (xL : G)⁻¹ * t := by
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = ((xL : G) * v * (xL : G)⁻¹) * t := by rw [← hval]
  have hcv : ((xL : G)⁻¹ * t) * v = v * ((xL : G)⁻¹ * t) := by
    calc ((xL : G)⁻¹ * t) * v = (xL : G)⁻¹ * (t * v) := by group
      _ = (xL : G)⁻¹ * ((xL : G) * v * (xL : G)⁻¹ * t) := by rw [htv]
      _ = v * ((xL : G)⁻¹ * t) := by group
  exact hcv.symm

end Ctx23L

private theorem isCyclic_fitting_of_caseB {D : Data G} {Ch : Choice2011 G}
    (hFit : S23_23CaseBFit D Ch) (h26 : S23_26Omega D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z))
    (hV : IsElemAbelian 2 c.V)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z))
    (hCaseB : S23_23OmegaCaseB c) :
    IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) := by
  apply isCyclic_fitting_of_forall_pCore D
  intro q hq hq2
  by_cases hq3 : q = 3
  · subst q
    exact isCyclic_pCore_three_of_sylow D fun P => (h26 h1930 c hOm P).2
  · have hq5 : 5 ≤ q := by
      have hq_gt2 : 2 < q := lt_of_le_of_ne hq.two_le (Ne.symm hq2)
      have hq_gt3 : 3 < q := by
        rcases lt_or_gt_of_ne hq3 with h | h
        · omega
        · exact h
      have hq_ne4 : q ≠ 4 := by
        rintro rfl
        norm_num at hq
      omega
    have hOm' : IsOmegaMinus (Bar2 c.L) 4 (CFSG.pRank 2 ↥D.Z) := by
      rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two D.Z]
    have hNat' : NatOmegaMinus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 (CFSG.pRank 2 ↥D.Z) := by
      rwa [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_two D.Z]
    exact hFit h1930 c hOm' hV hNat' hCaseB q hq hq5

private theorem Tstar_not_le_H_of_caseB {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hCaseB : S23_23OmegaCaseB c) :
    ¬ c.Tstar hV ≤ c.H hV := fun hle =>
  hCaseB.2.2 (Ctx23L.T_subset_mul_centralizer_of_Tstar_le_H c hV hle)

private theorem withB_B_ne_bot {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h5 : Nat.card ↥(c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)) = 5) :
    (c.withB (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G))
      (c.B5_mem_calB1 h5) inf_le_left).toCtx23.toCtx21.B ≠ ⊥ := by
  intro hbot
  have h5' : Nat.card ↥((c.withB (c.B0 ⊓ Subgroup.centralizer (D.Z : Set G))
    (c.B5_mem_calB1 h5) inf_le_left).toCtx23.toCtx21.B) = 5 := h5
  rw [hbot] at h5'
  norm_num at h5'

theorem s23_23CaseB_of (hJ : J1NotSp4SU3) (D : Data G) (Ch : Choice2011 G)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (hK : KOrdNatural)
    (hA : KTab23a) (h52 : S23_5_2Omega D Ch) (h53 : S23_5_3 D Ch) (h6 : S23_6 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h8 : S23_8 D Ch) (h2121 : S21_21B D Ch) (h2123 : S21_23 D Ch) (hsig : D.sig.Nonempty)
    (hKC : KOmC) (h26 : S23_26Omega D Ch) (hFit : S23_23CaseBFit D Ch) :
    S23_23CaseB D Ch := by
  intro h1930 c hOm hV hNat hCaseB
  let B5 : Subgroup G := c.B0 ⊓ Subgroup.centralizer (D.Z : Set G)
  have hB3 := c.card_B0_of_caseB h1930 h4 h52 h53 hOm hCaseB
  have h5 : Nat.card ↥B5 = 5 := hB3.2
  have h5σ : (5 : ℕ) ∉ D.sig := c.five_not_mem_sig h1930 h6 hsp h5
  have hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) :=
    isCyclic_fitting_of_caseB hFit h26 h1930 c hOm hV hNat hCaseB
  have hTH : ¬ c.Tstar hV ≤ c.H hV := Tstar_not_le_H_of_caseB c hV hCaseB
  have hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L :=
    le_of_eq (Ctx23L.inf_centralizer_V_eq_pCoreOf D Ch h2 h3 h4 hK h1930 c hOm)
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := by rw [hCaseB.1]
  obtain ⟨t, htT, htinv⟩ :=
    c.exists_inverting_t_of_caseB hV hA h4 h1930 hn2 hNat hCLV hKC hTH
  have hB7 : barImage D.M B5 ≤
      Subgroup.centralizer (CFSG.fittingSubgroup (Bar2 D.M) : Set (Bar2 D.M)) :=
    c.barImage_B5_le_centralizer_fitting h5 ⟨t, htT, htinv⟩ hcyc
  have hHyp : Hyp2120 D (c.withB B5 (c.B5_mem_calB1 h5) inf_le_left).toCtx23.toCtx21 :=
    c.hyp2120_ctx5 hJ h1930 h8 h2123 h5 h5σ hcyc hB7
  let c5 : Ctx23L D Ch := c.withB B5 (c.B5_mem_calB1 h5) inf_le_left
  have hB5ne : c5.toCtx23.toCtx21.B ≠ ⊥ := withB_B_ne_bot c h5
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨hHinfEq, -, hex⟩ :=
    h2121 h1930 c5.toCtx23.toCtx21 hB5ne hHyp p hp
  obtain ⟨n, hcases, hn, -, -⟩ := hex
  rcases hcases with
    ⟨⟨A, B, hA', hB', ⟨eAB⟩, hLA, hLB⟩, -⟩ |
    ⟨⟨A, B, hA', hB', ⟨eAB⟩, hUA, hLB⟩, -⟩
  · exact false_of_s23_8_of_hinf_prod D Ch h8 h1930 c5 hn
      (hHinfEq.symm ▸ eAB) (Or.inl hLA) hLB
  · exact false_of_s23_8_of_hinf_prod D Ch h8 h1930 c5 hn
      (hHinfEq.symm ▸ eAB) (Or.inr hUA) hLB

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
