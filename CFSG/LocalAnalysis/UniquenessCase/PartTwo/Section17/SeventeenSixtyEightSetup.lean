module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Ctx1768 (D : Data G) (L L' : Subgroup G) : Prop where
  hL : L ∈ calC D.M
  hL' : L' ∈ calC D.M
  hne : L' ≠ L
  hL'conj : L' ∈ conjSetOf D.M L
  hX : conjClosure D.M L = L ⊔ L'
  hAlt : IsAlt (Bar2 L) 5
  hAlt' : IsAlt (Bar2 L') 5
  h5 : 5 ∈ D.sig
  he3 : CFSG.Open.evenRank G = 3

theorem ctx1768_of_ne
    {D : Data G} {V₀ V : Subgroup G} (h42 : R17_42At D V₀ V) {p : ℕ} (hp : p ∈ D.sig)
    {L : Subgroup G} (hL : L ∈ calLp D p) (hne : conjClosure D.M L ≠ L)
    (hAlt : IsAlt (Bar2 L) 5) :
    p = 5 ∧ ∃ L', Ctx1768 D L L' := by
  obtain ⟨hp5, he3⟩ := p_eq_five_of_ne h42 hp hL hne hAlt
  obtain ⟨n, x, hxM, hXsup, -, -, -⟩ := p42_alt2_of_ne h42 hp hL.1 hne
  obtain ⟨hL'cal, hL'ne⟩ := conjSubgroup_mem_calC_and_ne hL.1 hxM hXsup hne
  have hL'conj : CFSG.Quasithin.conjSubgroup L x ∈ conjSetOf D.M L :=
    ⟨x⁻¹, D.M.inv_mem hxM, rfl⟩
  have hAlt' : IsAlt (Bar2 (CFSG.Quasithin.conjSubgroup L x)) 5 := by
    obtain ⟨e⟩ := bar2_conj_equiv L x⁻¹
    obtain ⟨e5⟩ := hAlt
    exact ⟨e.symm.trans e5⟩
  refine ⟨hp5, CFSG.Quasithin.conjSubgroup L x,
    ⟨hL.1, hL'cal, hL'ne, hL'conj, hXsup, hAlt, hAlt', hp5 ▸ hp, he3⟩⟩

namespace Ctx1768

theorem conjClosure_le {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    conjClosure D.M L ≤ D.M :=
  TwelveTwentyThree.conjClosure_le c.hL.1.le

theorem le_normalizer {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    D.M ≤ normalizer (conjClosure D.M L : Set G) :=
  TwelveTwentyThree.le_normalizer_conjClosure D.M L

theorem normal {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    ((conjClosure D.M L).subgroupOf D.M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer c.conjClosure_le).2 c.le_normalizer

theorem perfect {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    ⁅conjClosure D.M L, conjClosure D.M L⁆ = conjClosure D.M L :=
  ElevenNine.conjClosure_isPerfect c.hL

theorem isA5xA5_bar2 {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    IsA5xA5 (Bar2 (conjClosure D.M L)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X := conjClosure D.M L
  have hXsup : X = L ⊔ L' := c.hX
  have hLX : L ≤ X := le_sup_left.trans hXsup.symm.le
  have hL'X : L' ≤ X := le_sup_right.trans hXsup.symm.le
  obtain ⟨-, -, hC⟩ := conjSetOf_subset_calC_conjClosure c.hL
  have hLXcal : L ∈ calC X := hC L (self_mem_conjSetOf D.M L)
  have hL'Xcal : L' ∈ calC X := hC L' c.hL'conj
  have hLnormL' : L' ≤ normalizer (L : Set G) :=
    uc22p22u_calC_normalizes hLXcal hL'Xcal c.hne.symm
  have hL'normL : L ≤ normalizer (L' : Set G) :=
    uc22p22u_calC_normalizes hL'Xcal hLXcal c.hne
  have hLnorm : (L.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 (by
      rw [hXsup]
      exact sup_le Subgroup.le_normalizer hLnormL')
  have hL'norm : (L'.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL'X).2 (by
      rw [hXsup]
      exact sup_le hL'normL Subgroup.le_normalizer)
  let A : Subgroup (Bar2 X) := barImage X L
  let B : Subgroup (Bar2 X) := barImage X L'
  have hAn : A.Normal := s13_barImage_normal hLnorm
  have hBn : B.Normal := s13_barImage_normal hL'norm
  haveI : A.Normal := hAn
  haveI : B.Normal := hBn
  have hjoin : A ⊔ B = ⊤ := by
    have h1 : A ⊔ B = barImage X (L ⊔ L') := (s13_barImage_sup hLX hL'X).symm
    rw [h1, ← hXsup, s13_barImage_self]
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
    uc22p22l_barImage_commute hLXcal hL'Xcal c.hne.symm
  have hBcent : B ≤ Subgroup.centralizer (A : Set (Bar2 X)) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  obtain ⟨eA0, -⟩ := uc22p20d_bar2Equiv hLX hLXcal.1
  obtain ⟨eB0, -⟩ := uc22p20d_bar2Equiv hL'X hL'Xcal.1
  let eA : Bar2 L ≃* ↥A := eA0
  let eB : Bar2 L' ≃* ↥B := eB0
  obtain ⟨eAlt⟩ := c.hAlt
  obtain ⟨eAlt'⟩ := c.hAlt'
  have hAz : Subgroup.center ↥A = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv (eA.symm.trans eAlt)
      (alternatingGroup.center_eq_bot (by norm_num))
  have hdisj : A ⊓ B = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left A hBcent).trans_eq
      (CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center hAz))
  have hprod : ↥A × ↥B ≃* ↥(A ⊔ B) :=
    CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup (P₁ := A) (P₂ := B) hcomm hdisj
  have eTop : ↥(A ⊔ B) ≃* Bar2 X :=
    (MulEquiv.cast (M := fun x : Subgroup (Bar2 X) => ↥x) hjoin).trans Subgroup.topEquiv
  let eMain : ↥A × ↥B ≃* Bar2 X := hprod.trans eTop
  let eA5 : ↥A ≃* alternatingGroup (Fin 5) := eA.symm.trans eAlt
  let eB5 : ↥B ≃* alternatingGroup (Fin 5) := eB.symm.trans eAlt'
  exact ⟨eMain.symm.trans (eA5.prodCongr eB5)⟩

theorem isA5xA5_barImage {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    IsA5xA5 ↥(barImage D.M (conjClosure D.M L)) := by
  have hXM : conjClosure D.M L ≤ D.M := c.conjClosure_le
  have hsub : CFSG.Open.IsSubnormal (conjClosure D.M L) D.M :=
    CFSG.Open.IsSubnormal.step hXM c.normal (CFSG.Open.IsSubnormal.refl D.M)
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hXM hsub
  exact ⟨e.symm.trans (c.isA5xA5_bar2).some⟩

theorem five_dvd_card {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L') :
    5 ∣ Nat.card (conjClosure D.M L) := by
  have h5bar : 5 ∣ Nat.card (Bar2 (conjClosure D.M L)) := by
    obtain ⟨e⟩ := c.isA5xA5_bar2
    rw [Nat.card_congr e.toEquiv, Nat.card_prod,
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Excl.card_isAlt_five
        (X := alternatingGroup (Fin 5)) ⟨MulEquiv.refl _⟩]
    norm_num
  have h5X : 5 ∣ Nat.card ↥(conjClosure D.M L) :=
    h5bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(conjClosure D.M L)))
  exact h5X

theorem stronglyEmbedded {D : Data G} {L L' : Subgroup G} (c : Ctx1768 D L L')
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M :=
  CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC c.hL) c.h5

end Ctx1768

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
