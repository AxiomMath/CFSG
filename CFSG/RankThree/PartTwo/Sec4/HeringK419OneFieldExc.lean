module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res3ProofOneField
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldTransfer
public import CFSG.RankThree.PartTwo.Sec4.HeringK419OneFieldRank
import CFSG.Quasithin.Background.SmithB42G2Id
import CFSG.RankThree.PartTwo.Sec21.Item223Rank2ProofD4
import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def K419HasE9 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsType419 K →
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ 9 ≤ Nat.card E

namespace HeringOF

section Certs


theorem exists_centralizing_of_inner {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hL : IsComponent L) {M : Type} [Group M] (hZM : Subgroup.center M = ⊥)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* M) {a : G}
    (haL : a ∈ Subgroup.normalizer (L : Set G)) (ha3 : orderOf a = 3)
    (haC : a ∉ Subgroup.centralizer (L : Set G)) (hin : ¬ InducesOuterTheta a L)
    {K : Subgroup G} (hKle : K ≤ L ⊓ Subgroup.centralizer ({a} : Set G))
    (hKc : IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))))
    (ht : IsType419 K) :
    ∃ (g : M) (ι : K →* M), g ^ 3 = 1 ∧ g ≠ 1 ∧ Function.Injective ι ∧
      (∀ k, ι k * g = g * ι k) ∧ Subgroup.center K = ⊥ := by
  have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
  have hinner : IsInnerAut (inducedAutHom L e ⟨a, haL⟩) := by
    by_contra h
    exact hin ((not_isInnerAut_inducedAutHom_iff L e haL).mp h)
  obtain ⟨g, hg⟩ := hinner
  have hτ3 := inducedAutHom_pow_eq_one L e haL ha3'
  have hg3 : g ^ 3 = 1 := by
    have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg]; exact hτ3
    have h2 : g ^ 3 ∈ Subgroup.center M := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun γ : MulAut M => γ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * g ^ 3 = g ^ 3 * y * (g ^ 3)⁻¹ * g ^ 3 := by rw [this]
        _ = g ^ 3 * y := by group
    rwa [hZM, Subgroup.mem_bot] at h2
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply haC
    refine Item419Res3.mem_centralizer_of_inducedAutHom_eq_one hL e haL ?_
    rw [← hg, map_one]
  obtain ⟨hs, hZ, ι, hι, hfix⟩ := HeringOF.exists_injective_fixSub haL hKle hKc ht e
  refine ⟨g, ι, hg3, hg1, hι, fun k => ?_, hZ⟩
  have h := hfix k
  rw [← hg, HeringOF.fixSub_conj_eq_centralizer'] at h
  exact Subgroup.mem_centralizer_singleton_iff.mp h

theorem card_le_nine_of_adjointG2 {F : Type} [Field F] [Finite F] (hF3 : ringChar F ≠ 3)
    (hF4 : 4 ≤ Nat.card F) (E : Subgroup (adjointGroup .G2 F)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  by_cases h2 : ringChar F = 2
  · haveI : CharP F 2 := h2 ▸ ringChar.charP F
    haveI := Fintype.ofFinite F
    obtain ⟨n, hn, hcard⟩ := FiniteField.card F 2
    have hcard' : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
    have hmod : ChevalleyExceptionalModel (adjointGroup .G2 F) .G2 2 (n : ℕ) :=
      ⟨⟨hn, n.pos, rfl, by rw [← hcard']; omega⟩, F, inferInstance, inferInstance, hcard',
        ⟨(CFSG.RankThree.Chevalley.adjointQuotientEquiv .G2 F).symm⟩⟩
    obtain ⟨-, K', _, _, _, -, ⟨e'⟩⟩ :=
      CFSG.Quasithin.B42G2Id.exists_cayleyGroup_of_chevalleyExceptionalModel hmod
    have h9 := CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.cayleyGroup_card_le_nine
      (E.map e'.toMonoidHom) (isElemAbelian_map e'.toMonoidHom hE)
    rwa [Subgroup.card_map_of_injective e'.injective] at h9
  · have h3 : (3 : F) ≠ 0 := by
      intro h
      have hp : (ringChar F).Prime := by
        obtain ⟨p, hp⟩ := CharP.exists F
        rw [ringChar.eq F p]
        exact CharP.char_is_prime F p
      have : ringChar F ∣ 3 := (ringChar.spec F 3).mp (by exact_mod_cast h)
      exact hF3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp this)
    exact CFSG.RankThree.PartTwo.Sec21.Item223RankResProof.adjointG2_card_le_nine F h2 h3 E hE

end Certs

end HeringOF

section Final


theorem k419OneFieldG2_of_E9 (hE9 : K419HasE9) : K419OneFieldG2 := by
  intro G _ _ L hL h46 F _ _ hF3 hF4 x a hx3 hxa hxk haL ha3 haC hin K hKle hKc ht
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* adjointGroup Tag.G2 F) := by
    rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
  haveI : Finite (adjointGroup Tag.G2 F) := Finite.of_equiv _ e.toEquiv
  obtain ⟨g, ι, hg3, hg1, hι, hcomm, hZK⟩ := HeringOF.exists_centralizing_of_inner hL
    center_adjointGroup_eq_bot e haL ha3 haC hin hKle hKc ht
  obtain ⟨E, hE, hE9'⟩ := hE9 K ht
  obtain ⟨E', hE', hE'9⟩ := HeringOF.exists_elemAbelian_gt_nine hZK ι hι hg3 hg1 hcomm hE hE9'
  exact absurd hE'9 (not_lt.mpr (HeringOF.card_le_nine_of_adjointG2 hF3 hF4 E' hE'))

theorem k419OneFieldTriality_of_E9
    (hE9 : K419HasE9) : K419OneFieldTriality := by
  intro G _ _ L hL h46 f hf F _ _ hF σ hσ x a hx3 hxa hxk haL ha3 haC hin K hKle hKc ht
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := by
    rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
  haveI : Finite (graphFixedRootGroup TwistTag.D4 F σ.toRingHom) := Finite.of_equiv _ e.toEquiv
  obtain ⟨g, ι, hg3, hg1, hι, hcomm, hZK⟩ := HeringOF.exists_centralizing_of_inner hL
    (CFSG.TauCetiBridge.Twisted.center_graphFixedRootGroup_eq_bot σ.toRingHom) e haL ha3 haC hin
    hKle hKc ht
  obtain ⟨E, hE, hE9'⟩ := hE9 K ht
  obtain ⟨E', hE', hE'9⟩ := HeringOF.exists_elemAbelian_gt_nine hZK ι hι hg3 hg1 hcomm hE hE9'
  exact absurd hE'9 (not_lt.mpr
    (CFSG.RankThree.PartTwo.Sec21.Item223Rank2Proof.card_le_nine_of_graphFixedRootGroup hf hF hσ
      E' hE'))

theorem k419OneFieldLargeRee_of_E9 (hE9 : K419HasE9) : K419OneFieldLargeRee := by
  intro G _ _ L hL h46 b hb F _ _ _ hF x a hx3 hxa hxk haL ha3 haC hin K hKle hKc ht
  obtain ⟨e⟩ : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
      CFSG.LieType.Ree.ReeTag.F4.reeGamma F b) := by
    rcases hxk with ⟨e, -⟩ | ⟨e, -⟩ <;> exact ⟨e⟩
  haveI : Finite (CFSG.LieType.Ree.ReeTag.F4.reeGamma F b) := Finite.of_equiv _ e.toEquiv
  obtain ⟨g, ι, hg3, hg1, hι, hcomm, hZK⟩ := HeringOF.exists_centralizing_of_inner hL
    (CFSG.LieType.Ree.ReeTag.large_Ree_fixed_group_center_trivial b F hF) e haL ha3 haC hin hKle
    hKc ht
  obtain ⟨E, hE, hE9'⟩ := hE9 K ht
  obtain ⟨E', hE', hE'9⟩ := HeringOF.exists_elemAbelian_gt_nine hZK ι hι hg3 hg1 hcomm hE hE9'
  exact absurd hE'9 (not_lt.mpr
    (CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma b F hF E' hE'))

end Final

end CFSG.RankThree.PartTwo.Sec4
