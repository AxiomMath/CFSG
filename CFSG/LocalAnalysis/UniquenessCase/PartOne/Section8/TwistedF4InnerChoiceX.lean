module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R856Normal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight5xAShared

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)


theorem ok69_of_bar_inner_of_choiceX {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X)
    (hML : D.M ≤ normalizer (L : Set G)) (hZ : center (Bar2 L) = ⊥)
    {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) {a : Bar2 L}
    (ha : barConjAut (L := L) x = MulAut.conj a) : Ok69 a := by
  classical
  have hc := hX.cex
  have hxN : x ∈ normalizer (L : Set G) := hML (hc.sylowP.le (hX.le hx))
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective a
  have hact : ∀ y ∈ L,
      (x * y * x⁻¹) * ((l:G) * y * (l:G)⁻¹)⁻¹ ∈ pCoreOf 2 L := by
    intro y hy
    let yL : L := ⟨y,hy⟩
    have he : barConjAut (L := L) x (QuotientGroup.mk yL) =
        MulAut.conj a (QuotientGroup.mk yL) :=
      congrArg (fun α : MulAut (Bar2 L) => α (QuotientGroup.mk yL)) ha
    rw [barConjAut_of_mem hxN, barAction_mk, MulAut.conj_apply, ← hl] at he
    simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv] at he
    rw [QuotientGroup.eq_iff_div_mem] at he
    have hmem := (CFSG.mem_openPCoreOf_iff
      (((normalizerMonoidHom L) ⟨x,hxN⟩ yL) / (l * yL * l⁻¹))).mpr he
    have hecoe : (((normalizerMonoidHom L) ⟨x,hxN⟩ yL) : G) = x * y * x⁻¹ := rfl
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
      div_eq_mul_inv, hecoe] using hmem
  obtain ⟨hlist, hno, -, -⟩ := UC22.R856Normal.fusion_of_cex856 hSg h614 h63 hc
  have h61 := h61_of_list857
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.outerFixedE9_holds
    hc.mem hc.rank hlist hno hc.sylowQ hc.sylowP hc.le
    (hc.sylowP.le.trans hML) X hX.le hX.card hX.not_le_sylowQ
  have hE : HasGammaE9 D X := hasGammaE9_of_pRank hc h61
  rw [← hl]
  exact ok69_of_inner_action hSg h69 L Q P hc hZ X hX.le hX.card
    (fun hn => hX.notLe ((centralizer_le_normalizer _).trans hn)) hE x hx hx1 l hact

theorem false_of_inner_twistedF4_of_choiceX {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h63 : UC6.R6_3 D) (h69 : UC6.R6_9 D)
    {L Q P X : Subgroup G} (hX : ChoiceX D L Q P X)
    (hML : D.M ≤ normalizer (L : Set G)) {f : ℕ}
    (hmodel : CFSG.Blueprint.LieModel (Bar2 L) .twistedF4 0 2 f)
    (hNontrivial : ¬ ⁅L, X⁆ ≤ pCoreOf 2 L)
    (hInner : ∀ x ∈ X, ∃ l ∈ L, ∀ y ∈ L,
      (x * y * x⁻¹) * (l * y * l⁻¹)⁻¹ ∈ pCoreOf 2 L) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, -, -, hx1, hAut3, hAut1⟩ :=
    UC22.R856NormalFour.exists_generator_of_commutator_not_le hX.le
      (hX.cex.sylowP.le.trans hML) hX.card hNontrivial
  have hZ := UC22.R856NormalFour.center_twistedF4_eq_bot hmodel
  rcases UC22.R856NormalFour.outer_or_exists_inner_of_cube hZ (barConjAut (L := L) x) hAut3
      hAut1 with hout | ⟨a, ha3, ha⟩
  · exact hout ((barConjAut_mem_inner_iff x (hML (hX.cex.sylowP.le (hX.le hx)))).mpr
      (hInner x hx))
  · obtain ⟨R, hCard, haR, hNot⟩ :=
      UC22.R856NormalFour.order_twenty_seven_of_order_three_twistedF4 hmodel ha3
    exact not_ok69_of_nonabelian_order_27 hCard haR hNot
      (ok69_of_bar_inner_of_choiceX hSg h614 h63 h69 hX hML hZ hx hx1 ha)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
