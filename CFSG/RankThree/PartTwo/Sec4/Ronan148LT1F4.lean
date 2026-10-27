module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT1
public import CFSG.HardMathSupport.Dickson.Bal207.FamF42Class
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434F42
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14.Ronan148K
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.Bal207
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (f4TwoIndex)
open CFSG.LieType.Ree CFSG.Open CFSG.Blueprint.Chevalley


theorem three_dvd_card_of_f42CompType {Q : Type} [Group Q] (h : FamF42.F42CompType Q) :
    3 ∣ Nat.card Q := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) (by rw [hF]; norm_num)
  have hZ := center_statedSp_eq_bot_of_charP_two (K := F) 3
  rw [Nat.card_congr e.toEquiv, hZ]
  rw [show Nat.card (StatedSp 3 F ⧸ (⊥ : Subgroup (StatedSp 3 F))) = Nat.card (StatedSp 3 F) from
    Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
  decide

theorem isSolvable_outer_f4Two {X : Type} [Group X]
    (e : X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) : Group.IsSolvable (Outer X) := by
  have hmodel := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 CFSG.Assembly.RankThreeEven.primePowerTwo
    f4TwoIndex.2 rfl e
  obtain ⟨Y, _, _, hY, ⟨e'⟩⟩ := CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .F4 hmodel
  have hY' : Nat.card Y = 2 ^ 1 := hY
  have : CharP Y 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_refl 1) hY'
  obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (le_refl 1) Y hY'
  let φ : Outer (adjointGroup ReeTag.F4.tag Y) ≃* Multiplicative (ZMod (2 * 1)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Θ hsurj)
  have hsol : Group.IsSolvable (Outer (adjointGroup ReeTag.F4.tag Y)) :=
    Group.isSolvable_of_comm fun a b => φ.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  haveI := hsol
  let e'' : X ≃* adjointGroup ReeTag.F4.tag Y := e'
  exact solvable_of_surjective (f := (equivalence e'').symm.toMonoidHom)
    (equivalence e'').symm.surjective

theorem exists_conj_of_cubeInner {S : Type} [Group S] [IsSimpleGroup S]
    (hna : ∃ a b : S, a * b ≠ b * a) (hcube : Sec4.CubeInner S) {β : MulAut S} (hβ : β ^ 3 = 1)
    (hβ1 : β ≠ 1) : ∃ s : S, orderOf s = 3 ∧ MulAut.conj s = β := by
  obtain ⟨s, hs⟩ := hcube β hβ
  have hZ := Sec4.RonanK429H.center_eq_bot_of_simple_nonab hna
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hβ1 (by rw [← hs, map_one])
  have hs3 : s ^ 3 = 1 := by
    have hc : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, hs, hβ]
    have hmem : s ^ 3 ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun φ : MulAut S => φ g) hc
      simp only [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * s ^ 3 = s ^ 3 * g * (s ^ 3)⁻¹ * s ^ 3 := by rw [hg]
        _ = s ^ 3 * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  exact ⟨s, orderOf_eq_prime hs3 hs1, hs⟩

theorem kT1_eight_F4 : RowOf143 (TauCeti.CFSGIndex.lie f4TwoIndex).Group := by
  intro S _ _ hs hna ⟨e⟩ h3
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := Sec4.Item434F42.exists_model e
  refine row143_of_layer hs hna h3 (isSolvable_outer_f4Two e) fun β hβ hβ1 => ?_
  have hcube : Sec4.CubeInner S :=
    Sec4.cubeInner_of_not_three_dvd_card_outer (Sec4.Item434F42.not_three_dvd_card_outer e)
  obtain ⟨s, hso, rfl⟩ := exists_conj_of_cubeInner hna hcube hβ hβ1
  let e'' : S ≃* adjointGroup Tag.F4 K := e'
  have hx : orderOf (e'' s) = 3 := by rw [MulEquiv.orderOf_eq]; exact hso
  have hC := FamF42.compShape_conj_F4_two hK (e'' s) hx
  have hcongr : MulAut.congr e'' (MulAut.conj s) = MulAut.conj (e'' s) := by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  have hS : CompShape FamF42.F42CompType (MulAut.conj s) :=
    CompShape.of_congr FamF42.isoInvariant_f42CompType e'' (by rw [hcongr]; exact hC)
  exact ⟨hS.layer, fun J hJ => (three_dvd_card_of_f42CompType (hS.type J hJ)).trans
    (Subgroup.card_quotient_dvd_card _)⟩

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
