module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM23Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM24Nine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporHeNine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRuNine
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenHS
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint

@[expose] def K423SporThetaCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (∃ s ∈ [TauCeti.SporadicName.M23, .M24, .HS, .He, .Ru],
      Nonempty (X ≃* NativeSporadic.Carrier s)) →
    ∀ b : X, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set X)) = ⊥

namespace Res423Two

theorem census423_of_thetaCent_kill {X M : Type} [Group X] [Finite X] [Group M] [Finite M]
    (hZ : Subgroup.center X = ⊥) (e : X ≃* M)
    (hθ : ∀ b : M, b ^ 3 = 1 → b ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set M)) = ⊥)
    (hkill : ∀ P : Subgroup M, CFSG.Assembly.IsElemAbelian 3 P → Nat.card P = 9 →
      Item434SporGen.FixGen P ∨ Item434SporGen.NoSignalizer P) :
    Census423 X := by
  refine census423_of_alphaVanishes fun D hD hD9 => alphaVanishes_of_mulEquiv e ?_
  have hZM := center_eq_bot_of_mulEquiv hZ e
  have hD'e : CFSG.Assembly.IsElemAbelian 3 (D.map e.toMonoidHom) := isElemAbelian_map' _ hD.prop
  have hD'9 : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  rcases hkill _ hD'e hD'9 with ⟨S, hS, hSc⟩ | hNS
  · refine alphaVanishes_of_core hZM (comm_of_isElemAbelian hD'e)
      (fun b hb hb1 => hθ b (hD'e.2 b hb) hb1) (hS.trans (Subgroup.closure_mono ?_))
    intro σ hσ
    obtain ⟨-, p, hp, hp1, hpσ⟩ := hSc σ hσ
    exact ⟨p, hp, hp1, hpσ.symm⟩
  · exact alphaVanishes_of_noSignalizer hZM (comm_of_isElemAbelian hD'e)
      (ne_bot_of_card_nine hD'9) hNS

end Res423Two

open Res423Two

theorem census423_of_m23
    (hθ : K423SporThetaCent) {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* NativeSporadic.Carrier .M23) : Census423 X := by
  have : Finite NativeSporadic.M23 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num)
  exact census423_of_thetaCent_kill (M := NativeSporadic.M23) hZ e
    (hθ _ ⟨.M23, by simp, ⟨MulEquiv.refl _⟩⟩) Item434SporGen.kill9_m23

theorem census423_of_m24
    (hθ : K423SporThetaCent) {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* NativeSporadic.Carrier .M24) : Census423 X := by
  have : Finite NativeSporadic.M24 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M24]; norm_num)
  exact census423_of_thetaCent_kill (M := NativeSporadic.M24) hZ e
    (hθ _ ⟨.M24, by simp, ⟨MulEquiv.refl _⟩⟩) Item434SporGen.kill9_m24

theorem census423_of_he
    (hθ : K423SporThetaCent)
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* NativeSporadic.Carrier .He) : Census423 X := by
  have : Finite CFSG.Sporadic.HeldB.heP := inferInstance
  have eH : NativeSporadic.Carrier .He ≃* CFSG.Sporadic.HeldB.heP := CFSG.Sporadic.HeldB.heEquivP
  exact census423_of_thetaCent_kill hZ (e.trans eH)
    (hθ _ ⟨.He, by simp, ⟨eH.symm⟩⟩) Item434SporGen.kill9_he

theorem census423_of_ru
    (hθ : K423SporThetaCent)
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* NativeSporadic.Carrier .Ru) : Census423 X := by
  have : Finite CFSG.Sporadic.RuSchreier.ruP :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.RuSchreier.card_ruP']; norm_num)
  have eR : NativeSporadic.Carrier .Ru ≃* CFSG.Sporadic.RuSchreier.ruP :=
    CFSG.Sporadic.RuSchreier.ruEquivP
  exact census423_of_thetaCent_kill hZ (e.trans eR)
    (hθ _ ⟨.Ru, by simp, ⟨eR.symm⟩⟩) Item434SporGen.kill9_ru

theorem census423_of_hs
    (hθ : K423SporThetaCent)
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (e : X ≃* NativeSporadic.Carrier .HS) : Census423 X := by
  have : Finite CFSG.RankThree.Native.hs100P := inferInstance
  have eH : NativeSporadic.Carrier .HS ≃* CFSG.RankThree.Native.hs100P :=
    CFSG.RankThree.Native.hs100Equiv
  exact census423_of_thetaCent_kill hZ (e.trans eH)
    (hθ _ ⟨.HS, by simp, ⟨eH.symm⟩⟩) Item434SporGen.kill9_hs

end CFSG.RankThree.PartTwo.Sec4
