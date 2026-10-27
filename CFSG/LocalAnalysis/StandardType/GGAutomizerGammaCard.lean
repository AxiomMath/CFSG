module

public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGTwE6BadWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem card_ggAutomizer_eq_gamma_of_weylReflSet
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNoTr : GGNoTransvection p Bs) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hW : ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range ≤
      Subgroup.closure (ggTorusReflSet p (ggGamma X hN).range)) :
    Nat.card ↥(ggAutomizer X Bs) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) := by
  classical
  have huniq := existsUnique_overGamma_of_weylReflSet hp hp2
    hBs hSC hNoTr hN hZ hW
  let f : ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
        (ggGamma X hN).range) → ↥(ggAutomizer X Bs) := fun a =>
    ⟨Classical.choose (huniq a a.2),
      (Classical.choose_spec (huniq a a.2)).1.1⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have ha : GGOverGamma hN (f a : MulAut ↥Bs) (a : MulAut _) :=
      (Classical.choose_spec (huniq a a.2)).1.2
    have hb : GGOverGamma hN (f b : MulAut ↥Bs) (b : MulAut _) :=
      (Classical.choose_spec (huniq b b.2)).1.2
    have hc : (f a : MulAut ↥Bs) = (f b : MulAut ↥Bs) := congrArg Subtype.val hab
    rw [hc] at ha
    exact Subtype.ext (GGOverGamma.unique ha hb)
  have hle_inner : Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
        (ggGamma X hN).range) ≤ Nat.card ↥(ggAutomizer X Bs) :=
    Nat.card_le_card_of_injective f hf_inj
  have hdvd : Nat.card ↥(ggAutomizer X Bs) ∣
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
        (ggGamma X hN).range) :=
    card_ggAutomizer_dvd_gamma hp hBs hNoTr hN hZ
  have hactual : Nat.card ↥(ggAutomizer X Bs) =
      Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range (ggGamma X hN).range) := by
    rcases lt_or_eq_of_le hle_inner with hlt | heq
    · have hmod : Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
          (ggGamma X hN).range) % Nat.card ↥(ggAutomizer X Bs) =
          Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
            (ggGamma X hN).range) := Nat.mod_eq_of_lt hlt
      have hzero : Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
            (ggGamma X hN).range) % Nat.card ↥(ggAutomizer X Bs) = 0 :=
        Nat.mod_eq_zero_of_dvd hdvd
      rw [hmod] at hzero
      have hposinner : 0 < Nat.card ↥(ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
          (ggGamma X hN).range) := Nat.card_pos
      omega
    · exact heq.symm
  exact hactual

end CFSG.StandardType
