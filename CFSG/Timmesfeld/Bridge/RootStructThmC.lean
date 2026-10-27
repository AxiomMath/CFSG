module

public import CFSG.Timmesfeld.Bridge.RootStructThmB
public import CFSG.Timmesfeld.Bridge.InductionE

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def ThinOneOpposite (D : Set G) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, ∀ c ∈ D, ∀ x ∈ D, Commute a b → a * b ∈ D → Commute b c → b * c ∈ D →
    ¬ Commute b x → Odd (orderOf (b * x)) → ¬ Commute a x → Odd (orderOf (a * x)) →
    orderOf (x * c) = 4 →
    (∀ c' ∈ D, Commute b c' → b * c' ∈ D → Commute c c' → c * c' ∈ D →
      c' ∈ rootGroup D b ⊔ rootGroup D c) →
    OneOpposite D a x

theorem oneOppositeClosed_of_thin (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hR : NCoreCommutatorInRoot D) (hT : ThinOneOpposite D) : OneOppositeClosed D := by
  intro a ha b hb x hx hab habD hax hoddax hbx hoddbx ⟨c, hcD, hbc, hbcD, hxc⟩
  by_cases hthin : ∀ c' ∈ D, Commute b c' → b * c' ∈ D → Commute c c' → c * c' ∈ D →
      c' ∈ rootGroup D b ⊔ rootGroup D c
  · exact hT a ha b hb c hcD x hx hab habD hbc hbcD hbx hoddbx hax hoddax hxc hthin
  · push Not at hthin
    obtain ⟨c', hc', hbc', hbc'D, hcc', hcc'D, hoff⟩ := hthin
    exact oneOpposite_of_collinear_off_line h hc hs hR ha hb hcD hc' hx hab habD hbc hbcD hbc'
      hbc'D hcc' hcc'D hoff hbx hoddbx hax hoddax hxc

theorem existsCommSpec_of_thinOneOpposite (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hR : NCoreCommutatorInRoot D) (hconn : Moufang.ExcCollConnected D)
    (hT : ThinOneOpposite D) : ExistsCommSpec D :=
  existsCommSpec_of_oneOppositeClosed h.root hconn (oneOppositeClosed_of_thin h hc hs hR hT)

@[expose] def ThinOneOppositeStepE : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootIHStructE G →
    (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) → RootClosure D → SpecialClosure D →
    Moufang.ExcCollConnected D → ThinOneOpposite D

theorem existsCommSpecStepE_of_thin (hT : Moufang.Tim75Thm31) (hL : NCoreStepLarge)
    (hThin : ThinOneOppositeStepE) : ExistsCommSpecStepE :=
  fun G _ D hH IH hl hc hs =>
    have hconn := Moufang.collConnected_of_hyp hT hH
    existsCommSpec_of_thinOneOpposite hH hc hs (hL G D hH IH.toStruct.rootIH hl hc) hconn
      (hThin G D hH IH hl hc hs hconn)

end CFSG.Timmesfeld.Bridge
