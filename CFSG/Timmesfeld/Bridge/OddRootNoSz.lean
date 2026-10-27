module

public import CFSG.Timmesfeld.Bridge.OddRootDefs
import CFSG.Timmesfeld.Bridge.OddRootSzBlock
import CFSG.Timmesfeld.Bridge.OddRootSzStep

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki

@[expose] def SzMainStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Hyp G D → NoSzBelow (Nat.card G) →
    ∀ d ∈ D, ∀ E : Set G, IsMaxOrbit D d E →
    ∀ e ∈ E, ∀ f ∈ E, ¬ Commute e f → rootSet D e ⊆ E → rootSet D f ⊆ E →
    SqOut ↥(rootGen D e f) →
    CFSG.Timmesfeld.Connectivity.Disconnected
      (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E) →
    ∀ n : ℕ, 1 ≤ n →
      Nonempty (↥(Subgroup.closure E) ⧸ CFSG.Timmesfeld.Bridge.zStar ↥(Subgroup.closure E) ≃*
        CFSG.Theory.Comparator.SzModel n) → False

theorem noSzBelow_of
    (hM : SzMainStmt) : ∀ m : ℕ, NoSzBelow m := by
  intro m
  refine Nat.strong_induction_on m ?_
  intro k IH
  unfold NoSzBelow
  intro G _ _ D hcard h d hd x hx hdx hsq
  have hIH : NoSzBelow (Nat.card G) := IH (Nat.card G) hcard
  obtain ⟨c, hc, E, hE, e, he, f, hf, hef, hrE, hrF, hsq'⟩ :=
    exists_good_pair h ⟨d, hd, x, hx, hdx, hsq⟩
  obtain ⟨hdisc, n, hn, hquot⟩ := szMain_config hIH h hc hE he hf hef hrE hrF hsq'
  exact hM G D h hIH c hc E hE e he f hf hef hrE hrF hsq' hdisc n hn hquot

end CFSG.Timmesfeld.Bridge.OddRoot
