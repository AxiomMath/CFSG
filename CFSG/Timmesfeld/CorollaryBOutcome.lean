module

public import CFSG.Timmesfeld.CorollaryBSteps
public import CFSG.Timmesfeld.CorollaryBRankTwo
public import CFSG.Timmesfeld.CorollaryBBasic

public section

namespace CFSG.Timmesfeld.CorB

open CFSG.Blueprint

@[expose] def OutcomeTwo (G : Type) [Group G] (D : Set G) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ (∃ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) ∧ LieModel G .PSL 3 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ (∃ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) ∧ LieModel G .G2 0 2 f) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (∃ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f) ∧
    LieModel G .trialityD4 0 2 f) ∨
  LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
  NativeSporadic.IsSporadic G .J2

theorem outcomeTwo_of_ars {G : Type} [Group G] {D : Set G}
    (h : ARSOutcomeTwo G (rootClass D)) : OutcomeTwo G D := by
  rcases h with ⟨f, hf, ⟨_, ⟨d, hd, rfl⟩, hA⟩, hL⟩ | ⟨f, hf, ⟨_, ⟨d, hd, rfl⟩, hA⟩, hL⟩ |
    ⟨f, hf, ⟨_, ⟨d, hd, rfl⟩, hA⟩, hL⟩ | hU
  · exact Or.inl ⟨f, hf, ⟨d, hd, hA⟩, hL⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨d, hd, hA⟩, hL⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨d, hd, hA⟩, hL⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hU)))

theorem noOppCentral_rootClass {G : Type} [Group G] [Finite G] {D : Set G}
    (hD : IsRootInvolutionSet D) (hno : NoOddCent D) : NoOppCentral (rootClass D) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨⟨b, hb, rfl⟩, hab⟩ _ ⟨⟨c, hc, rfl⟩, hac⟩ hop
  have hamem : a ∈ rootGroup D a := Subgroup.subset_closure (mem_rootSet_self ha)
  have hbmem : b ∈ rootGroup D b := Subgroup.subset_closure (mem_rootSet_self hb)
  have hcmem : c ∈ rootGroup D c := Subgroup.subset_closure (mem_rootSet_self hc)
  have hodd := hop.odd_orderOf_mul (fun x hx => mul_self_eq_one_of_mem_rootGroup hD hb hx)
    hbmem (hD.ne_one hb) hcmem (hD.ne_one hc)
  have hbc := hno a ha b hb c hc (hab a hamem b hbmem) (hac a hamem c hcmem) hodd
  subst hbc
  exact hop.1 rfl

theorem largeFacts {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ Bridge.ExistsCommSpec D := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] (D : Set G), Nat.card G = n → Hyp G D →
      (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
        RootClosure D ∧ SpecialClosure D ∧ RootMoufang D ∧ Bridge.ExistsCommSpec D from
    key _ G D rfl h hl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ D hn h hl
    have IH : Bridge.RootIHStructE G := fun G' _ D' h' hlt =>
      ⟨outcome h', ih _ (hn ▸ hlt) G' D' rfl h'⟩
    exact largeStepSE_holds G D h IH hl

theorem outcomeTwo_of_noOddCent {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hno : NoOddCent D) : OutcomeTwo G D := by
  have := h.finite
  by_cases hJ : NativeSporadic.IsSporadic G .J2
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))
  have hNO := noOppCentral_rootClass h.root hno
  by_cases hlarge : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d
  · obtain ⟨hc, hs, hm, -⟩ := largeFacts h hlarge
    exact outcomeTwo_of_ars (outcomeTwo_of_noOppCentral (arsHyp_rootClass h hc hs hm) hNO)
  · push Not at hlarge
    have hsing : ∀ d ∈ D, rootSet D d = {d} := fun d hd =>
      rootSet_eq_singleton_of_forall hlarge hd
    by_cases hex : ∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧
        orderOf (d * c) ≠ 3
    · have IH : RootIH G := fun G' _ D' h' _ => outcome h'
      obtain ⟨hQ, hLL, hNP⟩ := exceptionalGlobalStepNJ2_holds G D h IH hsing hex hJ
      have hconn := commConnected_holds G D h
      rcases Moufang.exceptionalInput_at h hsing hex
          ⟨hQ, hLL, hNP, Moufang.lineCount_of h hsing hQ hLL hNP (hconn hNP)⟩ (hconn hNP)
          Moufang.a6Endgame Moufang.j2Endgame with he | hj
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
      · exact absurd hj hJ
    · push Not at hex
      exact outcomeTwo_of_ars (outcomeTwo_of_noOppCentral (arsHyp_rootClass h
        (rootClosure_of_singleton hsing) (specialClosure_of_singleton h.root hsing)
        (Moufang.rootMoufang_of_singleton hsing hex)) hNO)

end CFSG.Timmesfeld.CorB
