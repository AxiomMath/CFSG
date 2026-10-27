module

public import CFSG.Timmesfeld.SkeletonCases
public import CFSG.Timmesfeld.Moufang.Cases
public import CFSG.Timmesfeld.Moufang.LineCount

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open

@[expose] def RootIH (G : Type) [Group G] : Prop :=
  ∀ (G' : Type) [Group G'] (D' : Set G'), Hyp G' D' → Nat.card G' < Nat.card G → Outcome G'

theorem outcome_at {G : Type} [Group G] {D : Set G} (h : Hyp G D)
    (hL : (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
      RootClosure D ∧ SpecialClosure D ∧ RootMoufang D)
    (hX : (∀ d ∈ D, rootSet D d = {d}) →
      (∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧ orderOf (d * c) ≠ 3) →
      Moufang.CommLambda D ∧ Moufang.LL5 D ∧ Moufang.NoPolar D)
    (hconn : Moufang.NoPolar D → Closure.CommConnected D) (hA : ARSInput) : Outcome G := by
  by_cases hlarge : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d
  · obtain ⟨hc, hs, hm⟩ := hL hlarge
    exact hA G (rootClass D) (arsHyp_rootClass h hc hs hm)
  · push Not at hlarge
    have hsing : ∀ d ∈ D, rootSet D d = {d} := fun d hd =>
      rootSet_eq_singleton_of_forall hlarge hd
    by_cases hex : ∃ d ∈ D, ∃ c ∈ D, ¬ Commute d c ∧ Odd (orderOf (d * c)) ∧
        orderOf (d * c) ≠ 3
    · obtain ⟨hQ, hLL, hNP⟩ := hX hsing hex
      rcases Moufang.exceptionalInput_at h hsing hex
          ⟨hQ, hLL, hNP, Moufang.lineCount_of h hsing hQ hLL hNP (hconn hNP)⟩ (hconn hNP)
          Moufang.a6Endgame Moufang.j2Endgame with he | hj
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl he))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr hj))))))
    · push Not at hex
      exact hA G (rootClass D) (arsHyp_rootClass h (rootClosure_of_singleton hsing)
        (specialClosure_of_singleton h.root hsing) (Moufang.rootMoufang_of_singleton hsing hex))

end CFSG.Timmesfeld
