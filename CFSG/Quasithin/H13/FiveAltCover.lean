module

public import CFSG.Quasithin.H13.Statements
public import CFSG.LocalAnalysis.SectionRank.AlternatingCover
public import CFSG.Quasithin.Background.KnownMultOdd

public section

namespace CFSG.Quasithin.H13

theorem nonempty_mulEquiv_of_center_eq_bot {Q H : Type*} [Group Q] [Group H]
    (hZ : Subgroup.center Q = ⊥) (e : Q ⧸ Subgroup.center Q ≃* H) : Nonempty (Q ≃* H) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem five_alternating_small_central_cover_reduction {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.IsQuasisimple Q) (hodd : Odd (Nat.card (Subgroup.center Q))) {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
    (e : Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n)) :
    ((n = 5 ∨ n = 8) → Subgroup.center Q = ⊥ ∧ Nonempty (Q ≃* alternatingGroup (Fin n))) ∧
    ((n = 6 ∨ n = 7) →
      (Nat.card (Subgroup.center Q) = 1 ∨ Nat.card (Subgroup.center Q) = 3) ∧
      (Nat.card (Subgroup.center Q) = 1 → Nonempty (Q ≃* alternatingGroup (Fin n))) ∧
      (Nat.card (Subgroup.center Q) ≠ 1 → Group.IsPerfect Q ∧
        Nat.card (Subgroup.center Q) = 3 ∧
        Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n)))) ∧
    ((n = 5 ∨ n = 6) → QT13Five Q) := by
  have : Group.IsPerfect Q := hQ.1
  set π : Q →* alternatingGroup (Fin n) := e.toMonoidHom.comp (QuotientGroup.mk' _) with hπ
  have hsurj : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center Q))
  have hker : π.ker = Subgroup.center Q := ker_mk_comp_mulEquiv (Subgroup.center Q) e
  have h5 : 5 ≤ n := by omega
  have h8 : n ≤ 8 := by omega
  obtain ⟨hb58, hb67⟩ := CFSG.SectionRank.alternating_small_odd_cover_bound h5 h8 π hsurj
    hker.le (by rwa [hker])
  rw [hker] at hb58 hb67
  have hiso : Subgroup.center Q = ⊥ → Nonempty (Q ≃* alternatingGroup (Fin n)) :=
    fun hZ => nonempty_mulEquiv_of_center_eq_bot hZ e
  have hA : (n = 5 ∨ n = 8) → Subgroup.center Q = ⊥ ∧ Nonempty (Q ≃* alternatingGroup (Fin n)) :=
    fun h => ⟨hb58 h, hiso (hb58 h)⟩
  have hB : (n = 6 ∨ n = 7) →
      (Nat.card (Subgroup.center Q) = 1 ∨ Nat.card (Subgroup.center Q) = 3) ∧
      (Nat.card (Subgroup.center Q) = 1 → Nonempty (Q ≃* alternatingGroup (Fin n))) ∧
      (Nat.card (Subgroup.center Q) ≠ 1 → Group.IsPerfect Q ∧
        Nat.card (Subgroup.center Q) = 3 ∧
        Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin n))) := by
    intro h
    have h13 := hb67 h
    refine ⟨h13, fun h1 => hiso (Subgroup.eq_bot_of_card_eq _ h1), fun h1 => ⟨hQ.1, ?_, ⟨e⟩⟩⟩
    rcases h13 with h' | h'
    · exact absurd h' h1
    · exact h'
  refine ⟨hA, hB, ?_⟩
  rintro (rfl | rfl)
  · exact Or.inl (hA (Or.inl rfl)).2
  · obtain ⟨h13, h1, h3⟩ := hB (Or.inl rfl)
    by_cases hc : Nat.card (Subgroup.center Q) = 1
    · exact Or.inr (Or.inr (Or.inl (h1 hc)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (h3 hc))))

end CFSG.Quasithin.H13
