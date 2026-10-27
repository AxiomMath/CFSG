module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open CFSG.Open

section Map

variable {A B : Type*} [Group A] [Group B]

theorem isElemAbelian_map {p : ℕ} (f : A →* B) {E : Subgroup A} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  obtain ⟨hc, hp⟩ := hE
  refine ⟨inferInstance, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, hp x hx, map_one]

end Map

section PRank

variable {G : Type*} [Group G] [Finite G]

theorem le_pRank {p : ℕ} (hp : 1 < p) {H : Subgroup G} {k : ℕ} (E : Subgroup G) (hEH : E ≤ H)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) : k ≤ pRank p H := by
  unfold pRank
  apply le_csSup
  · refine ⟨Nat.card G, ?_⟩
    rintro j ⟨E', -, -, hE'⟩
    have h1 : p ^ j ≤ Nat.card G := hE' ▸ Subgroup.card_le_card_group E'
    have h2 : j < p ^ j := Nat.lt_pow_self hp
    omega
  · exact ⟨E, hEH, hE, hcard⟩

theorem pRank_le {p : ℕ} (H : Subgroup G) {m : ℕ}
    (h : ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → ∀ k, Nat.card E = p ^ k → k ≤ m) :
    pRank p H ≤ m := by
  unfold pRank
  apply csSup_le
  · exact ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by
      rw [Subgroup.mem_bot.1 hx, one_pow]⟩, by simp⟩
  · rintro k ⟨E, hEH, hE, hc⟩
    exact h E hEH hE k hc

theorem pRank_eq {p : ℕ} (hp : 1 < p) {H : Subgroup G} {k : ℕ} (E : Subgroup G) (hEH : E ≤ H)
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k)
    (h : ∀ E' : Subgroup G, E' ≤ H → IsElemAbelian p E' → ∀ j, Nat.card E' = p ^ j → j ≤ k) :
    pRank p H = k :=
  le_antisymm (pRank_le H h) (le_pRank hp E hEH hE hcard)

theorem pRank_le_of_equiv {B : Type*} [Group B] [Finite B] {p : ℕ} (hp : 1 < p) (e : G ≃* B) :
    pRank p (⊤ : Subgroup G) ≤ pRank p (⊤ : Subgroup B) := by
  refine pRank_le _ fun E _ hE k hk => ?_
  exact le_pRank hp (E.map e.toMonoidHom) le_top (isElemAbelian_map e.toMonoidHom hE)
    (by rw [Subgroup.card_map_of_injective e.injective, hk])

theorem pRank_congr {B : Type*} [Group B] [Finite B] {p : ℕ} (hp : 1 < p) (e : G ≃* B) :
    pRank p (⊤ : Subgroup G) = pRank p (⊤ : Subgroup B) :=
  le_antisymm (pRank_le_of_equiv hp e) (pRank_le_of_equiv hp e.symm)

end PRank

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
