module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K331Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.Open (IsElemAbelian)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.SectionRank (le_pRank pRank_top_eq_of_mulEquiv three_le_pRank_alternating
  sqtkSporadicNames SporadicThreeRankWitnesses)

theorem k331Idx_cyclic (p : ℕ) (hp : p.Prime) : K331Idx (.cyclic p hp) := by
  refine K331Idx.of_card (Or.inl ?_)
  have hc : Nat.card (TauCeti.CFSGIndex.cyclic p hp).Group = p := by
    change Nat.card (Multiplicative (ZMod p)) = p
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p), Nat.card_zmod]
  rw [hc]
  intro h
  rcases (Nat.dvd_prime hp).1 h with h1 | h1
  · omega
  · exact absurd (h1 ▸ hp) (by norm_num)

theorem k331Idx_alternating (n : ℕ) (hn : 5 ≤ n) : K331Idx (.alternating n hn) := by
  rcases (show n ≤ 8 ∨ 9 ≤ n by omega) with h8 | h9
  · refine K331Idx.of_card ?_
    change ¬ 20160 ∣ Nat.card (alternatingGroup (Fin n)) ∨
      Nat.card (alternatingGroup (Fin n)) = 20160
    interval_cases n <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> decide
  · refine K331Idx.of_three_le fun S _ _ ⟨e⟩ => ?_
    have e' : S ≃* alternatingGroup (Fin n) := e
    rw [pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e']
    exact three_le_pRank_alternating h9

section Sporadic

variable {s : TauCeti.SporadicName}

theorem k331Idx_sporadic_card (hbr : Nonempty (Carrier s ≃* s.Group))
    (h : ¬ 20160 ∣ Nat.card (Carrier s) ∨
      Nat.card (Carrier s) = 20160) : K331Idx (.sporadic s) := by
  obtain ⟨b⟩ := hbr
  refine K331Idx.of_card ?_
  have hc : Nat.card (TauCeti.CFSGIndex.sporadic s).Group = Nat.card (Carrier s) :=
    (Nat.card_congr b.toEquiv).symm
  rwa [hc]

theorem k331Idx_sporadic_rank (hbr : Nonempty (Carrier s ≃* s.Group))
    (hE : Nontrivial (Carrier s) →
      ∃ E : Subgroup (Carrier s), IsElemAbelian 3 E ∧
        ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k) : K331Idx (.sporadic s) := by
  obtain ⟨b⟩ := hbr
  intro L _ _ hs h3 ⟨e⟩
  have e' : L ≃* Carrier s := e.trans b.symm
  have : Finite (Carrier s) := Finite.of_equiv L e'.toEquiv
  have : Nontrivial L := hs.toNontrivial
  have : Nontrivial (Carrier s) := e'.symm.toEquiv.nontrivial
  obtain ⟨E, hEa, k, hk, hc⟩ := hE inferInstance
  have h1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier s)) :=
    le_pRank (by norm_num) le_top hEa hc
  rw [pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'] at h3
  omega

theorem k331Idx_sporadic_conclusion (hbr : Nonempty (Carrier s ≃* s.Group))
    (hs : s = .M24 ∨ s = .J4) : K331Idx (.sporadic s) := by
  obtain ⟨b⟩ := hbr
  intro L _ _ _ _ ⟨e⟩ T _ K _ _
  refine Or.inr (Or.inr ?_)
  rcases hs with rfl | rfl
  · exact Or.inl ⟨e.trans b.symm⟩
  · exact Or.inr ⟨e.trans b.symm⟩

end Sporadic

theorem k331Idx_sporadic
    (hbr : ∀ s : TauCeti.SporadicName, Nonempty (Carrier s ≃* s.Group))
    (hM11 : Nat.card (Carrier .M11) = 7920)
    (hM12 : Nat.card (Carrier .M12) = 2 ^ 6 * 3 ^ 3 * 5 * 11)
    (hJ1 : Nat.card (Carrier .J1) = 2 ^ 3 * 3 * 5 * 7 * 11 * 19)
    (hW : SporadicThreeRankWitnesses)
    (hM : Nontrivial (Carrier .M) →
      ∃ E : Subgroup (Carrier .M), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    {s : TauCeti.SporadicName}
    (hs : ¬ (s = .J2 ∨ s = .M22 ∨ s = .M23 ∨ s = .HS ∨ s = .He ∨ s = .Ru)) :
    K331Idx (.sporadic s) := by
  have hw : ∀ s, s ∉ sqtkSporadicNames → s ≠ .M → Nontrivial (Carrier s) →
      ∃ E : Subgroup (Carrier s), IsElemAbelian 3 E ∧
        ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k :=
    fun s h1 h2 _ => hW s h1 h2
  cases s with
  | M11 => exact k331Idx_sporadic_card (hbr _) (Or.inl (by rw [hM11]; decide))
  | M12 => exact k331Idx_sporadic_card (hbr _) (Or.inl (by rw [hM12]; decide))
  | J1 => exact k331Idx_sporadic_card (hbr _) (Or.inl (by rw [hJ1]; decide))
  | M24 => exact k331Idx_sporadic_conclusion (hbr _) (Or.inl rfl)
  | J4 => exact k331Idx_sporadic_conclusion (hbr _) (Or.inr rfl)
  | M =>
    exact k331Idx_sporadic_rank (hbr _) fun h =>
      let ⟨E, hE, hc⟩ := hM h
      ⟨E, hE, 4, by norm_num, hc⟩
  | J2 | M22 | M23 | HS | He | Ru => simp at hs
  | J3 | McL | Suz | ONan | Co1 | Co2 | Co3 | Fi22 | Fi23 | Fi24Prime | HN | Ly | Th | B =>
    exact k331Idx_sporadic_rank (hbr _) (hw _ (by decide) (by decide))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
