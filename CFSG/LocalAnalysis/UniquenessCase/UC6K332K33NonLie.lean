module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33Inj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Open (IsElemAbelian)
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.SectionRank (le_pRank pRank_top_eq_of_mulEquiv three_le_pRank_alternating
  sqtkSporadicNames SporadicThreeRankWitnesses)

theorem k33Models_cyclic {p : ℕ} (hp : p.Prime) {L : Type} [Group L]
    (e : L ≃* (TauCeti.CFSGIndex.cyclic p hp).Group) (hna : ∃ a b : L, a * b ≠ b * a) :
    K33Models L := by
  obtain ⟨a, b, hab⟩ := hna
  have hc : ∀ x y : (TauCeti.CFSGIndex.cyclic p hp).Group, x * y = y * x :=
    fun x y => mul_comm x y
  exact absurd (e.injective (by rw [map_mul, map_mul]; exact hc (e a) (e b))) hab

theorem k33Models_alternating {n : ℕ} (hn : 5 ≤ n) {L : Type} [Group L] [Finite L]
    (e : L ≃* (TauCeti.CFSGIndex.alternating n hn).Group)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  have e' : L ≃* alternatingGroup (Fin n) := e
  have hX : CFSG.Open.pRank 3 (⊤ : Subgroup L) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin n))) :=
    pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'
  rcases (show n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ 9 ≤ n by omega) with h | h | h | h | h
  · subst h
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ 1 :=
      CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three
        (k := 1) (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide)
    omega
  · subst h
    exact K33Models.of_isAlt_six ⟨e'⟩
  · subst h
    exact K33Models.of_isAlt_seven ⟨e'⟩
  · subst h
    obtain ⟨e8⟩ := CFSG.GH74.Exceptional.nonempty_mulEquiv_statedProj_of_alternating_eight e'
    exact K33Models.of_psl4 (p := 2) (f := 1) (by norm_num)
      (Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
        inferInstance, inferInstance, by simp, ⟨e8⟩⟩)
  · have := three_le_pRank_alternating h
    omega

theorem k33Idx_sporadic_rank {s : TauCeti.SporadicName}
    (hbr : Nonempty (Carrier s ≃* s.Group))
    (hE : Nontrivial (Carrier s) →
      ∃ E : Subgroup (Carrier s), IsElemAbelian 3 E ∧
        ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k)
    {L : Type} [Group L] [Finite L] [Nontrivial L]
    (e : L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : False := by
  obtain ⟨b⟩ := hbr
  have e' : L ≃* Carrier s := e.trans b.symm
  have : Finite (Carrier s) := Finite.of_equiv L e'.toEquiv
  have : Nontrivial (Carrier s) := e'.symm.toEquiv.nontrivial
  obtain ⟨E, hEa, k, hk, hc⟩ := hE inferInstance
  have h1 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier s)) :=
    le_pRank (by norm_num) le_top hEa hc
  rw [pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'] at h2
  omega

theorem k33Models_sporadic
    (hbr : ∀ s : TauCeti.SporadicName, Nonempty (Carrier s ≃* s.Group))
    (hJ1 : Nat.card (Carrier .J1) = 2 ^ 3 * 3 * 5 * 7 * 11 * 19)
    (hW : SporadicThreeRankWitnesses)
    (hM : Nontrivial (Carrier .M) →
      ∃ E : Subgroup (Carrier .M), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    {s : TauCeti.SporadicName} {L : Type} [Group L] [Finite L] [Nontrivial L]
    (e : L ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (h2 : CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2) : K33Models L := by
  by_cases hs : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨
      s = .He ∨ s = .Ru ∨ s = .J4
  · obtain ⟨b⟩ := hbr s
    exact K33Models.of_spor hs ⟨e.trans b.symm⟩
  · exfalso
    have hw : ∀ s, s ∉ sqtkSporadicNames → s ≠ .M → Nontrivial (Carrier s) →
        ∃ E : Subgroup (Carrier s), IsElemAbelian 3 E ∧
          ∃ k : ℕ, 3 ≤ k ∧ Nat.card E = 3 ^ k :=
      fun s h1 h2 _ => hW s h1 h2
    cases s with
    | M11 | M12 | M22 | M23 | M24 | J2 | HS | He | Ru | J4 => simp at hs
    | J1 =>
      obtain ⟨b⟩ := hbr .J1
      have e' : L ≃* Carrier .J1 := e.trans b.symm
      have : Finite (Carrier .J1) := Finite.of_equiv L e'.toEquiv
      have hle : CFSG.Open.pRank 3 (⊤ : Subgroup (Carrier .J1)) ≤ 1 :=
        CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd Nat.prime_three
          (k := 1) (by rw [hJ1]; decide)
      rw [pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'] at h2
      omega
    | M =>
      exact k33Idx_sporadic_rank (hbr _) (fun h =>
        let ⟨E, hE, hc⟩ := hM h
        ⟨E, hE, 4, by norm_num, hc⟩) e h2
    | J3 | McL | Suz | ONan | Co1 | Co2 | Co3 | Fi22 | Fi23 | Fi24Prime | HN | Ly | Th | B =>
      exact k33Idx_sporadic_rank (hbr _) (hw _ (by decide) (by decide)) e h2

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
