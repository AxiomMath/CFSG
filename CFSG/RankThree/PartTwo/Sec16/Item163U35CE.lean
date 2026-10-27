module

public import CFSG.RankThree.PartTwo.Sec16.Item163U35Conf

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

structure CE684 (A L K₁ K₂ T₁ T₂ : Subgroup G) : Prop where
  zeta₁ : IsZeta A L T₁ K₁
  zeta₂ : IsZeta A L T₂ K₂
  ne_bot : T₁ ⊓ T₂ ≠ ⊥
  not_conj : ¬ ∃ x ∈ xA A, K₁ = K₂.map (MulAut.conj x).toMonoidHom

@[expose] def MaxCE684 (A L K₁ K₂ T₁ T₂ : Subgroup G) : Prop :=
  CE684 A L K₁ K₂ T₁ T₂ ∧ ∀ K₁' K₂' T₁' T₂' : Subgroup G, CE684 A L K₁' K₂' T₁' T₂' →
    Nat.card (T₁' ⊓ T₂' : Subgroup G) ≤ Nat.card (T₁ ⊓ T₂ : Subgroup G)

theorem CE684.symm {A L K₁ K₂ T₁ T₂ : Subgroup G} (h : CE684 A L K₁ K₂ T₁ T₂) :
    CE684 A L K₂ K₁ T₂ T₁ := by
  refine ⟨h.zeta₂, h.zeta₁, by rw [inf_comm]; exact h.ne_bot, ?_⟩
  rintro ⟨x, hx, hxK⟩
  refine h.not_conj ⟨x⁻¹, inv_mem hx, ?_⟩
  rw [hxK, Late.map_conj_map_conj, inv_mul_cancel, Late.map_conj_one]

theorem MaxCE684.symm {A L K₁ K₂ T₁ T₂ : Subgroup G} (h : MaxCE684 A L K₁ K₂ T₁ T₂) :
    MaxCE684 A L K₂ K₁ T₂ T₁ := by
  refine ⟨h.1.symm, fun K₁' K₂' T₁' T₂' h' => ?_⟩
  rw [inf_comm T₂ T₁]
  exact h.2 K₁' K₂' T₁' T₂' h'

theorem exists_maxCE684 {A L K₁ K₂ T₁ T₂ : Subgroup G} (h : CE684 A L K₁ K₂ T₁ T₂) :
    ∃ K₁' K₂' T₁' T₂' : Subgroup G, MaxCE684 A L K₁' K₂' T₁' T₂' := by
  set s : Set (Subgroup G × Subgroup G × Subgroup G × Subgroup G) :=
    {p | CE684 A L p.1 p.2.1 p.2.2.1 p.2.2.2} with hs
  obtain ⟨⟨K₁', K₂', T₁', T₂'⟩, hmem, hmax⟩ := Set.exists_max_image s
    (fun p => Nat.card (p.2.2.1 ⊓ p.2.2.2 : Subgroup G)) (Set.toFinite s)
    ⟨(K₁, K₂, T₁, T₂), h⟩
  exact ⟨K₁', K₂', T₁', T₂', hmem, fun K₁'' K₂'' T₁'' T₂'' h'' =>
    hmax (K₁'', K₂'', T₁'', T₂'') h''⟩

theorem MaxCE684.exists_conj_of_card_lt {A L K₁ K₂ T₁ T₂ : Subgroup G}
    (h : MaxCE684 A L K₁ K₂ T₁ T₂) {K K' T T' : Subgroup G} (hT : IsZeta A L T K)
    (hT' : IsZeta A L T' K')
    (hlt : Nat.card (T₁ ⊓ T₂ : Subgroup G) < Nat.card (T ⊓ T' : Subgroup G)) :
    ∃ x ∈ xA A, K = K'.map (MulAut.conj x).toMonoidHom := by
  by_contra hn
  have hne : T ⊓ T' ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hlt
    exact absurd hlt (Nat.not_lt.mpr Nat.card_pos)
  exact absurd (h.2 K K' T T' ⟨hT, hT', hne, hn⟩) (Nat.not_le.mpr hlt)

end CFSG.RankThree.PartTwo.Sec16.Proof163U35
