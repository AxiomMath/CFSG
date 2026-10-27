module

public import CFSG.Quasithin.Background.A1bPGroups

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank.Ccomm

namespace A1c

section Structure

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem closure_pow_eq_top_of_closure_eq {G : Type*} [Group G] {Y : Subgroup G}
    (h : Subgroup.closure {x : G | x ∈ Y ∧ x ^ p = 1} = Y) :
    Subgroup.closure {x : ↥Y | x ^ p = 1} = ⊤ := by
  have hset : Y.subtype '' {x : ↥Y | x ^ p = 1} = {x : G | x ∈ Y ∧ x ^ p = 1} := by
    ext g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, by simpa using congrArg Subtype.val hu⟩
    · rintro ⟨hg, hgp⟩
      exact ⟨⟨g, hg⟩, Subtype.ext (by simpa using hgp), rfl⟩
  apply Subgroup.map_injective Y.subtype_injective
  rw [MonoidHom.map_closure, hset, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

variable {X : Type*} [Group X] [Finite X]

theorem frattini_eq_bot_of_commutative (hcomm : ∀ a b : X, a * b = b * a)
    (hexp : ∀ x : X, x ^ p = 1) : frattini X = ⊥ := by
  refine le_bot_iff.1 (frattini_le_of_commutator_pow_mem (p := p) (⊥ : Subgroup X) (fun a b => ?_)
    (fun a => ?_))
  · rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b)
  · rw [Subgroup.mem_bot]
    exact hexp a

omit [Finite X] in
theorem exists_not_commute_of_isPOnePlusTwo (hX : IsPOnePlusTwo p X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨hext, hcard, -⟩ := hX
  by_contra hcon
  push Not at hcon
  have hcen : Subgroup.center X = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact Subgroup.mem_center_iff.2 fun g => hcon g x
  have h1 := CFSG.IsExtraspecial.center_order_p p X
  rw [hcen, Subgroup.card_top, hcard] at h1
  have hp1 : 1 < p := hp.out.one_lt
  have : p < p ^ 3 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp1 (by norm_num)
  omega

theorem frattini_eq_center_of_isPOnePlusTwo (hX : IsPOnePlusTwo p X) :
    frattini X = Subgroup.center X := by
  have hnc := exists_not_commute_of_isPOnePlusTwo hX
  obtain ⟨hext, hcard, hexp⟩ := hX
  have := hext
  have hPg : Fact (IsPGroup p X) := ⟨CFSG.IsExtraspecial.isPGroup p X⟩
  obtain ⟨hcomm, -⟩ := nonabelian_prime_cube_central_structure hcard hnc
  rw [frattini_eq_closure_commutator_union_powers (R := X) (p := p), hcomm]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · show y ^ p ∈ Subgroup.center X
      rw [hexp y]
      exact Subgroup.one_mem _
  · intro x hx
    exact Subgroup.subset_closure (Or.inl hx)

theorem frattini_bot_or_isPOnePlusTwo (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hΩ : Subgroup.closure {x : X | x ^ p = 1} = ⊤) (hcl : ClassLeTwo (⊤ : Subgroup X))
    (hrank : pRank p (⊤ : Subgroup X) = 2) :
    (frattini X = ⊥ ∧ Nat.card X = p ^ 2) ∨ IsPOnePlusTwo p X := by
  have hexp := pow_eq_one_of_classLeTwo hp2 hcl hΩ
  rcases isElemAbelianOfRank_two_or_isPOnePlusTwo hp2 hX hΩ hrank hcl with he | h
  · left
    obtain ⟨e⟩ : Nonempty (X ≃* Multiplicative (Fin 2 → ZMod p)) := he
    have hcomm : ∀ a b : X, a * b = b * a := fun a b =>
      e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
    refine ⟨frattini_eq_bot_of_commutative hcomm hexp, ?_⟩
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod p) ≃ (Fin 2 → ZMod p))]
    simp
  · exact Or.inr h

theorem index_frattini_eq_sq (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hΩ : Subgroup.closure {x : X | x ^ p = 1} = ⊤) (hcl : ClassLeTwo (⊤ : Subgroup X))
    (hrank : pRank p (⊤ : Subgroup X) = 2) : (frattini X).index = p ^ 2 := by
  rcases frattini_bot_or_isPOnePlusTwo hp2 hX hΩ hcl hrank with ⟨h1, h2⟩ | h
  · rw [h1, Subgroup.index_bot, h2]
  · have hΦ := frattini_eq_center_of_isPOnePlusTwo h
    have := h.1
    have h3 := Subgroup.index_mul_card (frattini X)
    rw [hΦ, CFSG.IsExtraspecial.center_order_p p X, h.2.1] at h3
    have h4 : (Subgroup.center X).index * p = p ^ 2 * p := by rw [h3]; ring
    rw [hΦ]
    exact Nat.eq_of_mul_eq_mul_right hp.out.pos h4

theorem frattini_eq_bot_or_isPOnePlusTwo (hp2 : p ≠ 2) (hX : IsPGroup p X)
    (hΩ : Subgroup.closure {x : X | x ^ p = 1} = ⊤) (hcl : ClassLeTwo (⊤ : Subgroup X))
    (hrank : pRank p (⊤ : Subgroup X) ≤ 2) : frattini X = ⊥ ∨ IsPOnePlusTwo p X := by
  have hexp := pow_eq_one_of_classLeTwo hp2 hcl hΩ
  by_cases h2 : pRank p (⊤ : Subgroup X) = 2
  · rcases frattini_bot_or_isPOnePlusTwo hp2 hX hΩ hcl h2 with ⟨h, -⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  · left
    have h1 : pRank p (⊤ : Subgroup X) ≤ 1 := by omega
    apply frattini_eq_bot_of_commutative _ hexp
    by_cases hbot : (⊤ : Subgroup X) = ⊥
    · intro a b
      have ha : a ∈ (⊥ : Subgroup X) := hbot ▸ Subgroup.mem_top a
      have hb : b ∈ (⊥ : Subgroup X) := hbot ▸ Subgroup.mem_top b
      rw [Subgroup.mem_bot.1 ha, Subgroup.mem_bot.1 hb]
    · obtain ⟨z, -, hz, -⟩ := exists_eq_zpowers_of_pRank_le_one hX hbot (fun x _ => hexp x) h1
      intro a b
      have ha : a ∈ Subgroup.zpowers z := hz ▸ Subgroup.mem_top a
      have hb : b ∈ Subgroup.zpowers z := hz ▸ Subgroup.mem_top b
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow_self z m n).eq

end Structure

end A1c

end CFSG.Quasithin
