module

public import CFSG.Quasithin.EmptyFaithful.S146zUC2Off

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.S146zU.UC2

section Pair

variable {V : Type} [CommGroup V] {K₁ K₂ : Type} [Field K₁] [Field K₂] {L₁ L₂ : Subgroup (MulAut V)}
  {C : Subgroup V} {Φ : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂) →* MulAut V}
  {Θ : V →* Multiplicative (Fin 2 → K₁) × Multiplicative (Fin 2 → K₂)}

theorem pairModel_offender_core [Finite V] [Finite K₁] [Finite K₂] {m₁ m₂ : ℕ}
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 2 ^ m₁) (hK₂ : Nat.card K₂ = 2 ^ m₂)
    (Al : Subgroup (↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂))) (hAl : ∀ g ∈ Al, g ^ 2 = 1)
    (hge : Nat.card V ≤ Nat.card ↥Al * Nat.card ↥(fixV (Al.map Φ))) :
    ∃ (A₁ : Subgroup ↥(StatedSL 2 K₁)) (A₂ : Subgroup ↥(StatedSL 2 K₂)),
      (∀ g, g ∈ Al ↔ g.1 ∈ A₁ ∧ g.2 ∈ A₂) ∧ Nat.card ↥Al = Nat.card ↥A₁ * Nat.card ↥A₂ ∧
      (A₁ = ⊥ ∨ Nat.card ↥A₁ = Nat.card K₁) ∧ (A₂ = ⊥ ∨ Nat.card ↥A₂ = Nat.card K₂) := by
  set A₁ : Subgroup ↥(StatedSL 2 K₁) := Al.map (MonoidHom.fst _ _) with hA₁
  set A₂ : Subgroup ↥(StatedSL 2 K₂) := Al.map (MonoidHom.snd _ _) with hA₂
  have hsq₁ : ∀ x ∈ A₁, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    have := congrArg Prod.fst (hAl g hg)
    simpa using this
  have hsq₂ : ∀ y ∈ A₂, y ^ 2 = 1 := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have := congrArg Prod.snd (hAl g hg)
    simpa using this
  have hAl_mem : ∀ g ∈ Al, g.1 ∈ A₁ ∧ g.2 ∈ A₂ := fun g hg =>
    ⟨Subgroup.mem_map_of_mem _ hg, Subgroup.mem_map_of_mem _ hg⟩
  let f : ↥Al → ↥A₁ × ↥A₂ := fun g =>
    (⟨g.1.1, (hAl_mem g.1 g.2).1⟩, ⟨g.1.2, (hAl_mem g.1 g.2).2⟩)
  have hfinj : Function.Injective f := by
    intro g h hgh
    have h1 := congrArg (fun p : ↥A₁ × ↥A₂ =>
      ((p.1 : ↥(StatedSL 2 K₁)), (p.2 : ↥(StatedSL 2 K₂)))) hgh
    exact Subtype.ext h1
  have hAl_le : Nat.card ↥Al ≤ Nat.card ↥A₁ * Nat.card ↥A₂ := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective f hfinj
  have hfix := hM.card_fixV_le Al
  have h₁ := card_mul_card_fixNat_le hK₁ A₁ hsq₁
  have h₂ := card_mul_card_fixNat_le hK₂ A₂ hsq₂
  have hV := hM.card_V
  obtain ⟨e₁, e₂, e₃, e₄⟩ := eq_of_chain (V := Nat.card V) (c := Nat.card ↥C)
    (q₁ := Nat.card K₁ ^ 2) (q₂ := Nat.card K₂ ^ 2) (a := Nat.card ↥Al) (a₁ := Nat.card ↥A₁)
    (a₂ := Nat.card ↥A₂) (d := Nat.card ↥(fixV (Al.map Φ))) (f₁ := Nat.card ↥(fixNat A₁))
    (f₂ := Nat.card ↥(fixNat A₂)) Nat.card_pos (pow_pos Nat.card_pos 2) (pow_pos Nat.card_pos 2)
    Nat.card_pos Nat.card_pos Nat.card_pos Nat.card_pos hV hAl_le hfix h₁ h₂ hge
  refine ⟨A₁, A₂, fun g => ⟨hAl_mem g, fun hg => ?_⟩, e₁, ?_, ?_⟩
  · have hbij : Function.Bijective f :=
      hfinj.bijective_of_nat_card_le (by rw [Nat.card_prod]; exact e₁.symm.le)
    obtain ⟨k, hk⟩ := hbij.2 (⟨g.1, hg.1⟩, ⟨g.2, hg.2⟩)
    have h1 := congrArg (fun p : ↥A₁ × ↥A₂ =>
      ((p.1 : ↥(StatedSL 2 K₁)), (p.2 : ↥(StatedSL 2 K₂)))) hk
    have h2 : (k : ↥(StatedSL 2 K₁) × ↥(StatedSL 2 K₂)) = g := h1
    rw [← h2]
    exact k.2
  · by_cases hb : A₁ = ⊥
    · exact Or.inl hb
    · exact Or.inr (card_eq_field_of_mul_card_fixNat hK₁ hsq₁ hb e₃).1
  · by_cases hb : A₂ = ⊥
    · exact Or.inl hb
    · exact Or.inr (card_eq_field_of_mul_card_fixNat hK₂ hsq₂ hb e₄).1


theorem pairModel_offender_sub [Finite V] [Finite K₁] [Finite K₂] {m₁ m₂ : ℕ}
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 2 ^ m₁) (hK₂ : Nat.card K₂ = 2 ^ m₂)
    {A : Subgroup (MulAut V)} (hA : A ≤ L₁ ⊔ L₂) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hge : Nat.card V ≤ Nat.card ↥A * Nat.card ↥(fixV A)) :
    ∃ A₁ A₂ : Subgroup (MulAut V), A₁ ≤ L₁ ∧ A₂ ≤ L₂ ∧ A = A₁ ⊔ A₂ ∧
      (A₁ = ⊥ ∨ Nat.card ↥A₁ = Nat.card K₁) ∧ (A₂ = ⊥ ∨ Nat.card ↥A₂ = Nat.card K₂) := by
  obtain ⟨Al, hAmap, hcard, hsq'⟩ := hM.exists_lift hA
  have hsq : ∀ g ∈ Al, g ^ 2 = 1 := hsq' hA2
  have hge' : Nat.card V ≤ Nat.card ↥Al * Nat.card ↥(fixV (Al.map Φ)) := by
    rw [hAmap, hcard]
    exact hge
  obtain ⟨A₁, A₂, hmem, -, h₁, h₂⟩ := pairModel_offender_core hM hK₁ hK₂ Al hsq hge'
  let ι₁ : ↥(StatedSL 2 K₁) →* MulAut V := Φ.comp (MonoidHom.inl _ _)
  let ι₂ : ↥(StatedSL 2 K₂) →* MulAut V := Φ.comp (MonoidHom.inr _ _)
  have hι₁ : Function.Injective ι₁ := fun x y h => by
    simpa using congrArg Prod.fst (hM.inj h)
  have hι₂ : Function.Injective ι₂ := fun x y h => by
    simpa using congrArg Prod.snd (hM.inj h)
  refine ⟨A₁.map ι₁, A₂.map ι₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact hM.left_mem g
  · rintro _ ⟨g, -, rfl⟩
    exact hM.right_mem g
  · refine le_antisymm (fun a ha => ?_) (sup_le (fun a ha => ?_) (fun a ha => ?_))
    · rw [← hAmap] at ha
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      have hg' := (hmem g).mp hg
      have e : Φ g = ι₁ g.1 * ι₂ g.2 := by
        show Φ g = Φ (g.1, 1) * Φ (1, g.2)
        rw [← map_mul]
        simp
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem _ hg'.1)
        (Subgroup.mem_map_of_mem _ hg'.2)
    · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem Φ ((hmem (g, 1)).mpr ⟨hg, one_mem _⟩)
    · obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp ha
      rw [← hAmap]
      exact Subgroup.mem_map_of_mem Φ ((hmem (1, g)).mpr ⟨one_mem _, hg⟩)
  · rcases h₁ with h | h
    · exact Or.inl (by rw [h, Subgroup.map_bot])
    · exact Or.inr (by rw [Subgroup.card_map_of_injective hι₁, h])
  · rcases h₂ with h | h
    · exact Or.inl (by rw [h, Subgroup.map_bot])
    · exact Or.inr (by rw [Subgroup.card_map_of_injective hι₂, h])

theorem pairModel_offender_sylow [Finite V] [Finite K₁] [Finite K₂] {m₁ m₂ : ℕ}
    (hM : IsPairModel L₁ L₂ C Φ Θ) (hK₁ : Nat.card K₁ = 2 ^ m₁) (hK₂ : Nat.card K₂ = 2 ^ m₂)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂)
    (hL₁ : Nat.card ↥L₁ = Nat.card ↥(StatedSL 2 K₁))
    (hL₂ : Nat.card ↥L₂ = Nat.card ↥(StatedSL 2 K₂))
    {A : Subgroup (MulAut V)} (hA0 : A ≠ ⊥) (hA : A ≤ L₁ ⊔ L₂) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hge : Nat.card V ≤ Nat.card ↥A * Nat.card ↥(fixV A)) :
    (∃ S : Subgroup (MulAut V), IsSylowTwoOf S L₁ ∧ S ≤ A) ∨
      (∃ S : Subgroup (MulAut V), IsSylowTwoOf S L₂ ∧ S ≤ A) := by
  obtain ⟨A₁, A₂, h₁, h₂, hAeq, hA₁, hA₂⟩ := pairModel_offender_sub hM hK₁ hK₂ hA hA2 hge
  have hsyl : ∀ {K : Type} [Field K] [Finite K] {m : ℕ} {L B : Subgroup (MulAut V)},
      Nat.card K = 2 ^ m → 1 ≤ m → Nat.card ↥L = Nat.card ↥(StatedSL 2 K) → B ≤ L →
        Nat.card ↥B = Nat.card K → IsSylowTwoOf B L := by
    intro K _ _ m L B hK hm hL hBL hB
    have hodd : Odd (Nat.card K ^ 2 - 1) := by
      have hev : Even (Nat.card K ^ 2) := by
        rw [hK, ← pow_mul]
        exact (Nat.even_pow' (by omega)).mpr even_two
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ Nat.card_pos) hev odd_one
    refine isSylowTwoOf_of_card hBL (k := m) (m := Nat.card K ^ 2 - 1) (by rw [hB, hK]) ?_ hodd
    rw [hL, card_statedSL_two, hK]
  by_cases hb₁ : A₁ = ⊥
  · have hb₂ : A₂ ≠ ⊥ := fun hb₂ => hA0 (by rw [hAeq, hb₁, hb₂, sup_bot_eq])
    refine Or.inr ⟨A₂, hsyl hK₂ hm₂ hL₂ h₂ (hA₂.resolve_left hb₂), ?_⟩
    rw [hAeq]
    exact le_sup_right
  · refine Or.inl ⟨A₁, hsyl hK₁ hm₁ hL₁ h₁ (hA₁.resolve_left hb₁), ?_⟩
    rw [hAeq]
    exact le_sup_left

end Pair

end CFSG.Quasithin.S146zW
