module

public import CFSG.Quasithin.Background.HM22RowT0
public import CFSG.Quasithin.Background.HM22RowAbs

public section

namespace CFSG.Quasithin.H.Mathieu.M22Row

open CFSG.Quasithin.H13.MatNCert CFSG.Quasithin.H.Mathieu.H12Cert Matrix

theorem mem_four_of_mem_closure {M : Type*} [Group M] {a b : M} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {x : M} (hx : x ∈ Subgroup.closure {a, b}) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have step : ∀ s ∈ ({a, b} : Set M), ∀ y : M, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (s * y = 1 ∨ s * y = a ∨ s * y = b ∨ s * y = a * b) := by
    rintro s (rfl | rfl) y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one _))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
    · exact Or.inr (Or.inr (Or.inl (mul_one _)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
  refine Subgroup.closure_induction_left (p := fun x _ => x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    (Or.inl rfl) (fun s hs y _ hy => step s hs y hy) (fun s hs y _ hy => ?_) hx
  rcases hs with rfl | rfl
  · rw [hai]
    exact step _ (Or.inl rfl) y hy
  · rw [hbi]
    exact step _ (Or.inr rfl) y hy

theorem isPGroup_closure_pair {M : Type*} [Group M] {a b : M} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) : IsPGroup 2 ↥(Subgroup.closure {a, b}) := by
  rintro ⟨x, hx⟩
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, pow_two]
  rcases mem_four_of_mem_closure ha hb hab hx with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact ha
  · exact hb
  · rw [mul_assoc, ← mul_assoc b, ← hab, mul_assoc, hb, mul_one, ha]

theorem inv_mulVec_mulVec (c : GL (Fin 12) (ZMod 2)) (u : Fin 12 → ZMod 2) :
    ((c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
      (((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u) = u := by
  rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]

theorem mulVec_conj (c t : GL (Fin 12) (ZMod 2)) (u : Fin 12 → ZMod 2) :
    ((c * t * c⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
        (((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u) =
      ((c : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
        (((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u) := by
  simp only [Units.val_mul, ← mulVec_mulVec]
  rw [inv_mulVec_mulVec]

theorem exists_conj_T0 {E : Subgroup ↥G} (hE : IsPGroup 2 E) :
    ∃ c : ↥G, ∀ x ∈ E, (c : GL (Fin 12) (ZMod 2))⁻¹ * x * c ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : Nat.card ↥(T0.subgroupOf G) = 2 ^ 7 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_G).toEquiv, card_T0]
    norm_num
  obtain ⟨c, hc⟩ := exists_conj_le hP (by rw [card_G]; norm_num) hE
  exact ⟨c, fun x hx => Subgroup.mem_subgroupOf.mp (hc x hx)⟩

theorem card_fix_le_of_inv {g : GL (Fin 12) (ZMod 2)}
    (hg : g ∈ G) (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card {u : Fin 12 → ZMod 2 //
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u} ≤ 256 := by
  have h2 : (⟨g, hg⟩ : ↥G) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
  obtain ⟨c, hc⟩ := exists_conj_T0 (isPGroup_closure_pair h2 h2 rfl)
  have ht := hc _ (Subgroup.subset_closure (Set.mem_insert _ _))
  rw [← card_fix_conj (c : GL (Fin 12) (ZMod 2)) g]
  have ht2 : ((c : GL (Fin 12) (ZMod 2))⁻¹ * g * c) * ((c : GL (Fin 12) (ZMod 2))⁻¹ * g * c) =
      1 := by
    calc ((c : GL (Fin 12) (ZMod 2))⁻¹ * g * c) * ((c : GL (Fin 12) (ZMod 2))⁻¹ * g * c) =
        (c : GL (Fin 12) (ZMod 2))⁻¹ * (g * g) * c := by group
      _ = 1 := by rw [hg2, mul_one, inv_mul_cancel]
  refine card_fix_le_of_mem_T0 ht ht2 fun h => hg1 ?_
  calc g = (c : GL (Fin 12) (ZMod 2)) * ((c : GL (Fin 12) (ZMod 2))⁻¹ * g * c) *
        (c : GL (Fin 12) (ZMod 2))⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem exists_fix_of_inv {g g' : GL (Fin 12) (ZMod 2)}
    (hg : g ∈ G) (hg' : g' ∈ G) (hg2 : g * g = 1) (hg'2 : g' * g' = 1) (hg1 : g ≠ 1)
    (hg'1 : g' ≠ 1) (hgg' : g * g' = g' * g) (hne : g ≠ g') :
    ∃ u : Fin 12 → ZMod 2,
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u = u ∧
        ((g' : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u ≠ u := by
  have h2 : (⟨g, hg⟩ : ↥G) * ⟨g, hg⟩ = 1 := Subtype.ext hg2
  have h2' : (⟨g', hg'⟩ : ↥G) * ⟨g', hg'⟩ = 1 := Subtype.ext hg'2
  have h3 : (⟨g, hg⟩ : ↥G) * ⟨g', hg'⟩ = ⟨g', hg'⟩ * ⟨g, hg⟩ := Subtype.ext hgg'
  obtain ⟨c, hc⟩ := exists_conj_T0 (isPGroup_closure_pair h2 h2' h3)
  set d : GL (Fin 12) (ZMod 2) := (c : GL (Fin 12) (ZMod 2)) with hd
  have ht := hc _ (Subgroup.subset_closure (Set.mem_insert _ _))
  have ht' := hc _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  change d⁻¹ * g * d ∈ T0 at ht
  change d⁻¹ * g' * d ∈ T0 at ht'
  have hconj : ∀ x : GL (Fin 12) (ZMod 2), x = d * (d⁻¹ * x * d) * d⁻¹ := fun x => by group
  have hinv2 : ∀ x : GL (Fin 12) (ZMod 2), x * x = 1 → (d⁻¹ * x * d) * (d⁻¹ * x * d) = 1 :=
    fun x hx => by
      calc (d⁻¹ * x * d) * (d⁻¹ * x * d) = d⁻¹ * (x * x) * d := by group
        _ = 1 := by rw [hx, mul_one, inv_mul_cancel]
  have hne1 : ∀ x : GL (Fin 12) (ZMod 2), x ≠ 1 → d⁻¹ * x * d ≠ 1 := fun x hx h => hx (by
    rw [hconj x, h, mul_one, mul_inv_cancel])
  obtain ⟨u, hu, hu'⟩ := exists_fix_of_mem_T0 ht ht' (hinv2 g hg2) (hinv2 g' hg'2) (hne1 g hg1)
    (hne1 g' hg'1) (fun h => hne (by rw [hconj g, h, ← hconj g']))
  refine ⟨((d : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ u, ?_, ?_⟩
  · conv_lhs => rw [hconj g]
    rw [mulVec_conj, hu]
  · conv_lhs => rw [hconj g']
    rw [mulVec_conj]
    intro h
    apply hu'
    have h4 := congrArg
      (fun t => ((d⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ t) h
    simpa only [inv_mulVec_mulVec] using h4

end CFSG.Quasithin.H.Mathieu.M22Row
