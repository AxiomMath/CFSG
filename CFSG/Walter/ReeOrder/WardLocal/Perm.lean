module

public import CFSG.Walter.ReeOrder.Ward.Columns4

public section

open scoped BigOperators Classical

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.TwoRankLowerBound.Helpers CFSG.DirectProduct

section Perm

variable {W I : Type} [Group W] [Fintype W] [MulAction W I] [Fintype I]

theorem fixedPointCount_eq_one_add [Nonempty I] [MulAction.IsPretransitive W I]
    {ξ : W → ℂ} (hξ : ξ ∈ BlocksIrr W) (hξ1 : ξ ≠ 1) (hdeg : deg ξ + 1 = Nat.card I)
    (hpair : BlocksInnerProduct (fixedPointCount W I) ξ = 1) :
    fixedPointCount W I = 1 + ξ := by
  let data : FiniteComplexRepresentation W :=
    { vector := I → ℂ, representation := permutationRepresentation W I }
  obtain ⟨size, summand, hirr, hsum⟩ :=
    finiteComplexRepresentation_exists_irreducible_character_sum data
  let ψ : Fin size → W → ℂ := fun k => (summand k).character
  have hπ : ∀ w, fixedPointCount W I w = ∑ k, ψ k w := fun w => by
    rw [← hsum w]; exact (permutationRepresentation_character w).symm
  have hirr' : ∀ k, ψ k ∈ BlocksIrr W := fun k => by
    rw [blocksIrr_eq_irreducible_characters]; exact ⟨summand k, hirr k, rfl⟩
  have hip : ∀ χ ∈ BlocksIrr W, BlocksInnerProduct (fixedPointCount W I) χ =
      ((Finset.univ.filter fun k => ψ k = χ).card : ℂ) := by
    intro χ hχ
    have : BlocksInnerProduct (fixedPointCount W I) χ = ∑ k, BlocksInnerProduct (ψ k) χ := by
      simp only [BlocksInnerProduct, hπ, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [this, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(irreducible_character_basis W).1 _ (hirr' k) _ hχ]
    split_ifs <;> simp
  have horb : Nat.card (MulAction.orbitRel.Quotient W I) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨Quotient.mk _ (Classical.arbitrary I)⟩⟩
    obtain ⟨i, rfl⟩ := Quotient.exists_rep x
    obtain ⟨j, rfl⟩ := Quotient.exists_rep y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W j i
    exact Quotient.sound ⟨g, hg⟩
  have hA : (Finset.univ.filter fun k => ψ k = 1).card = 1 := by
    have h := hip 1 (one_mem_blocksIrr W)
    rw [blocksInnerProduct_fixedPointCount_one, horb] at h
    exact_mod_cast h.symm
  have hB : (Finset.univ.filter fun k => ψ k = ξ).card = 1 := by
    have h := hip ξ hξ
    rw [hpair] at h
    exact_mod_cast h.symm
  have hdegsum : ∑ k, deg (ψ k) = Nat.card I := by
    have h := hπ 1
    rw [fixedPointCount, MulAction.fixedBy_one_eq_univ, Nat.card_univ] at h
    have : ((∑ k, deg (ψ k) : ℤ) : ℂ) = ((Nat.card I : ℤ) : ℂ) := by
      push_cast
      rw [h]
      exact Finset.sum_congr rfl fun k _ => deg_eq (hirr' k)
    exact_mod_cast this
  have hdeg1 : deg (1 : W → ℂ) = 1 := by
    have h := deg_eq (one_mem_blocksIrr W)
    have : ((deg (1 : W → ℂ) : ℤ) : ℂ) = ((1 : ℤ) : ℂ) := by rw [h]; simp
    exact_mod_cast this
  have hdich : ∀ k, ψ k = 1 ∨ ψ k = ξ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨k₀, hk₁, hkξ⟩ := hcon
    set A := Finset.univ.filter fun k => ψ k = 1
    set B := Finset.univ.filter fun k => ψ k = ξ
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2
      exact hξ1 (h2.symm.trans h1)
    have hk₀ : k₀ ∉ A ∪ B := by
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, A, B]
      tauto
    have hsA : ∑ k ∈ A, deg (ψ k) = 1 := by
      rw [Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
        hA, hdeg1]
      simp
    have hsB : ∑ k ∈ B, deg (ψ k) = deg ξ := by
      rw [Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
        hB]
      simp
    have hle : ∑ k ∈ insert k₀ (A ∪ B), deg (ψ k) ≤ ∑ k, deg (ψ k) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ => (deg_pos (hirr' k)).le)
    rw [Finset.sum_insert hk₀, Finset.sum_union hAB, hsA, hsB, hdegsum, ← hdeg] at hle
    have := deg_pos (hirr' k₀)
    omega
  funext w
  rw [hπ w, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => ψ k = 1)]
  have h1 : ∑ k ∈ Finset.univ.filter (fun k => ψ k = 1), ψ k w = 1 := by
    rw [Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const,
      hA]
    simp
  have hnot : Finset.univ.filter (fun k => ¬ ψ k = 1) = Finset.univ.filter (fun k => ψ k = ξ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hdich k with h | h
    · exact ⟨fun h' => absurd h h', fun h' => absurd (h'.symm.trans h) hξ1⟩
    · exact ⟨fun _ => h, fun h' h'' => hξ1 (h'.symm.trans h'')⟩
  rw [h1, hnot, Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2],
    Finset.sum_const, hB]
  simp

end Perm

section Quotient

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem smul_mk_eq_iff (H : Subgroup G) (g a : G) :
    g • (a : G ⧸ H) = a ↔ a⁻¹ * g * a ∈ H := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
  constructor <;> intro h
  · have := H.inv_mem h; simpa [mul_assoc] using this
  · have := H.inv_mem h; simpa [mul_assoc] using this

theorem sum_fixedPointCount_mul (H : Subgroup G) (f : G → ℂ)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) :
    ∑ g : G, fixedPointCount G (G ⧸ H) g * f g =
      (H.index : ℂ) * ∑ g ∈ Finset.univ.filter (· ∈ H), f g := by
  have hfix : ∀ g : G, fixedPointCount G (G ⧸ H) g =
      ∑ x : G ⧸ H, if g • x = x then (1 : ℂ) else 0 := by
    intro g
    rw [fixedPointCount, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.sum_boole]
    simp [MulAction.mem_fixedBy]
  simp_rw [hfix, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  have hx : ∀ x : G ⧸ H, ∑ g : G, (if g • x = x then f g else 0) =
      ∑ g ∈ Finset.univ.filter (· ∈ H), f g := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    simp_rw [smul_mk_eq_iff]
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun g => a⁻¹ * g * a) (fun g => a * g * a⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro g hg
      simpa using hg
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      simpa [mul_assoc] using hg
    · intro g _; group
    · intro g _; group
    · intro g _
      have := hf a (a⁻¹ * g * a)
      rw [show a * (a⁻¹ * g * a) * a⁻¹ = g by group] at this
      exact this
  rw [Finset.sum_congr rfl fun x _ => hx x, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← Subgroup.index]

theorem blocksInnerProduct_fixedPointCount (H : Subgroup G) (f : G → ℂ)
    (hf : ∀ g x : G, f (g * x * g⁻¹) = f x) (hreal : starRingEnd ℂ ∘ f = f) :
    BlocksInnerProduct (fixedPointCount G (G ⧸ H)) f =
      (Nat.card H : ℂ)⁻¹ * ∑ g ∈ Finset.univ.filter (· ∈ H), f g := by
  have hr : ∀ g, starRingEnd ℂ (f g) = f g := fun g => congrFun hreal g
  rw [BlocksInnerProduct]
  simp_rw [hr]
  rw [sum_fixedPointCount_mul H f hf, ← H.card_mul_index]
  have hi : (H.index : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
  push_cast
  field_simp

end Quotient

section Inverted

variable {G : Type} [Group G] [Fintype G]

omit [Fintype G] in
theorem conj_pow_of_mul_self {t : G} (ht : t * t = 1) (x : G) (n : ℕ) :
    t * x ^ n * t = (t * x * t) ^ n := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have := map_pow (MulAut.conj t) x n
  simp only [MulAut.conj_apply, ht'] at this
  exact this

theorem card_inverted_mul (H : Subgroup G) {t : G} (ht : t * t = 1)
    (htH : ∀ h ∈ H, t * h * t ∈ H) (hodd : Odd (Nat.card H)) :
    (Finset.univ.filter fun h : G => h ∈ H ∧ t * h * t = h⁻¹).card *
      Nat.card (H ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = Nat.card H := by
  set X := Finset.univ.filter fun h : G => h ∈ H ∧ t * h * t = h⁻¹ with hX
  set Hs := Finset.univ.filter fun h : G => h ∈ H with hHs
  set C' := (H ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) with hC'
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  set φ : G → G := fun h => h * t * h⁻¹ * t with hφ
  have htinv : ∀ h ∈ H, t * h⁻¹ * t ∈ H := fun h hh => htH _ (H.inv_mem hh)
  have hmaps : ∀ h ∈ Hs, φ h ∈ X := by
    intro h hh
    simp only [hHs, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and, hφ]
    refine ⟨?_, ?_⟩
    · have := H.mul_mem hh (htinv h hh)
      simpa [mul_assoc] using this
    · calc t * (h * t * h⁻¹ * t) * t = t * h * t * h⁻¹ * (t * t) := by group
        _ = t * h * t * h⁻¹ := by rw [ht, mul_one]
        _ = (h * t * h⁻¹ * t)⁻¹ := by
          simp only [mul_inv_rev, inv_inv, ht']
          group
  have hcard : Hs.card = ∑ x ∈ X, (Hs.filter fun h => φ h = x).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hHs_card : Hs.card = Nat.card H := by
    rw [hHs, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    simp [Fintype.card_subtype]
  have hfib : ∀ x ∈ X, (Hs.filter fun h => φ h = x).card = Nat.card C' := by
    intro x hx
    simp only [hX, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hxH, hxt⟩ := hx
    have hxo : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard H hxH)
    obtain ⟨s, hs⟩ := hxo
    set y := x ^ (s + 1) with hy
    have hyH : y ∈ H := H.pow_mem hxH _
    have hyy : y * y = x := by
      rw [hy, ← pow_add, show s + 1 + (s + 1) = orderOf x + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    have hyt : t * y * t = y⁻¹ := by
      rw [hy, conj_pow_of_mul_self ht, hxt, inv_pow]
    have hφy : φ y = x := by
      simp only [hφ]
      have : t * y⁻¹ * t = y := by
        calc t * y⁻¹ * t = (t * y * t)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, ht']; group
          _ = y := by rw [hyt, inv_inv]
      calc y * t * y⁻¹ * t = y * (t * y⁻¹ * t) := by group
        _ = x := by rw [this, hyy]
    have hfiber : (Hs.filter fun h => φ h = x) =
        (Finset.univ.filter fun c : G => c ∈ C').image (y * ·) := by
      ext h
      rw [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hh, hφh⟩
        rw [hHs, Finset.mem_filter] at hh
        refine ⟨y⁻¹ * h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subgroup.mem_inf.mpr
          ⟨H.mul_mem (H.inv_mem hyH) hh.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩⟩,
          by group⟩
        rw [← hφy] at hφh
        simp only [hφ] at hφh
        have h1 : h * t * h⁻¹ = y * t * y⁻¹ := by
          have := congrArg (· * t) hφh
          simpa [mul_assoc, ht] using this
        calc y⁻¹ * h * t = y⁻¹ * (h * t * h⁻¹) * h := by group
          _ = y⁻¹ * (y * t * y⁻¹) * h := by rw [h1]
          _ = t * (y⁻¹ * h) := by group
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨hcH, hct⟩ := Subgroup.mem_inf.mp (Finset.mem_filter.mp hc).2
        rw [Subgroup.mem_centralizer_singleton_iff] at hct
        refine ⟨by rw [hHs, Finset.mem_filter]; exact ⟨Finset.mem_univ _, H.mul_mem hyH hcH⟩, ?_⟩
        rw [← hφy]
        simp only [hφ]
        calc y * c * t * (y * c)⁻¹ * t = y * (c * t) * c⁻¹ * y⁻¹ * t := by group
          _ = y * (t * c) * c⁻¹ * y⁻¹ * t := by rw [hct]
          _ = y * t * y⁻¹ * t := by group
    rw [hfiber, Finset.card_image_of_injective _ (mul_right_injective y)]
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    simp [Fintype.card_subtype]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcard
  rw [← hcard, hHs_card]

end Inverted

end CFSG.Walter.WardLocal
