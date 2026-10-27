module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1Pair
public import CFSG.Quasithin.Vol2.Ch12Sec1H9Lin

public section

namespace CFSG.Quasithin.H13

open Matrix
open scoped Matrix

namespace FF3

@[expose] def nMap (g : SpecialLinearGroup (Fin 3) (ZMod 2)) :
    (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) where
  toFun x := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x + x
  map_zero' := by rw [mulVec_zero, add_zero]
  map_add' x y := by
    rw [mulVec_add]
    abel

theorem nMap_apply (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    nMap g x = (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x + x :=
  rfl

theorem nMap_eq_zero_iff (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (x : Fin 3 → ZMod 2) :
    nMap g x = 0 ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x = x := by
  rw [nMap_apply]
  constructor
  · exact VecStab.eq_of_add_eq_zero
  · intro h
    rw [h, VecStab.add_self]

theorem nMap_nMap {g : SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g * g = 1)
    (x : Fin 3 → ZMod 2) : nMap g (nMap g x) = 0 := by
  have h1 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x) =
      x := by
    rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hg, Matrix.SpecialLinearGroup.coe_one,
      one_mulVec]
  rw [nMap_apply, nMap_apply, mulVec_add, h1]
  set y := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x
  have h2 := VecStab.add_self y
  have h3 := VecStab.add_self x
  calc x + y + (y + x) = (x + x) + (y + y) := by abel
    _ = 0 := by rw [h2, h3, add_zero]

theorem card_vec3 : Nat.card (Fin 3 → ZMod 2) = 8 := by
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  rfl

theorem card_range_le_two {g : SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g * g = 1) :
    Nat.card (nMap g).range ≤ 2 := by
  have h1 := AddSubgroup.card_ker_mul_card_range (nMap g)
  rw [card_vec3] at h1
  have hle : (nMap g).range ≤ (nMap g).ker := by
    rintro _ ⟨x, rfl⟩
    exact nMap_nMap hg x
  have h2 := AddSubgroup.card_le_of_le hle
  by_contra h3
  push Not at h3
  have h4 : 3 * 3 ≤ Nat.card (nMap g).ker * Nat.card (nMap g).range :=
    Nat.mul_le_mul (h3.trans_le h2) h3
  omega

theorem eq_of_mem_range {g : SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g * g = 1)
    {u w : Fin 3 → ZMod 2} (hu : u ∈ (nMap g).range) (hw : w ∈ (nMap g).range) (hu0 : u ≠ 0)
    (hw0 : w ≠ 0) : u = w := by
  classical
  by_contra hne
  have h1 := card_range_le_two hg
  have h2 : ({0, u, w} : Finset (Fin 3 → ZMod 2)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp [Ne.symm hu0, Ne.symm hw0]
  have h3 : ({0, u, w} : Finset (Fin 3 → ZMod 2)) ⊆ ((nMap g).range : Set _).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | rfl | rfl
    · exact (nMap g).range.zero_mem
    · exact hu
    · exact hw
  have h4 := Finset.card_le_card h3
  rw [Set.toFinset_card, h2, ← Nat.card_eq_fintype_card] at h4
  have : (Nat.card ((nMap g).range : Set (Fin 3 → ZMod 2))) = Nat.card (nMap g).range := rfl
  omega

theorem comp_eq_zero {g h : SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g * g = 1)
    (hh : h * h = 1) (hgh : g * h = h * g) (x : Fin 3 → ZMod 2) : nMap g (nMap h x) = 0 := by
  have hcomm : ∀ y, nMap g (nMap h y) = nMap h (nMap g y) := by
    intro y
    simp only [nMap_apply, mulVec_add, mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hgh]
    abel
  by_contra hne
  have hu'0 : nMap h x ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
  by_cases h0 : nMap g x = 0
  · exact hne (by rw [hcomm, h0, map_zero])
  · have h1 : nMap g x = nMap g (nMap h x) := eq_of_mem_range hg ⟨x, rfl⟩ ⟨_, rfl⟩ h0 hne
    have h2 : nMap g (nMap h x) = nMap h x :=
      eq_of_mem_range hh ⟨nMap g x, (hcomm x).symm⟩ ⟨x, rfl⟩ hne hu'0
    apply hne
    calc nMap g (nMap h x) = nMap g (nMap g (nMap h x)) := by conv_rhs => rw [h2]
      _ = nMap g (nMap g x) := by rw [← h1]
      _ = 0 := nMap_nMap hg x

theorem dot_mulVec (g : SpecialLinearGroup (Fin 3) (ZMod 2)) (x η : Fin 3 → ZMod 2) :
    η ⬝ᵥ ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x) =
      ((g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ η) ⬝ᵥ x := by
  rw [dotProduct_mulVec, mulVec_transpose]

variable (B : Subgroup (SpecialLinearGroup (Fin 3) (ZMod 2)))

@[expose] def fixS : AddSubgroup (Fin 3 → ZMod 2) where
  carrier := {ξ | ∀ g ∈ B, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ξ = ξ}
  add_mem' {x y} hx hy g hg := by rw [mulVec_add, hx g hg, hy g hg]
  zero_mem' g _ := mulVec_zero _
  neg_mem' {x} hx g hg := by rw [mulVec_neg, hx g hg]

@[expose] def fixT : AddSubgroup (Fin 3 → ZMod 2) where
  carrier := {η | ∀ g ∈ B, (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ η = η}
  add_mem' {x y} hx hy g hg := by rw [mulVec_add, hx g hg, hy g hg]
  zero_mem' g _ := mulVec_zero _
  neg_mem' {x} hx g hg := by rw [mulVec_neg, hx g hg]

variable {B}

theorem exists_ne (hB1 : B ≠ ⊥) : ∃ g ∈ B, g ≠ 1 := by
  by_contra h
  push Not at h
  exact hB1 (eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr (h g hg))

theorem fixS_ne_top (hB1 : B ≠ ⊥) : fixS B ≠ ⊤ := by
  obtain ⟨g, hg, hg1⟩ := exists_ne hB1
  intro h
  apply hg1
  refine PairStab.eq_of_mulVec_eq fun ξ => ?_
  have h1 : ξ ∈ fixS B := h ▸ AddSubgroup.mem_top ξ
  rw [h1 g hg, Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem card_mul_card_fixT_le (h4 : Nat.card (fixS B) = 4) :
    Nat.card B * Nat.card (fixT B) ≤ 8 := by
  classical
  have hidx : (fixS B).index = 2 := by
    have h1 := (fixS B).card_mul_index
    rw [h4, card_vec3] at h1
    omega
  obtain ⟨x₁, hx₁⟩ := AddSubgroup.index_eq_two_iff.mp hidx
  have hx₁S : x₁ ∉ fixS B := by
    have h := xor_iff_iff_not.mp (hx₁ 0)
    rw [zero_add] at h
    exact fun hx => (h.mp hx) (fixS B).zero_mem
  have hcases : ∀ x, x ∈ fixS B ∨ x + x₁ ∈ fixS B := by
    intro x
    rcases (hx₁ x).or with h | h
    · exact Or.inr h
    · exact Or.inl h
  let Φ : ↥B → {y : Fin 3 → ZMod 2 // ∀ η ∈ fixT B, η ⬝ᵥ y = 0} := fun g =>
    ⟨nMap g x₁, fun η hη => by
      rw [nMap_apply, dotProduct_add, dot_mulVec, hη g g.2]
      exact CharTwo.add_self_eq_zero _⟩
  have key : ∀ g ∈ B, ∀ h ∈ B, nMap g x₁ = nMap h x₁ → g = h := by
    intro g hg h hh h1
    have h2 : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x₁ =
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x₁ := by
      rw [nMap_apply, nMap_apply] at h1
      exact add_right_cancel h1
    refine PairStab.eq_of_mulVec_eq fun ξ => ?_
    rcases hcases ξ with h3 | h3
    · rw [h3 g hg, h3 h hh]
    · have e : ∀ k ∈ B, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ ξ =
          (ξ + x₁) + (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ x₁ := by
        intro k hk
        have h4 := h3 k hk
        rw [mulVec_add] at h4
        rw [← h4, add_assoc, VecStab.add_self, add_zero]
      rw [e g hg, e h hh, h2]
  have hΦ : Function.Injective Φ := fun g h hgh =>
    Subtype.ext (key g g.2 h h.2 (congrArg Subtype.val hgh))
  have h1 := Nat.card_le_card_of_injective Φ hΦ
  have h2 := H9Coord.card_mul_card_orth (fixT B)
  calc Nat.card B * Nat.card (fixT B) ≤
        Nat.card {y : Fin 3 → ZMod 2 // ∀ η ∈ fixT B, η ⬝ᵥ y = 0} * Nat.card (fixT B) :=
      Nat.mul_le_mul_right _ h1
    _ = 8 := by rw [mul_comm, h2]; rfl

section Elem

variable (hB2 : ∀ g ∈ B, g * g = 1) (hBc : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g)
include hB2 hBc

theorem nMap_mem_fixS {g : SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g ∈ B)
    (x : Fin 3 → ZMod 2) : nMap g x ∈ fixS B := fun h hh =>
  (nMap_eq_zero_iff h _).mp (comp_eq_zero (hB2 h hh) (hB2 g hg) (hBc h hh g hg) x)

theorem fixS_ne_bot (hB1 : B ≠ ⊥) : fixS B ≠ ⊥ := by
  obtain ⟨g, hg, hg1⟩ := exists_ne hB1
  intro h
  apply hg1
  refine PairStab.eq_of_mulVec_eq fun ξ => ?_
  have h1 : nMap g ξ ∈ (⊥ : AddSubgroup (Fin 3 → ZMod 2)) := h ▸ nMap_mem_fixS hB2 hBc hg ξ
  rw [AddSubgroup.mem_bot, nMap_eq_zero_iff] at h1
  rw [h1, Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem card_fixS (hB1 : B ≠ ⊥) : Nat.card (fixS B) = 2 ∨ Nat.card (fixS B) = 4 := by
  have hdvd : Nat.card (fixS B) ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = Nat.card (Fin 3 → ZMod 2) from card_vec3.symm]
    exact AddSubgroup.card_addSubgroup_dvd_card _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h1 : Nat.card (fixS B) ≠ 1 := fun h =>
    fixS_ne_bot hB2 hBc hB1 (AddSubgroup.eq_bot_of_card_eq _ h)
  have h8 : Nat.card (fixS B) ≠ 8 := fun h =>
    fixS_ne_top hB1 (AddSubgroup.eq_top_of_card_eq _ (h.trans card_vec3.symm))
  interval_cases k
  · exact absurd hk' (by simpa using h1)
  · exact Or.inl hk'
  · exact Or.inr hk'
  · exact absurd hk' (by simpa using h8)

end Elem

theorem slGraphAut_eq_transpose {g : SpecialLinearGroup (Fin 3) (ZMod 2)} (hg : g * g = 1) :
    (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 (ZMod 2) g :
      Matrix (Fin 3) (Fin 3) (ZMod 2)) = (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    inv_eq_of_mul_eq_one_right hg]

theorem card_sl3 : Nat.card (SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), Nat.card_zmod]
  decide

theorem card_le_eight (hB2 : ∀ g ∈ B, g * g = 1) : Nat.card B ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 B := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, pow_two]
    exact hB2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have h1 := Subgroup.card_subgroup_dvd_card B
  rw [card_sl3, hk] at h1
  have h2 : k ≤ 3 := by
    by_contra h
    push Not at h
    have h3 : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 h).trans h1
    norm_num at h3
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h2
    _ = 8 := by norm_num

theorem card_mul_card_mul_card_le (hB2 : ∀ g ∈ B, g * g = 1)
    (hBc : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g) (hB1 : B ≠ ⊥) :
    Nat.card B * Nat.card (fixS B) * Nat.card (fixT B) ≤ 32 ∧ 2 ≤ Nat.card (fixS B) ∧
      2 ≤ Nat.card (fixT B) := by
  set δ := (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 (ZMod 2)).toMonoidHom
  set B' := B.map δ with hB'
  have hδB : ∀ g ∈ B, (δ g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (g : Matrix _ _ _)ᵀ :=
    fun g hg => slGraphAut_eq_transpose (hB2 g hg)
  have hB2' : ∀ g ∈ B', g * g = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, hB2 g hg, map_one]
  have hBc' : ∀ g ∈ B', ∀ h ∈ B', g * h = h * g := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, hBc g hg h hh]
  have hB1' : B' ≠ ⊥ := by
    intro h
    apply hB1
    rw [hB', Subgroup.map_eq_bot_iff_of_injective _ (MulEquiv.injective _)] at h
    exact h
  have hS' : fixS B' = fixT B := by
    ext ξ
    constructor
    · intro h g hg
      rw [← hδB g hg]
      exact h _ ⟨g, hg, rfl⟩
    · rintro h _ ⟨g, hg, rfl⟩
      rw [hδB g hg]
      exact h g hg
  have hT' : fixT B' = fixS B := by
    ext ξ
    constructor
    · intro h g hg
      have := h _ ⟨g, hg, rfl⟩
      rwa [hδB g hg, transpose_transpose] at this
    · rintro h _ ⟨g, hg, rfl⟩
      rw [hδB g hg, transpose_transpose]
      exact h g hg
  have hcard' : Nat.card B' = Nat.card B :=
    Nat.card_congr (B.equivMapOfInjective δ (MulEquiv.injective _)).toEquiv.symm
  have hS := card_fixS hB2 hBc hB1
  have hT := card_fixS hB2' hBc' hB1'
  rw [hS'] at hT
  refine ⟨?_, by rcases hS with h | h <;> omega, by rcases hT with h | h <;> omega⟩
  rcases hS with hS | hS
  · rcases hT with hT | hT
    · rw [hS, hT]
      have := card_le_eight hB2
      omega
    · have h1 := card_mul_card_fixT_le (B := B') (by rw [hS']; exact hT)
      rw [hcard', hT'] at h1
      rw [hT]
      calc Nat.card B * Nat.card (fixS B) * 4 ≤ 8 * 4 := Nat.mul_le_mul_right _ h1
        _ = 32 := by norm_num
  · have h1 := card_mul_card_fixT_le hS
    rw [hS]
    calc Nat.card B * 4 * Nat.card (fixT B) = 4 * (Nat.card B * Nat.card (fixT B)) := by ring
      _ ≤ 4 * 8 := Nat.mul_le_mul_left _ h1
      _ = 32 := by norm_num

end FF3

end CFSG.Quasithin.H13
