module

public import CFSG.Monster.Existence.TwoPoint.OrbitEquation
public import CFSG.Monster.Existence.TwoPoint.Shapes

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

@[expose] def classIndex : Fin 9 → Fin 9 := ![0, 1, 2, 6, 7, 3, 4, 8, 5]

theorem classIndex_injective : Function.Injective classIndex := by
  decide

theorem classIndex_surjective : Function.Surjective classIndex := by
  decide

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem orderOf_mul_of_nineClass (hG : GMSF1Type d₀ a z₀) {y : G} :
    ∀ i : Fin 9, nineClass a z₀ (classIndex i) y → orderOf (a * y) = suborbitClassOrder i := by
  have ha : orderOf a = 2 := hG.1.1
  have hz : orderOf z₀ = 2 := hG.2.1
  intro i hi
  fin_cases i
  · have : y = a := nineClass_zero.1 hi
    rw [this, orderOf_eq_one_iff.2 (mul_self_of_isConj ha (IsConj.refl a))]
    rfl
  · exact orderOf_mul_of_mem_tableVIISet ha hz ((nineClass_even 0).1 hi)
  · exact orderOf_mul_of_mem_tableVIISet ha hz ((nineClass_even 1).1 hi)
  · exact orderOf_mul_of_oddNbrType ((nineClass_odd 0).1 hi).1 ((nineClass_odd 0).1 hi).2
  · exact orderOf_mul_of_oddNbrType ((nineClass_odd 1).1 hi).1 ((nineClass_odd 1).1 hi).2
  · exact orderOf_mul_of_mem_tableVIISet ha hz ((nineClass_even 2).1 hi)
  · exact orderOf_mul_of_mem_tableVIISet ha hz ((nineClass_even 3).1 hi)
  · exact orderOf_mul_of_oddNbrType ((nineClass_odd 2).1 hi).1 ((nineClass_odd 2).1 hi).2
  · exact orderOf_mul_of_mem_tableVIISet ha hz ((nineClass_even 4).1 hi)

omit [Finite G] in
theorem isConj_of_nineClass {y : G} : ∀ {j : Fin 9}, nineClass a z₀ j y → IsConj a y := by
  intro j hj
  rcases nineClass_cases j with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [nineClass_zero.1 hj]
  · exact isConj_of_mem_tableVIISet ((nineClass_even k).1 hj)
  · exact ((nineClass_odd k).1 hj).1.1

theorem isTwoAGraphData_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hex : OddExhaustive a z₀) (hsep : OddTypesSeparated a z₀) (b : Fin 9 → G)
    (hb : ∀ j, nineClass a z₀ j (b j))
    (hshape : ∀ i, TwoPointShape (cent2 a (b (classIndex i))) i)
    (hiii : ∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (a * b (classIndex 3)) →
      (∃ γ, IsConj a γ ∧ IsConj (α * γ) (a * b (classIndex 3)) ∧ IsConj a (β * γ)) ∧
      (∀ γ γ', IsConj a γ → IsConj (α * γ) (a * b (classIndex 3)) → IsConj a (β * γ) →
        IsConj a γ' → IsConj (α * γ') (a * b (classIndex 3)) → IsConj a (β * γ') →
        ∃ g ∈ cent2 α β, g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj a γ → IsConj (α * γ) (a * b (classIndex 3)) → IsConj a (β * γ) →
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent γ) .PSp 4 2 1)
    (hiv : ∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (a * b (classIndex 6)) →
      α ≠ β ∧ ¬ IsConj a (α * β) ∧
        ∃! γ, IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (γ * β))
    (hv : ∀ α β : G, IsConj a α → IsConj a β → IsConj (α * β) (a * b (classIndex 3)) →
      (∃ D : Set ↥(cent2 α β), CFSG.Blueprint.Fischer.Pair ↥(cent2 α β) D ∧
        {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} =
          Subtype.val '' D ∧
        ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(cent2 α β))) =
          2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
      Set.ncard {γ | IsConj a γ ∧ IsConj a (α * γ) ∧ IsConj a (β * γ)} = 31671)
    (h4a : ∃ s₁ s₂ : Set G, IsTriangle a s₁ ∧ IsTriangle a s₂ ∧ (∀ g : G, conjSet g s₁ ≠ s₂) ∧
      ∀ s, IsTriangle a s → ∃ g : G, conjSet g s = s₁ ∨ conjSet g s = s₂)
    (h4b : ∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      {s | IsShortTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 1 ∧
      {s | IsLongTriangle a s ∧ α ∈ s ∧ β ∈ s}.ncard = 3968055)
    (h4c : ∀ s, IsLongTriangle a s →
      CFSG.Blueprint.LieModel (pointStab s ⧸ CFSG.pCore 2 (pointStab s)) .PSU 6 2 1 ∧
      HasLayeredTwoShape (pointStab s) 3 20 fun X _ => CFSG.Blueprint.LieModel X .PSU 6 2 1)
    (h4d : ∀ α β : G, IsConj a α → IsConj a β → IsConj a (α * β) →
      ∃ γ δ : G, IsLongTriangle a {α, β, γ} ∧ IsConj a δ ∧
        IsConj (α * δ) (a * b (classIndex 3)) ∧ IsConj (β * δ) (a * b (classIndex 3)) ∧
        (cent2 α β ⊓ cent γ) ⊔ (cent2 α β ⊓ cent δ) = cent2 α β ∧
        CFSG.Blueprint.LieModel ↥(cent2 α β ⊓ cent δ) .PSp 4 2 1) :
    IsTwoAGraphData a z₀ := by
  have hx2 : a * a = 1 := mul_self_of_isConj hG.1.1 (IsConj.refl a)
  set c : Fin 9 → G := fun i => a * b (classIndex i) with hc
  have hcover : ∀ α β : G, IsConj a α → IsConj a β → ∃ i, IsConj (α * β) (c i) := by
    intro α β hα hβ
    obtain ⟨g, rfl⟩ := isConj_iff.1 hα
    set β' := g⁻¹ * β * g with hβ'
    have hβ'A : IsConj a β' := hβ.trans (isConj_iff.2 ⟨g⁻¹, by rw [hβ']; group⟩)
    obtain ⟨j, hj⟩ := nineClass_cover I hG hex hβ'A
    obtain ⟨i, rfl⟩ := classIndex_surjective j
    obtain ⟨h, hh, hhb⟩ := nineClass_transitive I hG (hb (classIndex i)) hj
    refine ⟨i, isConj_iff.2 ⟨(g * h)⁻¹, ?_⟩⟩
    have hha : h * a * h⁻¹ = a := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hh, mul_inv_cancel_right]
    calc (g * h)⁻¹ * (g * a * g⁻¹ * β) * (g * h)⁻¹⁻¹
        = h⁻¹ * (a * β') * h := by rw [hβ']; group
      _ = h⁻¹ * ((h * a * h⁻¹) * (h * b (classIndex i) * h⁻¹)) * h := by rw [hha, hhb]
      _ = c i := by rw [hc]; group
  refine ⟨fun α β β' hα hβ hβ' h => three_i I hG hex hsep hα hβ hβ' h, c, ?_, ?_, ?_, ?_, ?_,
    hcover, ?_, ?_, hiii, hiv, hv, h4a, h4b, h4c, h4d⟩
  ·
    intro i j hij
    obtain ⟨g, hg, hgb⟩ := three_i I hG hex hsep (IsConj.refl a) (isConj_of_nineClass (hb _))
      (isConj_of_nineClass (hb _)) hij
    have h1 := nineClass_conj hg _ (hb (classIndex i))
    rw [hgb] at h1
    exact classIndex_injective (nineClass_unique I hG h1 (hb (classIndex j)))
  ·
    show a * b (classIndex 0) = 1
    have : b (classIndex 0) = a := nineClass_zero.1 (hb 0)
    rw [this, hx2]
  · exact ((nineClass_even 0).1 (hb (classIndex 1))).2
  · exact ((nineClass_even 1).1 (hb (classIndex 2))).2
  · exact fun i => orderOf_mul_of_nineClass hG i (hb (classIndex i))
  · exact fun i => ⟨a, b (classIndex i), IsConj.refl a, isConj_of_nineClass (hb _),
      IsConj.refl _⟩
  · intro α β i hα hβ h
    exact twoPointShape_of_isConj I hG hex hsep hα hβ (isConj_of_nineClass (hb _)) h (hshape i)

end CFSG.Monster.Existence
