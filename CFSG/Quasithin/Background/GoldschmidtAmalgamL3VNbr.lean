module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Hyp

public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

theorem eq_or_eq_or_eq_of_index_three {X α : Type*} [Group X] (H : Subgroup X)
    (hH : H.index = 3) (f : X → α) (hf : ∀ x y, x⁻¹ * y ∈ H → f x = f y) {x₁ x₂ x₃ : X}
    (h12 : f x₁ ≠ f x₂) (h13 : f x₁ ≠ f x₃) (h23 : f x₂ ≠ f x₃) (x : X) :
    f x = f x₁ ∨ f x = f x₂ ∨ f x = f x₃ := by
  classical
  have hcard : Nat.card (X ⧸ H) = 3 := hH
  have hfin : Finite (X ⧸ H) := Nat.finite_of_card_ne_zero (by omega)
  let _ : Fintype (X ⧸ H) := Fintype.ofFinite _
  have hne : ∀ y y' : X, f y ≠ f y' → (y : X ⧸ H) ≠ (y' : X ⧸ H) := fun y y' hy he =>
    hy (hf y y' (QuotientGroup.eq.mp he))
  have hS : ({(x₁ : X ⧸ H), (x₂ : X ⧸ H), (x₃ : X ⧸ H)} : Finset (X ⧸ H)).card = 3 :=
    Finset.card_eq_three.mpr ⟨_, _, _, hne _ _ h12, hne _ _ h13, hne _ _ h23, rfl⟩
  have huniv : ({(x₁ : X ⧸ H), (x₂ : X ⧸ H), (x₃ : X ⧸ H)} : Finset (X ⧸ H)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hS, ← Nat.card_eq_fintype_card, hcard])
  have hx : (x : X ⧸ H) ∈ ({(x₁ : X ⧸ H), (x₂ : X ⧸ H), (x₃ : X ⧸ H)} : Finset (X ⧸ H)) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx
  · exact Or.inl (hf x x₁ (QuotientGroup.eq.mp hx))
  · exact Or.inr (Or.inl (hf x x₂ (QuotientGroup.eq.mp hx)))
  · exact Or.inr (Or.inr (hf x x₃ (QuotientGroup.eq.mp hx)))

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem eq_or_eq_of_adj_γ₀ {a₁ a₂ a₃ a : CosetGeom (A ⊔ B) A B}
    (h₁ : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) a₁)
    (h₂ : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) a₂)
    (h₃ : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) a₃)
    (h₄ : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) a)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) : a = a₁ ∨ a = a₂ ∨ a = a₃ := by
  have hadj : (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) (γ₁ (A ⊔ B) A B) :=
    adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)
  have hlift : ∀ {a' : CosetGeom (A ⊔ B) A B},
      (graph (A ⊔ B) A B).Adj (γ₀ (A ⊔ B) A B) a' → ∃ κ : ↥A,
        (⟨(κ : D), (le_sup_left : A ≤ A ⊔ B) κ.2⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B = a' := by
    intro a' ha'
    obtain ⟨k, hk0, hk1⟩ := exists_stab_smul_eq hadj ha'
    have hkA : (k : D) ∈ A := by
      have := mem_stab_of_smul_eq hk0
      rwa [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at this
    exact ⟨⟨(k : D), hkA⟩, hk1⟩
  obtain ⟨κ₁, e₁⟩ := hlift h₁
  obtain ⟨κ₂, e₂⟩ := hlift h₂
  obtain ⟨κ₃, e₃⟩ := hlift h₃
  obtain ⟨κ, e⟩ := hlift h₄
  let f : ↥A → CosetGeom (A ⊔ B) A B := fun κ =>
    (⟨(κ : D), (le_sup_left : A ≤ A ⊔ B) κ.2⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B
  have hf : ∀ x y : ↥A, x⁻¹ * y ∈ (A ⊓ B).subgroupOf A → f x = f y := by
    intro x y hxy
    have hB : ((x⁻¹ * y : ↥A) : D) ∈ B := ((Subgroup.mem_subgroupOf.mp hxy)).2
    have h1 := smul_γ₁_of_mem (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) (le_sup_right : B ≤ A ⊔ B) hB
    have hyx : (⟨(y : D), (le_sup_left : A ≤ A ⊔ B) y.2⟩ : ↥(A ⊔ B)) =
        ⟨(x : D), (le_sup_left : A ≤ A ⊔ B) x.2⟩ *
          ⟨((x⁻¹ * y : ↥A) : D), (le_sup_right : B ≤ A ⊔ B) hB⟩ := by
      apply Subtype.ext
      simp
    show (⟨(x : D), _⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B = (⟨(y : D), _⟩ : ↥(A ⊔ B)) • γ₁ (A ⊔ B) A B
    rw [hyx, mul_smul, h1]
  have key := eq_or_eq_or_eq_of_index_three ((A ⊓ B).subgroupOf A) h.gold.relIndex_left f hf
    (x₁ := κ₁) (x₂ := κ₂) (x₃ := κ₃) (by
      intro hc
      apply h12
      rw [← e₁, ← e₂]
      exact hc) (by
      intro hc
      apply h13
      rw [← e₁, ← e₃]
      exact hc) (by
      intro hc
      apply h23
      rw [← e₂, ← e₃]
      exact hc) κ
  rw [← e, ← e₁, ← e₂, ← e₃]
  exact key

theorem eq_or_eq_of_adj_γ₁ {a₁ a₂ a₃ a : CosetGeom (A ⊔ B) A B}
    (h₁ : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) a₁)
    (h₂ : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) a₂)
    (h₃ : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) a₃)
    (h₄ : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) a)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) : a = a₁ ∨ a = a₂ ∨ a = a₃ := by
  have hadj : (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) (γ₀ (A ⊔ B) A B) :=
    (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm
  have hlift : ∀ {a' : CosetGeom (A ⊔ B) A B},
      (graph (A ⊔ B) A B).Adj (γ₁ (A ⊔ B) A B) a' → ∃ κ : ↥B,
        (⟨(κ : D), (le_sup_right : B ≤ A ⊔ B) κ.2⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B = a' := by
    intro a' ha'
    obtain ⟨k, hk0, hk1⟩ := exists_stab_smul_eq hadj ha'
    have hkB : (k : D) ∈ B := by
      have := mem_stab_of_smul_eq hk0
      rwa [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at this
    exact ⟨⟨(k : D), hkB⟩, hk1⟩
  obtain ⟨κ₁, e₁⟩ := hlift h₁
  obtain ⟨κ₂, e₂⟩ := hlift h₂
  obtain ⟨κ₃, e₃⟩ := hlift h₃
  obtain ⟨κ, e⟩ := hlift h₄
  let f : ↥B → CosetGeom (A ⊔ B) A B := fun κ =>
    (⟨(κ : D), (le_sup_right : B ≤ A ⊔ B) κ.2⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B
  have hf : ∀ x y : ↥B, x⁻¹ * y ∈ (A ⊓ B).subgroupOf B → f x = f y := by
    intro x y hxy
    have hA : ((x⁻¹ * y : ↥B) : D) ∈ A := ((Subgroup.mem_subgroupOf.mp hxy)).1
    have h1 := smul_γ₀_of_mem (G₀ := A ⊔ B) (G₁ := A) (G₂ := B) (le_sup_left : A ≤ A ⊔ B) hA
    have hyx : (⟨(y : D), (le_sup_right : B ≤ A ⊔ B) y.2⟩ : ↥(A ⊔ B)) =
        ⟨(x : D), (le_sup_right : B ≤ A ⊔ B) x.2⟩ *
          ⟨((x⁻¹ * y : ↥B) : D), (le_sup_left : A ≤ A ⊔ B) hA⟩ := by
      apply Subtype.ext
      simp
    show (⟨(x : D), _⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B = (⟨(y : D), _⟩ : ↥(A ⊔ B)) • γ₀ (A ⊔ B) A B
    rw [hyx, mul_smul, h1]
  have hH : ((A ⊓ B).subgroupOf B).index = 3 := h.gold.relIndex_right
  have key := eq_or_eq_or_eq_of_index_three ((A ⊓ B).subgroupOf B) hH f hf
    (x₁ := κ₁) (x₂ := κ₂) (x₃ := κ₃) (by
      intro hc
      apply h12
      rw [← e₁, ← e₂]
      exact hc) (by
      intro hc
      apply h13
      rw [← e₁, ← e₃]
      exact hc) (by
      intro hc
      apply h23
      rw [← e₂, ← e₃]
      exact hc) κ
  rw [← e, ← e₁, ← e₂, ← e₃]
  exact key

theorem eq_or_eq_of_adj {v a₁ a₂ a₃ a : CosetGeom (A ⊔ B) A B}
    (h₁ : (graph (A ⊔ B) A B).Adj v a₁) (h₂ : (graph (A ⊔ B) A B).Adj v a₂)
    (h₃ : (graph (A ⊔ B) A B).Adj v a₃) (h₄ : (graph (A ⊔ B) A B).Adj v a)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) : a = a₁ ∨ a = a₂ ∨ a = a₃ := by
  have hpull : ∀ (g : ↥(A ⊔ B)) {w : CosetGeom (A ⊔ B) A B},
      (graph (A ⊔ B) A B).Adj v w → (graph (A ⊔ B) A B).Adj (g⁻¹ • v) (g⁻¹ • w) := fun g w hw =>
    (smul_adj g⁻¹).mpr hw
  have hinj : ∀ (g : ↥(A ⊔ B)) {x y : CosetGeom (A ⊔ B) A B}, g⁻¹ • x ≠ g⁻¹ • y ↔ x ≠ y :=
    fun g x y => by simp
  cases hv : vtype v
  · obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    have hv' : g⁻¹ • v = γ₀ (A ⊔ B) A B := by rw [hg, inv_smul_smul]
    have key := h.eq_or_eq_of_adj_γ₀ (hv' ▸ hpull g h₁) (hv' ▸ hpull g h₂) (hv' ▸ hpull g h₃)
      (hv' ▸ hpull g h₄) ((hinj g).mpr h12) ((hinj g).mpr h13) ((hinj g).mpr h23)
    rcases key with e | e | e
    · exact Or.inl (smul_left_cancel _ e)
    · exact Or.inr (Or.inl (smul_left_cancel _ e))
    · exact Or.inr (Or.inr (smul_left_cancel _ e))
  · obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    have hv' : g⁻¹ • v = γ₁ (A ⊔ B) A B := by rw [hg, inv_smul_smul]
    have key := h.eq_or_eq_of_adj_γ₁ (hv' ▸ hpull g h₁) (hv' ▸ hpull g h₂) (hv' ▸ hpull g h₃)
      (hv' ▸ hpull g h₄) ((hinj g).mpr h12) ((hinj g).mpr h13) ((hinj g).mpr h23)
    rcases key with e | e | e
    · exact Or.inl (smul_left_cancel _ e)
    · exact Or.inr (Or.inl (smul_left_cancel _ e))
    · exact Or.inr (Or.inr (smul_left_cancel _ e))

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
