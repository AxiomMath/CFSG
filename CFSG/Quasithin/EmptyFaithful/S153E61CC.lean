module

public import CFSG.Quasithin.EmptyFaithful.S153E61CB

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E61C

section Abstract

variable {G : Type*} [Group G] {I P V N₁ N₂ P₁ P₂ : Subgroup G}

theorem twist_of_mem {x a : G} (h : x * a⁻¹ ∈ V) : ∃ v ∈ V, x = v * a :=
  ⟨x * a⁻¹, h, by group⟩

theorem conj_mem_twist (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂) {a m : G} (ha : a ∈ P₁) (hm : m ∈ N₂) :
    ∃ u ∈ V, m * a * m⁻¹ = u * a := by
  have ha' := ha
  rw [pd.cent₁] at ha'
  refine ⟨_, V.inv_mem (ha'.2.2 m hm), ?_⟩
  group

theorem comm_of_twist (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂) {va vb a b : G} (hva : va ∈ V)
    (hvb : vb ∈ V) (ha : a ∈ P) (hb : b ∈ P) (h : (va * a) * (vb * b) = (vb * b) * (va * a)) :
    a * b = b * a := by
  have c1 : a * vb = vb * a := (pd.V_central vb hvb a ha).symm
  have c2 : b * va = va * b := (pd.V_central va hva b hb).symm
  have c3 : va * vb = vb * va := pd.V_central va hva vb (pd.V_le_P hvb)
  have e1 : (va * a) * (vb * b) = (va * vb) * (a * b) := by
    calc (va * a) * (vb * b) = va * (a * vb) * b := by group
      _ = va * (vb * a) * b := by rw [c1]
      _ = (va * vb) * (a * b) := by group
  have e2 : (vb * b) * (va * a) = (va * vb) * (b * a) := by
    calc (vb * b) * (va * a) = vb * (b * va) * a := by group
      _ = vb * (va * b) * a := by rw [c2]
      _ = (vb * va) * (b * a) := by group
      _ = (va * vb) * (b * a) := by rw [c3]
  rw [e1, e2] at h
  exact mul_left_cancel h

theorem cross_comm (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂)
    (hT₁ : ∀ a ∈ P₁, a ∉ V → ∀ b ∈ P₁, b ∉ V → ∃ m ∈ N₁, m * a * m⁻¹ * b⁻¹ ∈ V)
    (hT₂ : ∀ a ∈ P₂, a ∉ V → ∀ b ∈ P₂, b ∉ V → ∃ m ∈ N₂, m * a * m⁻¹ * b⁻¹ ∈ V)
    {p₁ p₂ : G} (hp₁ : p₁ ∈ P₁) (hp₁V : p₁ ∉ V) (hp₂ : p₂ ∈ P₂) (hp₂V : p₂ ∉ V)
    (hcomm : p₁ * p₂ = p₂ * p₁) : ∀ a ∈ P₁, ∀ b ∈ P₂, a * b = b * a := by
  intro a ha b hb
  by_cases haV : a ∈ V
  · exact pd.V_central a haV b (pd.P₂_le_P hb)
  by_cases hbV : b ∈ V
  · exact (pd.V_central b hbV a (pd.P₁_le_P ha)).symm
  obtain ⟨m₁, hm₁, h₁⟩ := hT₁ p₁ hp₁ hp₁V a ha haV
  obtain ⟨m₂, hm₂, h₂⟩ := hT₂ p₂ hp₂ hp₂V b hb hbV
  obtain ⟨v₁, hv₁, ev₁⟩ := twist_of_mem h₁
  obtain ⟨v₂, hv₂, ev₂⟩ := twist_of_mem h₂
  obtain ⟨u₂, hu₂, e₂⟩ := conj_mem_twist pd hp₁ hm₂
  obtain ⟨u₁, hu₁, e₁⟩ := conj_mem_twist pd.symm hb hm₁
  have hm₁I : m₁ ∈ I := pd.N₁_le_I hm₁
  have hA : (m₁ * m₂) * p₁ * (m₁ * m₂)⁻¹ = (m₁ * u₂ * m₁⁻¹ * v₁) * a := by
    calc (m₁ * m₂) * p₁ * (m₁ * m₂)⁻¹ = m₁ * (m₂ * p₁ * m₂⁻¹) * m₁⁻¹ := by group
      _ = m₁ * (u₂ * p₁) * m₁⁻¹ := by rw [e₂]
      _ = (m₁ * u₂ * m₁⁻¹) * (m₁ * p₁ * m₁⁻¹) := by group
      _ = (m₁ * u₂ * m₁⁻¹) * (v₁ * a) := by rw [ev₁]
      _ = (m₁ * u₂ * m₁⁻¹ * v₁) * a := by group
  have hB : (m₁ * m₂) * p₂ * (m₁ * m₂)⁻¹ = ((m₁ * v₂ * m₁⁻¹) * u₁) * b := by
    calc (m₁ * m₂) * p₂ * (m₁ * m₂)⁻¹ = m₁ * (m₂ * p₂ * m₂⁻¹) * m₁⁻¹ := by group
      _ = m₁ * (v₂ * b) * m₁⁻¹ := by rw [ev₂]
      _ = (m₁ * v₂ * m₁⁻¹) * (m₁ * b * m₁⁻¹) := by group
      _ = (m₁ * v₂ * m₁⁻¹) * (u₁ * b) := by rw [e₁]
      _ = ((m₁ * v₂ * m₁⁻¹) * u₁) * b := by group
  have hconj : ((m₁ * m₂) * p₁ * (m₁ * m₂)⁻¹) * ((m₁ * m₂) * p₂ * (m₁ * m₂)⁻¹) =
      ((m₁ * m₂) * p₂ * (m₁ * m₂)⁻¹) * ((m₁ * m₂) * p₁ * (m₁ * m₂)⁻¹) := by
    calc ((m₁ * m₂) * p₁ * (m₁ * m₂)⁻¹) * ((m₁ * m₂) * p₂ * (m₁ * m₂)⁻¹)
        = (m₁ * m₂) * (p₁ * p₂) * (m₁ * m₂)⁻¹ := by group
      _ = (m₁ * m₂) * (p₂ * p₁) * (m₁ * m₂)⁻¹ := by rw [hcomm]
      _ = ((m₁ * m₂) * p₂ * (m₁ * m₂)⁻¹) * ((m₁ * m₂) * p₁ * (m₁ * m₂)⁻¹) := by group
  rw [hA, hB] at hconj
  have hva : m₁ * u₂ * m₁⁻¹ * v₁ ∈ V := V.mul_mem (pd.conj_V hm₁I hu₂) hv₁
  have hvb : (m₁ * v₂ * m₁⁻¹) * u₁ ∈ V := V.mul_mem (pd.conj_V hm₁I hv₂) hu₁
  exact comm_of_twist pd hva hvb (pd.P₁_le_P ha) (pd.P₂_le_P hb) hconj

theorem inv_mem_P₁_or_P₂ (pd : S153E55.PDecomp I P V N₁ N₂ P₁ P₂)
    (h₁sq : ∀ x ∈ P₁, x * x = 1) (h₂sq : ∀ x ∈ P₂, x * x = 1)
    (hT₁ : ∀ a ∈ P₁, a ∉ V → ∀ b ∈ P₁, b ∉ V → ∃ m ∈ N₁, m * a * m⁻¹ * b⁻¹ ∈ V)
    (hT₂ : ∀ a ∈ P₂, a ∉ V → ∀ b ∈ P₂, b ∉ V → ∃ m ∈ N₂, m * a * m⁻¹ * b⁻¹ ∈ V)
    (hne : ∃ a ∈ P₁, a ∉ V) (hZ : ∀ x ∈ P, (∀ q ∈ P, q * x = x * q) → x ∈ V) :
    ∀ x ∈ P, x * x = 1 → x ∈ P₁ ∨ x ∈ P₂ := by
  intro x hx hx2
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := pd.exists_mul hx
  by_cases h1 : p₁ ∈ V
  · exact Or.inr (P₂.mul_mem (pd.V_le_P₂ h1) hp₂)
  by_cases h2 : p₂ ∈ V
  · exact Or.inl (P₁.mul_mem hp₁ (pd.symm.V_le_P₂ h2))
  exfalso
  have hcomm : p₁ * p₂ = p₂ * p₁ := by
    have e1 := h₁sq _ hp₁
    have e2 := h₂sq _ hp₂
    calc p₁ * p₂ = p₁ * ((p₁ * p₂) * (p₁ * p₂)) * p₂ := by rw [hx2]; group
      _ = (p₁ * p₁) * p₂ * p₁ * (p₂ * p₂) := by group
      _ = p₂ * p₁ := by rw [e1, e2]; group
  have hcross := cross_comm pd hT₁ hT₂ hp₁ h1 hp₂ h2 hcomm
  have hP₁ := fun {a b : G} (ha : a ∈ P₁) (hb : b ∈ P₁) => comm_of_sq_eq_one (A := P₁) h₁sq ha hb
  obtain ⟨a, ha, haV⟩ := hne
  apply haV
  refine hZ a (pd.P₁_le_P ha) fun q hq => ?_
  obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := pd.exists_mul hq
  calc q₁ * q₂ * a = q₁ * (q₂ * a) := by group
    _ = q₁ * (a * q₂) := by rw [hcross a ha q₂ hq₂]
    _ = (q₁ * a) * q₂ := by group
    _ = (a * q₁) * q₂ := by rw [hP₁ hq₁ ha]
    _ = a * (q₁ * q₂) := by group

end Abstract

end S153E61C

end CFSG.Quasithin
