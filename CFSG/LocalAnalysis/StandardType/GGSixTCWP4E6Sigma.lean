module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6FrameDef
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4E6Form
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE6Disc

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem isRoot_of_mem_a2Set
    {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) (hβ : IsRoot .E6 β) (hab : iform α β = -1)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ tcA2Set α β) : IsRoot .E6 γ := by
  have n2 : iform β β = 2 := e6_iform_self β (mem_rootFinset.2 hβ)
  have hne : α ≠ -β := by
    intro h
    rw [h, iform_neg_left_E6, n2] at hab
    norm_num at hab
  have hsum : IsRoot .E6 (α + β) :=
    isRoot_add_of_iform_neg hα hβ hne (by omega)
  simp only [tcA2Set, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
  rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hα
  · exact hβ
  · exact hsum
  · exact IsRoot.neg hα
  · exact IsRoot.neg hβ
  · exact IsRoot.neg hsum

theorem frame_u_abs_le {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ}
    (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot .E6 γ) :
    |iform γ α₃| ≤ 2 ∧ |iform γ β₃| ≤ 2 := by
  by_cases hX : γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂
  · obtain ⟨h1, h2⟩ := (fr.mem γ hγ).1 hX
    rw [h1, h2]
    simp
  · have h := fr.tab γ hγ hX
    simp [tab12] at h
    simp only [abs_le]
    omega

theorem sigma_eq_X {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ}
    (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃) {W : Set (Fin Tag.E6.rank → ℤ)}
    (hX : ∀ w ∈ W, ∀ γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂, (p : ℤ) ∣ ∑ j, γ j * w j)
    (hfull : ∀ s t : ℤ, ∃ w ∈ W, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * w j) - (s * iform γ α₃ + t * iform γ β₃)) :
    ∀ γ, IsRoot .E6 γ → ((∀ w ∈ W, (p : ℤ) ∣ ∑ j, γ j * w j) ↔
      γ ∈ tcA2Set α₁ β₁ ∪ tcA2Set α₂ β₂) := by
  intro γ hγ
  constructor
  · intro h
    obtain ⟨w₁, hw₁, hd₁⟩ := hfull 1 0
    obtain ⟨w₂, hw₂, hd₂⟩ := hfull 0 1
    have g₁ : (p : ℤ) ∣ iform γ α₃ := by
      simpa using dvd_sub (h w₁ hw₁) (hd₁ γ)
    have g₂ : (p : ℤ) ∣ iform γ β₃ := by
      simpa using dvd_sub (h w₂ hw₂) (hd₂ γ)
    obtain ⟨a₁, a₂⟩ := frame_u_abs_le fr hγ
    have b₁ : iform γ α₃ = 0 :=
      Int.eq_zero_of_abs_lt_dvd g₁ (lt_of_le_of_lt a₁ (by omega))
    have b₂ : iform γ β₃ = 0 :=
      Int.eq_zero_of_abs_lt_dvd g₂ (lt_of_le_of_lt a₂ (by omega))
    exact (fr.mem γ hγ).2 ⟨b₁, b₂⟩
  · intro hγX w hw
    exact hX w hw γ hγX

theorem rho_u_neg {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {α₁ β₁ α₂ β₂ α₃ β₃ : Fin Tag.E6.rank → ℤ} (fr : E6Frame α₁ β₁ α₂ β₂ α₃ β₃)
    {W : Set (Fin Tag.E6.rank → ℤ)} {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}
    (hρroot : ∀ γ, IsRoot .E6 (ρ γ) ↔ IsRoot .E6 γ)
    (hρc : ∀ w ∈ W, ∀ γ, IsRoot .E6 γ → (p : ℤ) ∣ (∑ j, (ρ γ) j * w j) + ∑ j, γ j * w j)
    (hfull : ∀ s t : ℤ, ∃ w ∈ W, ∀ γ : Fin Tag.E6.rank → ℤ,
      (p : ℤ) ∣ (∑ j, γ j * w j) - (s * iform γ α₃ + t * iform γ β₃)) :
    ∀ γ, IsRoot .E6 γ → iform (ρ γ) α₃ = - iform γ α₃ ∧ iform (ρ γ) β₃ = - iform γ β₃ := by
  intro γ hγ
  have hργ : IsRoot .E6 (ρ γ) := (hρroot γ).2 hγ
  obtain ⟨w₁, hw₁, hd₁⟩ := hfull 1 0
  obtain ⟨w₂, hw₂, hd₂⟩ := hfull 0 1
  have e : ∀ a b c d : ℤ, a + b - (a - c) - (b - d) = c + d := fun a b c d => by ring
  have k₁ : (p : ℤ) ∣ iform (ρ γ) α₃ + iform γ α₃ := by
    have h := dvd_sub (dvd_sub (hρc w₁ hw₁ γ hγ) (hd₁ (ρ γ))) (hd₁ γ)
    rw [e] at h
    simpa using h
  have k₂ : (p : ℤ) ∣ iform (ρ γ) β₃ + iform γ β₃ := by
    have h := dvd_sub (dvd_sub (hρc w₂ hw₂ γ hγ) (hd₂ (ρ γ))) (hd₂ γ)
    rw [e] at h
    simpa using h
  obtain ⟨a₁, a₂⟩ := frame_u_abs_le fr hργ
  obtain ⟨c₁, c₂⟩ := frame_u_abs_le fr hγ
  obtain ⟨a₁l, a₁u⟩ := abs_le.1 a₁
  obtain ⟨a₂l, a₂u⟩ := abs_le.1 a₂
  obtain ⟨c₁l, c₁u⟩ := abs_le.1 c₁
  obtain ⟨c₂l, c₂u⟩ := abs_le.1 c₂
  have z₁ : iform (ρ γ) α₃ + iform γ α₃ = 0 :=
    Int.eq_zero_of_abs_lt_dvd k₁ (abs_lt.2 ⟨by omega, by omega⟩)
  have z₂ : iform (ρ γ) β₃ + iform γ β₃ = 0 :=
    Int.eq_zero_of_abs_lt_dvd k₂ (abs_lt.2 ⟨by omega, by omega⟩)
  constructor <;> omega

end CFSG.StandardType.TableCRes

end
