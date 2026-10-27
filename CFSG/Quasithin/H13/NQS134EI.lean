module

public import CFSG.Quasithin.H13.NQS134EC

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem comm_ne_allOnes : ∀ σ : Perm (Fin 6), ∀ y : P6, ∑ i, Multiplicative.toAdd y i = 0 →
    G6.permAct 6 σ y * y ≠ G6.allOnes 6 := by
  decide +kernel

theorem eq_allOnes_of_wtP_six : ∀ x : P6, wtP x = 6 → x = G6.allOnes 6 := by decide +kernel

theorem wtP_e0123_allOnes : wtP (e0123 * G6.allOnes 6) = 2 := by decide

theorem wtP_e45_allOnes : wtP (e45 * G6.allOnes 6) = 4 := by decide

theorem fpf_not_comm_c3 : ∀ τ ∈ fpfList, swap (0 : Fin 6) 1 * swap 1 2 * τ ≠
    τ * (swap (0 : Fin 6) 1 * swap 1 2) := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace End134

variable (S : A6.Setting134 G T L V)
include S

variable {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
include hz hzL

theorem wtP_mul_zV :
    wtP (S.frame.ψ ⟨z * S.zV, mul_mem hz.1 S.zV_mem_V⟩ : P6) =
      6 - wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
  rw [psi_mul_zV S hz.1]
  rcases psi_z_cases' S hz hzL with h | h
  · rw [h, wtP_e0123_allOnes, wtP_e0123]
  · rw [h, wtP_e45_allOnes, wtP_e45]

theorem six_sub_wt_cases :
    6 - wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2 ∨ 6 - wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 4 := by
  rcases psi_z_cases' S hz hzL with h | h
  · rw [h, wtP_e0123]
    exact Or.inl rfl
  · rw [h, wtP_e45]
    exact Or.inr rfl

theorem comm_wt_of_orb (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {W : Subgroup G}
    (hWN : W ≤ normalizer (V : Set G)) (hVW : V ≤ normalizer (W : Set G))
    (horb : ∀ c ∈ W, c ≠ 1 → c ≠ z → ∃ g : G, g * c * g⁻¹ = S.zV ∨ g * c * g⁻¹ = z * S.zV)
    (hnz : ∀ x ∈ W, ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ≠ z) :
    ∀ (x : G) (hx : x ∈ W) (v : G) (hv : v ∈ V), x * v * x⁻¹ * v⁻¹ = 1 ∨
      wtP (G6.permAct 6 (S.frame.ρ ⟨x, hWN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
        (S.frame.ψ ⟨v, hv⟩ : P6)) = 6 - wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
  intro x hx v hv
  by_cases h1 : x * v * x⁻¹ * v⁻¹ = 1
  · exact Or.inl h1
  right
  have hcV : x * v * x⁻¹ * v⁻¹ ∈ V :=
    mul_mem ((mem_normalizer_iff.mp (hWN hx) v).mp hv) (inv_mem hv)
  have hcW : x * v * x⁻¹ * v⁻¹ ∈ W := by
    have h2 : v * x⁻¹ * v⁻¹ ∈ W := (mem_normalizer_iff.mp (hVW hv) _).mp (inv_mem hx)
    have e : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
    rw [e]
    exact mul_mem hx h2
  have hcomm := comm_psi S (hWN hx) hv hcV
  rw [← hcomm]
  have hne6 : (S.frame.ψ ⟨x * v * x⁻¹ * v⁻¹, hcV⟩ : P6) ≠ G6.allOnes 6 := by
    rw [hcomm]
    exact comm_ne_allOnes _ _ (G6.mem_coreMod.1 (S.frame.ψ ⟨v, hv⟩).2)
  obtain ⟨g, hg⟩ := horb _ hcW h1 (hnz x hx v hv)
  have key : ∀ (w : G) (hw : w ∈ V), g * (x * v * x⁻¹ * v⁻¹) * g⁻¹ = w →
      wtP (S.frame.ψ ⟨x * v * x⁻¹ * v⁻¹, hcV⟩ : P6) = wtP (S.frame.ψ ⟨w, hw⟩ : P6) := by
    intro w hw hgw
    obtain ⟨h, hh, hhw⟩ := S.lemma13_2_2_five h331 h1222 hcV hw (g := g⁻¹) (by
      rw [inv_inv]
      exact hgw)
    have hhN : h⁻¹ ∈ normalizer (V : Set G) :=
      inv_mem (sup_le S.frame.L_le S.frame.T_le hh)
    have h2 := S.psi_conj ⟨h⁻¹, hhN⟩ ⟨x * v * x⁻¹ * v⁻¹, hcV⟩
    have e : (⟨((⟨h⁻¹, hhN⟩ : ↥(normalizer (V : Set G))) : G) *
        ((⟨x * v * x⁻¹ * v⁻¹, hcV⟩ : ↥V) : G) *
        ((⟨h⁻¹, hhN⟩ : ↥(normalizer (V : Set G))) : G)⁻¹, (mem_normalizer_iff.mp hhN _).mp hcV⟩ :
          ↥V) = ⟨w, hw⟩ := Subtype.ext (by
      show h⁻¹ * (x * v * x⁻¹ * v⁻¹) * h⁻¹⁻¹ = w
      rw [inv_inv]
      exact hhw)
    rw [e] at h2
    rw [h2, G6.coreAct_coe, wtP_permAct]
  rcases hg with hg | hg
  · exfalso
    have h3 := key _ S.zV_mem_V hg
    rw [S.psi_zV] at h3
    exact hne6 (eq_allOnes_of_wtP_six _ (h3.trans wtP_allOnes))
  · rw [key _ (mul_mem hz.1 S.zV_mem_V) hg]
    exact wtP_mul_zV S hz hzL

theorem centralizer_index_two {W : Subgroup G} (hWN : W ≤ normalizer (V : Set G))
    (hW2 : ∀ x ∈ W, x * x = 1)
    (hcomm : ∀ (x : G) (hx : x ∈ W) (v : G) (hv : v ∈ V), x * v * x⁻¹ * v⁻¹ = 1 ∨
      wtP (G6.permAct 6 (S.frame.ρ ⟨x, hWN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
        (S.frame.ψ ⟨v, hv⟩ : P6)) = 6 - wtP (S.frame.ψ ⟨z, hz.1⟩ : P6)) :
    W ≤ centralizer (V : Set G) ∨ 2 * Nat.card ↥(W ⊓ centralizer (V : Set G)) = Nat.card W := by
  by_cases hex : ∃ (x₀ : G) (hx₀ : x₀ ∈ W), S.frame.ρ ⟨x₀, hWN hx₀⟩ ≠ 1
  · obtain ⟨x₀, hx₀, hx₀1⟩ := hex
    obtain ⟨hρ, -, -⟩ := rho_eq_of_comm S hWN hW2 (six_sub_wt_cases S hz hzL) hcomm hx₀ hx₀1
    exact Or.inr (card_inf_centralizer S hWN hx₀ hx₀1 hρ)
  · push Not at hex
    exact Or.inl fun x hx => (frame5_ker_iff S.frame _).1 (hex x hx)

theorem le_centralizer_of_wt_two (h2 : wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2) {W : Subgroup G}
    (hWN : W ≤ normalizer (V : Set G)) (hW2 : ∀ x ∈ W, x * x = 1)
    (hcomm : ∀ (x : G) (hx : x ∈ W) (v : G) (hv : v ∈ V), x * v * x⁻¹ * v⁻¹ = 1 ∨
      wtP (G6.permAct 6 (S.frame.ρ ⟨x, hWN hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
        (S.frame.ψ ⟨v, hv⟩ : P6)) = 6 - wtP (S.frame.ψ ⟨z, hz.1⟩ : P6))
    {y : G} (hyN : y ∈ normalizer (V : Set G)) (hyW : y ∈ normalizer (W : Set G))
    (hy : S.frame.ρ ⟨y, hyN⟩ = swap 0 1 * swap 1 2) : W ≤ centralizer (V : Set G) := by
  by_contra hWC
  obtain ⟨x₀, hx₀, hx₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hWC
  have hx₀1 : S.frame.ρ ⟨x₀, hWN hx₀⟩ ≠ 1 := fun h => hx₀C ((frame5_ker_iff S.frame _).1 h)
  obtain ⟨hρ, h4, -⟩ := rho_eq_of_comm S hWN hW2 (six_sub_wt_cases S hz hzL) hcomm hx₀ hx₀1
  have hτ := h4 (by rw [h2])
  have hx₁ : y * x₀ * y⁻¹ ∈ W := (mem_normalizer_iff.mp hyW x₀).mp hx₀
  have hρx₁ : S.frame.ρ ⟨y * x₀ * y⁻¹, hWN hx₁⟩ =
      (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x₀, hWN hx₀⟩ * (swap 0 1 * swap 1 2)⁻¹ := by
    rw [← hy, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rcases hρ _ hx₁ with h | h
  · apply hx₀1
    rw [hρx₁] at h
    have h' := congrArg (fun σ => (swap (0 : Fin 6) 1 * swap 1 2)⁻¹ * σ *
      (swap (0 : Fin 6) 1 * swap 1 2)) h
    simpa [mul_assoc] using h'
  · rw [hρx₁] at h
    apply fpf_not_comm_c3 _ hτ
    calc swap (0 : Fin 6) 1 * swap 1 2 * S.frame.ρ ⟨x₀, hWN hx₀⟩
        = (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x₀, hWN hx₀⟩ * (swap 0 1 * swap 1 2)⁻¹ *
          (swap 0 1 * swap 1 2) := by group
      _ = S.frame.ρ ⟨x₀, hWN hx₀⟩ * (swap 0 1 * swap 1 2) := by rw [h]

end End134

end CFSG.Quasithin.H13.NQS134
