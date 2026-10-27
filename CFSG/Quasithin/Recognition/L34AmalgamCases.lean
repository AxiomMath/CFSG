module

public import CFSG.Quasithin.Recognition.L34AmalgamGen
public meta import CFSG.Quasithin.Recognition.L34AmalgamGen
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public import CFSG.Quasithin.Recognition.L34AmalgamCasesInputs
public import Certificates.Certificate7035
public import Certificates.Certificate7036
public import Certificates.Certificate7037
public import Certificates.Certificate2195

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94

theorem cbWords_letters : ∀ s ∈ cbWords, ∀ x ∈ word s, x.1.val < 3 := by
  decide

theorem cb_comm :
    ∀ s ∈ cbWords, evalW gen (word s) * bT1 = bT1 * evalW gen (word s) :=
  Certificates.certificate7035.1

theorem count_C1 :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 = 1 ∧ ¬ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
    (∀ x, σ (σ x) = x) ∧ ¬ ∃ T ∈ bTabs, ∀ x : Fin 22,
      T.getD (σ x).val 0 = (tab bT1).getD (T.getD x.val 0).val 0) = 0 :=
  Certificates.certificate7035.2.1

theorem count_C2 :
    m22Count (fun σ => σ 0 = 0 ∧ σ 1 ≠ 1 ∧ (∀ p ∈ m22HexadL, σ p ∈ m22HexadL) ∧
    (∀ x, σ (σ x) = x) ∧ ¬ ∃ T ∈ cbTabs, ∃ R ∈ repTabs, ∀ x : Fin 22,
      T.getD (σ x).val 0 = R.getD (T.getD x.val 0).val 0) = 0 :=
  Certificates.certificate7035.2.2

theorem evalW_mem_B {s : String} (hs : ∀ x ∈ word s, x.1.val < 3) :
    evalW gen (word s) ∈ m22TwoStab ⊓ m22PtHexStab := by
  refine closure_c_le_B (evalW_mem_closure gen _ _ fun x hx => ?_)
  have := hs x hx
  have hx3 : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 := by
    rcases x with ⟨⟨v, hv⟩, b⟩
    simp only at this ⊢
    interval_cases v <;> simp
  rcases hx3 with h | h | h <;> simp [h]

theorem conj_eq_of_tab {σ β τ : M22} (h : ∀ x : Fin 22,
    (tab β).getD ((σ : Equiv.Perm (Fin 22)) x).val 0 = (tab τ).getD ((tab β).getD x.val 0).val 0) :
    β * σ * β⁻¹ = τ := by
  have h' : β * σ = τ * β := by
    apply Subtype.ext
    ext x
    have := h x
    rw [tab_getD, tab_getD, tab_getD] at this
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    exact congrArg Fin.val this
  rw [h', mul_inv_cancel_right]

theorem exists_conj_rep
    {σ₁ σ₂ : M22}
    (h₁ : σ₁ ∈ m22TwoStab) (h₁' : σ₁ ∉ m22PtHexStab)
    (hσ₁ : σ₁ * σ₁ = 1) (h₂ : σ₂ ∈ m22PtHexStab) (h₂' : σ₂ ∉ m22TwoStab) (hσ₂ : σ₂ * σ₂ = 1) :
    ∃ b ∈ m22TwoStab ⊓ m22PtHexStab, ∃ i : Fin 12, b * σ₁ * b⁻¹ = bT1 ∧ b * σ₂ * b⁻¹ = rep i := by
  have hinv : ∀ {σ : M22}, σ * σ = 1 → ∀ x, (σ : Equiv.Perm (Fin 22)) ((σ : Equiv.Perm (Fin 22)) x)
      = x := by
    intro σ hσ x
    have := congrArg (fun g : M22 => (g : Equiv.Perm (Fin 22)) x) hσ
    simpa using this
  obtain ⟨h10, h11⟩ := mem_m22TwoStab_iff.mp h₁
  have h1h : ¬ ∀ p ∈ m22HexadL, (σ₁ : Equiv.Perm (Fin 22)) p ∈ m22HexadL := fun h =>
    h₁' (M22Witt.mem_m22PtHexStab_iff.mpr ⟨h10, h⟩)
  have hc1 := not_of_count_eq_zero _ count_C1 σ₁
  simp only [not_and, not_not] at hc1
  obtain ⟨T, hT, hTσ⟩ := hc1 h10 h11 h1h (hinv hσ₁)
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hT
  set β := evalW gen (word s) with hβ
  have hβB : β ∈ m22TwoStab ⊓ m22PtHexStab := evalW_mem_B (bWords_letters s hs)
  have hβ1 : β * σ₁ * β⁻¹ = bT1 := conj_eq_of_tab hTσ
  set σ₃ := β * σ₂ * β⁻¹ with hσ₃
  have h₃ : σ₃ ∈ m22PtHexStab := m22PtHexStab.mul_mem (m22PtHexStab.mul_mem hβB.2 h₂)
    (m22PtHexStab.inv_mem hβB.2)
  have h₃' : σ₃ ∉ m22TwoStab := by
    intro h
    apply h₂'
    have := m22TwoStab.mul_mem (m22TwoStab.mul_mem (m22TwoStab.inv_mem hβB.1) h) hβB.1
    rwa [hσ₃, show β⁻¹ * (β * σ₂ * β⁻¹) * β = σ₂ by group] at this
  have hσ₃sq : σ₃ * σ₃ = 1 := by
    rw [hσ₃, show β * σ₂ * β⁻¹ * (β * σ₂ * β⁻¹) = β * (σ₂ * σ₂) * β⁻¹ by group, hσ₂, mul_one,
      mul_inv_cancel]
  obtain ⟨h30, h3h⟩ := M22Witt.mem_m22PtHexStab_iff.mp h₃
  have h31 : (σ₃ : Equiv.Perm (Fin 22)) 1 ≠ 1 := fun h => h₃' (mem_m22TwoStab_iff.mpr ⟨h30, h⟩)
  have hc2 := not_of_count_eq_zero _ count_C2 σ₃
  simp only [not_and, not_not] at hc2
  obtain ⟨T', hT', R, hR, hTR⟩ := hc2 h30 h31 h3h (hinv hσ₃sq)
  obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hT'
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hR
  set γ := evalW gen (word s') with hγ
  have hγB : γ ∈ m22TwoStab ⊓ m22PtHexStab := evalW_mem_B (cbWords_letters s' hs')
  have hγ3 : γ * σ₃ * γ⁻¹ = rep i := conj_eq_of_tab hTR
  have hγt : γ * bT1 * γ⁻¹ = bT1 := by rw [cb_comm s' hs', mul_inv_cancel_right]
  refine ⟨γ * β, Subgroup.mul_mem _ hγB hβB, i, ?_, ?_⟩
  · rw [show γ * β * σ₁ * (γ * β)⁻¹ = γ * (β * σ₁ * β⁻¹) * γ⁻¹ by group, hβ1, hγt]
  · rw [show γ * β * σ₂ * (γ * β)⁻¹ = γ * σ₃ * γ⁻¹ by rw [hσ₃]; group, hγ3]

end CFSG.Quasithin.L34Amalgam
