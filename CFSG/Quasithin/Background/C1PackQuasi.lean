module

public import CFSG.Quasithin.Background.C1PackImage
public import CFSG.Quasithin.Background.C1PackSchur
public import CFSG.Quasithin.Background.C1PackLemmaK

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_commutator_mem {H B₁ B₂ : Subgroup G} (hB₂ : IsBlock2 H B₂)
    (h : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    B₁ ≤ Subgroup.normalizer (B₂ : Set G) := by
  have key : ∀ a ∈ B₁, ∀ y ∈ B₂, a * y * a⁻¹ ∈ B₂ := by
    intro a ha y hy
    set f : G →* G := (MulAut.conj a).toMonoidHom with hf
    have hT : B₂.map f ≤ B₂ ⊔ pCoreOf 2 H := by
      rintro _ ⟨z, hz, rfl⟩
      have hc := h a ha z hz
      have e : f z = (a * z * a⁻¹ * z⁻¹) * z := by
        show a * z * a⁻¹ = _
        group
      rw [e, sup_comm]
      exact Subgroup.mul_mem_sup hc hz
    have hTO : oTwoUpper (B₂.map f) = B₂.map f := by
      rw [oTwoUpper_map, ← isShort2_eq_oTwoUpper hB₂.1]
    have hTB : B₂.map f ≤ B₂ := by
      calc B₂.map f = oTwoUpper (B₂.map f) := hTO.symm
        _ ≤ oTwoUpper (B₂ ⊔ pCoreOf 2 H) := oTwoUpper_mono hT
        _ = B₂ := (isBlock2_normal_sup_pCore hB₂).1.symm
    exact hTB ⟨y, hy, by simp [hf, MulAut.conj_apply]⟩
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact fun hg => key a ha g hg
  · intro hg
    have := key a⁻¹ (B₁.inv_mem ha) _ hg
    simpa [mul_assoc] using this

theorem commutator_mem_blockU_of_le_normalizer {H B₁ B₂ : Subgroup G} (hB₂ : IsBlock2 H B₂)
    (hN : B₁ ≤ Subgroup.normalizer (B₂ : Set G))
    (h : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) :
    ∀ x ∈ B₁, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ blockU B₂ := by
  intro x hx
  refine C1.commutator_mem_blockU_of_mem_blockQ hB₂.1 (y := x) (fun l hl => ?_)
  rw [blockQ_eq_inf_pCoreOf hB₂]
  refine ⟨?_, h x hx l hl⟩
  have h1 : x * l * x⁻¹ ∈ B₂ := (Subgroup.mem_normalizer_iff.mp (hN hx) l).mp hl
  exact B₂.mul_mem h1 (B₂.inv_mem hl)

theorem commutator_eq_bot_of_quasisimple {H B₁ B₂ : Subgroup G} (hB₁ : IsBlock2 H B₁)
    (hq : CFSG.IsQuasisimple (↥B₁ ⧸ CFSG.pCore 2 ↥B₁)) (hB₂ : IsBlock2 H B₂) (hne : B₁ ≠ B₂) :
    ⁅B₁, B₂⁆ = ⊥ := by
  have hcomm := commutator_mem_pCoreOf_of_quasisimple hB₁ hq hB₂ hne
  have hN : B₁ ≤ Subgroup.normalizer (B₂ : Set G) := le_normalizer_of_commutator_mem hB₂ hcomm
  have hU := commutator_mem_blockU_of_le_normalizer hB₂ hN hcomm
  have hperf : ⁅B₁, B₁⁆ = B₁ :=
    C1GN.isShort2_perfect_of_perfect_quotient hB₁.1 hq.1.commutator_eq_top
  have hAU := block_perfect_acts_trivially hB₂.1 hN hperf hU
  have hle : oTwoUpper B₁ ≤ Subgroup.centralizer (B₂ : Set G) := by
    refine (Subgroup.closure_le _).mpr fun a ⟨ha, hodd⟩ => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    exact (centralizes_of_odd_order hB₂.1 (hN ha) hodd (hU a ha) (hAU a ha) l hl).symm
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  calc B₁ = oTwoUpper B₁ := isShort2_eq_oTwoUpper hB₁.1
    _ ≤ Subgroup.centralizer (B₂ : Set G) := hle

end CFSG.Quasithin.C1Pack
