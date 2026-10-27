module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Transport
public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.LieKnownR2.SpecialLinearNC

open CFSG.Open

theorem ggRootNoCentralAt_map_of_odd_central_ker {U X : Type} [Group U] [Group X] [Finite X]
    (φ : U →* X) (hker : φ.ker ≤ Subgroup.center U) (hodd : Odd (Nat.card φ.ker))
    {R : Subgroup U} (hR : IsPGroup 2 R) (h : GGRootNoCentralAt (⊤ : Subgroup U) R) :
    GGRootNoCentralAt φ.range (R.map φ) := by
  intro A B hRA hAB hB hNA hNB hc
  set N : Subgroup U := Subgroup.normalizer (R : Set U) with hNdef
  have hN : N.map φ = φ.range ⊓ Subgroup.normalizer ((R.map φ : Subgroup X) : Set X) :=
    map_normalizer_eq_range_inf_normalizer_map hker hodd hR
  have hP : (pCoreOf 2 N).map φ = pCoreOf 2 (N.map φ) :=
    map_pCoreOf_eq_of_odd_central_ker hker hodd (hker.trans (Subgroup.center_le_normalizer _))
  rw [← hN] at hNA hNB hc
  rw [← hN, ← hP] at hB
  have h' := h
  unfold GGRootNoCentralAt at h'
  simp only [top_inf_eq] at h'
  set P : Subgroup U := pCoreOf 2 N with hPdef
  have hRP : R ≤ P :=
    GGRootNorm.le_pCoreOf_of_normalized Subgroup.le_normalizer hR
      fun m hm t ht => (Subgroup.mem_normalizer_iff.1 hm t).1 ht
  have hNP : ∀ n ∈ N, ∀ x ∈ P, n * x * n⁻¹ ∈ P := fun n hn x hx =>
    (Subgroup.mem_normalizer_iff.1 (GGRootNorm.le_normalizer_pCoreOf N hn) x).1 hx
  have hnorm : ∀ C : Subgroup X, N.map φ ≤ Subgroup.normalizer (C : Set X) →
      N ≤ Subgroup.normalizer ((P ⊓ C.comap φ : Subgroup U) : Set U) := by
    intro C hC n hn
    have hfwd : ∀ m ∈ N, ∀ x, x ∈ P ⊓ C.comap φ → m * x * m⁻¹ ∈ P ⊓ C.comap φ := by
      intro m hm x hx
      refine ⟨hNP m hm x hx.1, ?_⟩
      have := (Subgroup.mem_normalizer_iff.1 (hC (Subgroup.mem_map_of_mem φ hm)) (φ x)).1 hx.2
      simpa using this
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd n hn x, fun hx => ?_⟩
    have h2 := hfwd n⁻¹ (inv_mem hn) _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at h2
  have key := h' (P ⊓ A.comap φ) (P ⊓ B.comap φ)
    (le_inf hRP fun r hr => hRA (Subgroup.mem_map_of_mem φ hr))
    (inf_le_inf_left _ (Subgroup.comap_mono hAB)) inf_le_left (hnorm A hNA) (hnorm B hNB)
    (by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨?_, ?_⟩
      · have h1 := hNP g₂ hg₂ g₁⁻¹ (inv_mem hg₁.1)
        have h2 := mul_mem hg₁.1 h1
        simpa [commutatorElement_def, mul_assoc] using h2
      · have := hc (Subgroup.commutator_mem_commutator (H₁ := B) (H₂ := N.map φ) hg₁.2
          (Subgroup.mem_map_of_mem φ hg₂))
        simpa [commutatorElement_def] using this)
  intro b hb
  obtain ⟨p, hp, rfl⟩ := hB hb
  exact (key ⟨hp, hb⟩).2

end CFSG.StandardType.LieKnownR2.SpecialLinearNC
