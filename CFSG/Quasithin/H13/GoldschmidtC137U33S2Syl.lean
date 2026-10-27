module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Br
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ABGLocalTools
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.U3.GC137.S2

variable {W : Type} [CommGroup W] [Finite W]

structure G2FactsAt (X₀ L₀ S : Subgroup (MulAut W)) : Prop where
  card_X : Nat.card ↥X₀ = 12096
  rk_L : rkIdx (fixV L₀) = 6
  no_off : ∀ B : Subgroup (MulAut W), B ≤ L₀ → B ≠ ⊥ → IsElemAbelian2 B →
    Nat.card W ≤ Nat.card ↥B * Nat.card ↥(fixV B) → False
  sylow_self : X₀ ⊓ normalizer (S : Set (MulAut W)) ≤ S
  dichotomy : ∀ P : Subgroup (MulAut W), S ≤ P → P ≤ X₀ → P ≠ X₀ →
    (∀ H : Subgroup (MulAut W), P ≤ H → H ≤ X₀ → H = P ∨ H = X₀) →
      G2Line L₀ P ∨ G2Point X₀ L₀ P

omit [Finite W] in
theorem map_cg_inv_eq {S S' : Subgroup (MulAut W)} {k : MulAut W}
    (hk : ∀ x : MulAut W, x ∈ S' ↔ k⁻¹ * x * k ∈ S) : S'.map (cg k⁻¹) = S := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [cg_apply_self]
    have := (hk x).1 hx
    simpa using this
  · intro hy
    refine ⟨k * y * k⁻¹, (hk _).2 (by rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]; exact hy), ?_⟩
    rw [cg_apply_self]
    group

theorem G2Facts.of_at {X₀ L₀ S : Subgroup (MulAut W)} (hS : IsSylowTwoOf S X₀)
    (hL : ∀ k ∈ X₀, L₀.map (cg k) = L₀) (h : G2FactsAt X₀ L₀ S) : G2Facts X₀ L₀ := by
  have hSo := isSylowTwoOf_iff_isSylowOf.1 hS
  have key : ∀ S' : Subgroup (MulAut W), IsSylowTwoOf S' X₀ →
      ∃ k ∈ X₀, S'.map (cg k⁻¹) = S := fun S' hS' => by
    obtain ⟨k, hk, hkS⟩ := IsSylowOf.exists_mem_conj hSo (isSylowTwoOf_iff_isSylowOf.1 hS')
    exact ⟨k, hk, map_cg_inv_eq hkS⟩
  refine ⟨h.card_X, h.rk_L, h.no_off, ?_, ?_⟩
  · intro S' hS' x hx
    obtain ⟨k, hk, hkS⟩ := key S' hS'
    have hkinv : k⁻¹ ∈ X₀ := inv_mem hk
    have h1 : cg k⁻¹ x ∈ X₀ ⊓ normalizer (S : Set (MulAut W)) := by
      refine ⟨?_, ?_⟩
      · rw [← map_cg_of_mem hkinv]
        exact ⟨x, hx.1, rfl⟩
      · rw [← hkS]
        exact mem_normalizer_map_cg k⁻¹ hx.2
    have h2 := h.sylow_self h1
    rw [← hkS] at h2
    exact (Subgroup.mem_map_iff_mem (cg_injective _)).1 h2
  · intro S' P hS' hSP hPX hPne hmax
    obtain ⟨k, hk, hkS⟩ := key S' hS'
    set e : MulAut W := k⁻¹ with he
    have hkinv : e ∈ X₀ := inv_mem hk
    have hXe : X₀.map (cg e) = X₀ := map_cg_of_mem hkinv
    have hLe : L₀.map (cg e) = L₀ := hL e hkinv
    have hSle : S ≤ P.map (cg e) := by
      rw [← hkS]
      exact Subgroup.map_mono hSP
    have hPle : P.map (cg e) ≤ X₀ := by
      rw [← hXe]
      exact Subgroup.map_mono hPX
    have hPne' : P.map (cg e) ≠ X₀ := by
      intro h0
      rw [← hXe] at h0
      exact hPne (Subgroup.map_injective (cg_injective e) h0)
    have hmax' : ∀ H : Subgroup (MulAut W), P.map (cg e) ≤ H → H ≤ X₀ →
        H = P.map (cg e) ∨ H = X₀ := by
      intro H hPH hHX
      set H' : Subgroup (MulAut W) := H.map (MulAut.congr e).symm.toMonoidHom with hH'
      have hHH : H'.map (cg e) = H := map_cg_symm e H
      have h1 : P ≤ H' := (le_map_cg e).1 (by rw [hHH]; exact hPH)
      have h2 : H' ≤ X₀ := (le_map_cg e).1 (by rw [hHH, hXe]; exact hHX)
      rcases hmax H' h1 h2 with h3 | h3
      · left
        rw [← hHH, h3]
      · right
        rw [← hHH, h3, hXe]
    rcases h.dichotomy _ hSle hPle hPne' hmax' with hl | hp
    · refine Or.inl (G2Line.of_map e ?_)
      rw [hLe]
      exact hl
    · refine Or.inr (G2Point.of_map e ?_)
      rw [hLe, hXe]
      exact hp

end CFSG.Quasithin.H13.U3.GC137
