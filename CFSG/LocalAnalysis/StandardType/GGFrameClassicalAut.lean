module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly SpCoord Multiplicative

theorem mem_ggAutomizer_iff_isSignedPerm {L' : Type} [Group L'] {p k : ℕ}
    {A : Subgroup (MulAut L')} (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A)
    (hsgn : ∀ i : Fin k, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (sgnAut i))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      ggConjAut A hn = MulAut.congr Θ (permAut σ))
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)))
    (φ : MulAut ↥A) :
    φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ↔
      IsSignedPerm ⇑((MulAut.congr Θ).symm φ) := by
  set ΘA : MulAut (Fin k → Multiplicative (ZMod p)) ≃* MulAut ↥A := MulAut.congr Θ with hΘA
  set H : Subgroup (MulAut L') := (MulAut.conj : L' →* MulAut L').range with hH
  constructor
  · intro hφ
    rw [mem_ggAutomizer_iff] at hφ
    obtain ⟨g, hgH, hgN, hgapply⟩ := hφ
    rw [hH, MonoidHom.mem_range] at hgH
    obtain ⟨n, rfl⟩ := hgH
    have hEq : φ = ggConjAut A hgN := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [ggConjAut_apply, hgapply]
    rw [hEq]
    exact hsp n hgN
  · intro hφs
    have hind : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)),
        (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ggConjAut A hn = ΘA u) → u ∈ (ggAutomizer H A).comap ΘA.toMonoidHom := by
      rintro u ⟨n, hn, hEq⟩
      rw [Subgroup.mem_comap]
      change ΘA u ∈ ggAutomizer H A
      rw [← hEq]
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
    have hmem := mem_of_isSignedPerm (fun i => hind _ (hsgn i))
      (fun a b _ => hind _ (hperm (Equiv.swap a b))) hφs
    rw [Subgroup.mem_comap] at hmem
    change ΘA (ΘA.symm φ) ∈ ggAutomizer H A at hmem
    rwa [MulEquiv.apply_symm_apply] at hmem

end CFSG.StandardType.FrameRoute

end
