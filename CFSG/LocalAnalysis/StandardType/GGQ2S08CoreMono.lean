module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreOrbit
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreFrameVec
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreRescale
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CorePerms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_core_mono {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ} (hN : 10 ≤ N)
    (b : Module.Basis (Fin N) (ZMod 3) V) (R W : Subgroup (V ≃ₗ[ZMod 3] V))
    (hR : (∀ a, a ∈ R ↔ GGQ2S08Mono b a) ∨ (∀ a, a ∈ R ↔ GGQ2S08MonoEven b a))
    (hWR : W ≤ R) (hWgen : W = Subgroup.closure {s | s ∈ W ∧ GGLinRefl s})
    (xv : V) (hx : xv ≠ 0)
    (hWfix : ∀ v, (∀ w ∈ W, w v = v) ↔ v ∈ Submodule.span (ZMod 3) {xv})
    (hWirr : ∀ U : Submodule (ZMod 3) V, Submodule.span (ZMod 3) {xv} ≤ U →
      (∀ w ∈ W, ∀ u ∈ U, w u ∈ U) → U = Submodule.span (ZMod 3) {xv} ∨ U = ⊤)
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r)
    (hrx : ¬ ∃ c : ZMod 3, r xv = c • xv) :
    GGQ2S08M0 R W r xv = R ∨ GGQ2S08CoreRO (N := N) R W r xv := by
  have hRm : ∀ a ∈ R, GGQ2S08Mono b a := by
    intro a ha
    rcases hR with h | h
    · exact (h a).1 ha
    · obtain ⟨σ, ε, h1, -, h3⟩ := (h a).1 ha
      exact ⟨σ, ε, h1, h3⟩
  have hWm : ∀ w ∈ W, GGQ2S08Mono b w := fun w hw => hRm w (hWR hw)
  have hfixx : ∀ w ∈ W, w xv = xv := (hWfix xv).2 (Submodule.mem_span_singleton_self xv)
  rcases ggQ2s08core_orbit_dichotomy (by omega) b W hWm xv hx hWfix hWirr with
    ⟨i₀, hxi, htrans⟩ | ⟨hxall, htrans⟩
  · exact Or.inl (ggQ2s08core_frame_vector b R W hRm hWR xv i₀ hxi hx htrans r hrR hrx)
  · obtain ⟨f, hxf, hWf, hRf⟩ :=
      ggQ2s08core_rescale (by omega) b R W hR hWR hWgen xv hxall hfixx htrans
    subst hxf
    rcases ggQ2s08core_all_perms (by omega) f R W hRf hWf r hrR hr hrx with h | ⟨hev, hRb, hM⟩
    · exact Or.inl h
    · exact Or.inr ⟨hev, f, f.linearIndependent, f.span_eq, rfl, fun w hw => (hWf w).1 hw, hRb, hM⟩


end CFSG.StandardType

end
