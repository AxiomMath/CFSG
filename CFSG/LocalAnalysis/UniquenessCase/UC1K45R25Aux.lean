module

public import CFSG.CGT.PushingUpLit.SYMB.Split5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.UC46

open Subgroup
open scoped commutatorElement

theorem ker_eq_bot_of_equivariant_section {E V : Type*} [Group E] [Finite E]
    (η : E →* Equiv.Perm (Fin 5))
    (hA : ∀ e, η e ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, η e = σ)
    [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1)
    (act : E →* MulAut V)
    (hker : ∀ e, η e = 1 → ∀ v, act e v = v)
    (ψ : V →* CFSG.Quasithin.G6.coreMod 5) (hψs : Function.Surjective ψ)
    (hψ : ∀ e v, ψ (act e v) = CFSG.Quasithin.G6.coreAct 5 (η e) (ψ v))
    (hfix : ∀ e, ∀ c ∈ ψ.ker, act e c = c)
    (hgen : Subgroup.closure {u : V | ∃ e v, u = v * (act e v)⁻¹} = ⊤) :
    ψ.ker = ⊥ := by
  obtain ⟨s, hsv, hse⟩ :=
    CFSG.CGT.PushingUpLit.SYMB.exists_equivariant_section η hA hs hV act hker ψ hψs hψ
  have hrange : s.range = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro u ⟨e, v, rfl⟩
    set w : V := s (ψ v) with hw
    have hc : v * w⁻¹ ∈ ψ.ker := by
      rw [hw, MonoidHom.mem_ker, map_mul, map_inv, hsv, mul_inv_cancel]
    have hact : act e v = (v * w⁻¹) * act e w := by
      conv_lhs => rw [show v = (v * w⁻¹) * w by group]
      rw [map_mul, hfix e _ hc]
    have hkey : v * (act e v)⁻¹ = w * (act e w)⁻¹ := by
      rw [hact]
      conv_lhs =>
        enter [1]
        rw [show v = (v * w⁻¹) * w by group]
      calc ((v * w⁻¹) * w) * ((v * w⁻¹) * act e w)⁻¹
          = (v * w⁻¹) * w / ((v * w⁻¹) * act e w) := by rw [div_eq_mul_inv]
        _ = w / (act e w) := mul_div_mul_left_eq_div w (act e w) (v * w⁻¹)
        _ = w * (act e w)⁻¹ := by rw [div_eq_mul_inv]
    rw [hkey]
    exact Subgroup.mul_mem _ (MonoidHom.mem_range.mpr ⟨ψ v, hw.symm⟩)
      (Subgroup.inv_mem _ (MonoidHom.mem_range.mpr
        ⟨CFSG.Quasithin.G6.coreAct 5 (η e) (ψ v), by rw [hw, hse e (ψ v)]⟩))
  ext c
  constructor
  · intro hc
    rw [MonoidHom.mem_ker] at hc
    rw [Subgroup.mem_bot]
    obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (hrange.symm ▸ Subgroup.mem_top c)
    rw [← hw, hsv w] at hc
    rw [← hw, hc, map_one]
  · intro hc
    rw [Subgroup.mem_bot] at hc
    rw [hc, MonoidHom.mem_ker, map_one]

end CFSG.LocalAnalysis.UniquenessCase.UCK.UC46
