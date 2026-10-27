module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Decomp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec8.T81.Triple

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace T81

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}
  {r : ℕ} {S : Subgroup G}

theorem isRegFam_triple
    (h : Counterexample p A θ) (hA : TypeA p A θ) (hr : InPiTheta A θ r)
    (hS : IsSr p A θ r S) {B₁ B₂ B₃ : Subgroup G} {c₁₂ c₁₃ : G}
    (hP : ThreePlanes p A B₁ B₂ B₃ c₁₂ c₁₃) :
    IsRegFam A (sSup (Msig p A θ))
      (tripleFam (mFam θ (zOf S) B₁) (mFam θ (zOf S) B₂) (mFam θ (zOf S) B₃)) ⊥ := by
  obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
  have hM1 : sSup (Msig p A θ) ≠ ⊥ := by
    intro hbot
    apply h.not_isSolvable_apply ha ha1
    have : θ a = ⊥ := le_bot_iff.mp (hbot ▸ h.apply_le_sSup_msig ha ha1)
    rw [this]
    infer_instance
  refine isRegFam_tripleFam h.commutator_sSup_msig hM1 (isRegFam_mFam h hA hr hS hP.mem₁)
    (isRegFam_mFam h hA hr hS hP.mem₂) (isRegFam_mFam h hA hr hS hP.mem₃) hP.inf_eq_bot ?_
  rw [hP.mem₁.2, hP.mem₂.2, hP.mem₃.2, h.card]
  ring

end T81

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
