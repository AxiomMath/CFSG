
module

public import CFSG.RankThree.Native.LyConjugationBase

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native

theorem lyPhi_injective : Function.Injective lyPhi := by
  refine (injective_iff_map_eq_one lyPhi).2 fun g hg => eq_one_of_fix_all fun i => ?_
  have := congrArg (fun p : Equiv.Perm (Fin lyN) => p i) hg
  exact this

theorem lyPhiP_injective : Function.Injective lyPhiP := fun _ _ e =>
  lyPhi_injective (congrArg Subtype.val e)

theorem lyPhiP_bijective : Function.Bijective lyPhiP := ⟨lyPhiP_injective, lyPhiP_surjective⟩

@[expose] def lyPhiEquiv : J ≃* lyP := MulEquiv.ofBijective lyPhiP lyPhiP_bijective

theorem lyPhiEquiv_apply (g : J) : (lyPhiEquiv g : Equiv.Perm (Fin lyN)) = lyPhi g := rfl

@[expose] def lyEquivP : CFSG.Blueprint.NativeSporadic.Ly ≃* lyP := lyEquivJ.trans lyPhiEquiv

theorem lyEquivP_apply (g : CFSG.Blueprint.NativeSporadic.Ly) :
    (lyEquivP g : Equiv.Perm (Fin lyN)) = lyPhi (lyEquivJ g) := rfl

@[expose] def lyHomJ : CFSG.Blueprint.NativeSporadic.Ly →* J :=
  @MulEquiv.toMonoidHom _ _ Units.instMulOneClass _ lyEquivJ

theorem lyHomJ_apply (g : CFSG.Blueprint.NativeSporadic.Ly) : lyHomJ g = lyEquivJ g := rfl

theorem FAM_Ly_faithful_conjugation_action :
    Function.Bijective lyPhiP ∧ Nonempty (CFSG.Blueprint.NativeSporadic.Ly ≃* lyP) ∧
      ∃ ρ : CFSG.Blueprint.NativeSporadic.Ly →* Equiv.Perm (Fin lyN), Function.Injective ρ ∧
        ∀ i j : Fin lyN, ∃ g, ρ g i = j := by
  refine ⟨lyPhiP_bijective, ⟨lyEquivP⟩,
    ⟨lyPhi.comp lyHomJ, fun x y hxy => lyEquivJ.injective (lyPhi_injective hxy), fun i j => ?_⟩⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J i j
  refine ⟨lyEquivJ.symm g, ?_⟩
  change lyPhi (lyEquivJ (lyEquivJ.symm g)) i = j
  rw [MulEquiv.apply_symm_apply]
  exact hg

end CFSG.RankThree.Native
