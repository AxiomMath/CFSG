module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusTriFrame

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.G2D4Models.Twin

section Pinned

variable {F : Type} [Field F]

@[expose] def IsTrialityPinned
    (ρ : spinGroup (Spin.quadPlus 4 F) ≃* spinGroup (Spin.quadPlus 4 F)) : Prop :=
  ∀ k c, ρ (Steinberg.SpinPlus.x 4 F (by norm_num) (sroot k) c) =
      Steinberg.SpinPlus.x 4 F (by norm_num) (sroot (triPerm k)) c ∧
    ρ (Steinberg.SpinPlus.x 4 F (by norm_num) (-sroot k) c) =
      Steinberg.SpinPlus.x 4 F (by norm_num) (-sroot (triPerm k)) c

theorem exists_trialityPinned [Finite F] [CharP F 2] :
    ∃ ρ : spinGroup (Spin.quadPlus 4 F) ≃* spinGroup (Spin.quadPlus 4 F), IsTrialityPinned ρ := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨x', hD, hx'⟩ := exists_trialityLevis (F := F)
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨f, -, hF⟩ := FiniteField.card F 2
  have hadm : StatedLieAdmissible .POmegaPlus 4 2 f := ⟨Nat.prime_two, f.pos, le_refl 4⟩
  have hnt : ∃ (k : Fin 4) (c : F), Steinberg.SpinPlus.x 4 F hn3 (sroot (triPerm k)) c ≠ 1 := by
    obtain ⟨l, hl, hl'⟩ := hD.sl2 (triPerm 0)
    refine ⟨0, 1, fun h => tv_zero_one_one_ne_one (hl ?_)⟩
    rw [map_one, ← h, ← (hx' _ 1).1]
    exact (hl' 1).1
  obtain ⟨Ψ, hu, hv, hsurj, -⟩ := exists_surjective_of_simplyLacedFrame
    (CurtisTits.curtisTitsConclusion_spinPlus hadm
      (by rw [← Nat.card_eq_fintype_card] at hF; exact hF) hn3)
    (leviConePresented_spinPlus F hn3) hD (trialityFrame hD hx') closure_trialityFrame hnt
  have : NeZero 4 := ⟨by norm_num⟩
  have : Nonempty (Fin 4 ⊕ Fin 4) := ⟨Sum.inl 0⟩
  have hfin : Finite (spinGroup (Spin.quadPlus 4 F)) :=
    ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ Spin.coe_ker_spinMatrix_quadPlus
  have hinj : Function.Injective Ψ := Finite.injective_iff_surjective.mpr hsurj
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, fun k c =>
    ⟨(congrArg Ψ (hx' k c).1.symm).trans (hu k c), (congrArg Ψ (hx' k c).2.symm).trans (hv k c)⟩⟩

end Pinned

end CFSG.LocalAnalysis.WeakClosure81
