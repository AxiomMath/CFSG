module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcE8
public import CFSG.LieType.Steinberg.Isogeny.E7
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits

section Family

theorem ggRootDetect_E7 : GGRootDetect .E7 := by
  intro G _ _ n f ψ hadm _ hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨-, hf, -⟩ := hadm
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have : Finite ↥(e7Data_valid.minGroup (GaloisField 2 f)) := by
    have : Finite (Module.End (GaloisField 2 f) (Fin e7Data.d →₀ GaloisField 2 f)) :=
      Module.finite_of_finite (GaloisField 2 f)
    infer_instance
  change γ ∈ (e7Datum (GaloisField 2 f)).roots at hγ
  have hγ' : IsRoot .E7 γ := e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 _ |>.mp hγ
  have hε : ((e7Eps γ : ℤ) : GaloisField 2 f) * (e7Eps γ : GaloisField 2 f) = 1 := by
    rcases e7Eps_eq_one_or γ with h | h <;> rw [h] <;> norm_num
  exact RootDetectExc.ggPsiInnerDiag_of_isogeny (rootOperatorFamily .E7)
    (e7Datum (GaloisField 2 f)) (isPerfect_e7 (GaloisField 2 f)).commutator_eq_top
    center_adjointGroup_eq_bot (e7Isogeny_surjective (GaloisField 2 f))
    (ker_le_center_of_isQuasisimple (isQuasisimple_e7 (GaloisField 2 f))
      (exists_e7Isogeny_ne_one (GaloisField 2 f)))
    (hp.odd_of_ne_two hp2) (RootDetectExc.adjFieldForm_E7_E8 hf _ hK .E7 (Or.inl rfl) p) hker hc
    hcp (α := ⟨γ, hγ'⟩)
    (fun t => ⟨e7Data_valid.xm (GaloisField 2 f) γ ((e7Eps γ : GaloisField 2 f) * t),
      e7Data_valid.xm_mem_rootGroup _ γ _, by
        have h := e7Isogeny_xm (GaloisField 2 f) γ ((e7Eps γ : GaloisField 2 f) * t)
        rw [← mul_assoc, hε, one_mul, xPar_of_isRoot hγ'] at h
        exact h⟩) hT

end Family

end CFSG.StandardType
