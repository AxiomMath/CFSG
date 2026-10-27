module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModSecIrred
public import CFSG.Quasithin.EmptyFaithful.SzF53MSecB

public section

namespace CFSG.Quasithin.F53Mod

open CFSG.Open CFSG.LieType.BorelTits Equiv

variable {G : Type} [Group G] [Finite G]

theorem chiefStep_orth_or_nat_of_classification
    (hC5 : ∀ M : Model 5, M.IsIrred → (∃ σ w, M.act σ w ≠ w) →
      Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat))
    {H U L N : Subgroup G} (hq : Nonempty (OTwoQuot H ≃* Perm (Fin 5)))
    (hU : U ≤ pCoreOf 2 H) (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    cSecIn H L N = pCoreOf 2 H ∧ (IsOrthSec H L N ∨ IsNatSec H L N) := by
  have hUH : U ≤ H := hU.trans (pCoreOf_le 2 H)
  obtain ⟨φ, hφs, hφk⟩ := exists_toPerm_of_quot hq
  have hs := isSec_of_chiefStep hUH hU hstep
  have hQC := pCoreOf_le_cSecIn_of_chiefStep hUH hU hstep
  have hHL := normalizer_left hstep
  have hCQ := cSecIn_eq_pCoreOf_of_noncentral hq hUH hU hstep hnc
  have hk : φ.ker ≤ (cSecIn H L N).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQC ((hφk x).mp hx))
  have hirr := secModule_isIrred_of_isChiefStep hs φ hφs hk hstep
  have hnt : ∃ σ w, (secModule hs φ hφs hk).act σ w ≠ w := by
    by_contra hall
    push Not at hall
    refine hnc fun g hg x hx => ?_
    have h1 : (secModule hs φ hφs hk).act (φ ⟨g, hg⟩) = 1 := by
      ext w
      rw [hall]
      rfl
    exact ((mem_cSecIn_iff hHL).mp ((secModule_act_eq_one_iff hs φ hφs hk ⟨g, hg⟩).mp h1)).2 x hx
  have hker : φ.ker = (cSecIn H L N).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, hφk, Subgroup.mem_subgroupOf, hCQ]
  refine ⟨hCQ, ?_⟩
  rcases hC5 _ hirr hnt with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact Or.inl (isModelSec_of_iso hs φ hφs hker e.symm)
  · exact Or.inr (isModelSec_of_iso hs φ hφs hker e.symm)

end CFSG.Quasithin.F53Mod
