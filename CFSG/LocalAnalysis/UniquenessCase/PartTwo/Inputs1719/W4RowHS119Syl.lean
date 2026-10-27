module

public import CFSG.Quasithin.Background.SmithB45ExcHS
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.HS119

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier


theorem isSylowIn_hsS_inf {R' : Subgroup (Equiv.Perm (Fin 3850))} (hPR : hsP ≤ R')
    (hRR : R' ≤ hsR) : CFSG.Quasithin.IsSylowIn 2 (hsS ⊓ R') R' := by
  have hSyl : CFSG.Quasithin.IsSylowIn 2 hsS hsR :=
    CFSG.Quasithin.isSylowIn_of_card_eq hs_involution_centralizers.1
      CFSG.Quasithin.B45Exc.HS.card_hsS_eq
  refine hSyl.inf_normal hRR ?_
  by_cases hRP : R' ≤ hsP
  · have hR' : R' = hsP := le_antisymm hRP hPR
    subst hR'
    exact Subgroup.normal_of_index_eq_two CFSG.Quasithin.B45Exc.HS.hsP_index_two
  · have hR' : R' = hsR := by
      refine le_antisymm hRR ?_
      obtain ⟨r, hr, hrP⟩ := Set.not_subset.1 hRP
      intro x hx
      by_cases hxP : x ∈ hsP
      · exact hPR hxP
      · have hmem := CFSG.Quasithin.B45Exc.HS.inv_mul_mem_hsP (hRR hr) hx hrP hxP
        have := R'.mul_mem hr (hPR hmem)
        rwa [mul_inv_cancel_left] at this
    subst hR'
    rw [Subgroup.subgroupOf_self]
    exact inferInstance

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row.HS119
