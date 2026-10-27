module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case1C
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F146Field.Case1

variable {G : Type} [Group G] [Finite G]

theorem case1_equiv {T M H K : Subgroup G}
    (_hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H) (_hHK : H = K ⊔ T)
    (hker : kerIn (H ⊓ M) H = pCoreOf 2 H) :
    Nonempty (OTwoQuot K ≃* ↥(E2.star (H ⊓ M) H K)) := by
  have hKJ : K ⊓ kerIn (H ⊓ M) H = pCoreOf 2 K := by
    rw [hker]
    exact GoldS146R.inf_pCoreOf_eq_of_mem_cComp hK
  obtain ⟨e⟩ :=
    GoldS146R.nonempty_kbar_equiv_imgJ (J := kerIn (H ⊓ M) H) (le_of_mem_cComp hK) hKJ
  have hEq : CFSG.Open.pCore 2 ↥K = (pCoreOf 2 K).subgroupOf K :=
    (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hEq).trans e⟩

end CFSG.Quasithin.F146Field
