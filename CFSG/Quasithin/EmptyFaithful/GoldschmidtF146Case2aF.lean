module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aE
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverB

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem case2a_bq {T M H K : Subgroup G}
    (hmin : MinParabolic H T (H ⊓ M)) (hK : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hker : ∀ x : G, x ∈ kerIn (H ⊓ M) H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H)
    {m : ℕ} (hBen : E2.IsBenderOf m ↥(E2.star (H ⊓ M) H K)) :
    IsBenderQuot m (OTwoQuot K) := by
  obtain ⟨π, hπ, hc, ho⟩ := (Case2a.Setting.mk hmin hK hHK hTK hker).exists_cover
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hK)
  have hperf : Group.IsPerfect (OTwoQuot K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective _)
  exact isBenderQuot_of_oddCover hperf π hπ hc ho hBen

end CFSG.Quasithin.F146Field
