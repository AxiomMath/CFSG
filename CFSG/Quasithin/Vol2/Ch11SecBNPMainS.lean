module

public import CFSG.Quasithin.Vol2.Ch11SecBNPSyl
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1TwoAbs
public import CFSG.Quasithin.Background.E2TwoCLie
public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique

@[expose] def AS_p778_nParamS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H R : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T → InM T M →
    IsHStar T M H →
    (∀ K : Subgroup G, K ∈ cComp H → H = K ⊔ T → ¬ E2.E22LieCases H T (H ⊓ M) K) →
    R ≤ T → E1.nParam (R ⊔ oTwoUpper H) ≤ 1

theorem asP778NParamS_of_bound (hE22 : E2.E22StatementNoN)
    (hb : ∀ (G : Type) [Group G] [Finite G] (H T M K R : Subgroup G), T ≤ H → IsPGroup 2 T →
      K ∈ cComp H → H = K ⊔ T → E2.E22CasesNoN H T M K → ¬ E2.E22LieCases H T M K →
      SQTKGroup (E2.StarQuot M H) → R ≤ H → E1.nParam (R ⊔ oTwoUpper H) ≤ 1) :
    AS_p778_nParamS := by
  intro G _ _ T M H R hs hnab hK hT hM hH hlie hRT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  have hRH : R ≤ H := hRT.trans hTH
  set Y := R ⊔ oTwoUpper H with hYdef
  have hYH : Y ≤ H := sup_le hRH (oTwoUpper_le H)
  have hTi : ¬ 2 ∣ T.relIndex H := fun h2 =>
    hT.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))
  by_cases hNT : H ≤ Subgroup.normalizer (T : Set G)
  ·
    have hTS : IsSylowIn 2 T H := ⟨hTH, hT.1, hTi⟩
    have hTn : (T.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTH).mpr hNT
    refine nParam_le_one_of_normal_sylow (S := T ⊓ Y) (hT.1.to_le inf_le_left) inf_le_right ?_
      fun A hAY hA2 => le_inf (E1.le_of_isSylowIn_of_normal hTS hTn (hAY.trans hYH) hA2) hAY
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hNT (hYH hy)) x
    constructor
    · rintro ⟨hxT, hxY⟩
      exact ⟨h1.mp hxT, Y.mul_mem (Y.mul_mem hy hxY) (Y.inv_mem hy)⟩
    · rintro ⟨hxT, hxY⟩
      refine ⟨h1.mpr hxT, ?_⟩
      have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hxY) hy
      simpa [mul_assoc] using this
  ·
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hT
    have hmp : MinParabolic H T (H ⊓ M) := by
      refine ⟨⟨hTH, hT.1, hTi⟩, hNT, ?_⟩
      have hH' : IsHStar (S : Subgroup G) M H := hS ▸ hH
      have hTM : (S : Subgroup G) ≤ M := hS ▸ hM.2
      have := IsHStar.isUniqueMaxOver S hH' hTM
      rwa [hS] at this
    by_cases hsolv : Group.IsSolvable ↥H
    · have : Group.IsSolvable ↥Y :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYH)
      exact E1.solvable_nParam_le_one this
    · have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hH.1.2
      obtain ⟨⟨K, hKc, hHK, -, hcases⟩, hSQs⟩ := hE22 G H T (H ⊓ M) hmp hSQ hsolv
      exact hb G H T (H ⊓ M) K R hTH hT.1 hKc hHK hcases (hlie K hKc hHK) hSQs hRH

end CFSG.Quasithin.Vol2.Ch11.SecB
