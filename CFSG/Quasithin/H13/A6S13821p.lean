module

public import CFSG.Quasithin.H13.A6S13822b
public import CFSG.Quasithin.H13.A6S13824h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_transv_or_quad
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    (∃ x ∈ pCoreOf 2 (S.L1 ⊔ T), InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) ∨
      ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (S.L1 ⊔ T) ∧ ⁅⁅conjClosure S.V3 H, Y⁆, Y⁆ = ⊥ ∧
        4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y := by
  have hF := hS.hF H hH
  by_cases hA : ∃ x ∈ pCoreOf 2 (S.L1 ⊔ T),
      InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)
  · exact Or.inl hA
  right
  push Not at hA
  obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle⟩ := S.case2_of_no_transv_loc hF hA
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS H hH K hK hKn hHK γ γ' g s
    (conjClosure S.V3 H) le_rfl hDH.not_ge
  have hm := S.lem13818Four_loc hS.hNS h13315 h1356two hH hF h13314 hA s hDγ hDH hle hgen
  obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF s
  refine ⟨conjSub c (F8.Uγ V H (g : G)), hcR, ?_, ?_⟩
  · have h1 := congrArg (conjSub c) (S.comm_comm_UH_Vγ hF s)
    rwa [← conjSub_commutator, ← conjSub_commutator,
      conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 H hcH), conjSub_bot] at h1
  · have hY2 : IsPGroup 2 (conjSub c (F8.Uγ V H (g : G))) :=
      (pCoreOf_isPGroup 2 _).to_le hcR
    rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
    have hQ : conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
      conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
    rw [← hQ, ← conjSub_inf, F9.mIdx_conjSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) :=
        Nat.pow_le_pow_right (by norm_num) hm

end Setting4

end CFSG.Quasithin.H13.A6
