module

public import CFSG.Quasithin.H13.L32AC43a

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

@[expose] noncomputable def autE (B : Subgroup G) : Subgroup (MulAut (Hat V H W)) :=
  (B.subgroupOf H).map C.act

theorem mem_pCoreOf_iff_comm (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {f : G} (hf : f ∈ T) :
    f ∈ pCoreOf 2 H ↔ ∀ u ∈ conjClosure V H, f * u * f⁻¹ * u⁻¹ ∈ W := by
  rw [← C.act_eq_one_iff_comm ⟨f, C.hTH hf⟩]
  refine ⟨fun h => C.act_eq_one_of_mem h, fun h1 => ?_⟩
  exact C.mem_pCoreOf_of_commute h1222 h1332 h1334 hf fun k hk => by rw [h1, one_mul, mul_one]

theorem isA2_autE (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    IsA2 C.act.range (C.autE B) :=
  C.toTopW.isA2_autOf hB fun _ hf h => (C.mem_pCoreOf_iff_comm h1222 h1332 h1334 (hBT hf)).mpr h

theorem index_fixV_autE_le (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    (fixV (C.autE B)).index ≤ Nat.card (C.autE B) ^ 2 :=
  C.toTopW.index_fixV_autOf_le hB fun _ hf h =>
    (C.mem_pCoreOf_iff_comm h1222 h1332 h1334 (hBT hf)).mpr h

theorem isQuadratic_autE {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) :
    IsQuadratic (C.autE B) :=
  C.toTopW.isQuadratic_autOf hB

end Top43

end CFSG.Quasithin.H13.L32A.C
