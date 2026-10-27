module

public import CFSG.Quasithin.H13.A6S1373
public import CFSG.Quasithin.H13.A6S1512

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Input1379Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → ¬ IsHatA6 L → S.G1 ∈ S.Hz →
    IsElemAbelian 2 (conjClosure S.V3 S.G1) → IsElemAbelian 2 (conjClosure V S.G1)

theorem stmt13_7_8_of_inputs (h1332 : Stmt13_3_2)
    (h13316 : Stmt13_3_16) (h1341 : Stmt13_4_1) (h13512 : Stmt13_5_12_six)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h1379 : Input1379Six) : Stmt13_7_8 := by
  intro G _ _ T L V hH hV hA6V hNS hNU
  have hZV : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra h
    exact hNS (h1341 G T L V hH hV h)
  obtain ⟨S⟩ := exists_setting4 h1332 h13316 hH
    (a6CentralQuotient_of_isA6On h1332 h13316 hH hV hA6V) hV hZV
  have hg1 : g1 T V = S.G1 := S.normalizer_V1
  have hcomm : IsMulCommutative ↥(conjClosure S.V3 S.G1) := by
    by_contra hna
    apply hNU
    refine h13512 G T L V hH hV hA6V hNS ?_
    rw [S.v3_eq, hg1]
    exact hna
  have hab : IsElemAbelian 2 (conjClosure S.V3 S.G1) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall
      (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) fun k hk v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hcomm.is_comm.comm
      ⟨w, HypF91.conjSub_le_conjClosure hk hw⟩ ⟨v, le_conjClosure _ _ hv⟩)
  rw [hg1]
  by_cases hM : S.G1 ≤ Subgroup.normalizer (L : Set G)
  ·
    have hle : conjClosure V S.G1 ≤ V :=
      conjClosure_le fun _ hg _ hv => S.conj_mem_V_of_le_M hM hg hv
    exact (F7.isElemAbelian_mono S.elemAbelian_V hle).1
  · have hG1 := S.G1_mem_Hz_of hM
    by_cases hhat : IsHatA6 L
    ·
      exact (S.isElemAbelian_VH_of_hat hNS h13315 h1356two hG1 hab hhat).1
    ·
      exact (h1379 G T L V S hNS hNU hhat hG1 hab).1

end CFSG.Quasithin.H13.A6
