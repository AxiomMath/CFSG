module

public import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qBasic
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel

import CFSG.Quasithin.Recognition.St84.Gen.TransferU4qModule
import CFSG.Quasithin.Recognition.St84.Gen.TransferLeftCore
import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalLocal
import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Inner

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H] {L1 L2 S : Subgroup H} {m n f : ℕ}

theorem f112ll_u4q_mem_T_of_mem_trivOTwoQuot (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) {c : H} (hcS : c ∈ S)
    (hcα : c ∈ trivOTwoQuot (oTwoPrime (f112saP1' L1 L2 S)))
    (hcβ : c ∈ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S))) :
    c ∈ S ⊓ f112saK L1 L2 S := by
  have hindec : ⁅pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S)) := U4qLocalData.blockU_left hd
  rw [pCoreOf_oTwoPrime] at hindec
  exact f112ll_mem_T_of_commutator_mem_center_left hF hm hn h1 h2
    (f112ll_u4q_commutator_le_center_left hd) (f112ll_u4q_center_le_centralizer_left hd) hindec
    (f112ll_u4q_exists_torus_left hF hm hn h1 h2 hd) (f112ll_u4q_W_eq_bot hF hm hn h1 h2 hd)
    hcS hcα hcβ (f112ll_u4q_commutator_mem_center_left hF hm hn h1 h2 hd hcS hcα hcβ)

theorem f112ll_u4q_S_inf_trivOTwoQuot_right_le (hF : F112HypW L1 L2 S) (hm : 2 ≤ m)
    (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hd : U4qEdgeData L1 L2 S f) :
    S ⊓ trivOTwoQuot (oTwoPrime (f112saP2' L1 L2 S)) ≤ S ⊓ f112saK L1 L2 S := by
  classical
  let Lα := oTwoPrime (f112saP1' L1 L2 S)
  let Lβ := oTwoPrime (f112saP2' L1 L2 S)
  let Qα := pCoreOf 2 (f112saP1' L1 L2 S)
  let Qβ := pCoreOf 2 (f112saP2' L1 L2 S)
  let T := S ⊓ f112saK L1 L2 S
  intro c hc
  obtain ⟨hcS, hcβ⟩ := Subgroup.mem_inf.mp hc
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  have hSNα : S ≤ Subgroup.normalizer (f112saP1' L1 L2 S : Set H) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans
      (le_sup_right : bigB L1 L2 S ≤ f112P1 L1 L2 S)).trans
        (f112sa_P1_le_normalizer_P1' hF)
  have hTQ : T = Qβ ⊔ Qα := by
    change S ⊓ f112saK L1 L2 S = Qβ ⊔ Qα
    rw [← f112ll_pCoreOf_sup_eq hF hm hn h1 h2, sup_comm]
  have hQβT : Qβ ≤ T := by
    rw [hTQ]
    exact le_sup_left
  have hAT : Qβ ⊔ pCoreOf 2 Lα = T := by
    rw [hTQ, pCoreOf_oTwoPrime]
  obtain ⟨a, haQβ, ha⟩ :=
    exists_mul_inv_commutator_mem_pCoreOf_of_isL2Quot (L := Lα) (T := T) (A := Qβ)
      (f112ll_isL2Quot_oTwoPrime_P1' hF hm hn h1 h2)
      (f112sa_T_sylow_oTwoPrime_P1'_of_hyp111R hF hR) hQβT hAT
      (mem_normalizer_oTwoPrime (hSNα hcS))
      (f112ll_u4q_commute_pCoreOf_right hF hm hn h1 h2 hd hcS hcβ)
  have haT : a ∈ T := hQβT haQβ
  have haS : a ∈ S := (inf_le_left : T ≤ S) haT
  have haLα : a ∈ Lα := (hQβT.trans (f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR)) haQβ
  have haβ : a ∈ trivOTwoQuot Lβ := by
    refine pCoreOf_le_trivOTwoQuot Lβ ?_
    rw [pCoreOf_oTwoPrime]
    exact haQβ
  have hcaS : c * a⁻¹ ∈ S := S.mul_mem hcS (S.inv_mem haS)
  have hcaα : c * a⁻¹ ∈ trivOTwoQuot Lα := by
    refine mem_trivOTwoQuot.mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (mem_normalizer_oTwoPrime (hSNα hcS))
        (Subgroup.inv_mem _ (Subgroup.le_normalizer haLα))
    · intro l hl
      exact ha l hl
  have hcaβ : c * a⁻¹ ∈ trivOTwoQuot Lβ :=
    (trivOTwoQuot Lβ).mul_mem hcβ ((trivOTwoQuot Lβ).inv_mem haβ)
  have hcaT : c * a⁻¹ ∈ T :=
    f112ll_u4q_mem_T_of_mem_trivOTwoQuot hF hm hn h1 h2 hd hcaS hcaα hcaβ
  have hcEq : c = (c * a⁻¹) * a := by group
  rw [hcEq]
  exact T.mul_mem hcaT haT

end CFSG.Quasithin.F112R.St84

end
