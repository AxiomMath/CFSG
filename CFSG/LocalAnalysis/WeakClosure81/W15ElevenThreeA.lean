module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumann

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem U_le_qSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    U ≤ qSub15 M V₀ V U H P := by
  have hUO : U ≤ pCoreOf 2 H := c.hyp.fam.U_le_pCoreOf c.cex
  have hUKT : U ≤ kHull15 V₀ H ⊔ tSub15 M V₀ V U P := c.U_le_tSub15.trans le_sup_right
  have hp : IsPGroup 2 ((pCoreOf 2 H ⊓ (kHull15 V₀ H ⊔ tSub15 M V₀ V U P) : Subgroup G)) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hn : kHull15 V₀ H ⊔ tSub15 M V₀ V U P ≤
      normalizer ((pCoreOf 2 H ⊓ (kHull15 V₀ H ⊔ tSub15 M V₀ V U P) : Subgroup G) : Set G) :=
    (le_inf (c.kHull15_sup_tSub15_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (kHull15 V₀ H ⊔ tSub15 M V₀ V U P).le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := pCoreOf 2 H)
        (K := kHull15 V₀ H ⊔ tSub15 M V₀ V U P))
  exact (le_inf hUO hUKT).trans
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hn hp)

theorem v1Sub15_le_qSub15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    v1Sub15 V₀ U ≤ qSub15 M V₀ V U H P :=
  (Hyp1510.v1Sub15_le_iHull15 V₀ U H).trans c.iHull15_le_qSub15

end Cfg1511

namespace XData15

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem sup_le_centralizer_qSub15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    U ⊔ v1Sub15 V₀ U ≤ centralizer (qSub15 M V₀ V U H P : Set G) := by
  have hUV : U ⊔ v1Sub15 V₀ U ≤ V :=
    sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le)
  have hUI : U ⊔ v1Sub15 V₀ U ≤ iHull15 V₀ U H ⊔ U :=
    sup_le le_sup_right (le_sup_of_le_left (Hyp1510.v1Sub15_le_iHull15 V₀ U H))
  rw [Subgroup.le_centralizer_iff, c.qSub15_eq_sup hX]
  refine sup_le (fun i hi => ?_) ((c.cSub15_le_centralizer_V hX).trans ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact c.hyp.comm_iHull15_sup w (hUI hw) i (Subgroup.mem_sup_left hi)
  · exact Subgroup.centralizer_le hUV

theorem sup_le_zOmega15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    U ⊔ v1Sub15 V₀ U ≤ zOmega15 (qSub15 M V₀ V U H P) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hxQ : x ∈ qSub15 M V₀ V U H P := sup_le c.U_le_qSub15 c.v1Sub15_le_qSub15 hx
  have hxV : x ∈ V :=
    (sup_le c.cex.le ((v1Sub15_le_left V₀ U).trans c.cex.hyp.h6.le)) hx
  have hx2 : x ^ 2 = 1 := by
    rw [pow_two]
    exact CFSG.Open.IsElemAbelian.mul_self_eq_one c.cex.hyp.h6.elemAbelian hxV
  change x ∈ elemCenterIn 2 (qSub15 M V₀ V U H P)
  rw [mem_elemCenterIn_iff_centralizer]
  exact ⟨hxQ, hx2, fun j hj =>
    Subgroup.mem_centralizer_iff.1 (sup_le_centralizer_qSub15 c hX hx) j
      (elemThompsonIn_le 2 _ hj)⟩

end XData15

end CFSG.LocalAnalysis.WeakClosure81
