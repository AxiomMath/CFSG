module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Index
public import CFSG.RankThree.GF2n.Stroth80.Sec311bNatData
public import CFSG.RankThree.GF2n.Stroth80.Sec91

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem relIndex_LB_CN (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) :
    (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 := by
  classical
  have hs5 := hs.toSec5
  have hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B := sec9_notQB h34 hs
  obtain ⟨K, fK, finK, hK, φ, hφ, hker, hnorm, hn, ψ, hψ⟩ := hs.plus4
  haveI := hn
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK.trans he)
  have hq4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨c0, hc0, hc1⟩ := exists_ne_zero_ne_one_of_nat_card_ge_four hq4
  haveI : Nonempty (Fin 2 ⊕ Fin 2) := ⟨Sum.inl 0⟩
  have h3 : 3 ≤ Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hQ := nondegenerate_polarBilin_quadPlus 2 K
  obtain ⟨u, hQu, hu0, -, -, hLeq⟩ := hc.omega_points_flag h34 hs5 hnotQB hK
    (ElemMatrixIso.ofStated (coe_quadPlus 2 K)
      (Classify.commutator_orthogonalGroup_quadPlus_two K hc0 hc1)) hQ h3
    (addCommutantScalar_statedOmegaPlus_two ⟨c0, hc0, hc1⟩) φ hφ hker ψ hψ
  rw [← HS6.card_map_LB_eq_relIndex hc hs5.mem φ hker, hLeq,
    ElemMatrixIso.card_LomGL _ hQ hQu hu0, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin, hK]

end HS9

end CFSG.RankThree.GF2n.Stroth80
