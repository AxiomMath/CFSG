module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6B3
public import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.Ree CFSG.LieType.Simplicity.TitsBits CFSG.LieType.Simplicity.TitsBits.Letter
  CFSG.StandardType.TableBF4TwoInputs

@[expose] def g0Word : List Letter :=
  [x 2, x 1, n 2, n 1, x 1, n 3, n 1, n 2, n 0, n 1, n 2, n 3]

theorem bits_g0Word :
    mul (mul (evalB g0Word) (mul (pack (eltBits 44)) (pack (eltBits 47))))
        (evalB g0Word.reverse) % 2 ^ 2704 =
      mul (mul (pack (eltBits 1)) (pack (eltBits 6)))
        (mul (pack (eltBits 7)) (pack (eltBits 14))) % 2 ^ 2704 := by
  decide +kernel

section Seeds

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orthRoot_three_mem_longRoots : TableBF4Two.orthRoot 3 ∈ ReeTag.F4.longRoots :=
  ⟨TableBF4Two.isRoot_orthRoot 3, ReeTag.lengthParam_eq_prime_iff.2 (by decide +kernel)⟩

theorem neg_orthRoot_three_mem_longRoots : -TableBF4Two.orthRoot 3 ∈ ReeTag.F4.longRoots :=
  ⟨CFSG.LieType.Chevalley.IsRoot.neg (TableBF4Two.isRoot_orthRoot 3),
    ReeTag.lengthParam_eq_prime_iff.2 (by decide +kernel)⟩

theorem exists_mulEquiv_nodeElt_eq_torusGen_zero :
    ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K, α (nodeElt K) = TableBF4Two.torusGen K 0 := by
  refine ⟨MulAut.conj (nElt K)⁻¹, ?_⟩
  have h := nWord_conj_rho_zero (K := K)
  change nElt K * TableBF4Two.torusGen K 0 * (nElt K)⁻¹ = nodeElt K at h
  rw [MulAut.conj_apply, ← h]
  group

theorem hasBits_graphAut_nodeElt [CharP K ReeTag.F4.prime] :
    HasBits K (ReeTag.F4.finiteExceptionalAut K (nodeElt K))
      (mul (pack (eltBits 44)) (pack (eltBits 47))) := by
  have hβ : IsRoot ReeTag.F4.tag (TableBF4Two.orthRoot 3) := TableBF4Two.isRoot_orthRoot 3
  have hβ' : IsRoot ReeTag.F4.tag (-TableBF4Two.orthRoot 3) := CFSG.LieType.Chevalley.IsRoot.neg hβ
  obtain ⟨-, -, -, hx, -⟩ := CFSG.RankThree.Chevalley.even_Chevalley_pinned_root_SL2_maps .F4 K hβ
  have e : nodeElt K =
      ⟨pinnedX ReeTag.F4.tag K (TableBF4Two.orthRoot 3) 1, pinnedX_mem_adjointGroup _ 1⟩ *
        ⟨pinnedX ReeTag.F4.tag K (-TableBF4Two.orthRoot 3) 1, pinnedX_mem_adjointGroup _ 1⟩ := by
    apply Subtype.ext
    rw [nodeElt, TableBF4Two.coe_rho, map_mul, (hx 1).1, (hx 1).2]
    rfl
  have hφ := (congrArg (ReeTag.F4.finiteExceptionalAut K) e).trans
    (((ReeTag.F4.finiteExceptionalAut K).map_mul _ _).trans
      (congrArg₂ (· * ·) (finiteExceptionalAut_pinnedX_long orthRoot_three_mem_longRoots 1)
        (finiteExceptionalAut_pinnedX_long neg_orthRoot_three_mem_longRoots 1)))
  rw [hφ]
  exact (hasBits_pinnedX (a := 44) (ReeTag.isRoot_dualRoot hβ) (by decide +kernel)
    (by decide +kernel)).mul
      (hasBits_pinnedX (a := 47) (ReeTag.isRoot_dualRoot hβ') (by decide +kernel)
        (by decide +kernel))

theorem exists_mulEquiv_nodeElt_eq_s0s1 :
    ∃ α : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      α (nodeElt K) = TableBF4Two.torusGen K 0 * TableBF4Two.torusGen K 1 := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  refine ⟨(graphAutF4 K).trans (MulAut.conj (evalG K g0Word)), ?_⟩
  have hy : HasBits K (TableBF4Two.torusGen K 0 * TableBF4Two.torusGen K 1)
      (mul (mul (pack (eltBits 1)) (pack (eltBits 6)))
        (mul (pack (eltBits 7)) (pack (eltBits 14)))) :=
    (hasBits_rho 0).mul (hasBits_rho 1)
  exact conj_eq_of_bits g0Word hasBits_graphAut_nodeElt hy bits_g0Word

end Seeds

end CFSG.StandardType.SmallExc.F4Two

end
