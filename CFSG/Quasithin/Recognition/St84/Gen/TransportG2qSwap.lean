module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qVertexData
public import CFSG.Quasithin.Recognition.St84.Gen.TreeLLBase

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalMap
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeEquiv
import CFSG.Quasithin.Recognition.St84.Gen.TransportTreeLL

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

variable {H : Type} [Group H] [Finite H]

theorem f112ll_g2qLocalData_oTwoPrime_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qLocalData (X.L 1) (X.L 0) X.S f) :
    G2qLocalData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hdD : G2qLocalData (D.X.L 1) (D.X.L 0) D.X.S f := hd
  change G2qLocalData (oTwoPrime D.Pβ) (oTwoPrime D.Pα) (D.S ⊓ D.Ke) f
  refine G2qLocalData.of_mulEquiv (L1 := oTwoPrime D.Pβ) (L2 := oTwoPrime D.Pα)
    (S := D.S ⊓ D.Ke) (L1' := D.X.L 1) (L2' := D.X.L 0) (S' := D.X.S)
    (BaseEdgeData.equivOfB D).symm (BaseEdgeData.equivOfA D).symm ?_ ?_ hdD
  · exact f112ll_card_S_inf_K_of_tree hF hm hn h1 h2 hX0 hX1
  · exact (congrArg (fun K : Subgroup H => Nat.card K) (inf_comm _ _)).trans
      ((f112ll_card_pCoreOf_inf_of_tree hF hm hn h1 h2 hX0 hX1).trans
        (congrArg (fun K : Subgroup ↥D.E => Nat.card K) (inf_comm _ _)))

private theorem f112ll_gen_left_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qVertexData (X.L 1) (X.L 0) X.S f) {N : Subgroup H}
    (hZN : centerOf (pCoreOf 2 (oTwoPrime (f112saP1' L1 L2 S))) ≤ N)
    (hNQ : N ≤ pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)))
    (hNnorm : oTwoPrime (f112saP2' L1 L2 S) ≤ Subgroup.normalizer (N : Set H)) :
    N = pCoreOf 2 (oTwoPrime (f112saP2' L1 L2 S)) := by
  have hR : Hyp111R L1 L2 S := hyp111R_of_isL2Quot (by omega) (by omega) hF.1 h1 h2
  let D := f112EOddBaseEdgeData hF hR X hX0 hX1
  have hdD : G2qVertexData (D.X.L 1) (D.X.L 0) D.X.S f := hd
  have hZN' : centerOf (pCoreOf 2 (oTwoPrime D.Pα)) ≤ N := hZN
  have hNQ' : N ≤ pCoreOf 2 (oTwoPrime D.Pβ) := hNQ
  have hNnorm' : oTwoPrime D.Pβ ≤ Subgroup.normalizer (N : Set H) := hNnorm
  have hQαP : pCoreOf 2 (oTwoPrime D.Pα) ≤ f112P1 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pα)).trans
      ((oTwoPrime_le D.Pα).trans D.le_Pα)
  have hQβP₂ : pCoreOf 2 (oTwoPrime D.Pβ) ≤ f112P2 D.L1 D.L2 D.S :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (oTwoPrime D.Pβ)).trans
      ((oTwoPrime_le D.Pβ).trans D.le_Pβ)
  have hNP₂ : N ≤ f112P2 D.L1 D.L2 D.S := hNQ'.trans hQβP₂
  obtain ⟨N', hN'Q, hN'norm, hN'map⟩ := D.exists_comap_ofB_of_tree hNQ' hNnorm'
  have hZP₁ : centerOf (pCoreOf 2 (oTwoPrime D.Pα)) ≤ f112P1 D.L1 D.L2 D.S :=
    (inf_le_left : centerOf (pCoreOf 2 (oTwoPrime D.Pα)) ≤
      pCoreOf 2 (oTwoPrime D.Pα)).trans hQαP
  have hZP₂ : centerOf (pCoreOf 2 (oTwoPrime D.Pα)) ≤ f112P2 D.L1 D.L2 D.S :=
    hZN'.trans hNP₂
  have hZle : f112OfA D.L1 D.L2 D.S (centerOf (pCoreOf 2 (oTwoPrime D.Pα))) ≤
      f112OfB D.L1 D.L2 D.S N := by
    rw [ofA_subgroupOf_eq_ofB_subgroupOf D.L1 D.L2 D.S (le_inf hZP₁ hZP₂)]
    exact Subgroup.map_mono (f := (f112Gold D.L1 D.L2 D.S).ofB)
      (Subgroup.subgroupOf_mono (f112P2 D.L1 D.L2 D.S) hZN')
  have hcenterN' : centerOf (pCoreOf 2 (D.X.L 0)) ≤ N' := by
    intro c hc
    refine (Subgroup.mem_map_iff_mem D.E.subtype_injective).mp ?_
    have hmap : D.E.subtype c ∈ (centerOf (pCoreOf 2 (D.X.L 0))).map D.E.subtype :=
      Subgroup.mem_map.mpr ⟨c, hc, rfl⟩
    rw [D.centerOf_pCoreOf_L_zero_map] at hmap
    rw [hN'map]
    exact hZle hmap
  have hN'eq : N' = pCoreOf 2 (D.X.L 1) := hdD.gen_left N' hcenterN' hN'Q hN'norm
  have hle : pCoreOf 2 (oTwoPrime D.Pβ) ≤ N :=
    (D.le_iff_of_ofB_map_eq hQβP₂ hNP₂ D.pCoreOf_L_one_map hN'map).mp
      (le_of_eq hN'eq.symm)
  exact le_antisymm hNQ' hle

theorem f112ll_g2qVertexData_oTwoPrime_of_tree_swap {L1 L2 S : Subgroup H} {m n f : ℕ}
    (hF : F112HypW L1 L2 S) (hm : 2 ≤ m) (hn : 2 ≤ n) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (h2 : IsL2Quot n (oTwoQuot ↥L2))
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S)) (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : G2qVertexData (X.L 1) (X.L 0) X.S f) :
    G2qVertexData (oTwoPrime (f112saP2' L1 L2 S)) (oTwoPrime (f112saP1' L1 L2 S))
      (S ⊓ f112saK L1 L2 S) f :=
  { toG2qLocalData :=
      f112ll_g2qLocalData_oTwoPrime_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd.toG2qLocalData
    indec_left := f112ll_commutator_pCoreOf_P2'_of_tree hF hm hn h1 h2 hX0 hX1 hd.indec_left
    gen_left := fun N hZN hNQ hNnorm =>
      f112ll_gen_left_of_tree_swap hF hm hn h1 h2 hX0 hX1 hd hZN hNQ hNnorm }

end CFSG.Quasithin.F112R.St84

end
