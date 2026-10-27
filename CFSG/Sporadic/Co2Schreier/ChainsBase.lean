
module

public import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public import CFSG.Sporadic.Co2Schreier.Tuples
public import CFSG.Sporadic.Co2Cert.Order
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

structure WordFacts : Prop where
  invA : allInv aArrs = true
  invCInit : allInv cInitArrs = true
  invD : allInv dArrs = true
  invDStar : allInv dStarArrs = true
  invR : allInv rArrs = true
  invC : allInv cArrs = true
  invCStar : allInv cStarArrs = true
  invQ : allInv qArrs = true
  invS : allInv sArrs = true
  invW : isInvA 2300 wArr (invCand 2300 wArr) = true
  invH : isInvA 2300 hArr (invCand 2300 hArr) = true
  sizeA : aArrs.size = 2
  sizeCInit : cInitArrs.size = 2
  sizeD : dArrs.size = 2
  sizeDStar : dStarArrs.size = 7
  sizeR : rArrs.size = 10
  sizeC : cArrs.size = 2
  sizeCStar : cStarArrs.size = 9
  sizeQ : qArrs.size = 8
  sizeS : sArrs.size = 15
  eqC : ∀ k < 2, eqA 2300 localRec.chains.C.origArrs[k]! cArrs[k]! = true
  eqD : ∀ k < 2, eqA 2300 localRec.chains.D.origArrs[k]! dArrs[k]! = true
  eqS : ∀ k < 15, eqA 2300 localRec.chains.S.origArrs[k]! sArrs[k]! = true
  eqJoin : ∀ k < 4, eqA 2300 localRec.chains.join.origArrs[k]! (cArrs ++ dArrs)[k]! = true
  siftQ : ∀ k < 8, siftA 2300 levelsS localRec.chains.S.baseArr 0 qArrs[k]! = true
  siftR : ∀ k < 10, siftA 2300 levelsS localRec.chains.S.baseArr 0 rArrs[k]! = true
  siftZ : siftA 2300 levelsS localRec.chains.S.baseArr 0 zArr = true
  siftT : siftA 2300 levelsS localRec.chains.S.baseArr 0 tArr = true
  zSq : eqA 2300 (compA 2300 zArr zArr) (idA 2300) = true
  tSq : eqA 2300 (compA 2300 tArr tArr) (idA 2300) = true
  zNe : eqA 2300 zArr (idA 2300) = false
  tNe : eqA 2300 tArr (idA 2300) = false
  commZ : ∀ k < 2, commA cArrs[k]! zArr = true
  commT : ∀ k < 2, commA dArrs[k]! tArr = true

theorem aSeeds_length : aSeeds.length = 2 := rfl

theorem cInitTuple_length : cInitTuple.length = 2 := by
  rw [cInitTuple, List.length_map, localShape.cInit_length]

theorem dTuple_length : dTuple.length = 2 := by
  rw [dTuple, List.length_map, localShape.dWords_length]

theorem dStarTuple_length : dStarTuple.length = 7 := by
  rw [dStarTuple, extendTuple_length, dTuple_length, localShape.dDeriv_length]

theorem rTuple_length : rTuple.length = 10 := by
  rw [rTuple, List.length_map, localShape.rWords_length]

theorem cTuple_length : cTuple.length = 2 := by
  rw [cTuple, List.length_map, cInitTuple_length]

theorem cStarTuple_length : cStarTuple.length = 9 := by
  rw [cStarTuple, extendTuple_length, cTuple_length, localShape.cDeriv_length]

theorem qTuple_length : qTuple.length = 8 := by
  rw [qTuple, List.length_map, localShape.qWords_length]

theorem sTuple_length : sTuple.length = 15 := by
  rw [sTuple, List.length_append, qTuple_length, List.length_map, localShape.sWords_length]

theorem aSeeds_mem : ∀ g ∈ aSeeds, g ∈ co2P := by
  intro g hg
  simp only [aSeeds, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem cInitTuple_mem : ∀ g ∈ cInitTuple, g ∈ co2P := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordValue_mem _ _ aSeeds_mem w

theorem dTuple_mem : ∀ g ∈ dTuple, g ∈ co2P := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordValue_mem _ _ aSeeds_mem w

theorem locZ0_mem : locZ0 ∈ co2P := wordValue_mem _ _ cInitTuple_mem _

theorem dStarTuple_mem : ∀ g ∈ dStarTuple, g ∈ co2P :=
  extendTuple_mem co2P _ _ dTuple_mem

theorem rTuple_mem : ∀ g ∈ rTuple, g ∈ co2P := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordValue_mem _ _ dStarTuple_mem w

theorem locZ_mem : locZ ∈ co2P := wordValue_mem _ _ rTuple_mem _

theorem locT_mem : locT ∈ co2P := wordValue_mem _ _ dTuple_mem _

theorem locW_mem : locW ∈ co2P := wordValue_mem _ _ aSeeds_mem _

theorem locX_mem : locX ∈ co2P :=
  co2P.mul_mem (co2P.mul_mem locW_mem locZ0_mem) (co2P.inv_mem locW_mem)

theorem locH_mem : locH ∈ co2P :=
  co2P.mul_mem (co2P.pow_mem (co2P.mul_mem locX_mem locZ_mem) _)
    (co2P.pow_mem (co2P.mul_mem locZ0_mem locX_mem) _)

theorem cTuple_mem : ∀ g ∈ cTuple, g ∈ co2P := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
  exact co2P.mul_mem (co2P.mul_mem locH_mem (cInitTuple_mem x hx)) (co2P.inv_mem locH_mem)

theorem cStarTuple_mem_C : ∀ g ∈ cStarTuple, g ∈ locC :=
  extendTuple_mem locC _ _ fun _ hg => Subgroup.subset_closure hg

theorem qTuple_mem_C : ∀ g ∈ qTuple, g ∈ locC := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordValue_mem _ _ cStarTuple_mem_C w

theorem sTuple_mem_C : ∀ g ∈ sTuple, g ∈ locC := by
  intro g hg
  rcases List.mem_append.1 hg with hg | hg
  · exact qTuple_mem_C g hg
  · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact wordValue_mem _ _ cStarTuple_mem_C w

theorem dStarTuple_mem_D : ∀ g ∈ dStarTuple, g ∈ locD :=
  extendTuple_mem locD _ _ fun _ hg => Subgroup.subset_closure hg

theorem rTuple_mem_D : ∀ g ∈ rTuple, g ∈ locD := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact wordValue_mem _ _ dStarTuple_mem_D w

theorem locC_le_P : locC ≤ co2P := by
  rw [locC, Subgroup.closure_le]
  exact fun g hg => cTuple_mem g hg

theorem locD_le_P : locD ≤ co2P := by
  rw [locD, Subgroup.closure_le]
  exact fun g hg => dTuple_mem g hg

theorem locS_le_C : locS ≤ locC := by
  rw [locS, Subgroup.closure_le]
  exact fun g hg => sTuple_mem_C g hg

theorem locQ_le_C : locQ ≤ locC := by
  rw [locQ, Subgroup.closure_le]
  exact fun g hg => qTuple_mem_C g hg

theorem locR_le_D : locR ≤ locD := by
  rw [locR, Subgroup.closure_le]
  exact fun g hg => rTuple_mem_D g hg

theorem locS_le_P : locS ≤ co2P := locS_le_C.trans locC_le_P

theorem chainC_arrays :
    ChainArrays chainC localRec.chains.C.origArrs localRec.chains.C.strongArrs
    localRec.chains.C.baseArr localRec.chains.C.wordArrs := chainC_records.2.2

theorem chainD_arrays :
    ChainArrays chainD localRec.chains.D.origArrs localRec.chains.D.strongArrs
    localRec.chains.D.baseArr localRec.chains.D.wordArrs := chainD_records.2.2

theorem chainS_arrays :
    ChainArrays chainS localRec.chains.S.origArrs localRec.chains.S.strongArrs
    localRec.chains.S.baseArr localRec.chains.S.wordArrs := chainS_records.2.2

theorem chainJoin_arrays :
    ChainArrays chainJoin localRec.chains.join.origArrs
    localRec.chains.join.strongArrs localRec.chains.join.baseArr localRec.chains.join.wordArrs :=
  chainJoin_records.2.2

theorem chainJoin_le :
    localRec.chains.join.origArrs.size ≤ localRec.chains.join.strongArrs.size := by
  rw [localShape.chainJoin.origArrs_size, localShape.chainJoin.strongArrs_size]
  norm_num

theorem commA_iff {t u : Array ℕ} {g h : Equiv.Perm (Fin 2300)} (ht : Rep 2300 t g)
    (hu : Rep 2300 u h) : commA t u = true ↔ g * h = h * g :=
  eqA_iff (rep_compA ht hu) (rep_compA hu ht)

end CFSG.Sporadic.Co2Schreier
