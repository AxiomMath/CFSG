module

public import CFSG.Sporadic.Schreier.J1Order
public import CFSG.Sporadic.Schreier.CountSpec

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

variable {n : ℕ}

@[expose] def levTable (n : ℕ) (L : Level) (k : ℕ) : Table :=
  Array.ofFn (n := n) fun j => UInt32.ofNat (L.tr[k]!)[j.val]!

@[expose] def listTbl (n : ℕ) (l : List ℕ) : Table :=
  Array.ofFn (n := n) fun j => UInt32.ofNat (l.getD j 0)

section Chain

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ}

theorem levelTransversals_eq (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (i : Fin Q.baseCount) :
    levelTransversals Q i =
      (List.range (ChainArrays.lev n S base i).pts.size).map (ChainArrays.levT n S base i) := by
  obtain ⟨i, hi⟩ := i
  have hq := hA.orbitSearch_eq hF hi
  have ht := fun k (hk : k < (ChainArrays.lev n S base i).pts.size) =>
    hA.transversal_of_lt hF hi hk
  simp only [levelTransversals]
  rw [hq] at ht ⊢
  simp only [SchreierOrbitState.keys, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  rw [Function.comp_apply, Function.comp_apply, ht k (List.mem_range.1 hk), Option.getD_some]

theorem toTable_levT (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    {i k : ℕ} (hi : i < Q.baseCount) (hk : k < (ChainArrays.lev n S base i).pts.size) :
    toTable (ChainArrays.levT n S base i k) = levTable n (ChainArrays.lev n S base i) k := by
  have hrep := hA.rep_levT hF hi hk
  unfold toTable levTable
  congr 1
  funext j
  rw [hrep j]

theorem levelTables_eq (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
    {m : ℕ} (hm : Q.baseCount = m) :
    levelTables Q = (List.range m).map fun i =>
      (List.range (ChainArrays.lev n S base i).pts.size).map
        (levTable n (ChainArrays.lev n S base i)) := by
  subst hm
  rw [levelTables, List.map_map]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.length_map, List.length_finRange] at h1
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply]
  rw [levelTransversals_eq hA hF, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  rw [Function.comp_apply]
  exact toTable_levT hA hF h1 (List.mem_range.1 hk)

end Chain

theorem rep_listTbl (hn : n < 2 ^ 32) {l : List ℕ} (hl : isPermList n l = true) :
    Rep n (listTbl n l) (arrPerm n l) := by
  intro i hi
  rw [idx_of_lt _ hi, listTbl, ap_ofFn _ hi, UInt32.toNat_ofNat']
  have hget : l.getD i 0 = (arrPerm n l ⟨i, hi⟩ : ℕ) := (arrPerm_val hl ⟨i, hi⟩).symm
  rw [hget, Nat.mod_eq_of_lt ((arrPerm n l ⟨i, hi⟩).isLt.trans hn)]
  rfl

@[expose] def j1Levels : Array Level :=
  rawLevels 3080 J1Certificate.chain.strongArrs J1Certificate.chain.baseArr

@[expose] def j1Tables : List (List Table) :=
  (List.range 3).map fun i => (List.range (j1Levels[i]!).pts.size).map (levTable 3080 j1Levels[i]!)

theorem j1_baseCount
    {Q : RawSchreierDatum 3080} (hrec : J1Certificate.chain.Records Q) :
    Q.baseCount = 3 := by
  rw [← hrec.2.2.base_size]
  simp [ChainRecord.baseArr, j1_chain_base]

theorem j1_levelTables
    {Q : RawSchreierDatum 3080} (hrec : J1Certificate.chain.Records Q) :
    levelTables Q = j1Tables :=
  levelTables_eq hrec.2.2 (chainCheckFacts_of_chainRecordCheck j1_chain_check)
    (j1_baseCount hrec)

theorem rep_j1A1 : Rep 3080 (listTbl 3080 j1A1List) j1A1 := by
  rw [j1A1]
  exact rep_listTbl (by norm_num) isPermList_j1A1List

theorem rep_j1A2 : Rep 3080 (listTbl 3080 j1A2List) j1A2 := by
  rw [j1A2]
  exact rep_listTbl (by norm_num) isPermList_j1A2List

end CFSG.Sporadic.Schreier
