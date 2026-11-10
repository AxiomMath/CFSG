
module

public import CFSG.Sporadic.Co2Rank3.CheckBase
public import CFSG.Sporadic.Co2Cert.Order

@[expose] public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Co2Rank3.Native MulAction

structure Co2Rank3Facts : Prop where
  adj : adjOK 2300 co2OrigArrs co2Nbr co2DeltaList = true
  lev1 : Monster.B.Co2.Native.levelIdx co2StrongArrs co2BaseArr 1 = level1Idx
  lev2 : Monster.B.Co2.Native.levelIdx co2StrongArrs co2BaseArr 2 = level2Idx
  letters : stabWords.all (Monster.B.Co2.Native.lettersOK 11) = true
  fix : stabGens.all (fun g => g[0]! == 0 && g[3]! == 3) = true
  stab_size : stabGens.size = 3
  p0 : recOK lev1Gens p0Rec p0Roots = true
  stab : recOK stabGens stabRec stabRoots = true
  p01 : recOK lev2Gens p01Rec p01Roots = true
  loc36 : p0Rec.1[36]! = 3
  loc4 : p0Rec.1[4]! = 3
  loc5 : p0Rec.1[5]! = 3
  loc2 : p0Rec.1[2]! = 1
  loc8 : p0Rec.1[8]! = 1
  delta : listLabelOK 2300 co2DeltaList p0Rec.1 [3] = true
  nbr3 : listLabelOK 2300 co2Nbr[3]! stabRec.1 [0, 36, 4, 2] = true
  nbr1 : listLabelOK 2300 co2Nbr[1]! p01Rec.1 [4, 2] = true
  colour : colourLabelOK 2300 (co2ColourT 2) stabRec.1 [0, 1, 2, 3, 4, 5, 36] = true
  bounds : CFSG.Sporadic.FischerOddCore.Native.boundsOK 2300 co2Nbr
    (CFSG.Monster.B.Co2.Native.idA 2300) refineBase refineBounds 3 = true
  common3 : commonCount co2Nbr[0]! co2Nbr[3]! = 378
  common1 : commonCount co2Nbr[0]! co2Nbr[1]! = 324

theorem getElem!_toArray_map {α : Type*} {l : List α} {f : α → Array ℕ} {d : α} {k : ℕ}
    (hk : k < l.length) : ((l.map f).toArray)[k]! = f (l.getD k d) := by
  rw [getElem!_pos _ k (by simpa using hk), List.getD_eq_getElem _ _ hk]
  simp

theorem setOf_exists_getD {α : Type*} (l : List ℕ) (f : ℕ → α) :
    {g | ∃ k < l.length, f (l.getD k 0) = g} = {g | ∃ j ∈ l, f j = g} := by
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hj
    exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem co2Q_base_toList : co2Q.base.toList = [0, 1, 2, 3, 5, 4] :=
  List.map_injective_iff.2 Fin.val_injective (by rw [co2Q_base]; rfl)

theorem strongAt_co2Q
    {j : ℕ} (hj : j < 11) : ChainArrays.strongAt co2Q j = co2Strong j := by
  rw [ChainArrays.strongAt_of_lt co2Q (by rw [co2Q_strongCount]; exact hj), co2Q_strong_get]

theorem co2Strong_mem
    {j : ℕ} (hj : j < 11) : co2Strong j ∈ co2P := by
  rw [← strongAt_co2Q hj, ChainArrays.strongAt_of_lt co2Q (by rw [co2Q_strongCount]; exact hj),
    ← co2Q_originalSubgroup]
  exact co2Q.strong_get_mem_originalSubgroup co2Q_valid.1 _

theorem rep_co2StrongInv
    {j : ℕ} (hj : j < 11) :
    Rep 2300 (rawInvs 2300 co2StrongArrs)[j]! (co2Strong j)⁻¹ := by
  rw [← strongAt_co2Q hj]
  exact co2Q_chainArrays.rep_strongInv (chainCheckFacts co2Chain_check.1)
    (by rw [co2StrongArrs_size]; exact hj)

theorem co2Q_levelGenerators
    {i : ℕ} (hi : i ≤ 6) :
    co2Q.levelGenerators i = (Monster.B.Co2.Native.levelIdx co2StrongArrs co2BaseArr i).map
      (ChainArrays.strongAt co2Q) :=
  co2Q_chainArrays.levelGenerators_eq (chainCheckFacts co2Chain_check.1)
    (by rw [co2Q_baseCount]; exact hi)

theorem co2Q_levelSubgroup_eq
    {i : ℕ} (hi : i ≤ 6) {l : List ℕ}
    (hl : Monster.B.Co2.Native.levelIdx co2StrongArrs co2BaseArr i = l) (hl11 : ∀ j ∈ l, j < 11) :
    co2Q.levelSubgroup i = Subgroup.closure {g | ∃ k < l.length, co2Strong (l.getD k 0) = g} := by
  rw [RawSchreierDatum.levelSubgroup, co2Q_levelGenerators hi, hl, setOf_exists_getD]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, (strongAt_co2Q (hl11 j hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, strongAt_co2Q (hl11 j hj)⟩

def co2P0 : Subgroup (Equiv.Perm (Fin 2300)) :=
  co2P ⊓ stabilizer (Equiv.Perm (Fin 2300)) (0 : Fin 2300)

def co2P01 : Subgroup (Equiv.Perm (Fin 2300)) :=
  co2P0 ⊓ stabilizer (Equiv.Perm (Fin 2300)) (1 : Fin 2300)

theorem co2Q_levelSubgroup_one :
    co2Q.levelSubgroup 1 = co2P0 := by
  ext g
  rw [co2Q.mem_levelSubgroup_iff co2Q_valid.1 1 (by rw [co2Q_baseCount]; norm_num),
    co2Q_originalSubgroup, co2Q_base_toList, co2P0, Subgroup.mem_inf, mem_stabilizer_iff]
  simp

theorem co2Q_levelSubgroup_two :
    co2Q.levelSubgroup 2 = co2P01 := by
  ext g
  rw [co2Q.mem_levelSubgroup_iff co2Q_valid.1 2 (by rw [co2Q_baseCount]; norm_num),
    co2Q_originalSubgroup, co2Q_base_toList, co2P01, co2P0, Subgroup.mem_inf, Subgroup.mem_inf,
    mem_stabilizer_iff, mem_stabilizer_iff]
  simp [and_assoc]

theorem rep_lev1 {k : ℕ} (hk : k < lev1Gens.size) :
    Rep 2300 lev1Gens[k]! (co2Strong (level1Idx.getD k 0)) := by
  have hk' : k < level1Idx.length := by simpa [lev1Gens] using hk
  rw [lev1Gens, getElem!_toArray_map (d := 0) hk']
  have hmem : level1Idx.getD k 0 ∈ level1Idx := by
    rw [List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  exact rep_co2Strong ((by decide : ∀ j ∈ level1Idx, j < 11) _ hmem)

theorem rep_lev2 {k : ℕ} (hk : k < lev2Gens.size) :
    Rep 2300 lev2Gens[k]! (co2Strong (level2Idx.getD k 0)) := by
  have hk' : k < level2Idx.length := by simpa [lev2Gens] using hk
  rw [lev2Gens, getElem!_toArray_map (d := 0) hk']
  have hmem : level2Idx.getD k 0 ∈ level2Idx := by
    rw [List.getD_eq_getElem _ _ hk']
    exact List.getElem_mem hk'
  exact rep_co2Strong ((by decide : ∀ j ∈ level2Idx, j < 11) _ hmem)

def co2StabGen (k : ℕ) : Equiv.Perm (Fin 2300) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 11 => co2Strong h)
    (toLetters 11 (stabWords.getD k []))

theorem co2StabGen_mem
    (k : ℕ) : co2StabGen k ∈ co2P := by
  refine (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact co2Strong_mem h.2

def co2N : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {g | ∃ k < stabGens.size, co2StabGen k = g}

end CFSG.Sporadic.Co2Rank3
