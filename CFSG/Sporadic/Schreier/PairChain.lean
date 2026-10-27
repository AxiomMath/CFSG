module

public import CFSG.Sporadic.Schreier.PairWords
public import CFSG.Certificates.NativeSchreierEnum

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative

variable {n : ℕ}

theorem map_val_finRange (m : ℕ) : (List.finRange m).map Fin.val = List.range m := by
  apply List.ext_getElem (by simp)
  intro k _ _
  simp

theorem baseFaithful_of_valid {Q : RawSchreierDatum n} (hQ : ValidSchreier Q) :
    BaseFaithful Q.originalSubgroup (Q.base.toList.map Fin.val) := by
  intro h hh hfix
  have hmem : h ∈ Q.levelSubgroup Q.baseCount := by
    rw [Q.mem_levelSubgroup_iff hQ Q.baseCount le_rfl]
    refine ⟨hh, fun b hb => hfix b ?_⟩
    rw [List.take_of_length_le (by simp)] at hb
    exact List.mem_map_of_mem hb
  rw [Q.levelSubgroup_terminal_eq_bot hQ] at hmem
  exact hmem

@[expose] def levList (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (i : ℕ) :
    List (Equiv.Perm (Fin n)) :=
  (List.range (lev n S base i).pts.size).map (levT n S base i)

section Facts

variable {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
  {chunks : ℕ} (hA : ChainArrays Q O S base W) (hF : ChainCheckFacts n O S base W chunks)
include hA hF

theorem pairChain_levelTransversals_eq (i : Fin Q.baseCount) :
    levelTransversals Q i = levList n S base i := by
  obtain ⟨i, hi⟩ := i
  have hkeys : (Q.orbitSearch ⟨i, hi⟩).keys =
      (List.range (lev n S base i).pts.size).map (levPts Q S base i) := by
    rw [hA.orbitSearch_eq hF hi]
    simp [SchreierOrbitState.keys]
  unfold levelTransversals levList
  simp only
  rw [hkeys, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  rw [Function.comp_apply, hA.transversal_of_lt hF hi (List.mem_range.1 hk), Option.getD_some]

theorem enumeration_eq :
    enumeration Q = products ((List.range Q.baseCount).map (levList n S base)) := by
  rw [enumeration]
  congr 1
  rw [← map_val_finRange, List.map_map]
  exact List.map_congr_left fun i _ => pairChain_levelTransversals_eq hA hF i

theorem levT_mem_original (hQ : ValidSchreier Q) {i k : ℕ} (hi : i < Q.baseCount)
    (hk : k < (lev n S base i).pts.size) : levT n S base i k ∈ Q.originalSubgroup := by
  rw [← Q.levelSubgroup_zero_eq_original hQ]
  exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) (hA.levT_mem hF hi hk)

theorem forall₂_levelArr {i : ℕ} (hi : i < Q.baseCount) :
    List.Forall₂ (Rep n) (levelArr (rawLevels n S base) i).toList (levList n S base i) := by
  have e : (levelArr (rawLevels n S base) i).toList =
      (List.range (lev n S base i).pts.size).map fun k => (lev n S base i).tr[k]! := by
    rw [levelArr, Array.toList_ofFn, List.ofFn_eq_map, ← map_val_finRange, List.map_map]
    rfl
  rw [e, levList, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun k hk => ?_
  exact hA.rep_levT hF hi (List.mem_range.1 hk)

theorem repBlocks_blocksOf {groups : List (List ℕ)}
    (hg : ∀ g ∈ groups, ∀ i ∈ g, i < Q.baseCount) :
    RepBlocks n (blocksOf n (rawLevels n S base) groups)
      (groups.map fun g => products (g.map (levList n S base))) := by
  rw [RepBlocks, blocksOf, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.2 fun g hgm => repBlock_blockOf ?_
  rw [RepBlocks, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun i hi => forall₂_levelArr hA hF (hg g hgm i hi)

theorem mem_of_mem_blocks (hQ : ValidSchreier Q) {groups : List (List ℕ)}
    (hg : ∀ g ∈ groups, ∀ i ∈ g, i < Q.baseCount) :
    ∀ G ∈ groups.map (fun g => products (g.map (levList n S base))), ∀ t ∈ G,
      t ∈ Q.originalSubgroup := by
  intro G hG t ht
  obtain ⟨g, hgm, rfl⟩ := List.mem_map.1 hG
  refine mem_of_mem_products Q.originalSubgroup.toSubmonoid _ ?_ t ht
  intro T hT u hu
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hT
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hu
  exact levT_mem_original hA hF hQ (hg g hgm i hi) (List.mem_range.1 hk)

end Facts

theorem card_eq_countW {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W) (hc : 0 < chunks)
    (h : rawChainOK n O S base W chunks = true) {groups : List (List ℕ)}
    (hg : groups.flatten = List.range Q.baseCount) {f : List (Array ℕ) → Bool}
    {Pr : Equiv.Perm (Fin n) → Prop} [DecidablePred Pr]
    (hfP : ∀ w g, RepW n w g → g ∈ Q.originalSubgroup → (f w = true ↔ Pr g)) :
    Nat.card {x : Q.originalSubgroup // Pr x} =
      countW f (blocksOf n (rawLevels n S base) groups) [] := by
  have hF := chainCheckFacts h
  have hQ := (validSchreier_of_chainOK hA hc h).1
  have hgi : ∀ g ∈ groups, ∀ i ∈ g, i < Q.baseCount := fun g hgm i hi => by
    have : i ∈ groups.flatten := List.mem_flatten.2 ⟨g, hgm, hi⟩
    rw [hg] at this
    exact List.mem_range.1 this
  rw [card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ) Pr, enumeration_eq hA hF, ← hg, List.map_flatten,
    ← products_map_products, List.map_map,
    countW_spec_nil hfP (repBlocks_blocksOf hA hF hgi) (mem_of_mem_blocks hA hF hQ hgi)]
  rfl

end CFSG.Sporadic.Schreier
