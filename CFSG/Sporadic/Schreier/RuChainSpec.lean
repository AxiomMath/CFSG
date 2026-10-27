
module

public import CFSG.Sporadic.Schreier.RuCheckChainsInputs

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem ruFinList_map_val (n : ℕ) (hn : 0 < n) (b : List ℕ) :
    ((ruFinList n hn b).map Fin.val).toArray = ruBaseArr n b := by
  simp [ruFinList, ruBaseArr, Function.comp_def]

section Generic

variable {n : ℕ} {hn : 1 ≤ n} {hpos : 0 < n} {S : Array (Array ℕ)} {k s : ℕ} {hk : k ≤ S.size}
  {b : List ℕ} {hb : (ruFinList n hpos b).Nodup} {D : List (List ℤ)}

theorem ruChain_arrays (h : ruChainOK n S k s b D = true) :
    ChainArrays (RawSchreierDatum.ofArrays n hn S k hk (ruFinList n hpos b) hb (ruWordsArr k s D))
      (S.extract 0 k) S (ruBaseArr n b) (ruWordsArr k s D) := by
  have hF := chainCheckFacts (n := n) (chunks := 4) h
  have hA := chainArrays_ofArrays (n := n) (hn := hn) (k := k) (hk := hk)
    (base := ruFinList n hpos b) (hb := hb) (W := ruWordsArr k s D) hF.strong_inv
  rwa [ruFinList_map_val n hpos b] at hA

theorem ruChain_valid (h : ruChainOK n S k s b D = true) :
    ValidSchreier (RawSchreierDatum.ofArrays n hn S k hk (ruFinList n hpos b) hb
      (ruWordsArr k s D)) :=
  (validSchreier_of_chainOK (ruChain_arrays h) (by norm_num) h).1

theorem ruChain_card (h : ruChainOK n S k s b D = true) :
    Nat.card (RawSchreierDatum.ofArrays n hn S k hk (ruFinList n hpos b) hb
      (ruWordsArr k s D)).originalSubgroup = (rawOrbitSizes n S (ruBaseArr n b)).prod :=
  card_originalSubgroup_of_chainOK (ruChain_arrays h) (by norm_num) h

theorem ruChain_sift (h : ruChainOK n S k s b D = true) {t : Array ℕ}
    {G : Equiv.Perm (Fin n)} (hG : Rep n t G) :
    ruSift n S b t = true ↔ G ∈ (RawSchreierDatum.ofArrays n hn S k hk (ruFinList n hpos b) hb
      (ruWordsArr k s D)).originalSubgroup :=
  siftA_iff_mem_originalSubgroup (ruChain_arrays h) (by norm_num) h hG

theorem ruChain_strong_inv (h : ruChainOK n S k s b D = true) {j : ℕ} (hj : j < S.size) :
    isInvA n S[j]! (invCand n S[j]!) = true := by
  have := (chainCheckFacts (n := n) (chunks := 4) h).strong_inv j hj
  have e : (rawInvs n S)[j]! = invCand n S[j]! := by
    rw [rawInvs, getElem!_pos (Array.map (invCand n) S) j (by simpa using hj), Array.getElem_map,
      getElem!_pos S j hj]
  rwa [e] at this

end Generic

theorem ofArrays_original_toList {n : ℕ} {hn : 1 ≤ n} {S : Array (Array ℕ)} {k : ℕ}
    {hk : k ≤ S.size} {base : List (Fin n)} {hb : base.Nodup} {W : Array (List ℤ)} :
    (RawSchreierDatum.ofArrays n hn S k hk base hb W).original.toList =
      (List.range k).map fun i => permOfArr n S[i]! := by
  change (Vector.ofFn fun i : Fin k => permOfArr n S[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn]
  apply List.ext_getElem <;> simp

end CFSG.Sporadic.RuSchreier
