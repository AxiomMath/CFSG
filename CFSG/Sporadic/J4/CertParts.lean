module

import Mathlib.Tactic.IrreducibleDef
public import CFSG.Sporadic.J4.FaithSpec
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th CFSG.Perm.Native

noncomputable abbrev tbi0 : ByteArray := invTab nPts bs0.beta 3

noncomputable abbrev tx0 : Array (Array V2) := (locMats ()).map frTable

noncomputable abbrev txi0 : Array (Array V2) := (locInvs ()).map frTable

noncomputable abbrev zT (k : ℕ) : ByteArray := matTab bs0.keys bs0.slots nPts txi0[k]! 3

noncomputable abbrev O0 : VOrb := vorbit tx0 (rdV2 bs0.keys 24) 15180 15

noncomputable abbrev qIdx0 : Array ℕ :=
  (O0.pts.extract 0 qLen).map fun p => findIdx bs0.keys bs0.slots p - 1

noncomputable abbrev q00 : Array ℕ := qIdx0.push stripBase

noncomputable abbrev tS0 : Array V2 := frTable (sigRows (fsOf qIdx0))

noncomputable abbrev d0 : ByteArray := sigTable bs0.keys tS0 basisIdx 26

noncomputable abbrev letters0 : Array Th.Native.Table :=
  chainLetters 15180 (strongTables 15180 (tx0.map (posTable O0)) chainWords)

noncomputable irreducible_def trees0 : Array Tree := chainTrees 15180 letters0 chainBase

noncomputable abbrev O5 : VOrb := vorbit tx0 (rdV2 bs0.keys stripBase) stripOrbit 23

noncomputable abbrev o5idx : Array ℕ := O5.pts.map fun p => findIdx bs0.keys bs0.slots p - 1

noncomputable abbrev lev0 : Level := ⟨NatMap.ofKeys o5idx 23, O5.par, O5.lab, #[zT 0, zT 1, zT 2]⟩

noncomputable abbrev ts50 : Array (Array V2) := (stabMats ()).map frTable

noncomputable irreducible_def tg0 : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (Array ℕ) ℕ :=
  tupleGroup bs0.keys bs0.slots ts50 q00 stabOrder

noncomputable irreducible_def t20 : ByteArray × ByteArray := tree2 nPts bs0.alpha bs0.beta tbi0

noncomputable abbrev cpts0 : Array ℕ := pointsOfDepth nPts t20.2 cacheDepth

noncomputable abbrev pairs0 : Array ByteArray := mkPairs nPts bs0.alpha bs0.beta tbi0 3

noncomputable irreducible_def GD0 : GData :=
  ⟨nPts, bs0.alpha, bs0.beta, tbi0, t20.1, t20.2, q00, lev0, qLen, tg0.1, tg0.2.2.2, cacheDepth,
    NatMap.ofKeys cpts0 21, mkCache t20.1 bs0.alpha bs0.beta tbi0 q00 cpts0, pairs0⟩

noncomputable abbrev L0 : Labels :=
  labelPar nPts (zT 0) (zT 1) (zT 2) subReps subSizes.toArray labelGroups

structure J4NativeFacts : Prop where
  mat : MatFacts
  count : bs0.count = nPts
  orbit : orbitOK (frTable rowsA) (frTable rowsB) rootV bs0 nPts 3 = true
  inv : invOK32 nPts bs0.beta tbi0 3 = true
  z0 : matTabOK bs0.keys nPts txi0[0]! (zT 0) 3 = true
  z1 : matTabOK bs0.keys nPts txi0[1]! (zT 1) 3 = true
  z2 : matTabOK bs0.keys nPts txi0[2]! (zT 2) 3 = true
  o0 : vorbOK tx0 (rdV2 bs0.keys 24) O0 15180 = true
  qsize : qIdx0.size = qLen
  q : (List.range qLen).all (fun t => decide (qIdx0[t]! < nPts) &&
    (rdV2 bs0.keys qIdx0[t]!).beq O0.pts[t]!) = true
  sig : uniqueSigOK bs0.keys nPts tS0 basisIdx 26 d0 3 = true
  bsize : basisIdx.size = 112
  blt : basisIdx.all (· < nPts) = true
  basis : eqRows (mulRows basisRows (invRows basisRows)) idRows = true
  chain : chainOK 15180 letters0 chainBase (Array.range qLen) chainBase trees0 3 = true
  sizes : orbitSizes trees0 = chainSizes
  tg : tupleGroupOK bs0.keys nPts ts50 q00 tg0.1 tg0.2.1 tg0.2.2.1 = true
  tgsize : tg0.1.size = stabOrder
  tree : treeOK nPts bs0.alpha bs0.beta tbi0 t20.1 t20.2 3 = true
  pairs : pairsOK nPts bs0.alpha bs0.beta tbi0 pairs0 3 = true
  global : globalOK GD0 3 = true
  label : labelOK nPts (zT 0) (zT 1) (zT 2) L0 3 = true
  reps : (L0.reps == subReps) = true
  counts : ((countLab nPts 7 L0).toList == subSizes) = true

private theorem of_ite {c r : Bool} (h : (if (!c) = true then false else r) = true) :
    c = true ∧ r = true := by
  cases c <;> simp_all

private theorem of_ite_none {c : Bool} {r o : Option StoreOut}
    (h : (if (!c) = true then none else r) = o) (ho : o.isSome) : c = true ∧ r = o := by
  cases c with
  | false =>
    simp only [Bool.not_false, ite_true] at h
    subst h
    simp at ho
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h
    exact ⟨rfl, h⟩

private theorem of_andThen {o : Option StoreOut} {f : StoreOut → Bool} (h : andThen o f = true) :
    ∃ S, o = some S ∧ f S = true := by
  cases o with
  | none => simp [andThen] at h
  | some S => exact ⟨S, rfl, h⟩

private theorem storeOut_fields {S : StoreOut} {tbi z0 z1 z2 : ByteArray} {q0 : Array ℕ}
    {lev : Level} {tup : Array (Array ℕ)} {tmap : Std.HashMap (Array ℕ) ℕ}
    (h : S = ⟨tbi, z0, z1, z2, q0, lev, tup, tmap⟩) :
    S.tbi = tbi ∧ S.z0 = z0 ∧ S.z1 = z1 ∧ S.z2 = z2 ∧ S.q0 = q0 ∧ S.lev = lev ∧ S.tup = tup ∧
      S.tmap = tmap := by
  subst h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem j4Facts_of (h : j4Cert 3 = true) : J4NativeFacts := by
  unfold j4Cert at h
  obtain ⟨hm, h⟩ := of_ite h
  dsimp only at h
  obtain ⟨ho, h⟩ := of_ite h
  rw [Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨S, hS, h⟩ := of_andThen h
  have hs : (some S).isSome := rfl
  unfold storeChecks at hS
  dsimp only at hS
  obtain ⟨h1, hS⟩ := of_ite_none hS hs
  unfold stZ at hS
  dsimp only at hS
  obtain ⟨h2, hS⟩ := of_ite_none hS hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at h2
  unfold stO0 at hS
  dsimp only at hS
  obtain ⟨h3, hS⟩ := of_ite_none hS hs
  obtain ⟨h4, hS⟩ := of_ite_none hS hs
  rw [Bool.and_eq_true, beq_iff_eq] at h4
  unfold stSig at hS
  dsimp only at hS
  obtain ⟨h5, hS⟩ := of_ite_none hS hs
  obtain ⟨h6, hS⟩ := of_ite_none hS hs
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at h6
  unfold stChain at hS
  dsimp only at hS
  obtain ⟨h7, hS⟩ := of_ite_none hS hs
  rw [Bool.and_eq_true, beq_iff_eq] at h7
  unfold stO5 stTup at hS
  dsimp only at hS
  obtain ⟨h10, hS⟩ := of_ite_none hS hs
  rw [Bool.and_eq_true, beq_iff_eq] at h10
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := storeOut_fields (Option.some.inj hS).symm
  unfold finalChecks treeGlobal at h
  dsimp only at h
  obtain ⟨hlab, h⟩ := of_ite h
  obtain ⟨h11, h⟩ := of_ite h
  unfold stGlobal at h
  dsimp only at h
  obtain ⟨h13, h12⟩ := of_ite h
  unfold stLabel at hlab
  dsimp only at hlab
  simp -proj only [e1, e2, e3, e4, e5, e6, e7, e8] at hlab h11 h12 h13
  obtain ⟨hl, hc⟩ := Bool.and_eq_true_iff.mp hlab
  obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp hl
  have hGD : globalOK GD0 3 = true := by
    rw [← bs0_def, ← t20_def, ← tg0_def] at h12
    rw [GD0_def]
    exact h12
  clear h12
  simp only [← bs0_def, ← trees0_def, ← tg0_def, ← t20_def] at *
  exact ⟨matFacts_of hm, ho.1, ho.2, h1, h2.1.1, h2.1.2, h2.2, h3, h4.1, h4.2, h5, h6.1.1,
    h6.1.2, h6.2, h7.1, h7.2, h10.1, h10.2, h11, h13, hGD, hl, hr, hc⟩

end CFSG.Sporadic.J4
