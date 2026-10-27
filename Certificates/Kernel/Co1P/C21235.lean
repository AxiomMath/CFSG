module

public import Certificates.Kernel.Co1P.C21158
public import Certificates.Kernel.Co1P.Chk21235
public import Certificates.Kernel.Co1P.Chk21235P
public import CFSG.Certificates.Kernel.Co1POrbSound
public import CFSG.Certificates.Kernel.Co1PPinSound

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1P

open CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.Co1P CFSG.KD.Co1P CFSG.KLie.CT CFSG.KC.TreeK
  CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Patterson.Native
  CFSG.Sporadic.Co1Patterson.TwistNative CertificateChecks.KernelCo1B

theorem actWord_append (a b : List Nat) (v : Nat) : actWord (a ++ b) v = actWord a (actWord b v) := by
  unfold actWord
  rw [List.foldr_append]

theorem wMat_cons (l : Nat) (u : List Nat) :
    wMat (l :: u) = (wMat u).map (actWord (genWords.getD l [])) := by
  unfold wMat expandWord
  rw [List.flatMap_cons, List.map_map]
  apply List.map_congr_left
  intro v _
  rw [Function.comp_apply, actWord_append]

theorem actWord_lt {w : List Nat} {v : Nat} (hv : v < 256) : actWord w v < 256 := by
  unfold actWord
  induction w with
  | nil => exact hv
  | cons j w ih =>
    rw [List.foldr_cons]
    unfold actW
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem fieldsK_wKey : ∀ M : List Nat, (∀ v ∈ M, v < 256) → fieldsK 8 M.length (wKey M) = M
  | [], _ => rfl
  | v :: M, h => by
    change List.cons (Nat.mod (wKey (v :: M)) (Nat.shiftLeft 1 8))
      (fieldsK 8 M.length (Nat.shiftRight (wKey (v :: M)) 8)) = v :: M
    have hv := h v List.mem_cons_self
    have e : wKey (v :: M) = v + 256 * wKey M := rfl
    have h1 : Nat.mod (wKey (v :: M)) (Nat.shiftLeft 1 8) = v := by
      rw [e, shiftLeft_one]
      change (v + 256 * wKey M) % 256 = v
      omega
    have h2 : Nat.shiftRight (wKey (v :: M)) 8 = wKey M := by
      rw [e]
      change (v + 256 * wKey M) >>> 8 = wKey M
      rw [Nat.shiftRight_eq_div_pow]
      omega
    rw [h1, h2, fieldsK_wKey M fun x hx => h x (List.mem_cons_of_mem v hx)]

theorem wMat_lt (u : List Nat) : ∀ v ∈ wMat u, v < 256 := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hv
  refine actWord_lt ?_
  simp only [w0Basis, List.mem_cons, List.mem_nil_iff, or_false] at hb
  omega

theorem wMat_len (u : List Nat) : (wMat u).length = 6 := by simp [wMat, w0Basis]

theorem tab_eq {l v : Nat} (hl : l < 2) (hv : v < 256) :
    fget (TWl l) v 8 = actWord (genWords.getD l []) v := by
  have h := CFSG.KC.TreeK.andB_true ((allN_iff _ _).1 tab_chk v hv)
  rcases l with _ | _ | l
  · exact Nat.eq_of_beq_eq_true h.1
  · exact Nat.eq_of_beq_eq_true h.2
  · omega

theorem actK_wMat {l : Nat} (hl : l < 2) (u : List Nat) :
    actK l (wKey (wMat u)) = wKey (wMat (l :: u)) := by
  unfold actK
  have := fieldsK_wKey (wMat u) (wMat_lt u)
  rw [wMat_len] at this
  rw [this, wMat_cons]
  congr 1
  exact List.map_congr_left fun v hv => tab_eq hl (wMat_lt u v hv)

theorem wordsOf_eq (T : Array Nat × Array Nat) :
    wordsOf T = foldPush T.1.size fun i acc => if i == 0 then [] else T.2[i]! :: acc[T.1[i]!]! := rfl

theorem innerWords_eq : innerWords = (wordsOf (treeArr recsW)).toList := by
  unfold innerWords recsW
  rw [treeOfMasks_eq]
  rfl

theorem kW_pin : ∀ i < 20160, pinAt actK (wKey w0Basis) kW recW i = true :=
  chunks_all (f := pinAt actK (wKey w0Basis) kW recW) (N := 20160) (nc := 315) (by decide)
    fun c hc => WPin.all c hc

theorem skW_all : ∀ s < 20160, keyAt 20160 64 skW ixW kW s = true :=
  chunks_all (f := keyAt 20160 64 skW ixW kW) (N := 20160) (nc := 315) (by decide)
    fun c hc => WKey.all c hc

theorem kW_walk {i : Nat} (hi : i < 20160) : kW i = walkAt actK 2 (wKey w0Basis) recsW i :=
  pin_walk wordsW_ok recsW_pin (by rw [recsW_len]; exact kW_pin) i (by rw [recsW_len]; exact hi)

theorem kW_lt (i : Nat) : kW i < 2 ^ 64 := by
  unfold kW tabK fget maskN pw2
  rw [shiftLeft_one]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.sub_lt (Nat.two_pow_pos 64) Nat.one_pos)

theorem kW_inj {i j : Nat} (hi : i < 20160) (hj : j < 20160) (e : kW i = kW j) : i = j := by
  obtain ⟨s, hs, rfl⟩ := ix_surj skW_all hi
  obtain ⟨t, ht, rfl⟩ := ix_surj skW_all hj
  have es := (keyAt_parts skW_all hs).2.2
  have et := (keyAt_parts skW_all ht).2.2
  rw [lowK_eq, Nat.mod_eq_of_lt (kW_lt _)] at es et
  have hst : s = t := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 := keys_mono skW_all s t h ht
      rw [es, et, e] at h1
      exact Nat.lt_irrefl _ h1
    · have h1 := keys_mono skW_all t s h hs
      rw [es, et, e] at h1
      exact Nat.lt_irrefl _ h1
  rw [hst]

theorem nodup_of_inj {L : List Nat} {f : Nat → Nat} {n : Nat} (hl : L.length = n)
    (hf : ∀ i < n, f i = L[i]?.getD 0) (hinj : ∀ i < n, ∀ j < n, f i = f j → i = j) : L.Nodup := by
  rw [List.nodup_iff_injective_get]
  intro ⟨i, hi⟩ ⟨j, hj⟩ e
  have hi' : i < n := by omega
  have hj' : j < n := by omega
  have ei := hf i hi'
  have ej := hf j hj'
  rw [List.getElem?_eq_getElem hi, Option.getD_some] at ei
  rw [List.getElem?_eq_getElem hj, Option.getD_some] at ej
  simp only [List.get_eq_getElem] at e
  exact Fin.ext (hinj i hi' j hj' (by rw [ei, ej, e]))

theorem walkW_nodup : (treePts actK 2 (wKey w0Basis) recsW).1.Nodup :=
  nodup_of_inj ((walk_length wordsW_ok).trans (by rw [recsW_len])) (fun _ hi => kW_walk hi)
    fun _ hi _ hj e => kW_inj hi hj e

theorem key_word {j : Nat} (hj : j < recsW.length + 1) :
    wKey (wMat (wordsOf (treeArr recsW))[j]!) = walkAt actK 2 (wKey w0Basis) recsW j := by
  have hok := wordsW_ok
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    rw [wordsOf_eq, foldPush_tree _ _ _ _ (by rw [treeArr_size]; exact hj) (fun hp => by
      rcases j with _ | j
      · omega
      · rw [treeArr_par (by omega)]
        exact Nat.lt_succ_of_le (walkAt_succ hok (by omega)).1)]
    rcases j with _ | j
    · simp only [↓reduceIte]
      rw [walkAt_zero hok]
      simp [wMat, w0Basis, actWord, expandWord]
    · have hj' : j < recsW.length := by omega
      obtain ⟨hp, hl, he⟩ := walkAt_succ hok hj'
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [← wordsOf_eq, treeArr_par hj', treeArr_lab hj', he, ← ih _ (by omega) (by omega),
        actK_wMat hl]

theorem keys_walk {arr : Array (List Nat)} {P : List Nat} (hlen : arr.size = P.length)
    (key : ∀ j, j < P.length → wKey (wMat arr[j]!) = P[j]?.getD 0) :
    arr.toList.map (fun u => wKey (wMat u)) = P := by
  apply List.ext_getElem (by rw [List.length_map, Array.length_toList, hlen])
  intro j h1 h2
  have hj2 : j < arr.size := by rw [hlen]; exact h2
  rw [List.getElem_map, Array.getElem_toList, ← getElem!_pos arr j hj2, key j h2,
    List.getElem?_eq_getElem h2]
  rfl

theorem inner_bfs : innerBfsOK = true := by
  have hP := walk_length wordsW_ok
  have hlen : (wordsOf (treeArr recsW)).size = (treePts actK 2 (wKey w0Basis) recsW).1.length := by
    rw [wordsOf_eq, foldPush_size, treeArr_size, hP]
  have key : ∀ j, j < recsW.length + 1 → wKey (wMat (wordsOf (treeArr recsW))[j]!) =
      ((treePts actK 2 (wKey w0Basis) recsW).1)[j]?.getD 0 := fun j hj => key_word hj
  have hkeys := keys_walk hlen (fun j hj => key j (by rw [← hP]; exact hj))
  rw [← innerWords_eq] at hkeys
  have hlW : innerWords.length = 20160 := by
    rw [← List.length_map (f := fun u => wKey (wMat u)), hkeys, hP, recsW_len]
  have hd : CFSG.Sporadic.Co1.InvNative.distinctKeys (innerWords.map fun u => wKey (wMat u)) = true := by
    rw [hkeys]
    exact distinctKeys_of_nodup walkW_nodup
  unfold innerBfsOK
  change (innerWords.length == 20160 &&
    CFSG.Sporadic.Co1.InvNative.distinctKeys (innerWords.map fun u => wKey (wMat u)) &&
    wVecs.all fun v => actWord [0, 0, 0, 0, 0, 0] v == v) = true
  rw [hlW, hd, vec_chk]
  rfl

theorem inner_orb : innerOrbOK = true := by
  obtain ⟨h1, h2⟩ := CFSG.KC.TreeK.andB_true orb_chk
  have hq : (ptSet orbQ).contains (unpackR 24 (wK 64)) = PQ.any fun y => eqK (wK 64) y := by
    rw [orbQ_eq, treeT_eq]
    exact contains_mkOrbT (fun l hl => brayArr_get hl) (fun l hl => brayInvArr_get hl)
      (brayTree_parts treeQ_ok).1 (brayTree_parts treeQ_ok).2 _
  unfold innerOrbOK
  rw [zRows, repRows_eq, yRow_W, show yBits.getD 0 0 = 1 from rfl, beq_unpack, h1, qRows_eq, hq, h2]
  rfl

open Certificates in
theorem c21235 : CFSG.Sporadic.Co1Patterson.Native.innerBfsOK = true ∧
    CFSG.Sporadic.Co1Patterson.Native.innerOrbOK = true := ⟨inner_bfs, inner_orb⟩

end CertificateChecks.KernelCo1P

end
