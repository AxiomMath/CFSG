module

public import Certificates.Kernel.OmegaEight.Bridge3009
public import CFSG.Certificates.Kernel.J2CoverSound
public import Certificates.Kernel.OmegaEight.Pi416101Q
import CFSG.Certificates.Kernel.Child3Reps
import CFSG.Certificates.Kernel.Spor.PcompFacts
public import Certificates.Certificate3119

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.KC.J2Cover CFSG.ClassicalInvolution.Q3.TL4.Z2W.O8Pi
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native

theorem piGens_bind : (piGens ()).size = 4 ∧ ∀ j < 4, (piGens ())[j]! = unpack 360 9 (PI.S j) := by
  refine ⟨by simp [piGens, piIdx], fun j hj => ?_⟩
  have e : (piGens ())[j]! = genArrs[piIdx.getD j 0]! := by
    interval_cases j <;> simp [piGens, piIdx]
  have hi : piIdx.getD j 0 < 10 := by interval_cases j <;> decide
  rw [e, gen_get hi, Nat.eq_of_beq_eq_true (allN_spec kGenPI j hj)]

theorem piS_bind : (piS ()).size = 6 ∧ ∀ j < 6, (piS ())[j]! = unpack 360 9 (PI.S j) :=
  pushWords_eq piGens_bind PI.head

theorem bindsPI : Binds 360 9 PI.S 6 4 PI.BP (piS ()) ((piBase.map Fin.val).toArray) := by
  refine ⟨by norm_num, by norm_num, by norm_num, piS_bind.1, piS_bind.2, rfl, fun t ht => ?_⟩
  interval_cases t <;> rfl

theorem piChain_k : piChainCheck (piS ()) = true := by
  unfold piChainCheck
  rw [Bool.and_eq_true, wordsOf_eq]
  refine ⟨rawChainK_sound (chunks := 4) bindsPI PI.head PI.hl (by decide) PI.hs, ?_⟩
  rw [rawOrbitSizesK_sound bindsPI (perm_of_head PI.head) PI.hl]
  decide +kernel

theorem wPI_eq {wd : List Int} (h : lettersK 6 wd = true) :
    wordA 360 (piS ()) (rawInvs 360 (piS ())) wd = unpack 360 9 (wPI wd) :=
  (wordEqK_sound piS_bind (perm_of_head PI.head) (wordEqK_of h)).1

theorem tests_ok : ∀ c ∈ piTK, cn c = true ∧ pm c = true ∧ cn (pinv c) = true := by
  intro c hc
  have h := List.all_eq_true.1 kTests c hc
  simp only [bAnd_iff] at h
  exact h

theorem testA_eq : testA (piS ()) = piTK.map (unpack 360 9) := by
  have h1 := tests_ok (wPI [1, 2]) (by simp [piTK])
  unfold testA piTK
  simp only
  rw [wPI_eq (by decide +kernel), wPI_eq (by decide +kernel), invCand_pinv h1.2.1,
    compA_pc h1.2.2 (tests_ok (wPI [3, 6]) (by simp [piTK])).1]
  rfl

theorem ap_tab {X : Nat} (hX : cn X = true) (i : Nat) :
    ap (arrTable 360 (unpack 360 9 X)) i = pg9 X i := by
  obtain ⟨-, -, hz, hr⟩ := CFSG.KS.PF.canon_facts (m := mask 9) (nw := 360 * 9) hX
  rcases Nat.lt_or_ge i 360 with hi | hi
  · exact CFSG.KC.Child3.ap_tabP hi (by have := hr i hi; omega)
  · have h1 : ap (arrTable 360 (unpack 360 9 X)) i = 0 := by
      unfold ap
      rw [getElem!_neg _ i (by simp [arrTable]; omega)]
      rfl
    have h2 : pg9 X i = 0 := by
      unfold pg9 pg
      have e : Nat.mul 9 i = 360 * 9 + (9 * i - 360 * 9) := by change 9 * i = _; omega
      change Nat.land (X >>> Nat.mul 9 i) (mask 9) = 0
      rw [e, Nat.shiftRight_add, hz, Nat.zero_shiftRight]
      exact Nat.zero_and _
    rw [h1, h2]

theorem testT_eq : testT (piS ()) =
    piTests.map fun p => (arrTable 360 (unpack 360 9 p.1), arrTable 360 (unpack 360 9 p.2)) := by
  unfold testT piTests
  rw [testA_eq, List.map_map, List.map_map]
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp]
  rw [invCand_pinv (tests_ok c hc).2.1]

theorem all_eq_of {α : Type} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem ap_fun {X : Nat} (hX : cn X = true) : ap (arrTable 360 (unpack 360 9 X)) = pg9 X :=
  funext (ap_tab hX)

theorem pairB_eq {x y : Nat} (hx : cn x = true) (hy : cn y = true) :
    pairB (testT (piS ())) (arrTable 360 (unpack 360 9 x)) (arrTable 360 (unpack 360 9 y)) =
      pairBK piTests x y := by
  have hp : presB (arrTable 360 (unpack 360 9 x)) (arrTable 360 (unpack 360 9 y)) = presBK x y := by
    unfold presB presBK
    rw [ap_fun hx, ap_fun hy]
  have hq : q8Imgs (arrTable 360 (unpack 360 9 x)) (arrTable 360 (unpack 360 9 y)) = q8ImgsK x y := by
    unfold q8Imgs q8ImgsK
    rw [ap_fun hx, ap_fun hy]
  have hm : ((piTests.map fun p => (arrTable 360 (unpack 360 9 p.1),
      arrTable 360 (unpack 360 9 p.2))).all fun c =>
        movesB (q8ImgsK x y) (arrTable 360 (unpack 360 9 x)) (arrTable 360 (unpack 360 9 y)) c) =
      piTests.all (movesBK (q8ImgsK x y) x y) := by
    rw [List.all_map]
    apply all_eq_of
    intro p hp'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp'
    have h := tests_ok c hc
    unfold movesB movesBK conjImg conjImgK
    dsimp only [Function.comp]
    rw [ap_fun hx, ap_fun hy, ap_fun h.1, ap_fun h.2.2]
  unfold pairB pairBK
  rw [hp, hq, testT_eq, hm]

theorem sqList_eq :
    sqList (piS ()) = piSq.map (fun X => (arrTable 360 (unpack 360 9 X), sqKeyK X)) ∧
      ∀ X ∈ piSq, cn X = true := by
  have hf : ∀ X, canonK 360 9 (mask 9) (360 * 9) X = true →
      sqMoves (arrTable 360 (unpack 360 9 X)) = sqMovesK X := by
    intro X hX
    unfold sqMoves sqMovesK
    simp only [ap_tab hX]
  obtain ⟨e, hc⟩ := prodList_sound bindsPI (perm_of_head PI.head) PI.hl hf
  refine ⟨?_, hc⟩
  unfold sqList piSq
  rw [e, List.map_map]
  apply List.map_congr_left
  intro X hX
  simp only [Function.comp]
  unfold sqKey sqKeyK
  simp only [ap_tab (hc X hX)]

theorem grp_all {α β : Type} [DecidableEq β] [BEq β] [LawfulBEq β] (P : List (α × β))
    (F : α → α → Bool)
    (h : ∀ p ∈ P, ∀ q ∈ P, p.2 = q.2 → F p.1 q.1 = true) :
    ((P.map Prod.snd).dedup.all fun k =>
      ((P.filter fun p => p.2 == k).map Prod.fst).all fun x =>
        ((P.filter fun p => p.2 == k).map Prod.fst).all fun y => F x y) = true := by
  simp only [List.all_eq_true, List.mem_map, List.mem_filter, beq_iff_eq]
  rintro k - x ⟨p, ⟨hp, hpk⟩, rfl⟩ y ⟨q, ⟨hq, hqk⟩, rfl⟩
  exact h p hp q hq (hpk.trans hqk.symm)

theorem q8_pairs : ∀ x ∈ piSq, ∀ y ∈ piSq, sqKeyK x = sqKeyK y → pairBK piTests x y = true := by
  intro x hx y hy hk
  have hk' : kNat x = kNat y := by unfold kNat; rw [hk]
  have hmem : kNat x ∈ keysK := List.mem_dedup.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  have hc := q8_chunks (kNat x % 8) (Nat.mod_lt _ (by norm_num))
  unfold q8Part q8Chunk at hc
  have h := List.all_eq_true.1 hc (kNat x) (List.mem_filter.2 ⟨hmem, by simp⟩)
  simp only [List.all_eq_true, List.mem_filter, beq_iff_eq] at h
  exact h x ⟨hx, rfl⟩ y ⟨hy, hk'.symm⟩

theorem q8_k : q8Check (piS ()) = true := by
  obtain ⟨e, hc⟩ := sqList_eq
  have hP : ∀ p ∈ sqList (piS ()), ∀ q ∈ sqList (piS ()), p.2 = q.2 →
      pairB (testT (piS ())) p.1 q.1 = true := by
    rw [e]
    intro p hp q hq hpq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
    rw [pairB_eq (hc x hx) (hc y hy)]
    exact q8_pairs x hx y hy hpq
  unfold q8Check
  dsimp only
  generalize sqList (piS ()) = P at hP ⊢
  generalize testT (piS ()) = T at hP ⊢
  exact grp_all P (pairB T) hP

theorem check_k : check () = true := by
  unfold check
  simp only [Bool.and_eq_true]
  refine ⟨⟨piChain_k, ?_⟩, q8_k⟩
  rw [testA_eq, List.all_map, List.all_eq_true]
  intro c hc
  exact isInvA_of (tests_ok c hc).2.1

end CertificateChecks.KernelO8

namespace Certificates

open CertificateChecks

theorem certificate416101 : CFSG.ClassicalInvolution.Q3.TL4.Z2W.O8Pi.check () = true :=
  KernelO8.check_k

end Certificates
