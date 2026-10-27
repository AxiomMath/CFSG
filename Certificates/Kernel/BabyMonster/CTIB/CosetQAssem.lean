module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQFuse
public import CFSG.Certificates.Kernel.MonsterB.CTIBBfsSound
public import Certificates.Data.CFSGNative.CTIB.Coset

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB
  CFSG.KC.Bfs

set_option exponentiation.threshold 1024

variable {G : Array ℕ}

theorem symG_gArr : SymG (gArr ()) := by
  unfold SymG
  decide +kernel

theorem autComp_assoc {B C : Array ℕ} (hC : RelOK G C) (A : Array ℕ) :
    autComp G (autComp G A B) C = autComp G A (autComp G B C) := by
  unfold autComp
  rw [Array.map_map]
  congr 1
  funext n
  exact (autApply_autComp hC B n).symm

theorem id23_eq : id23 () = arrOf (id32 22) := by decide +kernel

theorem autApply_id23 {n : ℕ} (hn : n < 2 ^ 23) : autApply G (id23 ()) n = n := by
  rw [id23_eq]
  exact autApply_id G hn

theorem arrOf_fold (hG : SymG G) (P : ℕ → ℕ) : ∀ (st : List ℕ) (acc : ℕ),
    arrOf (st.foldl (fun A s => compAut (loOf G) A (P s)) acc) =
      st.foldl (fun A s => autComp G A (arrOf (P s))) (arrOf acc)
  | [], _ => rfl
  | s :: st, acc => by
    rw [List.foldl_cons, List.foldl_cons, arrOf_fold hG P st, compAut_loOf G hG]

theorem autApply_fold (L : ℤ → Array ℕ) (hL : ∀ l, RelOK G (L l)) : ∀ (w : List ℤ) (A : Array ℕ)
    (y : ℕ), autApply G (w.foldl (fun A l => autComp G A (L l)) A) y =
      w.foldl (fun y l => autApply G (L l) y) (autApply G A y)
  | [], _, _ => rfl
  | l :: w, A, y => by
    rw [List.foldl_cons, List.foldl_cons, autApply_fold L hL w, autApply_autComp (hL l)]

theorem fold_lt (L : ℤ → Array ℕ) : ∀ (w : List ℤ) (y : ℕ), y < 2 ^ 23 →
    w.foldl (fun y l => autApply G (L l) y) y < 2 ^ 23
  | [], _, h => h
  | _ :: w, _, _ => fold_lt L w _ (autApply_lt _ _ _)

theorem fold_inv (L : ℤ → Array ℕ) : ∀ (w : List ℤ),
    (∀ l ∈ w, ∀ z < 2 ^ 23, autApply G (L l) (autApply G (L (-l)) z) = z) →
    ∀ y < 2 ^ 23, w.foldl (fun y l => autApply G (L l) y)
      ((invWord w).foldl (fun y l => autApply G (L l) y) y) = y
  | [], _, _, _ => rfl
  | l :: w, h, y, hy => by
    have e : invWord (l :: w) = invWord w ++ [-l] := by
      simp [invWord]
    simp only [e, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [h l List.mem_cons_self _ (fold_lt L _ _ hy)]
    exact fold_inv L w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) y hy

theorem undo_of {A B : ℕ} (hB : RelOK G (arrOf B)) (h : autComp G (arrOf A) (arrOf B) = id23 ())
    {z : ℕ} (hz : z < 2 ^ 23) : autApply G (arrOf B) (autApply G (arrOf A) z) = z := by
  rw [← autApply_autComp hB, h, autApply_id23 hz]

@[expose] def symLetters (s : ℕ) : List ℤ :=
  if s = 0 then [1] else if s ≤ 12 then List.replicate s 2 else List.replicate (s - 12) (-2)

structure SymFacts (G : Array ℕ) (S : List ℕ) : Prop where
  g0 : genImgs 0 = arrOf (nthN S 0)
  g1 : genImgs 1 = arrOf (nthN S 1)
  gi : genInvImgs () = arrOf (nthN S 13)
  r0 : RelOK G (arrOf (nthN S 0))
  r1 : RelOK G (arrOf (nthN S 1))
  r13 : RelOK G (arrOf (nthN S 13))
  sq0 : autComp G (arrOf (nthN S 0)) (arrOf (nthN S 0)) = id23 ()
  inv1 : autComp G (arrOf (nthN S 1)) (arrOf (nthN S 13)) = id23 ()
  inv13 : autComp G (arrOf (nthN S 13)) (arrOf (nthN S 1)) = id23 ()
  pow : ∀ r < 11, arrOf (nthN S (r + 2)) = autComp G (arrOf (nthN S (r + 1))) (arrOf (nthN S 1))
  ipow : ∀ r < 3,
    arrOf (nthN S (r + 14)) = autComp G (arrOf (nthN S (r + 13))) (arrOf (nthN S 13))

theorem letterImgs_rel {S : List ℕ} (hS : SymFacts G S) (l : ℤ) :
    RelOK G (letterImgs (genInvImgs ()) l) := by
  unfold letterImgs
  split_ifs
  · rw [hS.g0]
    exact hS.r0
  · rw [hS.g1]
    exact hS.r1
  · rw [hS.gi]
    exact hS.r13

theorem fold_rep {B : Array ℕ} (hB : RelOK G B) (L : ℤ → Array ℕ) {l : ℤ} (hl : L l = B)
    (P : ℕ → Array ℕ) {m : ℕ} (h1 : P 1 = B) (hP : ∀ r, 1 ≤ r → r < m → P (r + 1) = autComp G (P r) B) :
    ∀ r, 1 ≤ r → r ≤ m → ∀ A,
      (List.replicate r l).foldl (fun A l => autComp G A (L l)) A = autComp G A (P r)
  | 0, h, _, _ => absurd h (by decide)
  | 1, _, _, A => by rw [List.replicate_one, List.foldl_cons, List.foldl_nil, hl, h1]
  | r + 2, _, hr, A => by
    rw [List.replicate_succ', List.foldl_append, fold_rep hB L hl P h1 hP (r + 1) (by omega)
      (by omega), List.foldl_cons, List.foldl_nil, hl, autComp_assoc hB, ← hP (r + 1) (by omega)
      (by omega)]

theorem fold_sym {S : List ℕ} (hS : SymFacts G S) {s : ℕ} (hs : s < 17) (A : Array ℕ) :
    (symLetters s).foldl (fun A l => autComp G A (letterImgs (genInvImgs ()) l)) A =
      autComp G A (arrOf (nthN S s)) := by
  unfold symLetters
  by_cases h0 : s = 0
  · subst h0
    rw [ite_eq_left rfl, List.foldl_cons, List.foldl_nil]
    simp only [letterImgs, true_or, ite_true]
    rw [hS.g0]
  rw [ite_eq_right h0]
  by_cases h12 : s ≤ 12
  · rw [ite_eq_left h12]
    exact fold_rep hS.r1 _ (by simp [letterImgs, hS.g1]) (fun r => arrOf (nthN S r)) rfl
      (fun r hr hrm => by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        exact hS.pow r' (by omega)) s (by omega) h12 A
  · rw [ite_eq_right h12]
    have e := fold_rep hS.r13 (letterImgs (genInvImgs ())) (l := -2) (by simp [letterImgs, hS.gi])
      (fun r => arrOf (nthN S (12 + r))) (m := 4) rfl
      (fun r hr hrm => by
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        have := hS.ipow r' (by omega)
        rw [(by omega : 12 + (r' + 1 + 1) = r' + 14), (by omega : 12 + (r' + 1) = r' + 13)]
        exact this) (s - 12) (by omega) (by omega) A
    rw [e, (by omega : 12 + (s - 12) = s)]

theorem word_aut {S : List ℕ} (hS : SymFacts (gArr ()) S) (st : List ℕ)
    (hst : ∀ s ∈ st, s < 17) :
    wordAut (genInvImgs ()) (st.flatMap symLetters) =
      st.foldl (fun A s => autComp (gArr ()) A (arrOf (nthN S s))) (id23 ()) := by
  unfold wordAut
  rw [List.foldl_flatMap]
  exact List.foldl_ext _ _ _ fun A s hs => fold_sym hS (hst s hs) A

theorem word_imgs {S CT : List ℕ} (hS : SymFacts (gArr ()) S)
    (hct : ∀ s < 17, nthN CT s = ctabK (loOf (gArr ())) (nthN S s)) (st : List ℕ)
    (hst : ∀ s ∈ st, s < 17) :
    wordAut (genInvImgs ()) (st.flatMap symLetters) = arrOf (wordKF S CT st (id32 22)) := by
  rw [word_aut hS st hst, wordKF_eq (gArr ()) symG_gArr S CT st _ fun s hs => hct s (hst s hs),
    arrOf_fold symG_gArr (nthN S) st (id32 22), ← id23_eq]

theorem sym_undo {S : List ℕ} (hS : SymFacts (gArr ()) S) {s : ℕ} {l : ℤ} (hl : l ∈ symLetters s)
    {z : ℕ} (hz : z < 2 ^ 23) :
    autApply (gArr ()) (letterImgs (genInvImgs ()) l)
      (autApply (gArr ()) (letterImgs (genInvImgs ()) (-l)) z) = z := by
  have hl' : l = 1 ∨ l = 2 ∨ l = -2 := by
    unfold symLetters at hl
    split_ifs at hl
    · exact Or.inl (List.mem_singleton.1 hl)
    · exact Or.inr (Or.inl (List.eq_of_mem_replicate hl))
    · exact Or.inr (Or.inr (List.eq_of_mem_replicate hl))
  have e1 : letterImgs (genInvImgs ()) 1 = genImgs 0 := by simp [letterImgs]
  have e1' : letterImgs (genInvImgs ()) (-1) = genImgs 0 := by simp [letterImgs]
  have e2 : letterImgs (genInvImgs ()) 2 = genImgs 1 := by simp [letterImgs]
  have e2' : letterImgs (genInvImgs ()) (-2) = genInvImgs () := by simp [letterImgs]
  rcases hl' with rfl | rfl | rfl
  · rw [e1, e1', hS.g0]
    exact undo_of hS.r0 hS.sq0 hz
  · rw [e2, e2', hS.g1, hS.gi]
    exact undo_of hS.r1 hS.inv13 hz
  · rw [neg_neg, e2, e2', hS.g1, hS.gi]
    exact undo_of hS.r13 hS.inv1 hz

theorem word_inv {S : List ℕ} (hS : SymFacts (gArr ()) S) (st : List ℕ) {y : ℕ}
    (hy : y < 2 ^ 23) :
    autApply (gArr ()) (wordAut (genInvImgs ()) (st.flatMap symLetters))
      (autApply (gArr ()) (wordAut (genInvImgs ()) (invWord (st.flatMap symLetters))) y) = y := by
  unfold wordAut
  rw [autApply_fold _ (letterImgs_rel hS), autApply_fold _ (letterImgs_rel hS), autApply_id23 hy,
    autApply_id23 (fold_lt _ _ _ hy)]
  refine fold_inv _ _ (fun l hl z hz => ?_) y hy
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 hl
  exact sym_undo hS hs hz

theorem pow3_map (H : Array ℕ) :
    autPow (gArr ()) H 3 = (id23 ()).map fun n =>
      autApply (gArr ()) H (autApply (gArr ()) H (autApply (gArr ()) H n)) := by
  simp only [autPow, autComp, Array.map_map]
  rfl

theorem id23_getElem (f : ℕ → ℕ) {i : ℕ} (hi : i < 22) : ((id23 ()).map f)[i]! = f (2 ^ i) := by
  simp [id23, hi]

theorem deltaAut_of {AP k Bs T : ℕ} (hS : Setup (gArr ()) AP k Bs T) {GP d : ℕ}
    (hr : relOK (loOf (gArr ())) GP = true) (hd : dOK (loOf (gArr ())) AP GP d = true)
    {g : List ℤ}
    (hinv : ∀ y < 2 ^ 23, autApply (gArr ()) (arrOf GP)
      (autApply (gArr ()) (wordAut (genInvImgs ()) (invWord g)) y) = y) :
    deltaAutOK (genInvImgs ()) (arrOf AP) (arrOf GP) g d = true := by
  unfold deltaAutOK innerOK
  rw [pow3_map]
  simp only [autComp, Array.map_map, Array.size_map, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range]
  refine ⟨rfl, fun i hi => ?_⟩
  rw [id23_getElem _ hi]
  simp only [Function.comp_apply]
  have h2i : (2 : ℕ) ^ i < 2 ^ 23 := Nat.pow_lt_pow_right (by decide) (by omega)
  rw [hS.sq _ h2i]
  set H := arrOf AP
  set y := autApply (gArr ()) (wordAut (genInvImgs ()) (invWord g)) (autApply (gArr ()) H (2 ^ i))
  have hy : y < 2 ^ 23 := autApply_lt _ _ _
  have hdr := congrArg Subtype.val (delta_rel hS symG_gArr hr hd (mkQ y hy))
  rw [QC.mul_val, QC.mul_val, homOf_val, mkQ_val, phiS, homOf_val, homOf_val, homOf_val,
    mkQ_val] at hdr
  change qmul (gArr ()) d (autApply (gArr ()) (arrOf GP) (autApply (gArr ()) H y)) =
    qmul (gArr ()) (autApply (gArr ()) H (autApply (gArr ()) (arrOf GP) y)) d at hdr
  rw [hinv _ (autApply_lt _ _ _), hS.sq _ h2i] at hdr
  have hx := autApply_lt (gArr ()) (arrOf GP) (autApply (gArr ()) H y)
  generalize autApply (gArr ()) (arrOf GP) (autApply (gArr ()) H y) = x at hdr hx ⊢
  have e : x = qmul (gArr ()) (qinvG (gArr ()) d) (qmul (gArr ()) d x) := by
    rw [← qmul_assoc, qinvG_mul, qmul_zero_left _ hx]
  rw [e, hdr, ← qmul_assoc]
  rfl

theorem reach_bfs {act : ℕ → ℕ → ℕ} {ngen root x : ℕ} :
    Reach act ngen root x ↔ CFSG.KC.Bfs.Reach act ngen root x := by
  constructor
  · intro h
    induction h with
    | root => exact .root
    | step i hi _ ih => exact .step i hi ih
  · intro h
    induction h with
    | root => exact .root
    | step i hi _ ih => exact .step i hi ih

theorem natBfs_native {act : ℕ → ℕ → ℕ} {ngen : ℕ} {valid : ℕ → Bool} {root fuel : ℕ}
    (S : Finset ℕ) (hS : ∀ x, Reach act ngen root x ↔ x ∈ S) (hv : ∀ x ∈ S, valid x = true)
    (hfuel : S.card ≤ fuel) :
    natCertOK act ngen valid root (natBfs act ngen root fuel).1 (natBfs act ngen root fuel).2.1
        (natBfs act ngen root fuel).2.2.1 (natBfs act ngen root fuel).2.2.2 = true ∧
      (∀ x, x ∈ (natBfs act ngen root fuel).1 ↔ x ∈ S) ∧
      (natBfs act ngen root fuel).1.size = S.card := by
  obtain ⟨hc, hmem, hsz, -⟩ := CFSG.KC.Bfs.natBfs_spec (valid := valid) S
    (fun x => reach_bfs.symm.trans (hS x)) hv hfuel
  rw [CFSG.KC.Bfs.natBfs_eq] at hc hmem hsz
  rw [native_natBfs_eq]
  refine ⟨?_, hmem, hsz⟩
  simp only [CFSG.Monster.B.TwoA.Census.natCertOK, Bool.and_eq_true] at hc
  simp only [natCertOK, Bool.and_eq_true]
  exact ⟨⟨hc.1.1, hc.1.2⟩, (CFSG.Monster.B.CTIB.chainLt_iff _).2 (of_decide_eq_true hc.2)⟩

@[expose] noncomputable def qrecs (k PT npts : ℕ) : List (ℕ × ℕ) :=
  (List.range npts).map fun p => (repOf PT p, sizeOf k PT p)

theorem card_filter_range (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    ((Finset.range n).filter P).card = ((List.range n).filter fun q => decide (P q)).length := by
  rw [Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]

variable {AP k Bs T w VT PT TR RT npts : ℕ} {Gs Ds : List ℕ} {off : ℕ}

theorem fuse_rec (R : RankOK (gArr ()) AP k Bs T w VT PT TR RT npts Gs Ds off)
    (act : ℕ → ℕ → ℕ) (hact1 : ∀ i < 22, ∀ n, act i n = qconj (gArr ()) (arrOf AP) i n)
    (hact2 : ∀ t < 15, ∀ n,
      act (22 + t) n = fuse (gArr ()) (arrOf (nthN Gs (off + t))) (nthN Ds (off + t)) n)
    {p : ℕ} (hp : p < npts) (h0 : fld32 TR p = 0) {sz : ℕ}
    (hsz : ((Finset.range npts).filter (fun q => labOf PT q = labOf PT p)).sum (sizeOf k PT) = sz) :
    natCertOK act 37 (fun n => decide (n < 2 ^ 23) && isInv (gArr ()) (arrOf AP) w n)
        (repOf PT p) (natBfs act 37 (repOf PT p) (sz + 1)).1
        (natBfs act 37 (repOf PT p) (sz + 1)).2.1 (natBfs act 37 (repOf PT p) (sz + 1)).2.2.1
        (natBfs act 37 (repOf PT p) (sz + 1)).2.2.2 = true ∧
      (natBfs act 37 (repOf PT p) (sz + 1)).1.size = sz ∧
      (natBfs act 37 (repOf PT p) (sz + 1)).1.all (repOf PT p ≤ ·) = true ∧
      ((qrecs k PT npts).filter fun q => (natBfs act 37 (repOf PT p) (sz + 1)).1.contains q.1).length =
        ((Finset.range npts).filter (fun q => labOf PT q = labOf PT p)).card := by
  obtain ⟨S, hSm, hScard, hSv, hSrep⟩ :=
    forb_facts R act hact1 hact2 hp ((trOK_spec (R.tr p hp)).1 h0)
  obtain ⟨hc, hmem, hsize⟩ := natBfs_native (valid := fun n => decide (n < 2 ^ 23) &&
      isInv (gArr ()) (arrOf AP) w n) (fuel := sz + 1) S (fun x => (hSm x).symm)
    (fun x hx => by rw [Bool.and_eq_true, decide_eq_true_eq]; exact (hSv x hx).1) (by omega)
  refine ⟨hc, by rw [hsize, hScard, hsz], ?_, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    exact decide_eq_true ((hSv _ ((hmem _).1 (Array.getElem_mem hi))).2)
  · rw [card_filter_range, qrecs, List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun q hq => ?_
    have hq' := List.mem_range.1 hq
    simp only [Function.comp_apply]
    rw [decide_eq_decide.2 ((hSrep q hq').symm.trans (hmem _).symm)]
    exact Bool.eq_iff_iff.2 (Array.contains_iff_mem.trans decide_eq_true_iff.symm)

theorem getD_range_map {α : Type} (f : ℕ → α) (d : α) {t : ℕ} (ht : t < 15) :
    ((List.range 15).map f).toArray.getD t d = f t := by
  simp [ht]

theorem chainLt_map {f : ℕ → ℕ} {n : ℕ} (hf : ∀ p q, p < q → q < n → f p < f q) :
    chainLt ((List.range n).map f) = true := by
  rw [CFSG.Monster.B.CTIB.chainLt_iff, List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {p q} _ hq hpq => hf p q hpq (List.mem_range.1 hq)) ?_
  exact List.pairwise_lt_range

theorem cosetOK_of {count nl : ℕ} {S CT : List ℕ} {Steps : List (List ℕ)}
    (R : RankOK (gArr ()) AP k Bs T w VT PT TR RT npts Gs Ds off)
    (hSym : SymFacts (gArr ()) S)
    (hct : ∀ s < 17, nthN CT s = ctabK (loOf (gArr ())) (nthN S s))
    (hA : (liftImgsN k).toArray = arrOf AP)
    (hL : ∀ i < 22, (liftRowsN k).toArray[i]! = fld32 AP i % 2 ^ 22)
    (hw : sqCode k = w) (hcount : 2 ^ (k + 1) * cntV VT (2 ^ (22 - 2 * k)) = count)
    (hqr : orbitRecs k = qrecs k PT npts)
    (hsum : ((List.range npts).map (sizeOf k PT)).sum = count)
    (hfr : fusionRecsN k = (List.range nl).map fun r =>
      (((Finset.range npts).filter (fun q => labOf PT q = r)).card,
        ((Finset.range npts).filter (fun q => labOf PT q = r)).sum (sizeOf k PT),
        repOf PT (fld32 RT r)))
    (hroot : ∀ r < nl, fld32 RT r < npts ∧ fld32 TR (fld32 RT r) = 0 ∧ labOf PT (fld32 RT r) = r)
    (hfrInc : repsIncreasing ((fusionRecsN k).map (·.2.2)) = true)
    (hfrSum : ((fusionRecsN k).map (·.2.1)).sum = count)
    (hwords : ∀ j < 15, centWordN k j = (nthLL Steps (off + j)).flatMap symLetters)
    (hsteps : ∀ j < 15, ∀ s ∈ nthLL Steps (off + j), s < 17)
    (hW : ∀ j < 15, wordKF S CT (nthLL Steps (off + j)) (id32 22) = nthN Gs (off + j))
    (hds : ∀ j < 15, deltaN k j = nthN Ds (off + j)) :
    cosetOK k count = true := by
  have hS := setup_of R.symm R.setup
  have hgA : ∀ j < 15, wordAut (genInvImgs ()) (centWordN k j) = arrOf (nthN Gs (off + j)) :=
    fun j hj => by rw [hwords j hj, word_imgs hSym hct _ (hsteps j hj), hW j hj]
  have hgL : ((List.range 15).map fun j => wordAut (genInvImgs ()) (centWordN k j)) =
      (List.range 15).map fun j => arrOf (nthN Gs (off + j)) :=
    List.map_congr_left fun j hj => hgA j (List.mem_range.1 hj)
  have hdL : ((List.range 15).map fun j => deltaN k j) =
      (List.range 15).map fun j => nthN Ds (off + j) :=
    List.map_congr_left fun j hj => hds j (List.mem_range.1 hj)
  have hact1 : ∀ i < 22, ∀ n, fuseAct (arrOf AP) ((List.range 15).map fun j =>
      arrOf (nthN Gs (off + j))).toArray ((List.range 15).map fun j => nthN Ds (off + j)).toArray
      i n = qconj (gArr ()) (arrOf AP) i n := fun i hi n => by
    rw [fuseAct, ite_eq_left hi]
  have hact2 : ∀ t < 15, ∀ n, fuseAct (arrOf AP) ((List.range 15).map fun j =>
      arrOf (nthN Gs (off + j))).toArray ((List.range 15).map fun j => nthN Ds (off + j)).toArray
      (22 + t) n = fuse (gArr ()) (arrOf (nthN Gs (off + t))) (nthN Ds (off + t)) n :=
    fun t ht n => by
      rw [fuseAct, ite_eq_right (by omega), (by omega : 22 + t - 22 = t), getD_range_map _ _ ht,
        getD_range_map _ _ ht]
  unfold cosetOK
  simp only [hA, hw, hgL, hdL, hqr, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, hfrInc⟩, hfrSum⟩, ?_⟩, ?_⟩
  · rw [countInv_eq R.symm hS R.hk R.hw hL R.v R.pt]
    exact hcount
  · rw [qrecs, List.all_eq_true]
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    have hp' := List.mem_range.1 hp
    obtain ⟨O, hO1, hO2, hO3⟩ := qorb_facts R.symm hS R.hk R.hw (R.pt p hp')
    refine orbitOK_of_reach O (fun x => reach_bfs.symm.trans (hO1 x).symm) (fun x hx => ?_) hO2
      fun x hx => (hO3 x hx).2
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact (hO3 x hx).1
  · rw [qrecs, List.map_map]
    exact chainLt_map fun p q hpq hq => by
      have h1 := incOK_mono R.inc (Nat.le_of_lt hpq) hq
      rcases Nat.lt_or_eq_of_le h1 with h2 | h2
      · exact h2
      · exact absurd (incOK_inj R.inc (by omega) hq h2) (Nat.ne_of_lt hpq)
  · rw [qrecs, List.map_map]
    exact hsum
  · rw [hfr, List.all_eq_true]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hp, h0, hlab⟩ := hroot r (List.mem_range.1 hr)
    obtain ⟨g1, g2, g3, g4⟩ := fuse_rec R _ hact1 hact2 hp h0 (sz := ((Finset.range npts).filter
      (fun q => labOf PT q = r)).sum (sizeOf k PT)) (by rw [hlab])
    simp only [Bool.and_eq_true, beq_iff_eq]
    rw [hlab] at g4
    exact ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩
  · rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    rw [getD_range_map _ _ hj', hds j hj']
    refine deltaAut_of hS (R.rel j hj') (R.d j hj') fun y hy => ?_
    rw [← hgA j hj', hwords j hj']
    exact word_inv hSym _ hy

end CertificateChecks.KernelBM.CTIB.CosetQ

end
