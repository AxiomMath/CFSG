module

public import Certificates.Kernel.Co2Pump.K
public import Certificates.Kernel.Misc.Perm.C2M
public import Certificates.Kernel.Misc.Perm.C2J
public import CFSG.Certificates.Kernel.MonsterB.BfsTruncSound
public import CFSG.Certificates.Kernel.MonsterB.ArrBfsSound
public import CFSG.Certificates.Kernel.Spor.TextSound
public import CFSG.Certificates.Kernel.SporSch.DerivsSound
public import CFSG.Certificates.Kernel.SporSch.PairJ3FaithSound
public import CFSG.RankThree.Native.F2EnumPoint
public import Certificates.Data.Co2Pump
public meta import Certificates.Data.Co2Pump
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.Misc.ArrEnumSound
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
public import Certificates.Kernel.Misc.Perm.CertBind

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Pump

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2 CertificateChecks.KernelMisc.Co2K
open CFSG.HardMathSupport.Solomon.Coordinator.Co2Pump CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.Certificates.Native
open CFSG.Sporadic.Schreier.Co3.Native (hexLine layoutOK)
open CFSG.Monster.B.Co2 (allLt_iff)
open CFSG.KC.Bfs (replayLoop replayOK)

theorem good_mm' {A B : ℕ} (hA : ∀ v ∈ co2FiveV, vmul 22 v A ∈ co2FiveV)
    (hB : ∀ v ∈ co2FiveV, vmul 22 v B ∈ co2FiveV) : Good (mmK A B) := by
  rw [hmm]
  exact ⟨maps_mmul hA hB, mmul_lt _ _⟩

theorem hexLine_append (b c : ByteArray) {L : Nat} (h : (L + 1) * (3 * 2300 + 1) ≤ b.size + 1) :
    hexLine (b ++ c) 3 2300 L = hexLine b 3 2300 L := by
  unfold hexLine
  apply Array.ext (by simp)
  intro i h1 h2
  simp only [Array.getElem_ofFn]
  have hi : i < 2300 := by simpa using h1
  have hle : L * (3 * 2300 + 1) + 3 * i + 3 ≤ b.size := by nlinarith
  exact CFSG.KS.SporSch.PF2.hexAt_append_left b c _ 3 hle

theorem perm_get {L : Nat} (hL : L < 6) : pumpPerm L = unpack 2300 12 (PR L) := by
  have hb := CFSG.KS.Text.hexBind_sound tbind L hL
  have hl := CFSG.KS.SporSch.hexBind_layout tbind (w' := 3) (n' := 2300) rfl
  have es : String.ofList (PT.chars ++ ['\n']) = pumpText ++ "\n" := by
    rw [String.ofList_append, ← PT.eq]
  rw [es, CFSG.KS.SporSch.PF2.toUTF8_append, Nat.zero_add] at hb
  rw [es, CFSG.KS.SporSch.PF2.toUTF8_append] at hl
  have hsz : (pumpText.toUTF8 ++ "\n".toUTF8).size = 6 * (3 * 2300 + 1) := by
    unfold layoutOK at hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    exact hl.1
  have hnl : "\n" = "".push '\n' := by decide
  have h1 : "\n".toUTF8.size = 1 := by
    rw [hnl, String.toUTF8_eq_toByteArray, String.size_toByteArray, String.utf8ByteSize_push,
      String.utf8ByteSize_empty, Nat.zero_add]
    exact Char.utf8Size_eq_one_iff.2 (by decide)
  rw [ByteArray.size_append, h1] at hsz
  rw [pumpPerm, ← hb]
  generalize pumpText.toUTF8 = b at hsz ⊢
  exact (hexLine_append b _ (by omega)).symm

theorem nF {L : Nat} (hL : L < 6) :
    Inv 22 co2FiveV (NM L) (NMI L) ∧ pumpPerm L = permOfMat 22 co2FiveV (NM L) ∧
      NM L < 2 ^ (22 * 22) :=
  bind_facts (perm_get hL) (allN_spec pbind L hL)

theorem goodN {L : Nat} (hL : L < 6) : Good (NM L) := ⟨(nF hL).1.1, (nF hL).2.2⟩

theorem siftN {L : Nat} (hL : L < 6) :
    inP (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T.levels ())
      (permOfMat 22 co2FiveV (NM L)) = true := by
  unfold inP CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T.levels
  exact sift_of (nF hL).1.1 (allN_spec psift L hL)

theorem oF {k : Nat} (hk : k < 2) :
    Inv 22 co2FiveV (OM k) (OMI k) ∧
      CFSG.Sporadic.Co2Cert.co2OrigArrs[k]! = permOfMat 22 co2FiveV (OM k) ∧
      OM k < 2 ^ (22 * 22) := by
  have h := allN_spec obind k hk
  rw [Bool.and_eq_true] at h
  exact bind_facts (CFSG.KC.Misc.ArrEnum.arrBind_sound h.1) h.2

theorem goodO {k : Nat} (hk : k < 2) : Good (OM k) := ⟨(oF hk).1.1, (oF hk).2.2⟩

theorem good_fold {G : ℕ → ℕ} {m : ℕ} (hG : ∀ l < m, Good (G l)) :
    ∀ (w : List ℕ) (A : ℕ), Good A → (∀ l ∈ w, l < m) →
      Good (w.foldl (fun acc l => mmK (G l) acc) A)
  | [], _, hA, _ => hA
  | l :: w, A, hA, h => by
    rw [List.foldl_cons]
    exact good_fold hG w _ (good_mm (hG l (h l List.mem_cons_self)) hA)
      fun l' hl' => h l' (List.mem_cons_of_mem _ hl')

theorem fold_mat {gs : Array (Array ℕ)} {G : ℕ → ℕ} {m : ℕ}
    (hg : ∀ l < m, gs[l]! = permOfMat 22 co2FiveV (G l)) (hG : ∀ l < m, Good (G l)) :
    ∀ (w : List ℕ) (A : ℕ), (∀ l ∈ w, l < m) →
      w.foldl (fun acc l => compA 2300 acc gs[l]!) (permOfMat 22 co2FiveV A) =
        permOfMat 22 co2FiveV (w.foldl (fun acc l => mmK (G l) acc) A)
  | [], _, _ => rfl
  | l :: w, A, h => by
    have hl := h l List.mem_cons_self
    rw [List.foldl_cons, List.foldl_cons, hg l hl, compA_good (hG l hl)]
    exact fold_mat hg hG w _ fun l' hl' => h l' (List.mem_cons_of_mem _ hl')

theorem posWord_mat {gs : Array (Array ℕ)} {G : ℕ → ℕ} {m : ℕ}
    (hg : ∀ l < m, gs[l]! = permOfMat 22 co2FiveV (G l)) (hG : ∀ l < m, Good (G l)) {w : List ℕ}
    (hw : ∀ l ∈ w, l < m) :
    posWord 2300 gs w = permOfMat 22 co2FiveV (wM G w) ∧ Good (wM G w) := by
  unfold posWord wM
  rw [idA_eq]
  exact ⟨fold_mat hg hG w I22 hw, good_fold hG w I22 good_I22 hw⟩

theorem qW_size : co2E81.qW.size = 3 := by simp [co2E81]

theorem dW_size : (co2E81.dW[0]!).size = 4 := by simp [co2E81]

theorem pg_get : ∀ l < 2, co2E81.pg[l]! = permOfMat 22 co2FiveV (OM l) := by
  intro l hl
  interval_cases l
  · exact (oF (k := 0) (by norm_num)).2.1
  · exact (oF (k := 1) (by norm_num)).2.1

theorem qG {j : ℕ} (hj : j < 3) :
    (qGens2 ())[j]! = permOfMat 22 co2FiveV (QD j) ∧ Good (QD j) := by
  have h := allN_spec qchk j hj
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hw : ∀ l ∈ co2E81.qW[j]!, l < 2 := fun l hl => Nat.blt_eq.mp (h.1 l hl)
  obtain ⟨e, g⟩ := posWord_mat pg_get (fun l hl => goodO hl) hw
  have hq := Nat.eq_of_beq_eq_true h.2
  unfold qGens2 qGens
  rw [getElem!_pos _ j (by rw [Array.size_map, qW_size]; exact hj), Array.getElem_map,
    ← getElem!_pos _ j (by rw [qW_size]; exact hj)]
  change posWord 2300 co2E81.pg _ = _ ∧ _
  rw [e, hq]
  exact ⟨rfl, hq ▸ g⟩

theorem dG {i : ℕ} (hi : i < 4) :
    (dGens ())[i]! = permOfMat 22 co2FiveV (DD i) ∧ Good (DD i) := by
  have h := allN_spec dchk i hi
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hw : ∀ l ∈ (co2E81.dW[0]!)[i]!, l < 3 := fun l hl => Nat.blt_eq.mp (h.1 l hl)
  obtain ⟨e, g⟩ := posWord_mat (gs := qGens2 ()) (G := QD) (m := 3) (fun l hl => (qG hl).1)
    (fun l hl => (qG hl).2) hw
  have hq := Nat.eq_of_beq_eq_true h.2
  unfold dGens
  rw [getElem!_pos _ i (by rw [Array.size_map, dW_size]; exact hi), Array.getElem_map,
    ← getElem!_pos _ i (by rw [dW_size]; exact hi), e, hq]
  exact ⟨rfl, hq ▸ g⟩

theorem eG {k : ℕ} (hk : k < 81) :
    (dElts ())[k]! = permOfMat 22 co2FiveV (ED k) ∧ Good (ED k) := by
  have hq := Nat.eq_of_beq_eq_true (allN_spec echk k hk)
  obtain ⟨d0, g0⟩ := dG (i := 0) (by norm_num)
  obtain ⟨d1, g1⟩ := dG (i := 1) (by norm_num)
  obtain ⟨d2, g2⟩ := dG (i := 2) (by norm_num)
  obtain ⟨d3, g3⟩ := dG (i := 3) (by norm_num)
  unfold dElts
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  unfold dProd
  rw [d0, d1, d2, d3, pow_good g0, pow_good g1, pow_good g2, pow_good g3,
    compA_good (good_pw g3 _), compA_good (good_mm (good_pw g3 _) (good_pw g2 _)),
    compA_good (good_mm (good_mm (good_pw g3 _) (good_pw g2 _)) (good_pw g1 _)), ← hq]
  unfold DF
  exact ⟨rfl, good_mm (good_mm (good_mm (good_pw g3 _) (good_pw g2 _)) (good_pw g1 _))
    (good_pw g0 _)⟩

theorem guard {A B C D x y : Bool} (h : A = true → C = true → x = y) :
    (A && B && C && D && x) = (A && B && C && D && y) := by
  cases A <;> cases C
  · rfl
  · rfl
  · simp only [Bool.and_false, Bool.false_and]
  · rw [h rfl rfl]

theorem fuse_get {g : ℕ} (hg : g < 2) : (fuseGens ())[g]! = permOfMat 22 co2FiveV (NM g) := by
  unfold fuseGens
  rw [getElem!_pos _ g (by simpa using hg), Array.getElem_ofFn]
  exact (nF (by omega)).2.1

theorem fuse_ok : fuseCheck () = true := by
  unfold fuseCheck
  dsimp only
  rw [Bool.and_eq_true, allLt_iff, allLt_iff]
  refine ⟨fun i hi => ?_, fun k hk => ?_⟩
  · rw [fuse_get hi, validA_inv (nF (by omega)).1, Bool.true_and]
    exact siftN (by omega)
  · have h := allN_spec fchk k hk
    unfold fuseK at h
    rw [← h]
    refine congrArg _ (guard fun hp hg => ?_)
    have hp' := of_decide_eq_true hp
    have hg' := of_decide_eq_true hg
    have hi := (nF (L := tGen[k]!) (by omega)).1
    have hA : ∀ v ∈ co2FiveV, vmul 22 v (mmK (NMI tGen[k]!) (ED tPar[k]!)) ∈ co2FiveV := by
      rw [hmm]
      exact maps_mmul hi.2.1 (eG hp').2.1
    rw [(eG hk).1, (eG hp').1, fuse_get hg', conj_good hi (eG hp').2,
      eqA_good (eG hk).2 (good_mm' hA hi.1)]

theorem good_tree {P I : ℕ → ℕ} {g M : ℕ} (hg : g + 1 < 6) (h0 : Nat.beq (P 0) I22 = true)
    (ht : allN M (treeK P I g) = true) : ∀ j < M, Good (P j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.eq_of_beq_eq_true h0]
      exact good_I22
    · have h := allN_spec ht j hj
      unfold treeK at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
      rcases h with h | ⟨⟨h1, h2⟩, h3⟩
      · omega
      · rw [h3]
        exact good_mm (ih _ h1 (by omega)) (goodN (by change g + LAB I j < 6; omega))

theorem pair_get {g i : ℕ} (hg : g + 1 < 6) (hi : i < 2) :
    (Array.ofFn (n := 2) fun j => pumpPerm (g + j.val))[i]! =
      permOfMat 22 co2FiveV (NM (g + i)) := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  exact (nF (by omega)).2.1

theorem pair_of {C g M : ℕ} {P I : ℕ → ℕ} (hC : C < 81) (hg : g + 1 < 6) (hM : 1100 ≤ M)
    (hpg : allN 2 (fun i => pairG C (Nat.add g i)) = true) (h0 : Nat.beq (P 0) I22 = true)
    (hed : allN 1100 (edgeK P I g M) = true) (htr : allN M (treeK P I g) = true)
    (hord : allN M (ordK P I M) = true) (hrep : (replayLoop (EE I) 2 1100 0 1 == some M) = true) :
    pairCheck (dElts ())[C]! (Array.ofFn (n := 2) fun j => pumpPerm (g + j.val)) 1100 = true := by
  set gs : Array (Array ℕ) := Array.ofFn (n := 2) fun j => pumpPerm (g + j.val) with hgs
  have hsz : gs.size = 2 := by simp [hgs]
  have hG := good_tree hg h0 htr
  set L : Array (Array ℕ) := Array.ofFn (n := M) fun j => permOfMat 22 co2FiveV (P j.val) with hL
  have hLs : L.size = M := by simp [hL]
  have hLg : ∀ j < M, L[j]! = permOfMat 22 co2FiveV (P j) := fun j hj => by
    rw [hL, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have hkey : ∀ j < M, keyA 2300 co2FiveKeyPts L[j]! = keyK P j := by
    intro j hj
    rw [hLg j hj]
    have h := keyA_permOfMat sys hvm (hG j hj).1 (PM := P) (i := j) rfl co2FiveKeyPts
      (by rw [V_size]; decide)
    rwa [V_size] at h
  have hinj : ∀ a < L.size, ∀ b < L.size,
      keyA 2300 co2FiveKeyPts L[a]! = keyA 2300 co2FiveKeyPts L[b]! → a = b := by
    intro a ha b hb e
    rw [hLs] at ha hb
    rw [hkey a ha, hkey b hb] at e
    refine inj_of_order (N := M) (f := keyK P) (SO := SOK I) (SOI := SOIK I) (fun j hj => ?_)
      (fun j hj => ?_) ha hb e
    · have h := allN_spec hord j hj
      unfold ordK at h
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      exact h.1
    · have h := allN_spec hord j (by omega)
      unfold ordK at h
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at h
      rcases h.2 with h' | h'
      · have h2 : Nat.blt (Nat.add j 1) M = true := by rw [Nat.blt_eq]; exact hj
        rw [h'] at h2
        exact absurd h2 Bool.false_ne_true
      · exact h'
  have hE : ∀ i < 1100, ∀ k < gs.size, EE I i k < L.size ∧
      L[EE I i k]! = leftA 2300 gs k L[i]! := by
    intro i hi k hk
    rw [hsz] at hk
    have h := allN_spec (allN_spec hed i hi) k hk
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    rw [hLs]
    refine ⟨h.1, ?_⟩
    unfold leftA
    rw [hLg _ h.1, hLg i (by omega), hgs, pair_get hg hk, compA_good (hG i (by omega)),
      Nat.eq_of_beq_eq_true h.2]
    rfl
  have hr : replayLoop (EE I) gs.size 1100 0 1 = some L.size := by
    rw [hsz, hLs]
    exact beq_iff_eq.mp hrep
  have h00 : L[0]! = idA 2300 := by
    rw [hLg 0 (by omega), Nat.eq_of_beq_eq_true h0, ← idA_eq]
  obtain ⟨hpts, htree⟩ := CFSG.KC.Bfs.gBfs_trunc (act := leftA 2300 gs) (ngen := gs.size)
    (key := keyA 2300 co2FiveKeyPts) (by rw [hLs]; omega) h00 hinj hE hr
  have hgv : ∀ k < 2, validA 2300 gs[k]! = true := fun k hk => by
    rw [hgs, pair_get hg hk]
    exact validA_inv (nF (by omega)).1
  unfold pairCheck treeOK
  dsimp only
  rw [CFSG.KC.Bfs.arrBfs_eq]
  dsimp only
  rw [hpts]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allLt_iff, hsz]
  and_intros
  · trivial
  · intro i hi
    have h := allN_spec hpg i hi
    unfold pairG at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hc, h5⟩, h1⟩ := h
    have hgi := goodN (L := g + i) (by omega)
    rw [hgs, pair_get hg hi, validA_inv (nF (by omega)).1, siftN (by omega), (eG hC).1,
      commA_good hgi (eG hC).2, pow_good hgi, idA_eq, eqA_good (good_pw hgi 5) good_I22,
      eqA_good hgi good_I22]
    exact ⟨⟨⟨⟨rfl, rfl⟩, hc⟩, h5⟩, h1⟩
  · exact hgv
  · rw [hLs]
    omega
  · exact h00
  · intro i hi
    rw [hLs] at hi
    rw [Bool.or_eq_true, beq_iff_eq]
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2, h3⟩ := htree i h (by rw [hLs]; exact hi)
      refine Or.inr ?_
      rw [hsz] at h2
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      exact ⟨⟨h1, h2⟩, h3⟩
  · exact CFSG.KC.Bfs.pairwise_lt_mergeSort (CFSG.KC.Bfs.nodup_map_of_inj _ hinj)
  · rw [hLs]
    omega

theorem pairA_ok : pairACheck () = true :=
  pair_of (C := 3) (g := 2) (by norm_num) (by norm_num) (by norm_num) pgA rootA edgeA treeA ordA
    repA

theorem pairB_ok : pairBCheck () = true :=
  pair_of (C := 1) (g := 4) (by norm_num) (by norm_num) (by norm_num) pgB rootB edgeB treeB ordB
    repB

theorem pts_of_lit {gs : Array (Array ℕ)} {c : ArrCert} {N fuel : ℕ} {E : ℕ → ℕ → ℕ}
    (hc : enumOK 2300 gs co2FiveKeyPts c = true) (hN : c.pts.size = N)
    (hE : ∀ i < N, ∀ k < gs.size, (c.edges[i]!)[k]! = E i k)
    (hrep : replayOK E gs.size N = true) (hf : N ≤ fuel) :
    (enumBfs 2300 gs co2FiveKeyPts fuel).pts = c.pts := by
  simp only [enumOK, Bool.and_eq_true] at hc
  have ha := hc.2
  have hpos := arrCertOK_pos ha
  unfold enumBfs
  rw [CFSG.KC.Bfs.arrBfs_eq]
  refine CFSG.KC.Bfs.gBfs_eq_of_replay hpos (arrCertOK_root ha)
    (fun a h1 b h2 e => arrCertOK_keys_inj ha h1 h2 e) (fun i hi k hk => ?_) (by rwa [hN])
    (by rw [hN]; exact hf)
  have hp := arrCertOK_pointOK ha hi
  simp only [arrPointOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at hp
  rw [← hE i (by rwa [hN] at hi) k hk]
  exact hp.1.2 k hk

theorem C0_pts : co2FiveC0Cert.pts = co2FiveC0Lit.pts := by
  obtain ⟨hN, -, hE, -⟩ := litC0
  exact pts_of_lit enumC0 hN (fun i hi k hk => (hE i hi).2 k hk) repC0 (by norm_num)

theorem Q_pts : co2FiveQCert.pts = co2FiveQLit.pts := by
  obtain ⟨hN, -, hE, -⟩ := litQ
  exact pts_of_lit enumQ hN (fun i hi k hk => (hE i hi).2 k hk) repQ (by norm_num)

theorem five_ok : fiveCheck () = true := by
  obtain ⟨hCN, hCP, -, -⟩ := litC0
  obtain ⟨hQN, hQP, -, -⟩ := litQ
  unfold fiveCheck
  dsimp only
  rw [C0_pts, Q_pts, allLt_iff, hCN, hQN]
  intro i hi
  have hg := gC0 i hi
  have h : fiveK i = true := by
    rcases Nat.lt_or_ge i 1500 with h | h
    · exact allN_spec fiveA i h
    · have := allN_spec fiveB (i - 1500) (by omega)
      rwa [show Nat.add 1500 (i - 1500) = i by simp only [Nat.add_eq]; omega] at this
  unfold fiveK cntK at h
  rw [hCP i hi, pow_good hg, idA_eq, eqA_good (good_pw hg 3) good_I22, eqA_good hg good_I22]
  have e : ∀ j ∈ List.range 125, commA 2300 co2FiveQLit.pts[j]! (permOfMat 22 co2FiveV (PC0 i)) =
      comm (PQ j) (PC0 i) := fun j hj => by
    rw [hQP j (List.mem_range.1 hj), commA_good (gQ j (List.mem_range.1 hj)) hg]
  rw [List.filter_congr e, ← h]

open Certificates in
open CFSG.HardMathSupport.Solomon.Coordinator.Co2Pump in
theorem ok36904 : fuseCheck () = true ∧ pairACheck () = true ∧ pairBCheck () = true ∧
    fiveCheck () = true := ⟨fuse_ok, pairA_ok, pairB_ok, five_ok⟩

end CertificateChecks.KernelCo2Pump

end
