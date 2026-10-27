module

public import Certificates.Kernel.D4QK.Glue
public import Certificates.Kernel.D4QK.Checks7
public import Certificates.Kernel.S63K.L4234
public import CFSG.Certificates.Kernel.D4QK.PlSound

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 600

namespace CertificateChecks.KernelD4Q.C300207

open CertificateChecks.KernelD4Q
open CFSG.KC.Enum CFSG.KC.S63K CFSG.KC.Co1F2 CFSG.KC.D4QK CFSG.LargeExtraspecial.S63
open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
open CFSG.Quasithin.Background.Harris.R1.D4Vert
open CFSG.KC.Co1B (mulWK)
open CertificateChecks.KernelS63

theorem ptArr_get : ∀ (w : List ℕ), (∀ k ∈ w, k < 8) → ∀ x < 819,
    (ptArr w)[x]! = HD.ptW w x ∧ HD.ptW w x < 819
  | [], _, x, hx => by
    refine ⟨?_, hx⟩
    unfold ptArr idA
    rw [List.foldr_nil, getElem!_pos _ x (by simp [hx])]
    simp [HD.ptW]
  | k :: w, hw, x, hx => by
    obtain ⟨h1, h2⟩ := ptArr_get w (fun k' hk' => hw k' (List.mem_cons_of_mem k hk')) x hx
    have hk := hw k List.mem_cons_self
    have e : HD.ptW (k :: w) x = HD.im k (HD.ptW w x) := rfl
    refine ⟨?_, by rw [e]; exact (HD.pa_get hk h2).2⟩
    unfold ptArr
    rw [List.foldr_cons, HD.compA_get' hx]
    change (CFSG.D4Hex.permArrs[k]!)[(ptArr w)[x]!]! = _
    rw [h1, HD.perm_get hk h2, e]

theorem flagP : (CFSG.D4Hex.sortKey (HD.ptW (nWords.getD 4 []) 0) (HD.ptW (nWords.getD 4 []) 1)
      (HD.ptW (nWords.getD 4 []) 5) == CFSG.D4Hex.lineKey 0 1 5) = true ∧
    notB (Nat.beq (HD.ptW (nWords.getD 4 []) 0) 0) = true ∧
    Nat.beq (HD.ptW (hWords.getD 2 []) 0) 0 = true ∧ Nat.beq (HD.ptW (hWords.getD 3 []) 0) 0 = true := by
  have h := flag
  unfold flagK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem fixLine_eq (w : List ℕ) (hw : ∀ k ∈ w, k < 8) :
    fixLine w = (CFSG.D4Hex.sortKey (HD.ptW w 0) (HD.ptW w 1) (HD.ptW w 5) ==
      CFSG.D4Hex.lineKey 0 1 5) := by
  unfold fixLine CFSG.D4Hex.fixesLine0
  rw [(ptArr_get w hw 0 (by norm_num)).1, (ptArr_get w hw 1 (by norm_num)).1,
    (ptArr_get w hw 5 (by norm_num)).1]

theorem movePt_eq (w : List ℕ) (hw : ∀ k ∈ w, k < 8) :
    movePt w = notB (Nat.beq (HD.ptW w 0) 0) := by
  unfold movePt
  rw [(ptArr_get w hw 0 (by norm_num)).1, HD.beq_nat, ← notB_eq]

theorem fixPt_eq (w : List ℕ) (hw : ∀ k ∈ w, k < 8) : fixPt w = Nat.beq (HD.ptW w 0) 0 := by
  unfold fixPt
  rw [(ptArr_get w hw 0 (by norm_num)).1, HD.beq_nat]

theorem n4 : ∀ k ∈ nWords.getD 4 [], k < 8 := by decide

theorem h2 : ∀ k ∈ hWords.getD 2 [], k < 8 := by decide

theorem h3 : ∀ k ∈ hWords.getD 3 [], k < 8 := by decide

theorem c1 : fixLine (nWords.getD 4 []) = true := (fixLine_eq _ n4).trans flagP.1

theorem c2 : movePt (nWords.getD 4 []) = true := (movePt_eq _ n4).trans flagP.2.1

theorem c3 : fixPt (hWords.getD 2 []) = true := (fixPt_eq _ h2).trans flagP.2.2.1

theorem c4 : fixPt (hWords.getD 3 []) = true := (fixPt_eq _ h3).trans flagP.2.2.2

theorem hx0 : x0A = unpackR 24 X0 := by
  rw [x0A, I21111.word_eq (by decide)]
  rfl

theorem hz0 : z0R = unpackR 24 Z0 := L4234.z0_eq

theorem c5 : x0IsVB = true := by
  unfold x0IsVB
  rw [L4234.cz_eq]
  change (x0A == (ElG ID.ZP 819)[1]!) = true
  rw [elG_get (by norm_num), hx0, beq_eqM]
  exact x0vb

theorem zconjP :
    eqM (mulWK ZE (ID.G 0)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [2]) ZE) = true ∧
    eqM (mulWK ZE (ID.G 1)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [0, 1]) ZE) = true ∧
    eqM (mulWK ZE (ID.G 2)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [1, 2]) ZE) = true ∧
    eqM (mulWK ZE (ID.G 6)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM [0, 2, 6, 0, 2]) ZE) =
      true := by
  have h := zconj
  unfold zconjK at h
  simp only [bAnd_eq', Bool.and_eq_true] at h
  exact h

theorem conj1 {k : ℕ} (hk : k < 8) {w : List ℕ} (hw : ∀ k ∈ w, k < 8)
    (h : eqM (mulWK ZE (ID.G k)) (mulWK (wordK ID.G CFSG.KS.SporSch.M24.idM w) ZE) = true) :
    (mulR zA d4Gens[k]! == mulR (wordR d4Gens w) zA) = true := by
  rw [hz, ID.gens_eq k hk, I21111.word_eq hw, mulWK_eq, mulWK_eq, beq_eqM]
  exact h

theorem c6 : zetaConjOK = true := by
  unfold zetaConjOK
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨conj1 (by norm_num) (by decide) zconjP.1, conj1 (by norm_num) (by decide) zconjP.2.1,
    conj1 (by norm_num) (by decide) zconjP.2.2.1, conj1 (by norm_num) (by decide) zconjP.2.2.2⟩

theorem c7 : vCommOK = true := by
  unfold vCommOK
  rw [hqA, all_ofFn, hz0, hx0]
  have e : (allN 14 fun l => (fun g => mulR g (unpackR 24 Z0) == mulR (unpackR 24 Z0) g &&
        mulR g (unpackR 24 X0) == mulR (unpackR 24 X0) g) (unpackR 24 (GQ l))) =
      allN 14 fun l => strictB (GQ l) fun g =>
        Bool.rec (motive := fun _ => Bool) false (eqM (mulWK g X0) (mulWK X0 g))
          (eqM (mulWK g Z0) (mulWK Z0 g)) := by
    refine congrArg (allN 14) (funext fun l => ?_)
    dsimp only
    rw [strictB_eq', bAnd_eq', mulWK_eq, mulWK_eq, mulWK_eq, mulWK_eq, beq_eqM, beq_eqM]
  rw [e]
  exact vcomm

theorem c8 : r0NotComm = true := by
  unfold r0NotComm
  rw [hr0, hx0, mulWK_eq, mulWK_eq, beq_eqM, ← notB_eq]
  exact r0nc

theorem c9 : centerCheck tQ = true := by
  rw [tQ_eq, centerCheck_eq hone hqA hz0 hx0]
  exact center

theorem c10 : kcCheck tK = true := by
  rw [tK_eq, kcCheck_eq hone hqA]
  exact kc

theorem c11 : bTabOK = true := by
  unfold bTabOK
  have hsz : bGens.size = 4 := by simp [bGens]
  have hT : buildTabR bGens (bfsPl bGens) = ElG BT.P BT.N := by
    rw [bfsPl_of_K hsz hb bPin]
    exact buildTabR_eq (root_of bPin) hsz hb (pin_tree bPin) (by decide)
  exact tabOK_of bPin hsz hb hbi hbiv hT

theorem hsA : sGensA = Array.ofFn (n := 14) fun l => unpackR 24 (GS l.val) := by
  apply Array.ext
  · simp [sGensA, phiArr]
  · intro i h1 _
    have hi : i < 14 := by simpa [sGensA, phiArr] using h1
    rw [← getElem!_pos sGensA i h1, hs i hi, Array.getElem_ofFn]

theorem c12 : sInQ2 = true := by
  unfold sInQ2
  change sGensA.all (memR tQ (lookup (mkIdx tQ))) = true
  obtain ⟨-, -, hP, hinj, -⟩ := pin_parts qPin
  rw [tQ_eq, hsA, all_ofFn, allN_iff']
  intro l hl
  rw [memR_elG (N := 2048) hP hinj]
  have h := allN_iff'.1 sin l hl
  rw [strictB_eq', anyK_iff] at h
  obtain ⟨w, hw, e⟩ := h
  exact ⟨w, hw, eqM_iff.1 e⟩

theorem c13 : sTabOK = true := by
  unfold sTabOK
  have hsz : sGensA.size = 14 := by simp [sGensA, phiArr]
  have hT : buildTabR sGensA (bfsPl sGensA) = ElG ST.P ST.N := by
    rw [bfsPl_of_K hsz hs sPin]
    exact buildTabR_eq (root_of sPin) hsz hs (pin_tree sPin) (by decide)
  exact tabOK_of sPin hsz hs hsi (fun l hl => ⟨_, hsiv l hl⟩) hT

open Certificates in
open CFSG.Quasithin.Background.Harris.R1.D4Vert in
theorem cert :
    fixLine (nWords.getD 4 []) = true
    ∧ movePt (nWords.getD 4 []) = true
    ∧ fixPt (hWords.getD 2 []) = true
    ∧ fixPt (hWords.getD 3 []) = true
    ∧ x0IsVB = true
    ∧ zetaConjOK = true
    ∧ vCommOK = true
    ∧ r0NotComm = true
    ∧ centerCheck tQ = true
    ∧ kcCheck tK = true
    ∧ bTabOK = true
    ∧ sInQ2 = true
    ∧ sTabOK = true :=
  ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩

end CertificateChecks.KernelD4Q.C300207

end
