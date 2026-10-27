module

public import Certificates.Kernel.Co2Three.QChecks
public import Certificates.Kernel.Co2Three.Checks
public import Certificates.Kernel.Co2Pump.Facts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2 CertificateChecks.KernelMisc.Co2K
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2T CFSG.Certificates.Native
open CFSG.KC.Bfs (replayOK)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

theorem inv_of_good {A A' : ℕ} (hA : Good A) (h1 : mmK A A' = I22) (h2 : mmK A' A = I22) :
    Inv 22 co2FiveV A A' := by
  rw [hmm, I22_eq] at h1 h2
  refine (inv_of_images hd22 sys.nodup sys.lt (a := permOfMat 22 co2FiveV A)
    (by simp [permOfMat]) (fun i hi => ?_) h1 h2).1
  obtain ⟨hlt, hget⟩ := getElem_vidx (hA.1 _ (mem_of_lt hi))
  rw [permOfMat_get hi]
  exact ⟨hlt, hget⟩

theorem tm_maps {l k : ℕ} (hl : l < 6) (hk : k < mL l) :
    ∀ v ∈ co2FiveV, vmul 22 v (TM l k) ∈ co2FiveV :=
  (LF.inv l (by rw [base_size]; exact hl) k hk).1

theorem maps_gProd {T : ℕ → ℕ} (hT : ∀ l < 6, T l < mL l) :
    ∀ n ≤ 6, ∀ v ∈ co2FiveV,
      vmul 22 v (Nat.rec (motive := fun _ => ℕ) I22 (fun i acc => mmK (TM i (T i)) acc) n) ∈
        co2FiveV
  | 0, _ => maps_I22
  | n + 1, hn => by
    change ∀ v ∈ co2FiveV, vmul 22 v (mmK (TM n (T n))
      (Nat.rec (motive := fun _ => ℕ) I22 (fun i acc => mmK (TM i (T i)) acc) n)) ∈ co2FiveV
    rw [hmm]
    exact maps_mmul (tm_maps (by omega) (hT n (by omega))) (maps_gProd hT n (by omega))

theorem good_gProd {T : ℕ → ℕ} (hT : ∀ l < 6, T l < mL l) : Good (gProd T) :=
  CertificateChecks.KernelCo2Pump.good_mm' (tm_maps (by norm_num) (hT 5 (by norm_num)))
    (maps_gProd hT 5 (by norm_num))

theorem pts_of_lit_keys {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} {N fuel : ℕ}
    {E : ℕ → ℕ → ℕ} (hc : enumOK 2300 gs ps c = true) (hN : c.pts.size = N)
    (hE : ∀ i < N, ∀ k < gs.size, (c.edges[i]!)[k]! = E i k)
    (hrep : replayOK E gs.size N = true) (hf : N ≤ fuel) :
    (enumBfs 2300 gs ps fuel).pts = c.pts := by
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

@[expose] noncomputable def qLit : ArrCert where
  pts := Array.ofFn fun i : Fin 729 => permOfMat 22 co2FiveV (QP i.val)
  edges := Array.ofFn fun i : Fin 729 => Array.ofFn fun k : Fin 3 => QE i.val k.val
  par := Array.ofFn fun i : Fin 729 => QR i.val
  lab := Array.ofFn fun i : Fin 729 => QL i.val

theorem qLit_size : qLit.pts.size = 729 := by simp [qLit]

theorem qLit_pt {i : ℕ} (hi : i < 729) : qLit.pts[i]! = permOfMat 22 co2FiveV (QP i) := by
  change (Array.ofFn fun i : Fin 729 => permOfMat 22 co2FiveV (QP i.val))[i]! = _
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem qLit_edges {i : ℕ} (hi : i < 729) :
    (qLit.edges[i]!).size = 3 ∧ ∀ k < 3, (qLit.edges[i]!)[k]! = QE i k := by
  have e : qLit.edges[i]! = Array.ofFn fun k : Fin 3 => QE i k.val := by
    change (Array.ofFn fun i : Fin 729 => Array.ofFn fun k : Fin 3 => QE i.val k.val)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  rw [e]
  refine ⟨by simp, fun k hk => ?_⟩
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem qLit_parlab {i : ℕ} (hi : i < 729) : qLit.par[i]! = QR i ∧ qLit.lab[i]! = QL i := by
  constructor
  · change (Array.ofFn fun i : Fin 729 => QR i.val)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]
  · change (Array.ofFn fun i : Fin 729 => QL i.val)[i]! = _
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem qGens2_size : (qGens2 ()).size = 3 := by
  unfold qGens2 qGens
  rw [Array.size_map, CertificateChecks.KernelCo2Pump.qW_size]

theorem qD_get {j : ℕ} (hj : j < 3) :
    (qGens2 ())[j]! = permOfMat 22 co2FiveV (QD j) ∧ Good (QD j) :=
  CertificateChecks.KernelCo2Pump.qG hj

theorem qD_inv {j : ℕ} (hj : j < 3) : Inv 22 co2FiveV (QD j) (QDI j) := by
  have h := ch13636Q_all j hj
  unfold ch13636Q qK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact inv_of_good (qD_get hj).2 h.1.1.1 h.1.1.2

theorem of_chunk81 {f : ℕ → Bool} {i : ℕ} (hi : i < 729)
    (h : ∀ c < 9, allN 81 (fun t => f (Nat.add (Nat.mul 81 c) t)) = true) : f i = true :=
  of_chunk (h (i / 81) (by omega)) (by simp only [Nat.mul_eq]; omega)
    (by simp only [Nat.mul_eq]; omega)

theorem qPoint {i : ℕ} (hi : i < 729) : pointM mmK 3 729 QD QP QE QR QL i = true :=
  of_chunk81 hi fun c hc => by
    have h := ch13636QP_all c hc
    unfold ch13636QP qPtsK at h
    exact h

theorem qKeyAt {j : ℕ} (hj : j < 729) : (Nat.blt (QSO j) 729 && Nat.beq (QSOI (QSO j)) j &&
    (!(Nat.blt (Nat.add j 1) 729) || Nat.blt (qKey QP (QSO j)) (qKey QP (QSO (Nat.add j 1))))) =
      true :=
  of_chunk81 (f := fun j => Nat.blt (QSO j) 729 && Nat.beq (QSOI (QSO j)) j &&
    (!(Nat.blt (Nat.add j 1) 729) || Nat.blt (qKey QP (QSO j)) (qKey QP (QSO (Nat.add j 1)))))
    hj fun c hc => by
      have h := ch13636QK_all c hc
      unfold ch13636QK qKeysK at h
      exact h

theorem qRoot : QP 0 = I22 ∧ replayOK QE 3 729 = true := by
  have h := ch13636QR_all 0 (by norm_num)
  unfold ch13636QR qRootK at h
  rw [Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem enumQ : enumOK 2300 (qGens2 ()) co2E81.qKeys qLit = true := by
  have h := enumOK_of_pointM sys hvm hmm I22_eq (ngen := 3) (N := 729) (GM := QD) (GMI := QDI)
    (PM := QP) qGens2_size (fun k hk => (qD_get hk).1) (fun k hk => qD_inv hk)
    (ps := co2E81.qKeys) (by rw [V_size]; decide) qLit_size (fun i hi => qLit_pt hi)
    (fun i hi => qLit_edges hi) (fun i hi => qLit_parlab hi) (by norm_num) qRoot.1
    (fun i hi => qPoint hi) (SO := QSO) (SOI := QSOI)
    (fun j hj => by
      have := qKeyAt hj
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
      exact ⟨this.1.1, this.1.2⟩)
    (fun j hj => by
      have := qKeyAt (j := j) (by omega)
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Nat.blt_eq] at this
      rcases this.2 with h' | h'
      · have h2 : Nat.blt (Nat.add j 1) 729 = true := by rw [Nat.blt_eq]; exact hj
        rw [h'] at h2
        exact absurd h2 Bool.false_ne_true
      · rw [V_size]
        exact h')
  rwa [V_size] at h

theorem qCert2_pts : (qCert2 ()).pts = qLit.pts := by
  change (enumBfs 2300 (qGens2 ()) co2E81.qKeys 731).pts = qLit.pts
  refine pts_of_lit_keys enumQ qLit_size (fun i hi k hk => (qLit_edges hi).2 k ?_) ?_
    (by norm_num)
  · rwa [qGens2_size] at hk
  · rw [qGens2_size]
    exact qRoot.2

theorem qCert2_size : (qCert2 ()).pts.size = 729 := by rw [qCert2_pts, qLit_size]

theorem qCert2_pt {i : ℕ} (hi : i < 729) :
    (qCert2 ()).pts[i]! = permOfMat 22 co2FiveV (QP i) := by rw [qCert2_pts, qLit_pt hi]

theorem good_QP {i : ℕ} (hi : i < 729) : Good (QP i) :=
  tree_good hd22 sys.lt hmm I22_eq (fun k hk => (qD_get hk).2.1) qRoot.1 (fun i hi => qPoint hi)
    i hi

theorem sift_DMt {j : ℕ} (hj : j < 7) :
    siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 (CertificateChecks.KernelCo2Pump.DMt j) =
      true :=
  ch13636S_all j hj

theorem qGens_inP {j : ℕ} (hj : j < 3) : inP (Co2T.levels ()) (qGens2 ())[j]! = true := by
  rw [(qD_get hj).1]
  unfold inP Co2T.levels
  exact sift_of (qD_get hj).2.1 (sift_DMt (by omega))

theorem dGens_inP {i : ℕ} (hi : i < 4) : inP (Co2T.levels ()) (dGens ())[i]! = true := by
  obtain ⟨e, g⟩ := CertificateChecks.KernelCo2Pump.dG hi
  rw [e]
  unfold inP Co2T.levels
  exact sift_of g.1 (sift_DMt (j := 3 + i) (by omega))

theorem hM_facts {i : ℕ} (hi : i < 16) :
    Good (HM i) ∧ Inv 22 co2FiveV (HM i) (HMI i) ∧
      inP (Co2T.levels ()) (permOfMat 22 co2FiveV (HM i)) = true := by
  have h := ch13636H_all i hi
  unfold ch13636H hK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨hT, hG⟩, h1⟩, h2⟩, hs⟩ := h
  have hgood : Good (HM i) := by
    rw [hG]
    exact good_gProd fun l hl => Nat.blt_eq.mp (allN_spec hT l hl)
  refine ⟨hgood, inv_of_good hgood h1 h2, ?_⟩
  unfold inP Co2T.levels
  exact sift_of hgood.1 hs

theorem fusK_spec {H HI : ℕ → ℕ} {P κ i k : ℕ} (h : fusK H HI P κ i k = true) :
    pwK P 3 ≠ I22 ∨ P = I22 ∨ (k < 81 ∧ ED k = P) ∨
      (i < 16 ∧ k < 81 ∧ ED k = mmK (mmK (HI i) P) (H i)) := by
  unfold fusK at h
  cases h0 : Nat.beq κ 0
  · cases h1 : Nat.beq κ 1
    · simp only [h0, h1, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      exact Or.inr (Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩))
    · simp only [h0, h1, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
      exact Or.inr (Or.inr (Or.inl h))
  · simp only [h0, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with h | h
    · refine Or.inl fun e => ?_
      rw [e, Nat.beq_refl] at h
      exact absurd h (by decide)
    · exact Or.inr (Or.inl (Nat.eq_of_beq_eq_true h))

theorem anyLt_of {n : ℕ} {p : ℕ → Bool} {i : ℕ} (hi : i < n) (h : p i = true) :
    CFSG.Sporadic.Schreier.Co3.Native.anyLt n p = true := by
  unfold CFSG.Sporadic.Schreier.Co3.Native.anyLt
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  exact ⟨⟨i, hi⟩, List.mem_finRange _, h⟩

theorem inD_of {X : ℕ} (hX : Good X) {k : ℕ} (hk : k < 81)
    (h : CertificateChecks.KernelCo2Pump.ED k = X) :
    inD (dElts ()) (permOfMat 22 co2FiveV X) = true := by
  unfold inD
  refine anyLt_of hk ?_
  obtain ⟨e, g⟩ := CertificateChecks.KernelCo2Pump.eG hk
  rw [e, eqA_good hX g, h]
  exact Nat.beq_refl _

theorem fus_parts {k : ℕ} (hk : k < 729) :
    eqA 2300 (powArr 2300 (qCert2 ()).pts[k]! 3) (idA 2300) = false ∨
      eqA 2300 (qCert2 ()).pts[k]! (idA 2300) = true ∨
      inD (dElts ()) (qCert2 ()).pts[k]! = true ∨
      ∃ i < 16, inD (dElts ())
        (conjA 2300 (permOfMat 22 co2FiveV (HM i)) (qCert2 ()).pts[k]!) = true := by
  have hg := good_QP hk
  have h := of_chunk81 (f := fun j => fusK HM HMI (QP j) (FKd j) (FH j) (FE j)) hk
    fun c hc => by
      have h := ch13636Fus_all c hc
      unfold ch13636Fus at h
      exact h
  rw [qCert2_pt hk]
  rcases fusK_spec h with h | h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · refine Or.inl ?_
    rw [pow_good hg, idA_eq, eqA_good (good_pw hg 3) good_I22]
    exact Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)
  · refine Or.inr (Or.inl ?_)
    rw [idA_eq, eqA_good hg good_I22, h]
    exact Nat.beq_refl _
  · exact Or.inr (Or.inr (Or.inl (inD_of hg h1 h2)))
  · refine Or.inr (Or.inr (Or.inr ⟨FH k, h1, ?_⟩))
    obtain ⟨hgH, hinv, -⟩ := hM_facts h1
    rw [conj_good hinv hg]
    have hX : Good (mmK (mmK (HMI (FH k)) (QP k)) (HM (FH k))) :=
      CertificateChecks.KernelCo2Pump.good_mm' (by rw [hmm]; exact maps_mmul hinv.2.1 hg.1) hgH.1
    exact inD_of hX h2 h3

end CertificateChecks.KernelCo2Three

end
