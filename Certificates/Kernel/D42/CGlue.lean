module

public import Certificates.Kernel.D42.UGlue
public import CFSG.Sporadic.SmallOddCore.LocalSpec
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

set_option maxRecDepth 400000

namespace CFSG.KD.D42

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
open CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th (Rep)
open CFSG.Sporadic.SmallOddCore (genOf)
open CFSG.Sporadic.Schreier (tablePerm tablePerm_eq)

theorem ap_lt {r : Nat} (hr : cn r = true) {i : Nat} (hi : i < 360) :
    ap (tabT (unpack 360 9 r)) i < 360 := by
  rw [ap_tabT _ (unpack_lt hr), CFSG.KS.Raw.Orb.unpack_get hi]
  have h := hr
  unfold cn canonK at h
  simp only [bAnd_iff] at h
  exact Nat.le_of_ble_eq_true (allN_spec h.2.2 i hi)

theorem rep_rinv {P R : Table} {g : Perm (Fin 360)} (hP : Rep 360 P g)
    (hR : ∀ i < 360, ap R i < 360) (e : compT 360 P R = idT 360) : Rep 360 R g⁻¹ := by
  intro i hi
  have h1 : ap (compT 360 P R) i = ap P (ap R i) := by
    unfold compT
    rw [CFSG.Sporadic.Th.ap_ofFn _ hi]
    rfl
  have h2 : ap (idT 360) i = i := by
    have := (CFSG.Sporadic.Th.Rep.idT (G := Perm (Fin 360)) (n := 360) (by norm_num)) i hi
    rwa [CFSG.Sporadic.Th.idx_one] at this
  rw [e, h2, hP _ (hR i hi)] at h1
  have := congrArg (CFSG.Sporadic.Th.idx 360 g⁻¹) h1
  rw [CFSG.Sporadic.Th.idx_inv_idx] at this
  exact this.symm

theorem rep_pc {p q : Nat} {g h : Perm (Fin 360)} (hp : cn p = true) (hq : cn q = true)
    (hg : Rep 360 (tabT (unpack 360 9 p)) g) (hh : Rep 360 (tabT (unpack 360 9 q)) h) :
    Rep 360 (tabT (unpack 360 9 (pc p q))) (g * h) ∧ cn (pc p q) = true := by
  refine ⟨?_, CFSG.KC.BfsPin.canonK_pcomp hp hq⟩
  unfold pc
  rw [← compT_unpack hp hq]
  exact CFSG.Sporadic.Th.Rep.compT hg hh

theorem rep_rinvK {p r : Nat} {g : Perm (Fin 360)} (hp : cn p = true)
    (hg : Rep 360 (tabT (unpack 360 9 p)) g) (h : rinvK p r = true) :
    Rep 360 (tabT (unpack 360 9 r)) g⁻¹ ∧ cn r = true := by
  unfold rinvK at h
  simp only [bAnd_iff] at h
  refine ⟨rep_rinv hg (fun i hi => ap_lt h.1 hi) ?_, h.1⟩
  have e : pcomp 360 9 (mask 9) p r = pidn 360 9 := Nat.eq_of_beq_eq_true h.2
  rw [compT_unpack hp h.1, e, hid360]

theorem strict_of_succ {c : Nat → Nat} {m : Nat} (h : ∀ r < m, c r < c (r + 1)) :
    ∀ s ≤ m, ∀ r < s, c r < c s
  | 0, _, r, hr => absurd hr (Nat.not_lt_zero _)
  | s + 1, hs, r, hr => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with h' | rfl
    · exact (strict_of_succ h s (by omega) r h').trans (h s (by omega))
    · exact h r (by omega)

theorem nine_le_of_row {U : Subgroup (Perm (Fin 360))} {cntU : Nat} {UT : Nat → Nat}
    (hUc : ∀ l < cntU, cn (UT l) = true)
    (hUm : ∀ l < cntU, ∃ u ∈ U, Rep 360 (tabT (unpack 360 9 (UT l))) u)
    {yc row : Nat} {y : Perm (Fin 360)} (hyc : cn yc = true)
    (hy : Rep 360 (tabT (unpack 360 9 yc)) y) (h : rowOK cntU UT yc row = true) :
    9 ≤ Nat.card ↥⁅U, Subgroup.zpowers y⁆ := by
  unfold rowOK rowGo at h
  simp only [bAnd_iff] at h
  obtain ⟨hry, hall, hinc⟩ := h
  obtain ⟨hyi, hyic⟩ := rep_rinvK hyc hy hry
  have hrow : ∀ r < 9, ∃ u ∈ U,
      Rep 360 (tabT (unpack 360 9 (cmK (UT (lane row r)) yc (pinv yc)))) (u * y * u⁻¹ * y⁻¹) ∧
        cn (cmK (UT (lane row r)) yc (pinv yc)) = true := by
    intro r hr
    have hf := allN_spec hall r hr
    simp only [bAnd_iff] at hf
    have hl : lane row r < cntU := Nat.le_of_ble_eq_true hf.1
    obtain ⟨u, hu, hur⟩ := hUm _ hl
    have huc := hUc _ hl
    obtain ⟨hui, huic⟩ := rep_rinvK huc hur hf.2
    obtain ⟨h1, c1⟩ := rep_pc huc hyc hur hy
    obtain ⟨h2, c2⟩ := rep_pc c1 huic h1 hui
    obtain ⟨h3, c3⟩ := rep_pc c2 hyic h2 hyi
    exact ⟨u, hu, h3, c3⟩
  have hlt := strict_of_succ (c := fun r => cmK (UT (lane row r)) yc (pinv yc)) (m := 8)
    (fun r hr => Nat.le_of_ble_eq_true (allN_spec hinc r hr))
  have hnd : ((List.range 9).map fun r =>
      tablePerm 360 (tabT (unpack 360 9 (cmK (UT (lane row r)) yc (pinv yc))))).Nodup := by
    refine List.Nodup.map_on (fun r hr s hs e => ?_) List.nodup_range
    rw [List.mem_range] at hr hs
    obtain ⟨u, -, hu, hcu⟩ := hrow r hr
    obtain ⟨v, -, hv, hcv⟩ := hrow s hs
    rw [tablePerm_eq hu, tablePerm_eq hv] at e
    have hb := (CFSG.Sporadic.SmallOddCore.tblEq_iff_eq hu hv).2 e
    rw [tblEq_unpack hcu hcv] at hb
    have hcs := Nat.eq_of_beq_eq_true hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact absurd hcs (Nat.ne_of_lt (hlt s (by omega) r h'))
    · exact absurd hcs (Nat.ne_of_gt (hlt r (by omega) s h'))
  have hmem : ∀ g ∈ (List.range 9).map (fun r =>
      tablePerm 360 (tabT (unpack 360 9 (cmK (UT (lane row r)) yc (pinv yc))))),
      g ∈ ⁅U, Subgroup.zpowers y⁆ := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hg
    rw [List.mem_range] at hr
    obtain ⟨u, hu, hur, -⟩ := hrow r hr
    rw [tablePerm_eq hur]
    have := Subgroup.commutator_mem_commutator hu (Subgroup.mem_zpowers y)
    rwa [commutatorElement_def] at this
  have := CFSG.Sporadic.SmallOddCore.length_le_card_of_nodup hnd hmem
  rwa [List.length_map, List.length_range] at this

theorem rec_spec {k cnt cap m : Nat} {G GI GJ T PL POS SRT SRI HS HSI : Nat → Nat}
    {gs : List Table} (hG : ∀ j < k, G j = pidn 360 9) (hg : TabsOK 360 9 k GI gs.toArray)
    (hgj : ∀ j < k, invEqK 360 9 (mask 9) (360 * 9) (GI j) (GJ j) = true ∧
      canonK 360 9 (mask 9) (360 * 9) (GJ j) = true)
    (hh : penumHdK (pidn 360 9) cnt cap T PL = true)
    (hp : ∀ i < cnt, penumPtK 360 9 (mask 9) (360 * 9) true G GI k cnt T PL POS SRT SRI i = true)
    (hs : ∀ i < cnt, hsortPtK 360 9 (mask 9) cnt T HS HSI i = true)
    (he : CFSG.Sporadic.SmallOddCore.enumOK 360 cap m gs = true) :
    (∀ x ∈ genOf 360 gs, ∃ i < cnt, Rep 360 (tabT (unpack 360 9 (T i))) x) ∧
      ∀ i < cnt, ∃ u ∈ genOf 360 gs, Rep 360 (tabT (unpack 360 9 (T i))) u := by
  obtain ⟨e, -, -⟩ := mulH_sound hn360 hG hg hh hp hs
  have hperm : ∀ g ∈ gs, CFSG.Sporadic.SmallOddCore.permOK 360 g = true := by
    intro g hgm
    obtain ⟨j, hj, rfl, hc⟩ := TabsOK_list hg hgm
    exact permOK_unpack hc (hgj j hj).1
  obtain ⟨-, hrep, hcov, -⟩ := CFSG.Sporadic.SmallOddCore.enumOK_spec (by norm_num) hperm he
  rw [e] at hrep hcov
  refine ⟨fun x hx => ?_, fun i hi => ?_⟩
  · obtain ⟨i, hi, hr⟩ := hcov x hx
    rw [hRec_size] at hi
    rw [hRec_get hi] at hr
    exact ⟨i, hi, hr⟩
  · have hi' : i < (hRec 360 9 cnt T PL).1.size := by
      rw [hRec_size]
      exact hi
    obtain ⟨h1, h2⟩ := hrep i hi'
    rw [hRec_get hi] at h1 h2
    exact ⟨_, h2, h1⟩

theorem comm_of {j : Nat} (hj : j < 2) (hS : sylowCheck j = true) (hU : uCheck j = true)
    {kU cP cU : Nat} {G GI GJ T PL POS SRT SRI HS HSI PC : Nat → Nat}
    {G' GI' GJ' T' PL' POS' SRT' SRI' HS' HSI' : Nat → Nat}
    (hgp : genP G GI GJ j = true)
    (hhp : penumHdK (pidn 360 9) cP (pOrder j) T PL = true)
    (hpp : ∀ i < cP, penumPtK 360 9 (mask 9) (360 * 9) true G GI 2 cP T PL POS SRT SRI i = true)
    (hsp : ∀ i < cP, hsortPtK 360 9 (mask 9) cP T HS HSI i = true)
    (hku : (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data.uWords.getD j []).length = kU)
    (hgu : genU G' GI' GJ' j (mainIdx j) kU = true)
    (hhu : penumHdK (pidn 360 9) cU 512 T' PL' = true)
    (hpu : ∀ i < cU,
      penumPtK 360 9 (mask 9) (360 * 9) true G' GI' kU cU T' PL' POS' SRT' SRI' i = true)
    (hsu : ∀ i < cU, hsortPtK 360 9 (mask 9) cU T' HS' HSI' i = true)
    (hrow : ∀ i < cP, i ≠ 0 → rowOK cU T' (T i) (PC i) = true) :
    ∀ y ∈ genOf 360 (pGens j), y ≠ 1 →
      9 ≤ Nat.card ↥⁅genOf 360 (uGens j), Subgroup.zpowers y⁆ := by
  intro y hy hy1
  obtain ⟨hGp, hptabs, hpgj⟩ := pTabs hj hgp
  obtain ⟨hgU, hutabs, hugj⟩ := uTabs hj hku hgu
  have heP : CFSG.Sporadic.SmallOddCore.enumOK 360 (pOrder j) (pOrder j) (pGens j) = true := by
    have h := hS
    unfold sylowCheck at h
    simp only [Bool.and_eq_true] at h
    exact h.2
  have heU : CFSG.Sporadic.SmallOddCore.enumOK 360 512 512 (uGens j) = true := by
    have h := hU
    unfold uCheck at h
    simp only [Bool.and_eq_true] at h
    exact h.1.2
  obtain ⟨hcovP, -⟩ := rec_spec hGp hptabs hpgj hhp hpp hsp heP
  obtain ⟨-, hmemU⟩ := rec_spec (fun r hr => (hgU r hr).1) hutabs hugj hhu hpu hsu heU
  obtain ⟨k, hk, hyk⟩ := hcovP y hy
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hy1
    have hh := hhp
    unfold penumHdK at hh
    simp only [bAnd_iff] at hh
    rw [Nat.eq_of_beq_eq_true hh.2.2.1, ← hid360] at hyk
    exact CFSG.Sporadic.Schreier.rep_unique hyk (CFSG.Sporadic.Th.Rep.idT (by norm_num))
  exact nine_le_of_row (fun l hl => penumPt_canon (hpu l hl)) hmemU (penumPt_canon (hpp k hk)) hyk
    (hrow k hk hk0)

theorem P0_cnt : P0.cnt = 81 := by
  have hb := baseP0
  simp only [bAnd_iff] at hb
  exact Nat.eq_of_beq_eq_true hb.2.1

theorem P1_cnt : P1.cnt = 9 := by
  have hb := baseP1
  simp only [bAnd_iff] at hb
  exact Nat.eq_of_beq_eq_true hb.2.1

theorem P0_pe : ∀ i < P0.cnt,
    penumPtK 360 9 (mask 9) (360 * 9) true P0.G P0.GI 2 P0.cnt P0.T P0.PL P0.POS P0.SRT P0.SRI i =
      true := by
  intro i hi
  have hi' : i < 81 := P0_cnt ▸ hi
  exact CFSG.KS.BaseMask.penumSl_spec (peP0_all (i / 16) (by omega))
    (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem P1_pe : ∀ i < P1.cnt,
    penumPtK 360 9 (mask 9) (360 * 9) true P1.G P1.GI 2 P1.cnt P1.T P1.PL P1.POS P1.SRT P1.SRI i =
      true := by
  intro i hi
  have hi' : i < 9 := P1_cnt ▸ hi
  exact CFSG.KS.BaseMask.penumSl_spec peP10 (by simp only [Nat.mul_eq]; omega)
    (by simp only [Nat.mul_eq]; omega) hi

theorem P0_hs : ∀ i < P0.cnt, hsortPtK 360 9 (mask 9) P0.cnt P0.T P0.HS P0.HSI i = true := by
  intro i hi
  have hi' : i < 81 := P0_cnt ▸ hi
  have h := hsP0
  unfold hsP at h
  simp only [bAnd_iff] at h
  exact slK_spec h.1 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem P1_hs : ∀ i < P1.cnt, hsortPtK 360 9 (mask 9) P1.cnt P1.T P1.HS P1.HSI i = true := by
  intro i hi
  have hi' : i < 9 := P1_cnt ▸ hi
  have h := hsP0
  unfold hsP at h
  simp only [bAnd_iff] at h
  exact slK_spec h.2 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

theorem cmP0_all : ∀ s < 9, cmP0 s = true := by
  intro s hs
  interval_cases s
  exacts [cmP00, cmP01, cmP02, cmP03, cmP04, cmP05, cmP06, cmP07, cmP08]

theorem row_of {i : Nat} {r : Bool} (hi : i ≠ 0)
    (h : Bool.rec (motive := fun _ => Bool) r true (Nat.beq i 0) = true) : r = true := by
  have hb : Nat.beq i 0 = false := by
    cases e : Nat.beq i 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true e) hi
  rw [hb] at h
  exact h

theorem comm_k0 : ∀ y ∈ genOf 360 (pGens 0), y ≠ 1 →
    9 ≤ Nat.card ↥⁅genOf 360 (uGens 0), Subgroup.zpowers y⁆ := by
  have hb := baseP0
  simp only [bAnd_iff] at hb
  obtain ⟨-, -, hh, hgp, -, -, hhu, hgu⟩ := hb
  refine comm_of (j := 0) (by norm_num) sylowCheck_k0 uCheck_k0 (PC := P0C) hgp hh P0_pe P0_hs
    rfl hgu hhu U0_pe U0_hs fun i hi hi0 => row_of hi0 ?_
  have hi' : i < 81 := P0_cnt ▸ hi
  exact slK_spec (cmP0_all (i / 10) (by omega)) i (by simp only [Nat.mul_eq]; omega)
    (by simp only [Nat.mul_eq]; omega) hi

theorem comm_k1 : ∀ y ∈ genOf 360 (pGens 1), y ≠ 1 →
    9 ≤ Nat.card ↥⁅genOf 360 (uGens 1), Subgroup.zpowers y⁆ := by
  have hb := baseP1
  simp only [bAnd_iff] at hb
  obtain ⟨-, -, hh, hgp, -, -, hhu, hgu⟩ := hb
  refine comm_of (j := 1) (by norm_num) sylowCheck_k1 uCheck_k1 (PC := P1C) hgp hh P1_pe P1_hs
    rfl hgu hhu U1_pe U1_hs fun i hi hi0 => row_of hi0 ?_
  have hi' : i < 9 := P1_cnt ▸ hi
  exact slK_spec cmP10 i (by simp only [Nat.mul_eq]; omega) (by simp only [Nat.mul_eq]; omega) hi

end CFSG.KD.D42

end
