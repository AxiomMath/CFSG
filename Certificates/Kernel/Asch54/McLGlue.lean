module

public import Certificates.Kernel.Asch54.McLChecks
public import Certificates.Kernel.Sporadic.McLC.Syl
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporMcLZ2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLAsch

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.SmallOddCore CFSG.ClassicalInvolution
open CFSG.KS.SporSch CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native CFSG.KS.Raw
open CFSG.Sporadic.SmallOddCore.Native CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CertificateChecks.KernelSpor.McLC
open CFSG.LocalAnalysis.WeakClosure81.SporMcL (z2Set)
open Subgroup

noncomputable abbrev tb (p : Nat) : Table := tabT (unpack 275 9 p)

theorem rep_of_pk {p : Nat} (hp : cKS p = true) {g : Equiv.Perm (Fin 275)}
    (h : ∀ x < 275, pk p x = actN g x) : Rep 275 (tb p) g :=
  rep_of_actN fun x hx => by rw [ap_unpack hp hx, h x hx]

theorem cKS_pc {p q : Nat} (hp : cKS p = true) (hq : cKS q = true) : cKS (pc p q) = true :=
  canonK_pcomp hp hq

theorem rep_pc {p q : Nat} (hp : cKS p = true) (hq : cKS q = true) {g h : Equiv.Perm (Fin 275)}
    (hg : Rep 275 (tb p) g) (hh : Rep 275 (tb q) h) : Rep 275 (tb (pc p q)) (g * h) := by
  have e : tb (pc p q) = compT 275 (tb p) (tb q) := (compT_unpack hp hq).symm
  rw [e]
  exact Rep.compT hg hh

theorem beq_iff {p q : Nat} (hp : cKS p = true) (hq : cKS q = true) {g h : Equiv.Perm (Fin 275)}
    (hg : Rep 275 (tb p) g) (hh : Rep 275 (tb q) h) : Nat.beq p q = true ↔ g = h := by
  rw [← tblEq_unpack hp hq]
  exact tblEq_iff_eq hg hh

theorem rep_inv {p r : Nat} (hp : cKS p = true) (hr : cKS r = true)
    (h : invEqK 275 9 (mask 9) (275 * 9) p r = true) {g : Equiv.Perm (Fin 275)}
    (hg : Rep 275 (tb p) g) : Rep 275 (tb r) g⁻¹ := by
  have e : invT 275 (tb p) = tb r := invT_unpack (by norm_num) h
  rw [← e]
  exact rep_invT hg (by rw [e]; exact invOK_unpack hp hr h)

theorem cKS_pidn : cKS (pidn 275 9) = true := sylBase.2.1

theorem rep_pidn : Rep 275 (tb (pidn 275 9)) (1 : Equiv.Perm (Fin 275)) := by
  change Rep 275 (tabT (unpack 275 9 (pidn 275 9))) (1 : Equiv.Perm (Fin 275))
  rw [← hid]
  exact Rep.idT McLProof.hn

theorem comm_iff {x t a : Equiv.Perm (Fin 275)} :
    (x * t * x⁻¹ * t⁻¹ = 1 ∨ x * t * x⁻¹ * t⁻¹ = a) ↔ (x * t = t * x ∨ x * t = a * (t * x)) := by
  constructor
  · rintro (h | h)
    · left
      calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
        _ = t * x := by rw [h, one_mul]
    · right
      calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
        _ = a * (t * x) := by rw [h]
  · rintro (h | h)
    · left
      rw [h]
      group
    · right
      rw [h]
      group

theorem cnt_S : McLCS.cnt = 128 := sylBase.2.2.2.2.1

noncomputable abbrev sP (i : Nat) : Equiv.Perm (Fin 275) := tablePerm 275 (tb (sT i))

theorem sT_canon {i : Nat} (hi : i < 128) : cKS (sT i) = true :=
  s_canon i (by rw [cnt_S]; exact hi)


theorem s_facts : (∀ i < 128, Rep 275 (tb (sT i)) (sP i) ∧ sP i ∈ McLProof.S) ∧
    (∀ x ∈ McLProof.S, ∃ i < 128, x = sP i) := by
  obtain ⟨-, hrep, hcov, -⟩ := enumOK_spec McLProof.hn McLProof.sgens_perm enum_ok
  rw [closure_eq.1, hRec_size, cnt_S] at hrep hcov
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · have h := hrep i hi
    rw [hRec_get hi] at h
    exact h
  · obtain ⟨k, hk, hr⟩ := hcov x hx
    rw [hRec_get hk] at hr
    exact ⟨k, hk, (tablePerm_eq hr).symm⟩

theorem gS_facts {j : Nat} (hj : j < 4) : cKS (McLCS.GI j) = true ∧
    Rep 275 (tb (McLCS.GI j)) (tp 275 (tb (McLCS.GI j))) ∧
      tp 275 (tb (McLCS.GI j)) ∈ McLProof.S := by
  obtain ⟨hsz, hg⟩ := s_tabs
  obtain ⟨he, hc⟩ := hg j hj
  have hmem : tb (McLCS.GI j) ∈ McLData.sgens := by
    have h := getElem!_mem_array (A := McLData.sgens.toArray) (l := j) (by rw [hsz]; exact hj)
    rw [he] at h
    simpa using h
  exact ⟨hc, rep_tp (McLProof.sgens_perm _ hmem), tp_mem_genOf hmem⟩

theorem vBase : r32 McLAV 0 < 128 ∧ r32 McLAV 1 < 128 ∧ r32 McLAV 2 < 128 ∧
    (∀ x < 275, pk aT x = r32 McLK.AL x) ∧ auT = pc aT uT ∧ uT ≠ pidn 275 9 ∧ uT ≠ aT := by
  have h := vBase_ok
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3,
    fun x hx => Nat.eq_of_beq_eq_true (allN_spec h4 x hx), Nat.eq_of_beq_eq_true h5, ?_, ?_⟩
  · intro e
    have hb : Nat.beq uT (pidn 275 9) = true := by rw [e]; exact Nat.beq_refl _
    rw [hb] at h6
    exact Bool.false_ne_true h6
  · intro e
    have hb : Nat.beq uT aT = true := by rw [e]; exact Nat.beq_refl _
    rw [hb] at h7
    exact Bool.false_ne_true h7

noncomputable abbrev uP : Equiv.Perm (Fin 275) := sP (r32 McLAV 1)

theorem aT_canon : cKS aT = true := sT_canon vBase.1

theorem uT_canon : cKS uT = true := sT_canon vBase.2.1

theorem auT_canon : cKS auT = true := sT_canon vBase.2.2.1

theorem rep_aT : Rep 275 (tb aT) McLProof.pa := by
  rw [McLProof.pa, tp_Ta]
  exact rep_of_pk aT_canon fun x hx => by rw [vBase.2.2.2.1 x hx, actN_alP hx]

theorem rep_uT : Rep 275 (tb uT) uP := (s_facts.1 _ vBase.2.1).1

theorem rep_auT : Rep 275 (tb auT) (McLProof.pa * uP) := by
  rw [vBase.2.2.2.2.1]
  exact rep_pc aT_canon uT_canon rep_aT rep_uT

theorem sP_a : sP (r32 McLAV 0) = McLProof.pa := tablePerm_eq rep_aT

theorem pa_mem_S : McLProof.pa ∈ McLProof.S := sP_a ▸ (s_facts.1 _ vBase.1).2

theorem uP_mem_S : uP ∈ McLProof.S := (s_facts.1 _ vBase.2.1).2

theorem uP_ne_one : uP ≠ 1 := fun e =>
  vBase.2.2.2.2.2.1 (Nat.eq_of_beq_eq_true ((beq_iff uT_canon cKS_pidn rep_uT rep_pidn).2 e))

theorem uP_ne_pa : uP ≠ McLProof.pa := fun e =>
  vBase.2.2.2.2.2.2 (Nat.eq_of_beq_eq_true ((beq_iff uT_canon aT_canon rep_uT rep_aT).2 e))

theorem center_S : ∀ x ∈ McLProof.S, (∀ t ∈ McLProof.S, x * t = t * x) →
    x = 1 ∨ x = McLProof.pa := by
  intro x hx hc
  obtain ⟨i, hi, rfl⟩ := s_facts.2 x hx
  have hr := (s_facts.1 i hi).1
  have hci := sT_canon hi
  have h := allN_spec cen_ok i hi
  unfold cenK at h
  rw [bIf_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨-, h⟩
  · exact Or.inl ((beq_iff hci cKS_pidn hr rep_pidn).1 h1)
  rw [bIf_iff] at h
  rcases h with ⟨h1, -⟩ | ⟨-, h⟩
  · exact Or.inr ((beq_iff hci aT_canon hr rep_aT).1 h1)
  obtain ⟨j, hj, hn⟩ := List.any_eq_true.1 h
  obtain ⟨hgc, hgr, hgS⟩ := gS_facts (List.mem_range.1 hj)
  rw [bIf_iff] at hn
  rcases hn with ⟨-, hf⟩ | ⟨hcomm, -⟩
  · exact absurd hf Bool.false_ne_true
  · have e : Nat.beq (pc (sT i) (McLCS.GI j)) (pc (McLCS.GI j) (sT i)) = true :=
      (beq_iff (cKS_pc hci hgc) (cKS_pc hgc hci) (rep_pc hci hgc hr hgr)
        (rep_pc hgc hci hgr hr)).2 (hc _ hgS)
    unfold commK at hcomm
    rw [e] at hcomm
    exact Bool.noConfusion hcomm

theorem z2K_iff {x s : Nat} (hx : cKS x = true) (hs : cKS s = true) {g h : Equiv.Perm (Fin 275)}
    (hg : Rep 275 (tb x) g) (hh : Rep 275 (tb s) h) :
    z2K aT x s = true ↔ (g * h = h * g ∨ g * h = McLProof.pa * (h * g)) := by
  unfold z2K
  rw [strictB_eq'', strictB_eq'', bIf_iff]
  have e1 := beq_iff (cKS_pc hx hs) (cKS_pc hs hx) (rep_pc hx hs hg hh) (rep_pc hs hx hh hg)
  have e2 := beq_iff (cKS_pc hx hs) (cKS_pc aT_canon (cKS_pc hs hx)) (rep_pc hx hs hg hh)
    (rep_pc aT_canon (cKS_pc hs hx) rep_aT (rep_pc hs hx hh hg))
  constructor
  · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
    · exact Or.inl (e1.1 h1)
    · exact Or.inr (e2.1 h2)
  · rintro (h1 | h2)
    · exact Or.inl ⟨e1.2 h1, rfl⟩
    · by_cases hb : Nat.beq (pc x s) (pc s x) = true
      · exact Or.inl ⟨hb, rfl⟩
      · exact Or.inr ⟨Bool.eq_false_iff.2 hb, e2.2 h2⟩

noncomputable abbrev vPL : List (Nat × Equiv.Perm (Fin 275)) :=
  [(pidn 275 9, 1), (aT, McLProof.pa), (uT, uP), (auT, McLProof.pa * uP)]

theorem vL_eq : vL = vPL.map Prod.fst := rfl

theorem vPL_facts : ∀ q ∈ vPL, cKS q.1 = true ∧ Rep 275 (tb q.1) q.2 ∧ q.2 ∈ McLProof.S := by
  intro q hq
  simp only [vPL, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨cKS_pidn, rep_pidn, one_mem _⟩
  · exact ⟨aT_canon, rep_aT, pa_mem_S⟩
  · exact ⟨uT_canon, rep_uT, uP_mem_S⟩
  · exact ⟨auT_canon, rep_auT, mul_mem pa_mem_S uP_mem_S⟩

theorem mem_vL {w : Nat} (hw : w ∈ vL) : ∃ q ∈ vPL, q.1 = w := by
  rw [vL_eq] at hw
  obtain ⟨q, hq, e⟩ := List.mem_map.1 hw
  exact ⟨q, hq, e⟩

theorem mem_z2Set {x : Equiv.Perm (Fin 275)} : x ∈ z2Set ↔ ∃ q ∈ vPL, x = q.2 := by
  constructor
  · rintro ⟨hx, hz⟩
    obtain ⟨i, hi, rfl⟩ := s_facts.2 x hx
    have hr := (s_facts.1 i hi).1
    have hci := sT_canon hi
    have h := allN_spec z2out_ok i hi
    unfold z2outK at h
    rw [bIf_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨-, h⟩
    · obtain ⟨w, hw, hb⟩ := List.any_eq_true.1 h1
      obtain ⟨q, hq, rfl⟩ := mem_vL hw
      obtain ⟨qc, qr, -⟩ := vPL_facts q hq
      exact ⟨q, hq, (beq_iff hci qc hr qr).1 hb⟩
    · obtain ⟨j, hj, hn⟩ := List.any_eq_true.1 h
      obtain ⟨hgc, hgr, hgS⟩ := gS_facts (List.mem_range.1 hj)
      rw [bIf_iff] at hn
      rcases hn with ⟨-, hf⟩ | ⟨hz2, -⟩
      · exact absurd hf Bool.false_ne_true
      · have := (z2K_iff hci hgc hr hgr).2 (comm_iff.1 (hz _ hgS))
        rw [hz2] at this
        exact absurd this Bool.false_ne_true
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨qc, qr, qS⟩ := vPL_facts q hq
    refine ⟨qS, fun t ht => ?_⟩
    obtain ⟨i, hi, rfl⟩ := s_facts.2 t ht
    have hv : z2inK q.1 = true := by
      have h := List.all_eq_true.1 z2in_ok q.1 (by rw [vL_eq]; exact List.mem_map_of_mem hq)
      exact h
    have h := allN_spec hv i hi
    exact comm_iff.2 ((z2K_iff qc (sT_canon hi) qr (s_facts.1 i hi).1).1 h)

theorem pa_mem_z2 : McLProof.pa ∈ z2Set := mem_z2Set.2 ⟨(aT, McLProof.pa), by simp [vPL], rfl⟩

theorem uP_mem_z2 : uP ∈ z2Set := mem_z2Set.2 ⟨(uT, uP), by simp [vPL], rfl⟩

theorem norm_of {g : Nat} (hg : cKS g = true) {γ : Equiv.Perm (Fin 275)} (hr : Rep 275 (tb g) γ)
    (h : normK g = true) : γ ∈ normalizer z2Set := by
  rw [mem_set_normalizer_iff]
  intro x
  have key : ∀ q ∈ vPL, (∃ q' ∈ vPL, γ * q.2 * γ⁻¹ = q'.2) ∧ ∃ q' ∈ vPL, γ⁻¹ * q.2 * γ = q'.2 := by
    intro q hq
    obtain ⟨qc, qr, -⟩ := vPL_facts q hq
    have hv := List.all_eq_true.1 h q.1 (by rw [vL_eq]; exact List.mem_map_of_mem hq)
    rw [bAnd_iff] at hv
    obtain ⟨w1, hw1, e1⟩ := List.any_eq_true.1 hv.1
    obtain ⟨w2, hw2, e2⟩ := List.any_eq_true.1 hv.2
    obtain ⟨q1, hq1, rfl⟩ := mem_vL hw1
    obtain ⟨q2, hq2, rfl⟩ := mem_vL hw2
    obtain ⟨c1, r1, -⟩ := vPL_facts q1 hq1
    obtain ⟨c2, r2, -⟩ := vPL_facts q2 hq2
    have f1 := (beq_iff (cKS_pc hg qc) (cKS_pc c1 hg) (rep_pc hg qc hr qr) (rep_pc c1 hg r1 hr)).1 e1
    have f2 := (beq_iff (cKS_pc qc hg) (cKS_pc hg c2) (rep_pc qc hg qr hr) (rep_pc hg c2 hr r2)).1 e2
    refine ⟨⟨q1, hq1, ?_⟩, ⟨q2, hq2, ?_⟩⟩
    · rw [f1]
      group
    · rw [mul_assoc, f2]
      group
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := mem_z2Set.1 hx
    obtain ⟨q', hq', e⟩ := (key q hq).1
    exact mem_z2Set.2 ⟨q', hq', e⟩
  · intro hx
    obtain ⟨q, hq, e⟩ := mem_z2Set.1 hx
    obtain ⟨q', hq', e'⟩ := (key q hq).2
    refine mem_z2Set.2 ⟨q', hq', ?_⟩
    rw [← e', ← e]
    group

noncomputable abbrev NN : Subgroup (Equiv.Perm (Fin 275)) := McLProof.P ⊓ normalizer z2Set

theorem S_le_NN : McLProof.S ≤ NN := by
  refine le_inf (McLProof.S_le_K.trans McLProof.K_le_P) ?_
  rw [closure_le]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨j, hj, rfl, -⟩ := TabsOK_list s_tabs (by simpa using hg)
  obtain ⟨hgc, hgr, -⟩ := gS_facts hj
  have hn := norm_ok
  rw [bAnd_iff] at hn
  have h : normK (McLCS.GI j) = true := allN_spec hn.2 j hj
  exact norm_of hgc hgr h

theorem hWords_letters : ∀ j < 3, ∀ l ∈ CFSG.LocalAnalysis.WeakClosure81.SporMcL.hWords.getD j [],
    l = 1 ∨ l = 2 := by
  decide +kernel

noncomputable abbrev hP (j : Nat) : Equiv.Perm (Fin 275) :=
  wp qAB (CFSG.LocalAnalysis.WeakClosure81.SporMcL.hWords.getD j [])

theorem hG_facts {j : Nat} (hj : j < 3) : cKS (McLAHG j) = true ∧ Rep 275 (tb (McLAHG j)) (hP j) := by
  have h := allN_spec hGen_ok j hj
  rw [bAnd_iff] at h
  refine ⟨h.1, rep_of_pk h.1 fun x hx => ?_⟩
  rw [Nat.eq_of_beq_eq_true (allN_spec h.2 x hx)]
  exact foldr_wp (fun c hc y hy => GA_eq (hWords_letters j hj c hc) hy) hx

theorem qAB_mem_P (l : Nat) : qAB l ∈ McLProof.P := by
  unfold qAB
  split_ifs
  · rw [← tp_Ta]
    exact McLProof.pa_mem
  · rw [← tp_eq rep_Tb]
    exact McLProof.pb_mem

theorem hP_mem {j : Nat} (hj : j < 3) : hP j ∈ NN := by
  obtain ⟨hc, hr⟩ := hG_facts hj
  refine ⟨wp_mem fun c _ => qAB_mem_P c, ?_⟩
  have hn := norm_ok
  rw [bAnd_iff] at hn
  have h : normK (McLAHG j) = true := allN_spec hn.1 j hj
  exact norm_of hc hr h

noncomputable abbrev eGens : List Table := [tb (McLAE.GI 0), tb (McLAE.GI 1)]

theorem eBase : (∀ j < 2, McLAE.GI j = McLAHG j ∧ McLAE.G j = pidn 275 9 ∧ cKS (McLAEI j) = true ∧
      invEqK 275 9 (mask 9) (275 * 9) (McLAE.GI j) (McLAEI j) = true) ∧ McLAE.cnt = 9 ∧
    penumHdK (pidn 275 9) McLAE.cnt 50000 McLAE.T McLAE.PL = true := by
  have h := eBase_ok
  rw [bAnd_iff, bAnd_iff] at h
  refine ⟨fun j hj => ?_, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩
  have h' := allN_spec h.1 j hj
  simp only [bAnd_iff] at h'
  exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2.1, h'.2.2.1, h'.2.2.2⟩

theorem eGI {j : Nat} (hj : j < 2) : cKS (McLAE.GI j) = true ∧ Rep 275 (tb (McLAE.GI j)) (hP j) := by
  rw [(eBase.1 j hj).1]
  exact hG_facts (by omega)

theorem e_tabs : TabsOK 275 9 2 McLAE.GI eGens.toArray := by
  refine ⟨rfl, fun j hj => ⟨?_, (eGI hj).1⟩⟩
  interval_cases j <;> rfl

theorem e_enum : enumOK 275 50000 9 eGens = true := by
  refine enumOK_of (GJ := McLAEI) (HS := McLAE.HS) (HSI := McLAE.HSI) (POS := McLAE.POS)
    (SRT := McLAE.SRT) (SRI := McLAE.SRI) (CL := McLAECl) sylBase.1
    (fun j hj => (eBase.1 j hj).2.1) e_tabs
    (fun j hj => ⟨(eBase.1 j hj).2.2.2, (eBase.1 j hj).2.2.1⟩) eBase.2.2
    (fun i hi => penumSl_spec eE_ok i (Nat.zero_le _) (by omega) hi)
    (fun i hi => slK_spec eH_ok i (Nat.zero_le _) (by omega) hi)
    (fun c hc => slK_spec eCl_ok c (Nat.zero_le _) (by change c < Nat.mul McLAE.cnt 4; omega)
      (by change c < Nat.mul McLAE.cnt 4; omega)) eBase.2.1

theorem eGens_perm : ∀ g ∈ eGens, CFSG.Sporadic.SmallOddCore.permOK 275 g = true := by
  intro g hg
  simp only [eGens, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact permOK_of_rep (eGI (j := 0) (by norm_num)).2
  · exact permOK_of_rep (eGI (j := 1) (by norm_num)).2

theorem card_E : Nat.card (genOf 275 eGens) = 9 := (enumOK_spec McLProof.hn eGens_perm e_enum).1

theorem E_le_NN : genOf 275 eGens ≤ NN := by
  rw [closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ eGens := by simpa using hg
  simp only [eGens, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl
  · rw [tp_eq (eGI (j := 0) (by norm_num)).2]
    exact hP_mem (by norm_num)
  · rw [tp_eq (eGI (j := 1) (by norm_num)).2]
    exact hP_mem (by norm_num)

theorem card_NN_dvd : 1152 ∣ Nat.card NN := by
  have h1 : 128 ∣ Nat.card NN := McLProof.card_S ▸ card_dvd_of_le S_le_NN
  have h2 : 9 ∣ Nat.card NN := card_E ▸ card_dvd_of_le E_le_NN
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1 h2

theorem uBase : (∀ j < 2, cKS (McLAU.G j) = true ∧ cKS (McLAU.GI j) = true ∧
      invEqK 275 9 (mask 9) (275 * 9) (McLAU.G j) (McLAU.GI j) = true) ∧
    (∀ x < 275, pk (McLAU.G 0) x = LJ 0 x ∧ pk (McLAU.G 1) x = LJ 2 x) ∧
    McLAU.cnt = 210 ∧ McLAU.R = uT ∧
    penumHdK McLAU.R McLAU.cnt 50000 McLAU.T McLAU.PL = true := by
  have h := uBase_ok
  simp only [bAnd_iff] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨fun j hj => ?_, fun x hx => ?_, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4, h5⟩
  · have h' := allN_spec h1 j hj
    simp only [bAnd_iff] at h'
    exact h'
  · have h' := allN_spec h2 x hx
    simp only [bAnd_iff] at h'
    exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2⟩

noncomputable abbrev kP (j : Nat) : Equiv.Perm (Fin 275) := sg (2 * j)

theorem uG_facts {j : Nat} (hj : j < 2) : Rep 275 (tb (McLAU.G j)) (kP j) ∧
    Rep 275 (tb (McLAU.GI j)) (kP j)⁻¹ ∧ kP j ∈ McLProof.K := by
  obtain ⟨c, ci, inv⟩ := uBase.1 j hj
  have hr : Rep 275 (tb (McLAU.G j)) (kP j) := by
    refine rep_of_pk c fun x hx => ?_
    interval_cases j
    · rw [(uBase.2.1 x hx).1, actN_sg (by norm_num) hx]
    · rw [(uBase.2.1 x hx).2, actN_sg (by norm_num) hx]
  refine ⟨hr, rep_inv c ci inv hr, ?_⟩
  change sg (2 * j) ∈ genOf 275 McLData.kgens
  rw [genOf_kgens]
  interval_cases j
  · exact sg0_mem
  · exact sg2_mem

theorem u_pt {i : Nat} (hi : i < 210) : penumPtK 275 9 (mask 9) (275 * 9) true McLAU.G McLAU.GI 2
    McLAU.cnt McLAU.T McLAU.PL McLAU.POS McLAU.SRT McLAU.SRI i = true :=
  penumSl_spec uE_ok i (Nat.zero_le _) (by rw [uBase.2.2.1]; omega) (by rw [uBase.2.2.1]; exact hi)

theorem u_conj : ∀ i < 210, cKS (McLAU.T i) = true ∧
    ∃ c ∈ McLProof.K, Rep 275 (tb (McLAU.T i)) (c * uP * c⁻¹) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have sp := penumPt_specH (u_pt hi)
    refine ⟨sp.1, ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · refine ⟨1, one_mem _, ?_⟩
      have e : McLAU.T 0 = uT := by
        have hh := uBase.2.2.2.2
        unfold penumHdK at hh
        simp only [bAnd_iff] at hh
        rw [Nat.eq_of_beq_eq_true hh.2.2.1, uBase.2.2.2.1]
      rw [e, one_mul, inv_one, mul_one]
      exact rep_uT
    · obtain ⟨hp, hl, he, -⟩ := sp.2.1 (by omega)
      obtain ⟨pc0, c, hc, hr⟩ := ih _ hp (by omega)
      obtain ⟨gr, gir, gK⟩ := uG_facts (show labOf McLAU.PL i < 2 from hl)
      obtain ⟨c1, c2, -⟩ := uBase.1 _ hl
      refine ⟨kP (labOf McLAU.PL i) * c, mul_mem gK hc, ?_⟩
      have e : McLAU.T i = pc (pc (McLAU.G (labOf McLAU.PL i)) (McLAU.T (parOf McLAU.PL i)))
          (McLAU.GI (labOf McLAU.PL i)) := he
      rw [e]
      have := rep_pc (cKS_pc c1 pc0) c2 (rep_pc c1 pc0 gr hr) gir
      simpa only [mul_inv_rev, mul_assoc] using this

theorem u_inj : ∀ a < 210, ∀ b < 210, McLAU.T a = McLAU.T b → a = b := by
  have h := inj_of_sortH (cnt := McLAU.cnt) (T := McLAU.T) (S := r32 McLAU.SRT)
    (SI := r32 McLAU.SRI) fun i hi => (penumPt_specH (u_pt (by rw [← uBase.2.2.1]; exact hi))).2.2.2
  rw [uBase.2.2.1] at h
  exact h

theorem conjClass_ge : 210 ≤ (CFSG.Sporadic.SmallOddCore.conjClass McLProof.K uP).ncard := by
  classical
  let L : List (Equiv.Perm (Fin 275)) := (List.range 210).map fun i => tablePerm 275 (tb (McLAU.T i))
  have hL : ∀ i < 210, Rep 275 (tb (McLAU.T i)) (tablePerm 275 (tb (McLAU.T i))) := fun i hi => by
    obtain ⟨-, c, -, hr⟩ := u_conj i hi
    rw [tablePerm_eq hr]
    exact hr
  have hnd : L.Nodup := by
    refine List.Nodup.map_on (fun a ha b hb e => ?_) List.nodup_range
    have ha' := List.mem_range.1 ha
    have hb' := List.mem_range.1 hb
    exact u_inj a ha' b hb' (Nat.eq_of_beq_eq_true
      ((beq_iff (u_conj a ha').1 (u_conj b hb').1 (hL a ha') (hL b hb')).2 e))
  have hsub : (L.toFinset : Set (Equiv.Perm (Fin 275))) ⊆
      CFSG.Sporadic.SmallOddCore.conjClass McLProof.K uP := by
    intro y hy
    rw [Finset.mem_coe, List.mem_toFinset] at hy
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hy
    obtain ⟨-, c, hc, hr⟩ := u_conj i (List.mem_range.1 hi)
    exact ⟨c, hc, tablePerm_eq hr⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd] at h1
  simpa [L] using h1

theorem card_CK : Nat.card ↥(McLProof.K ⊓ centralizer ({uP} : Set (Equiv.Perm (Fin 275)))) ≤ 192 := by
  have h := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card McLProof.K uP
  rw [McLC.card_K] at h
  have h2 := Nat.mul_le_mul_right
    (Nat.card ↥(McLProof.K ⊓ centralizer ({uP} : Set (Equiv.Perm (Fin 275))))) conjClass_ge
  omega

theorem conj_in_V {g : Equiv.Perm (Fin 275)} (hg : g ∈ NN) {v : Equiv.Perm (Fin 275)}
    (hv : v ∈ z2Set) (hv1 : v ≠ 1) :
    g * v * g⁻¹ = McLProof.pa ∨ g * v * g⁻¹ = uP ∨ g * v * g⁻¹ = McLProof.pa * uP := by
  have h := (mem_set_normalizer_iff.1 hg.2 v).1 hv
  obtain ⟨q, hq, e⟩ := mem_z2Set.1 h
  simp only [vPL, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact absurd (by simpa using e : v = 1) hv1
  · exact Or.inl e
  · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr e)

theorem card_NN_le : Nat.card NN ≤ 1152 := by
  classical
  let f : Equiv.Perm (Fin 275) → Equiv.Perm (Fin 275) × Equiv.Perm (Fin 275) :=
    fun g => (g * McLProof.pa * g⁻¹, g * uP * g⁻¹)
  let T6 : Finset (Equiv.Perm (Fin 275) × Equiv.Perm (Fin 275)) :=
    [(McLProof.pa, uP), (McLProof.pa, McLProof.pa * uP), (uP, McLProof.pa),
      (uP, McLProof.pa * uP), (McLProof.pa * uP, McLProof.pa),
      (McLProof.pa * uP, uP)].toFinset
  let sN : Finset (Equiv.Perm (Fin 275)) := (NN : Set (Equiv.Perm (Fin 275))).toFinset
  let C : Subgroup (Equiv.Perm (Fin 275)) :=
    McLProof.K ⊓ centralizer ({uP} : Set (Equiv.Perm (Fin 275)))
  let sC : Finset (Equiv.Perm (Fin 275)) := (C : Set (Equiv.Perm (Fin 275))).toFinset
  have hpa1 : McLProof.pa ≠ 1 := McLProof.pa_ne_one
  have himg : sN.image f ⊆ T6 := by
    intro b hb
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hb
    have hg' : g ∈ NN := by simpa [sN] using hg
    have hne : g * McLProof.pa * g⁻¹ ≠ g * uP * g⁻¹ := fun e =>
      uP_ne_pa (mul_left_cancel (mul_right_cancel e)).symm
    have ha := conj_in_V hg' pa_mem_z2 hpa1
    have hu := conj_in_V hg' uP_mem_z2 uP_ne_one
    simp only [T6, f, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq]
    rcases ha with ha | ha | ha <;> rcases hu with hu | hu | hu <;>
      rw [ha, hu] at hne ⊢ <;> simp_all
  have hfib : ∀ b ∈ sN.image f, (sN.filter fun a => f a = b).card ≤ 192 := by
    intro b hb
    obtain ⟨g0, hg0, rfl⟩ := Finset.mem_image.1 hb
    have hg0' : g0 ∈ NN := by simpa [sN] using hg0
    have hle : (sN.filter fun a => f a = f g0).card ≤ sC.card := by
      refine Finset.card_le_card_of_injOn (fun x => g0⁻¹ * x) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        obtain ⟨hxN, hfx⟩ := hx
        have hx' : x ∈ NN := by simpa [sN] using hxN
        have e1 : x * McLProof.pa * x⁻¹ = g0 * McLProof.pa * g0⁻¹ := congrArg Prod.fst hfx
        have e2 : x * uP * x⁻¹ = g0 * uP * g0⁻¹ := congrArg Prod.snd hfx
        have hP' : g0⁻¹ * x ∈ McLProof.P := mul_mem (inv_mem hg0'.1) hx'.1
        have c1 : g0⁻¹ * x * McLProof.pa = McLProof.pa * (g0⁻¹ * x) := by
          calc g0⁻¹ * x * McLProof.pa = g0⁻¹ * (x * McLProof.pa * x⁻¹) * x := by group
            _ = McLProof.pa * (g0⁻¹ * x) := by rw [e1]; group
        have c2 : g0⁻¹ * x * uP = uP * (g0⁻¹ * x) := by
          calc g0⁻¹ * x * uP = g0⁻¹ * (x * uP * x⁻¹) * x := by group
            _ = uP * (g0⁻¹ * x) := by rw [e2]; group
        have hK : g0⁻¹ * x ∈ McLProof.K := by
          rw [← McLProof.centralizerIn_P McLProof.card_P]
          exact mem_centralizerIn.2 ⟨hP', c1⟩
        have hC : g0⁻¹ * x ∈ C := ⟨hK, mem_centralizer_singleton_iff.2 c2⟩
        simpa [sC] using hC
      · intro x _ y _ e
        exact mul_left_cancel e
    have hsC : sC.card = Nat.card C :=
      (Nat.card_eq_card_toFinset (C : Set (Equiv.Perm (Fin 275)))).symm
    exact hle.trans (hsC.trans_le card_CK)
  have h1 := Finset.card_le_mul_card_image sN 192 hfib
  have h2 := (Finset.card_le_card himg).trans (List.toFinset_card_le _)
  have hsN : Nat.card NN = sN.card :=
    Nat.card_eq_card_toFinset (NN : Set (Equiv.Perm (Fin 275)))
  rw [hsN]
  calc sN.card ≤ 192 * (sN.image f).card := h1
    _ ≤ 192 * 6 := Nat.mul_le_mul_left _ (by simpa using h2)
    _ = 1152 := by norm_num

theorem card_NN : Nat.card NN = 1152 :=
  le_antisymm card_NN_le (Nat.le_of_dvd Nat.card_pos card_NN_dvd)

noncomputable abbrev qKH (l : Nat) : Equiv.Perm (Fin 275) :=
  if l = 1 then sg 0 else if l = 2 then sg 2 else hP (l - 3)

theorem khWords_letters : (∀ l ∈ CFSG.LocalAnalysis.WeakClosure81.SporMcL.khWordA, 1 ≤ l ∧ l ≤ 5) ∧
    ∀ l ∈ CFSG.LocalAnalysis.WeakClosure81.SporMcL.khWordB, 1 ≤ l ∧ l ≤ 5 := by
  decide +kernel

theorem GKH_eq {l : Nat} (hl : 1 ≤ l ∧ l ≤ 5) {y : Nat} (hy : y < 275) :
    GKH l y = actN (qKH l) y := by
  unfold GKH qKH
  by_cases h1 : l = 1
  · subst h1
    rw [if_pos rfl, actN_sg (by norm_num) hy]
    rfl
  by_cases h2 : l = 2
  · subst h2
    rw [if_neg (by decide), if_pos rfl, actN_sg (by norm_num) hy]
    rfl
  have b1 : Nat.beq l 1 = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  have b2 : Nat.beq l 2 = false := Bool.eq_false_iff.2 fun h => h2 (Nat.eq_of_beq_eq_true h)
  rw [b1, b2, if_neg h1, if_neg h2]
  obtain ⟨hc, hr⟩ := hG_facts (j := l - 3) (by omega)
  have := hr y hy
  rw [ap_unpack hc hy, idx_eq] at this
  exact this

theorem qKH_mem {l : Nat} (hl : 1 ≤ l ∧ l ≤ 5) : qKH l ∈ McLProof.K ⊔ NN := by
  unfold qKH
  split_ifs
  · refine le_sup_left (a := McLProof.K) ?_
    change sg 0 ∈ genOf 275 McLData.kgens
    rw [genOf_kgens]
    exact sg0_mem
  · refine le_sup_left (a := McLProof.K) ?_
    change sg 2 ∈ genOf 275 McLData.kgens
    rw [genOf_kgens]
    exact sg2_mem
  · exact le_sup_right (a := McLProof.K) (hP_mem (by omega))

theorem P_le_sup : McLProof.P ≤ McLProof.K ⊔ NN := by
  have hw := word_ok
  have hA : ∀ x < 275, actN alP x =
      actN (wp qKH CFSG.LocalAnalysis.WeakClosure81.SporMcL.khWordA) x := fun x hx => by
    have h := ((bAnd_iff _ _).1 (allN_spec hw x hx)).1
    rw [actN_alP hx, ← Nat.eq_of_beq_eq_true h]
    exact foldr_wp (fun c hc y hy => GKH_eq (khWords_letters.1 c hc) hy) hx
  have hB : ∀ x < 275, actN beP x =
      actN (wp qKH CFSG.LocalAnalysis.WeakClosure81.SporMcL.khWordB) x := fun x hx => by
    have h := ((bAnd_iff _ _).1 (allN_spec hw x hx)).2
    rw [actN_beP hx, ← Nat.eq_of_beq_eq_true h]
    exact foldr_wp (fun c hc y hy => GKH_eq (khWords_letters.2 c hc) hy) hx
  rw [closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ McLData.abT := by simpa using hg
  simp only [McLData.abT, List.mem_cons, List.not_mem_nil, or_false] at hg'
  rcases hg' with rfl | rfl
  · rw [tp_Ta, perm_ext hA]
    exact wp_mem fun c hc => qKH_mem (khWords_letters.1 c hc)
  · rw [tp_eq rep_Tb, perm_ext hB]
    exact wp_mem fun c hc => qKH_mem (khWords_letters.2 c hc)

theorem mcl_facts : McLProof.pa ∈ McLProof.S ∧
    (∀ x ∈ McLProof.S, (∀ t ∈ McLProof.S, x * t = t * x) → x = 1 ∨ x = McLProof.pa) ∧
    Nat.card ↥(McLProof.P ⊓ normalizer z2Set) = 1152 ∧
    McLProof.P ≤ McLProof.K ⊔ (McLProof.P ⊓ normalizer z2Set) :=
  ⟨pa_mem_S, center_S, card_NN, P_le_sup⟩

end CertificateChecks.KernelSpor.McLAsch

end
