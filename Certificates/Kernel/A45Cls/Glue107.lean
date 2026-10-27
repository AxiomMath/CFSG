
module

public import Certificates.Kernel.A45Cls.Glue218c
public import Certificates.Kernel.A45Cls.Checks5
public import Certificates.Kernel.A45Cls.Checks6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10F107Over
public import Certificates.Data.OmegaS107Facts
public import CFSG.Sporadic.Th.Max3.Data
public import Certificates.Kernel.SporSch.Co2M.ThirdGlue
public import Certificates.Certificate3042Base
public import Certificates.Certificate3055Base
public import CFSG.Certificates.Kernel.SporSch.Co2ThirdSound
public import CFSG.Certificates.Kernel.SporSch.ThirdChainHPrelude
public import CFSG.Certificates.Kernel.SporSch.ThirdDfsBase
public import CFSG.Certificates.Kernel.SporSch.ThirdDfsPrelude
public import CFSG.Sporadic.Co2Schreier.Centralizers

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelA45

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.OrbGroup
  CFSG.KC.EnumSound CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.GH74.KGroups CFSG.Sporadic.Schreier Subgroup CFSG.KC.LeftOrb CFSG.KC.BfsPin
  CFSG.KC.ConjOrb Certificates.OmegaS107

local notation "P45" => Equiv.Perm (Fin 45)

abbrev T0 : Subgroup P45 := QT0.originalSubgroup

@[expose] def t0g (k : ℕ) : P45 := (gensT0 ()).getD k 1

@[expose] def qg (k : ℕ) : P45 :=
  [Certificates.OmegaF1051.gq1 (), Certificates.OmegaF1051.gq2 (), Certificates.OmegaF1051.gq3 (),
    Certificates.OmegaF1051.gq4 ()].getD k 1

@[expose] def wvA (l : List ℕ) : P45 := (l.map gA').prod

@[expose] def bg (j k : ℕ) : P45 := wvA ((bW j).getD k [])

theorem prep_pid : PRep 45 6 (pidn 45 6) 1 := prep_pidn (by norm_num) (by norm_num)

theorem prep_wvA {l : List ℕ} (hl : lettersK 3 l = true) : PRep 45 6 (wordK 45 6 KA.G l) (wvA l) ∧
    wvA l ∈ A := by
  refine ⟨wordK_prep (by norm_num) (by norm_num) _ fun k hk => prep_gA k (lettersK_spec hl k hk),
    list_prod_mem fun y hy => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  exact gA'_mem (lettersK_spec hl k hk)

theorem exN_of {N : ℕ} {f : ℕ → Bool} {i : ℕ} (hi : i < N) (h : f i = true) : exN N f = true := by
  unfold exN
  cases e : allN N fun i => !f i
  · rfl
  · have := PK.allN_iff.1 e i hi
    rw [h] at this
    exact absurd this (by decide)

theorem eqP_sound {P Q : ℕ} {g h : P45} (e : eqP 45 6 P Q = true) (hP : PRep 45 6 P g)
    (hQ : PRep 45 6 Q h) : g = h := by
  simpa using eq22_sound e hP prep_pid hQ prep_pid

theorem eqP_of {P Q : ℕ} {g : P45} (hP : PRep 45 6 P g) (hQ : PRep 45 6 Q g) :
    eqP 45 6 P Q = true :=
  eq22_of_eq hP prep_pid hQ prep_pid rfl

theorem inPts_spec {N P : ℕ} {T : ℕ → ℕ} {c : ℕ → P45} {v : P45}
    (hc : ∀ i < N, PRep 45 6 (T i) (c i)) (h : inPts 45 6 N T P = true) (hv : PRep 45 6 P v) :
    ∃ i < N, c i = v := by
  obtain ⟨i, hi, e⟩ := exN_spec h
  exact ⟨i, hi, eqP_sound e (hc i hi) hv⟩

theorem inPts_of {N P i : ℕ} {T : ℕ → ℕ} {v : P45} (hi : i < N) (hT : PRep 45 6 (T i) v)
    (hv : PRep 45 6 P v) : inPts 45 6 N T P = true :=
  exN_of hi (eqP_of hT hv)

theorem getD_mem_or {α : Type*} (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases h : i < l.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (not_lt.1 h)

theorem enum_A {N ng : ℕ} {G T E D S : ℕ → ℕ} {g : ℕ → P45}
    (hg : ∀ k < ng, PRep 45 6 (G k) (g k))
    (hcl : ∀ i < N, closPtL 45 6 ng N G T E i = true)
    (htr : ∀ i < N, treePt ng N 0 E D i = true) (hN : 0 < N) (h0 : T 0 = pidn 45 6)
    (hK : distinctK N (fun i => pkeyK 45 6 ps (T i)) S = true) :
    ∃ c : ℕ → P45, (∀ i < N, PRep 45 6 (T i) (c i) ∧ c i ∈ closure (g '' {k | k < ng})) ∧
      (∀ y ∈ closure (g '' {k | k < ng}), ∃ i < N, c i = y) ∧
      Nat.card (closure (g '' {k | k < ng})) = N := by
  have hid : PRep 45 6 (T 0) 1 := by
    rw [h0]
    exact prep_pid
  obtain ⟨c, hc0, hc, hmem, hcl', hinj⟩ := leftOrb_reps (g := g) hn45 hg hcl htr hN hid ps_lt hK
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) (fun _ _ h => h) g c ⟨0, hN, hc0⟩ hmem
    hcl' hinj
  exact ⟨c, fun i hi => ⟨hc i hi, hmem i hi⟩, fun y hy => hall y hy, hcard⟩

theorem closure_t0g : closure (t0g '' {k | k < 3}) = T0 := by
  change Subgroup.closure _ = QT0.originalSubgroup
  rw [QT0, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, t0g, gensT0]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩

theorem t0g_mem {k : ℕ} (hk : k < 3) : t0g k ∈ T0 := by
  have h : t0g k ∈ closure (t0g '' {k | k < 3}) := subset_closure ⟨k, hk, rfl⟩
  rwa [closure_t0g] at h

theorem closure_qg : closure (qg '' {k | k < 4}) = Q0 := by
  unfold Q0
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, qg, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
    · exact ⟨3, by norm_num, rfl⟩

theorem prep_t0g : ∀ k < 3, PRep 45 6 (TZ.G k) (t0g k) := by
  obtain ⟨b0, b1, b2, -⟩ := binds3
  intro k hk
  interval_cases k
  · rw [← b0]
    exact prep_cOf _
  · rw [← b1]
    exact prep_cOf _
  · rw [← b2]
    exact prep_cOf _

theorem prep_qg : ∀ k < 4, PRep 45 6 (QZ.G k) (qg k) := by
  obtain ⟨-, -, -, b0, b1, b2, b3, -⟩ := binds3
  intro k hk
  interval_cases k
  · rw [← b0]
    exact prep_cOf _
  · rw [← b1]
    exact prep_cOf _
  · rw [← b2]
    exact prep_cOf _
  · rw [← b3]
    exact prep_cOf _

theorem t0_enum : ∃ c : ℕ → P45, (∀ i < 64, PRep 45 6 (TZ.T i) (c i) ∧ c i ∈ T0) ∧
    ∀ y ∈ T0, ∃ i < 64, c i = y := by
  obtain ⟨c, hc, hall, -⟩ := enum_A prep_t0g TZ.cl TZ.tr (by decide) ids3.1 TZ.k
  rw [closure_t0g] at hc hall
  exact ⟨c, hc, hall⟩

theorem q_enum : ∃ c : ℕ → P45, (∀ i < 32, PRep 45 6 (QZ.T i) (c i) ∧ c i ∈ Q0) ∧
    ∀ y ∈ Q0, ∃ i < 32, c i = y := by
  obtain ⟨c, hc, hall, -⟩ := enum_A prep_qg QZ.cl QZ.tr (by decide) ids3.2.1 QZ.k
  rw [closure_qg] at hc hall
  exact ⟨c, hc, hall⟩

theorem q0_le : Q0 ≤ T0 := by
  rw [← closure_qg, closure_le]
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨c, hc, -⟩ := t0_enum
  obtain ⟨i, hi, e⟩ := inPts_spec (fun i hi => (hc i hi).1)
    (PK.allN_iff.1 zFacts.2.2.2.2.2.2.1 k hk) (prep_qg k hk)
  rw [← e]
  exact (hc i hi).2

theorem t0I_lt (p : ℕ) : t0If p < 64 := by
  unfold t0If
  rcases getD_mem_or t0I p 0 with h | h
  · exact witBounds.1 _ h
  · rw [h]
    norm_num

theorem prep_t0I {c : ℕ → P45} (hc : ∀ i < 64, PRep 45 6 (TZ.T i) (c i)) {p : ℕ} (hp : p < 64) :
    c (t0If p) = (c p)⁻¹ := by
  have h := PK.allN_iff.1 zFacts.2.2.2.2.2.1 p hp
  rw [isIdK_iff (prep_pcomp hn45 (hc p hp) (hc _ (t0I_lt p)))] at h
  exact eq_inv_of_mul_eq_one_right h

@[expose] noncomputable def dT (c : ℕ → P45) (u : P45) (p : ℕ) : P45 :=
  if p < 64 then c p else c (p - 64) * u

theorem prep_tP {c : ℕ → P45} (hc : ∀ i < 64, PRep 45 6 (TZ.T i) (c i)) {U Ui : ℕ} {u : P45}
    (hu : PRep 45 6 U u) (hui : PRep 45 6 Ui u⁻¹) {p : ℕ} (hp : p < 128) :
    PRep 45 6 (tP 45 6 64 TZ.T U p) (dT c u p) ∧
      PRep 45 6 (tPI 45 6 64 TZ.T t0If Ui p) (dT c u p)⁻¹ := by
  by_cases h : p < 64
  · have hb : Nat.blt p 64 = true := Nat.blt_eq.mpr h
    have e1 : tP 45 6 64 TZ.T U p = TZ.T p := by
      unfold tP
      rw [hb]
    have e2 : tPI 45 6 64 TZ.T t0If Ui p = TZ.T (t0If p) := by
      unfold tPI
      rw [hb]
    rw [e1, e2, dT, if_pos h]
    refine ⟨hc p h, ?_⟩
    rw [← prep_t0I hc h]
    exact hc _ (t0I_lt p)
  · have hb : Nat.blt p 64 = false := by
      cases e : Nat.blt p 64
      · rfl
      · exact absurd (Nat.blt_eq.mp e) h
    have e1 : tP 45 6 64 TZ.T U p = pcomp 45 6 (mask 6) (TZ.T (p - 64)) U := by
      unfold tP
      rw [hb]
    have e2 : tPI 45 6 64 TZ.T t0If Ui p = pcomp 45 6 (mask 6) Ui (TZ.T (t0If (p - 64))) := by
      unfold tPI
      rw [hb]
    have hq : p - 64 < 64 := by omega
    rw [e1, e2, dT, if_neg h]
    refine ⟨prep_pcomp hn45 (hc _ hq) hu, ?_⟩
    rw [mul_inv_rev, ← prep_t0I hc hq]
    exact prep_pcomp hn45 hui (hc _ (t0I_lt _))

theorem prep_cjP {c : ℕ → P45} (hc : ∀ i < 64, PRep 45 6 (TZ.T i) (c i)) {U Ui X : ℕ} {u x : P45}
    (hu : PRep 45 6 U u) (hui : PRep 45 6 Ui u⁻¹) (hx : PRep 45 6 X x) {p : ℕ} (hp : p < 128) :
    PRep 45 6 (cjP 45 6 64 TZ.T t0If U Ui p X) (dT c u p * x * (dT c u p)⁻¹) := by
  obtain ⟨h1, h2⟩ := prep_tP hc hu hui hp
  rw [mul_assoc]
  exact prep_pcomp hn45 h1 (prep_pcomp hn45 hx h2)

theorem prep_cjProd {c : ℕ → P45} (hc : ∀ i < 64, PRep 45 6 (TZ.T i) (c i)) {U Ui X : ℕ}
    {u x : P45} (hu : PRep 45 6 U u) (hui : PRep 45 6 Ui u⁻¹) (hx : PRep 45 6 X x) :
    ∀ l : List ℕ, (∀ p ∈ l, p < 128) → ∃ v, PRep 45 6 (cjProd 45 6 64 TZ.T t0If U Ui X l) v ∧
      ∀ Y : Subgroup P45, (∀ p < 128, dT c u p * x * (dT c u p)⁻¹ ∈ Y) → v ∈ Y
  | [], _ => ⟨1, prep_pid, fun Y _ => Y.one_mem⟩
  | p :: l, hl => by
    obtain ⟨v, hv, hY⟩ := prep_cjProd hc hu hui hx l fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p List.mem_cons_self
    refine ⟨_, prep_pcomp hn45 (prep_cjP hc hu hui hx hp) hv, fun Y hY' => ?_⟩
    exact Y.mul_mem (hY' p hp) (hY Y hY')

theorem dT_mem {c : ℕ → P45} (hc : ∀ i < 64, PRep 45 6 (TZ.T i) (c i) ∧ c i ∈ T0)
    {T : Subgroup P45} (hT0 : T0 ≤ T) {u : P45} (hu : u ∈ T) {p : ℕ} (hp : p < 128) :
    dT c u p ∈ T := by
  unfold dT
  split_ifs with h
  · exact hT0 (hc p h).2
  · exact T.mul_mem (hT0 (hc _ (by omega)).2) hu

theorem dT_cover
    {c : ℕ → P45} (hall : ∀ y ∈ T0, ∃ i < 64, c i = y) {T : Subgroup P45} (hT0 : T0 ≤ T)
    (hTA : T ≤ A) (hT2 : IsPGroup 2 T) {u : P45} (hu : u ∈ T) (hu0 : u ∉ T0) {y : P45}
    (hy : y ∈ T) : ∃ p < 128, dT c u p = y := by
  by_cases h : y ∈ T0
  · obtain ⟨i, hi, rfl⟩ := hall y h
    exact ⟨i, by omega, by rw [dT, if_pos hi]⟩
  · obtain ⟨a, ha, rfl⟩ :=
      CFSG.OddStandard.SmallF3.Omega.Mo107.exists_mul_over hT0 hTA hT2 hu hu0 hy h
    obtain ⟨i, hi, rfl⟩ := hall a ha
    exact ⟨i + 64, by omega, by rw [dT, if_neg (by omega), Nat.add_sub_cancel]⟩

theorem model_at
    {T : Subgroup P45} (hT0 : T0 ≤ T) (hTA : T ≤ A) (hT2 : IsPGroup 2 T) {j : ℕ} (hj : j < 3)
    (huT : wvA (uW.getD j []) ∈ T) (huT0 : wvA (uW.getD j []) ∉ T0)
    {BG BT BE BD BS : ℕ → ℕ} (hbcl : ∀ i < 16, closPtL 45 6 4 16 BG BT BE i = true)
    (hbtr : ∀ i < 16, treePt 4 16 0 BE BD i = true) (hb0 : BT 0 = pidn 45 6)
    (hbK : distinctK 16 (fun i => pkeyK 45 6 ps (BT i)) BS = true)
    (hbw : bindWs 45 6 3 KA.G BG (bW j) 0 = true)
    (hy : (isInvK 45 6 (y2P j) && Nat.beq (fixK 45 6 (y2P j)) 15 &&
      !inPts 45 6 64 TZ.T (y2P j)) = true)
    (hb2 : b2K 45 6 3 32 TZ.G QZ.T BT (uP j) (y2P j) = true)
    (hout : outK 45 6 64 TZ.T t0If BT BG (uP j) (uiP j) (aWit j) (bWit j) = true) :
    ∃ B2 y2, M107 T B2 y2 := by
  obtain ⟨c0, hc0, hc0all⟩ := t0_enum
  obtain ⟨cq, hcq, hcqall⟩ := q_enum
  have hbwl : (bW j).length = 4 := by interval_cases j <;> rfl
  have hbg : ∀ k < 4, PRep 45 6 (BG k) (bg j k) := fun k hk => (prep_word hbw (by omega)).1
  obtain ⟨cb, hcb, hcball, hcard⟩ := enum_A hbg hbcl hbtr (by norm_num) hb0 hbK
  set B2 := closure (bg j '' {k | k < 4}) with hB2
  set u := wvA (uW.getD j []) with hu_def
  obtain ⟨hl1, -⟩ := Bool.and_eq_true _ _ ▸ binds3.2.2.2.2.2.2.2.2.2.2
  have hlet := PK.allN_iff.1 (Bool.and_eq_true _ _ ▸ binds3.2.2.2.2.2.2.2.2.2.2).2 j hj
  rw [Bool.and_eq_true] at hlet
  have hu : PRep 45 6 (uP j) u := (prep_wvA hlet.1).1
  have hui : PRep 45 6 (uiP j) u⁻¹ := by
    have h := PK.allN_iff.1 zFacts.2.2.1 j hj
    have hw : PRep 45 6 (uiP j) (wvA (uiW.getD j [])) := (prep_wvA hlet.2).1
    rw [isIdK_iff (prep_pcomp hn45 hu hw)] at h
    rw [← eq_inv_of_mul_eq_one_right h]
    exact hw
  have hyb : y2p j < 64 := witBounds.2.2.1 j hj
  set y2 := c0 (y2p j) * u with hy2_def
  have hy2 : PRep 45 6 (y2P j) y2 := prep_pcomp hn45 (hc0 _ hyb).1 hu
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hy
  obtain ⟨⟨hyinv, hyfix⟩, hyout⟩ := hy
  have hy2T0 : y2 ∉ T0 := by
    intro h
    obtain ⟨i, hi, e⟩ := hc0all y2 h
    rw [inPts_of hi (e ▸ (hc0 i hi).1) hy2] at hyout
    exact absurd hyout (by decide)
  have hy2T : y2 ∈ T := T.mul_mem (hT0 (hc0 _ hyb).2) huT
  have hord : orderOf y2 = 2 := (isInvK_iff hn45 hy2).1 hyinv
  have hy2sq : y2 * y2 = 1 := by
    rw [← sq, ← hord]
    exact pow_orderOf_eq_one y2
  have hy21 : y2 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  simp only [b2K, Bool.and_eq_true] at hb2
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb2
  have hmemB : ∀ b : P45, b ∈ B2 ↔
      (b ∈ Q0 ∧ b * y2 = y2 * b) ∨ ∃ c ∈ Q0, c * y2 = y2 * c ∧ c * y2 = b := by
    intro b
    constructor
    · intro hb
      obtain ⟨m, hm, rfl⟩ := hcball b hb
      have h := PK.allN_iff.1 h1 m hm
      simp only [Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with ⟨hq, hc⟩ | h
      · obtain ⟨k, hk, e⟩ := inPts_spec (fun i hi => (hcq i hi).1) hq (hcb m hm).1
        exact Or.inl ⟨e ▸ (hcq k hk).2, eq22_sound hc (hcb m hm).1 hy2 hy2 (hcb m hm).1⟩
      · obtain ⟨k, hk, e⟩ := exN_spec h
        rw [Bool.and_eq_true] at e
        refine Or.inr ⟨cq k, (hcq k hk).2, eq22_sound e.1 (hcq k hk).1 hy2 hy2 (hcq k hk).1, ?_⟩
        simpa using eq22_sound e.2 (hcq k hk).1 hy2 (hcb m hm).1 prep_pid
    · intro hb
      have key : ∀ c ∈ Q0, c * y2 = y2 * c → c ∈ B2 ∧ c * y2 ∈ B2 := by
        intro c hc hcy
        obtain ⟨k, hk, rfl⟩ := hcqall c hc
        have h := PK.allN_iff.1 h2 k hk
        simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
        rcases h with h | ⟨ha, hb'⟩
        · rw [eq22_of_eq (hcq k hk).1 hy2 hy2 (hcq k hk).1 hcy] at h
          exact absurd h (by decide)
        · obtain ⟨m, hm, e⟩ := inPts_spec (fun i hi => (hcb i hi).1) ha (hcq k hk).1
          obtain ⟨m', hm', e'⟩ := inPts_spec (fun i hi => (hcb i hi).1) hb'
            (prep_pcomp hn45 (hcq k hk).1 hy2)
          exact ⟨e ▸ (hcb m hm).2, e' ▸ (hcb m' hm').2⟩
      rcases hb with ⟨hq, hc⟩ | ⟨c, hc, hcy, rfl⟩
      · exact (key b hq hc).1
      · exact (key c hc hcy).2
  have hcomm : ∀ a ∈ B2, ∀ b ∈ B2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, hm, rfl⟩ := hcball a ha
    obtain ⟨m', hm', rfl⟩ := hcball b hb
    have h := PK.allN_iff.1 h3 m hm
    rw [Bool.and_eq_true] at h
    exact eq22_sound (PK.allN_iff.1 h.2 m' hm') (hcb m hm).1 (hcb m' hm').1 (hcb m' hm').1
      (hcb m hm).1
  have hsq : ∀ a ∈ B2, a * a = 1 := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := hcball a ha
    have h := PK.allN_iff.1 h3 m hm
    rw [Bool.and_eq_true] at h
    exact (isIdK_iff (prep_pcomp hn45 (hcb m hm).1 (hcb m hm).1)).1 h.1
  have hle : B2 ≤ T := by
    intro b hb
    rcases (hmemB b).1 hb with ⟨hq, -⟩ | ⟨c, hc, -, rfl⟩
    · exact hT0 (q0_le hq)
    · exact T.mul_mem (hT0 (q0_le hc)) hy2T
  have hTle : T ≤ closure (t0g '' {k | k < 3} ∪ {u}) := by
    intro x hx
    by_cases hxT0 : x ∈ T0
    · rw [← closure_t0g] at hxT0
      exact closure_mono Set.subset_union_left hxT0
    · obtain ⟨a, ha, rfl⟩ :=
        CFSG.OddStandard.SmallF3.Omega.Mo107.exists_mul_over hT0 hTA hT2 huT huT0 hx hxT0
      have ha' : a ∈ closure (t0g '' {k | k < 3}) := by
        rw [closure_t0g]
        exact ha
      exact mul_mem (closure_mono Set.subset_union_left ha')
        (subset_closure (Set.mem_union_right _ rfl))
  have hconjB : ∀ {g : P45} {G : ℕ}, PRep 45 6 G g →
      (∀ m < 16, exN 16 (fun m' => eq22 45 6 (mask 6) G (BT m) (BT m') G) = true) →
      ∀ b ∈ B2, g * b * g⁻¹ ∈ B2 := by
    intro g G hG hc b hb
    obtain ⟨m, hm, rfl⟩ := hcball b hb
    obtain ⟨m', hm', e⟩ := exN_spec (hc m hm)
    have e' := eq22_sound e hG (hcb m hm).1 (hcb m' hm').1 hG
    rw [e', mul_inv_cancel_right]
    exact (hcb m' hm').2
  have hnorm : ∀ g ∈ T, ∀ b ∈ B2, g * b * g⁻¹ ∈ B2 := by
    refine fun g hg => conj_closed_A (O := (B2 : Set P45)) ?_ g (hTle hg)
    rintro s (⟨k, hk, rfl⟩ | rfl)
    · exact hconjB (prep_t0g k hk) fun m hm => by
        have h := PK.allN_iff.1 h4 m hm
        rw [Bool.and_eq_true] at h
        exact PK.allN_iff.1 h.1 k hk
    · exact hconjB hu fun m hm => by
        have h := PK.allN_iff.1 h4 m hm
        rw [Bool.and_eq_true] at h
        exact h.2
  have hcover : ∀ y ∈ T, ∃ p < 128, dT c0 u p = y := fun y hy =>
    dT_cover hc0all hT0 hTA hT2 huT huT0 hy
  have hc0' : ∀ i < 64, PRep 45 6 (TZ.T i) (c0 i) := fun i hi => (hc0 i hi).1
  have houter : ∀ x ∈ T, x ∉ T0 → x * x = 1 → ∃ X, PRep 45 6 X x ∧
      ∃ aw bw, (∀ ws ∈ aw, ∀ p ∈ ws, p < 128) ∧ bw.getD 1 0 < 16 ∧
        outX 45 6 64 TZ.T t0If BT BG (uP j) (uiP j) X aw bw = true := by
    intro x hx hx0 hxx
    obtain ⟨a, ha, rfl⟩ :=
      CFSG.OddStandard.SmallF3.Omega.Mo107.exists_mul_over hT0 hTA hT2 huT huT0 hx hx0
    obtain ⟨i, hi, rfl⟩ := hc0all a ha
    have hX := prep_pcomp hn45 (hc0 i hi).1 hu
    refine ⟨_, hX, (aWit j).getD i [], (bWit j).getD i [], ?_, ?_, ?_⟩
    · intro ws hws p hp
      rcases getD_mem_or (aWit j) i [] with h | h
      · exact witBounds.2.2.2.1 j hj _ h ws hws p hp
      · rw [h] at hws
        exact absurd hws (by simp)
    · rcases getD_mem_or (bWit j) i [] with h | h
      · exact (witBounds.2.2.2.2 j hj _ h).2
      · rw [h]
        norm_num
    · have h := PK.allN_iff.1 hout i hi
      rw [strictB_eq', Bool.or_eq_true, Bool.not_eq_true'] at h
      rcases h with h | h
      · have hinv : isInvK 45 6 (pcomp 45 6 (mask 6) (TZ.T i) (uP j)) = true := by
          rw [isInvK_iff hn45 hX]
          refine orderOf_eq_prime (by rw [sq]; exact hxx) fun h1 => hx0 ?_
          rw [h1]
          exact T0.one_mem
        rw [hinv] at h
        exact absurd h (by decide)
      · exact h
  have hdT : ∀ p < 128, dT c0 u p ∈ T := fun p hp => dT_mem hc0 hT0 huT hp
  have hX : ∀ X : Subgroup P45, X ≤ T → (∀ a ∈ X, ∀ b ∈ X, a * b = b * a) →
      (∀ a ∈ X, a * a = 1) → ¬ X ≤ T0 → ∃ x ∈ X, x ∉ T0 ∧ ∃ P, PRep 45 6 P x ∧
        ∃ aw bw, (∀ ws ∈ aw, ∀ p ∈ ws, p < 128) ∧ bw.getD 1 0 < 16 ∧
          outX 45 6 64 TZ.T t0If BT BG (uP j) (uiP j) P aw bw = true := by
    intro X hXT _ hXs hX0
    obtain ⟨x, hxX, hx0⟩ := SetLike.not_le_iff_exists.1 hX0
    exact ⟨x, hxX, hx0, houter x (hXT hxX) hx0 (hXs x hxX)⟩
  refine ⟨B2, y2, ⟨hle, hcomm, hsq, hcard, hnorm, ?_, hy2T0, ?_, hmemB, ?_, ?_⟩⟩
  · exact (hmemB y2).2 (Or.inr ⟨1, Q0.one_mem, by simp, by simp⟩)
  · refine ⟨hTA hy2T, hy2sq, hy21, ?_⟩
    rw [card_cent_eq (hTA hy2T) hy2sq hy21, ← fixK_eq hy2, Nat.eq_of_beq_eq_true hyfix]
    rfl
  · intro X hXT hXc hXs hXcard hXn hX0
    obtain ⟨x, hxX, -, P, hP, aw, bw, haw, -, ho⟩ := hX X hXT hXc hXs hX0
    unfold outX at ho
    simp only [Bool.or_eq_true, Bool.and_eq_true] at ho
    rcases ho with ⟨-, hgen⟩ | ⟨⟨⟨⟨hnc, -⟩, -⟩, hp⟩, -⟩
    · have hBX : B2 ≤ X := by
        rw [hB2, closure_le]
        rintro _ ⟨k, hk, rfl⟩
        have hk' := PK.allN_iff.1 hgen k hk
        have hl : ∀ p ∈ aw.getD k [], p < 128 := by
          intro p hp
          rcases getD_mem_or aw k [] with h | h
          · exact haw _ h p hp
          · rw [h] at hp
            exact absurd hp (by simp)
        obtain ⟨v, hv, hY⟩ := prep_cjProd hc0' hu hui hP (aw.getD k []) hl
        rw [eqP_sound hk' (hbg k hk) hv]
        exact hY X fun p hp => hXn _ (hdT p hp) x hxX
      exact (Subgroup.eq_of_le_of_card_ge hBX (by rw [hXcard, hcard])).symm
    · exfalso
      have hp' : bw.getD 0 0 < 128 := by
        have := Nat.blt_eq.mp hp
        omega
      have hcj := prep_cjP hc0' hu hui hP hp'
      rw [strictB_eq', Bool.not_eq_true'] at hnc
      have hin := hXn _ (hdT _ hp') x hxX
      rw [eq22_of_eq hcj hP hP hcj (hXc _ hin x hxX)] at hnc
      exact absurd hnc (by decide)
  · intro X hXT hXc hXs hXcard hX0
    obtain ⟨x, hxX, hx0, P, hP, aw, bw, -, hbw, ho⟩ := hX X hXT hXc hXs hX0
    unfold outX at ho
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at ho
    rcases ho with ⟨hxB, -⟩ | ⟨⟨⟨⟨-, hcnt⟩, hcm⟩, -⟩, hmout⟩
    · obtain ⟨m, hm, e⟩ := inPts_spec (fun i hi => (hcb i hi).1) hxB hP
      exact ⟨x, hxX, e ▸ (hcb m hm).2, hx0⟩
    · set m := bw.getD 1 0
      have hym := (hcb m hbw).1
      have hyc : cb m * x = x * cb m := eq22_sound hcm hym hP hP hym
      have hy0 : cb m ∉ T0 := by
        intro h
        obtain ⟨i, hi, e⟩ := hc0all _ h
        rw [inPts_of hi (e ▸ (hc0 i hi).1) hym] at hmout
        exact absurd hmout (by decide)
      let F := (Finset.range 128).filter fun p => (strictB (tP 45 6 64 TZ.T (uP j) p) fun g =>
        eq22 45 6 (mask 6) g P P g) = true
      have hF : F.card = 16 := by
        rw [← cntN_eq]
        exact Nat.eq_of_beq_eq_true hcnt
      have hsub : (X : Set P45) ⊆ (F.image (dT c0 u) : Set P45) := by
        intro g hg
        obtain ⟨p, hp, rfl⟩ := hcover g (hXT hg)
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, Finset.mem_filter.2
          ⟨Finset.mem_range.2 hp, ?_⟩, rfl⟩)
        rw [strictB_eq']
        exact eq22_of_eq (prep_tP hc0' hu hui hp).1 hP hP (prep_tP hc0' hu hui hp).1
          (hXc _ hg x hxX)
      have hfin : (F.image (dT c0 u) : Set P45).ncard ≤ 16 := by
        rw [Set.ncard_coe_finset, ← hF]
        exact Finset.card_image_le
      have hXn : (X : Set P45).ncard = 16 := by
        rw [← hXcard]
        exact (Nat.card_coe_set_eq (X : Set P45)).symm
      have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hXn]; exact hfin)
        (Set.toFinite _)
      have hyT : cb m ∈ T := hle (hcb m hbw).2
      obtain ⟨p, hp, e⟩ := hcover _ hyT
      have hyF : cb m ∈ (F.image (dT c0 u) : Set P45) := by
        refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, Finset.mem_filter.2
          ⟨Finset.mem_range.2 hp, ?_⟩, e⟩)
        rw [strictB_eq']
        exact eq22_of_eq (prep_tP hc0' hu hui hp).1 hP hP (prep_tP hc0' hu hui hp).1
          (e ▸ hyc)
      rw [← heq] at hyF
      exact ⟨cb m, hyF, (hcb m hbw).2, hy0⟩

theorem facts442006 : Facts := by
  refine ⟨q0_le, ?_, fun T hT0 hTA hT2 w hw hw0 => ?_⟩
  · obtain ⟨-, -, -, hcard⟩ := enum_A prep_qg QZ.cl QZ.tr (by decide) ids3.2.1 QZ.k
    rwa [closure_qg] at hcard
  obtain ⟨c0, hc0, hc0all⟩ := t0_enum
  have hnorm := CFSG.OddStandard.SmallF3.Omega.Mo107.normal_over hT0 hTA hT2 hw hw0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlet⟩ := binds3
  simp only [Bool.and_eq_true] at hlet
  obtain ⟨⟨hlc, hlci⟩, hlu⟩ := hlet
  set c := wvA czW
  have hcz : PRep 45 6 czP c := (prep_wvA hlc).1
  have hcA : c ∈ A := (prep_wvA hlc).2
  have hczi : PRep 45 6 cziP (wvA cziW) := (prep_wvA hlci).1
  have hci : wvA cziW = c⁻¹ := by
    have h := zFacts.2.1
    rw [isIdK_iff (prep_pcomp hn45 hcz hczi)] at h
    exact eq_inv_of_mul_eq_one_right h
  rw [hci] at hczi
  have htA : PRep 45 6 (KA.T KA.r0) (Certificates.P43Twin.tA ()) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, bt, -⟩ := binds
    rw [← bt]
    exact prep_cOf _
  set z := Certificates.OmegaT0.z0 ()
  have hz : PRep 45 6 zP z := prep_cOf _
  have hzc : z = c * Certificates.P43Twin.tA () * c⁻¹ := by
    rw [mul_assoc]
    exact eqP_sound zFacts.1 hz (prep_pcomp hn45 hcz (prep_pcomp hn45 htA hczi))
  have hz1 : z ≠ 1 := by
    intro h
    have h2 := fixC_conj (Certificates.P43Twin.tA ()) c
    rw [← hzc, h, fix_tA] at h2
    exact absurd h2 (by decide)
  have hzT0 : ∀ t ∈ T0, z * t = t * z := by
    intro t ht
    rw [← closure_t0g] at ht
    have hle : closure (t0g '' {k | k < 3}) ≤ centralizer ({z} : Set P45) := by
      rw [closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact mem_centralizer_singleton_iff.2
        (eq22_sound (PK.allN_iff.1 zFacts.2.2.2.2.1 k hk) hz (prep_t0g k hk) (prep_t0g k hk) hz).symm
    exact (mem_centralizer_singleton_iff.1 (hle ht)).symm
  have hzin : z ∈ T0 := by
    obtain ⟨i, hi, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) zFacts.2.2.2.2.2.2.2 hz
    exact e ▸ (hc0 i hi).2
  have hwz : w * z = z * w := by
    have hz' : w * z * w⁻¹ ∈ T0 := hnorm w hw z hzin
    obtain ⟨i, hi, e⟩ := hc0all _ hz'
    have hcomm : ∀ k < 3, c0 i * t0g k = t0g k * c0 i := by
      intro k hk
      have ht : w⁻¹ * t0g k * w⁻¹⁻¹ ∈ T0 := hnorm _ (T.inv_mem hw) _ (t0g_mem hk)
      have h := hzT0 _ ht
      rw [e]
      calc w * z * w⁻¹ * t0g k = w * (z * (w⁻¹ * t0g k * w⁻¹⁻¹)) * w⁻¹ := by group
        _ = w * ((w⁻¹ * t0g k * w⁻¹⁻¹) * z) * w⁻¹ := by rw [h]
        _ = t0g k * (w * z * w⁻¹) := by group
    have h := PK.allN_iff.1 zFacts.2.2.2.1 i hi
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases h with (h | h) | h
    · have : allN 3 (fun k => eq22 45 6 (mask 6) (TZ.T i) (TZ.G k) (TZ.G k) (TZ.T i)) = true :=
        PK.allN_iff.2 fun k hk => eq22_of_eq (hc0 i hi).1 (prep_t0g k hk) (prep_t0g k hk)
          (hc0 i hi).1 (hcomm k hk)
      rw [this] at h
      exact absurd h (by decide)
    · rw [isIdK_iff (hc0 i hi).1, e] at h
      exfalso
      apply hz1
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = 1 := by rw [h]; group
    · have h' := eqP_sound h (hc0 i hi).1 hz
      rw [e] at h'
      calc w * z = w * z * w⁻¹ * w := by group
        _ = z * w := by rw [h']
  have hwA : w ∈ A := hTA hw
  have hmem : c⁻¹ * w * c ∈ A ⊓ centralizer ({Certificates.P43Twin.tA ()} : Set P45) := by
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hcA) hwA) hcA, mem_centralizer_singleton_iff.2 ?_⟩
    have htz : Certificates.P43Twin.tA () = c⁻¹ * z * c := by rw [hzc]; group
    rw [htz]
    calc c⁻¹ * w * c * (c⁻¹ * z * c) = c⁻¹ * (w * z) * c := by group
      _ = c⁻¹ * (z * w) * c := by rw [hwz]
      _ = c⁻¹ * z * c * (c⁻¹ * w * c) := by group
  obtain ⟨i, hi, hpi⟩ := centA_eq.2.2 _ hmem
  have hX : PRep 45 6 (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.T i) cziP)) w := by
    have h := prep_pcomp hn45 hcz (prep_pcomp hn45 hpi hczi)
    rwa [show c * (c⁻¹ * w * c * c⁻¹) = w by group] at h
  have hww : w * w ∈ T0 := by
    by_contra h
    obtain ⟨a, ha, e⟩ :=
      CFSG.OddStandard.SmallF3.Omega.Mo107.exists_mul_over hT0 hTA hT2 hw hw0 (T.mul_mem hw hw) h
    exact hw0 (mul_right_cancel e ▸ ha)
  have hcos := PK.allN_iff.1 cosets i hi
  unfold cosK at hcos
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hcos
  rcases hcos with ((h | h) | h) | h
  · have : nrmP 45 6 3 64 TZ.G TZ.T
        (pcomp 45 6 (mask 6) czP (pcomp 45 6 (mask 6) (CA.T i) cziP)) = true := by
      refine PK.allN_iff.2 fun k hk => ?_
      have ht : w * t0g k * w⁻¹ ∈ T0 := hnorm w hw _ (t0g_mem hk)
      obtain ⟨m, hm, e⟩ := hc0all _ ht
      exact exN_of hm (eq22_of_eq hX (prep_t0g k hk) (hc0 m hm).1 hX (by rw [e]; group))
    rw [this] at h
    exact absurd h (by decide)
  · obtain ⟨m, hm, e⟩ := inPts_spec (fun i hi => (hc0 i hi).1) h hX
    exact absurd (e ▸ (hc0 m hm).2) hw0
  · obtain ⟨m, hm, e⟩ := hc0all _ hww
    rw [inPts_of hm (e ▸ (hc0 m hm).1) (prep_pcomp hn45 hX hX)] at h
    exact absurd h (by decide)
  · obtain ⟨m, hm, hm'⟩ := exN_spec h
    obtain ⟨k, hk, e⟩ := exN_spec hm'
    have hlm := PK.allN_iff.1 hlu m hm
    rw [Bool.and_eq_true] at hlm
    have hum := (prep_wvA hlm.1).1
    have e' := eq22_sound e hX prep_pid (hc0 k hk).1 hum
    rw [mul_one] at e'
    have huw : wvA (uW.getD m []) = (c0 k)⁻¹ * w := by rw [e']; group
    have huT : wvA (uW.getD m []) ∈ T := by
      rw [huw]
      exact T.mul_mem (T.inv_mem (hT0 (hc0 k hk).2)) hw
    have huT0 : wvA (uW.getD m []) ∉ T0 := by
      intro h0
      apply hw0
      rw [e']
      exact T0.mul_mem (hc0 k hk).2 h0
    interval_cases m
    · exact model_at hT0 hTA hT2 (by norm_num) huT huT0 BZ0.cl BZ0.tr ids3.2.2.1 BZ0.k
        binds3.2.2.2.2.2.2.2.1 tj0.1 tj0.2.1 tj0.2.2
    · exact model_at hT0 hTA hT2 (by norm_num) huT huT0 BZ1.cl BZ1.tr ids3.2.2.2.1 BZ1.k
        binds3.2.2.2.2.2.2.2.2.1 tj1.1 tj1.2.1 tj1.2.2
    · exact model_at hT0 hTA hT2 (by norm_num) huT huT0 BZ2.cl BZ2.tr ids3.2.2.2.2 BZ2.k
        binds3.2.2.2.2.2.2.2.2.2.1 tj2.1 tj2.2.1 tj2.2.2

end CertificateChecks.KernelA45

end
