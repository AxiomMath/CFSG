module

public import Certificates.Kernel.D42Tri.P0Chk
public import Certificates.Kernel.D42Tri.P0K2N
public import Certificates.Kernel.D42Tri.T2Glue
public import CFSG.Certificates.Kernel.Spor.RecGroup
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.HardMathSupport.Dickson.Bal207.D42TriInputs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group
public import CFSG.Certificates.Kernel.Spor.RawOrbGrp
public import CFSG.ClassicalInvolution.SmallCases.NobqLists
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD42Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.RecGroup
  CertificateChecks.KernelO8 CFSG.EvenSmallLie.OmegaEight CFSG.HardMathSupport.Dickson.Bal207.D42Tri
  Equiv

noncomputable abbrev p0T : Perm (Fin 360) := CFSG.Sporadic.SmallOddCore.tp 360 (t2Tbl ())

noncomputable abbrev p0L (i : Fin 5) : Perm (Fin 360) :=
  CFSG.Sporadic.SmallOddCore.tp 360 (l0Tbls ()).toArray[i.val]!

abbrev p0R (X : ℕ) (g : Perm (Fin 360)) : Prop :=
  CFSG.Sporadic.Th.Rep 360 (tabT (unpack 360 9 X)) g

theorem p0_strictB (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem p0_bIf {c t e : Bool} (h : bIf(c, t, e) = true) :
    (c = true ∧ t = true) ∨ (c = false ∧ e = true) := by
  cases c
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

theorem p0_nq {X Y : ℕ} (h : nq X Y = true) : X ≠ Y := by
  rintro rfl
  unfold nq at h
  rw [Nat.beq_refl] at h
  exact absurd h (by decide)

theorem p0R_mul {X Y : ℕ} {g h : Perm (Fin 360)} (hX : cn X = true) (hY : cn Y = true)
    (h1 : p0R X g) (h2 : p0R Y h) : p0R (pq X Y) (g * h) :=
  rep_pcomp hX hY h1 h2

theorem p0_cn {X Y : ℕ} (hX : cn X = true) (hY : cn Y = true) : cn (pq X Y) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hX hY

theorem p0_prep_pid : CFSG.KS.Raw.Orb.PRep 360 9 pid 1 :=
  CFSG.KS.Raw.Orb.prep_pidn (n := 360) (w := 9) (by norm_num) (by norm_num)

theorem p0R_pid : p0R pid 1 := rep_tabT_unpack p0_prep_pid

theorem p0_cn_pid : cn pid = true := kPid'.1

theorem p0R_beq {X Y : ℕ} {g h : Perm (Fin 360)} (hX : cn X = true) (hY : cn Y = true)
    (h1 : p0R X g) (h2 : p0R Y h) : Nat.beq X Y = true ↔ g = h := by
  constructor
  · intro e
    rw [Nat.eq_of_beq_eq_true e] at h1
    exact perm_eq_of_rep h1 h2
  · rintro rfl
    rw [eq_of_rep_eq hX hY h1 h2]
    exact Nat.beq_refl Y

noncomputable def p0Perm (X : ℕ) : Perm (Fin 360) :=
  CFSG.Monster.B.Co2.permOfArr 360 (unpack 360 9 X)

theorem p0_prep {X : ℕ} (h : pm X = true) : CFSG.KS.Raw.Orb.PRep 360 9 X (p0Perm X) :=
  CFSG.KS.Raw.Orb.prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr (CFSG.KS.Raw.Orb.isInvA_unpack h)).1

theorem p0_mem {X : ℕ} {g : Perm (Fin 360)} (hc : cn X = true)
    (hp : pm X = true) (hg : CFSG.KS.Raw.Orb.PRep 360 9 X g) (hs : siftO X = true) :
    g ∈ omegaT := by
  have hG : Nat.shiftRight X (360 * 9) = 0 := by
    unfold cn canonK at hc
    simp only [bAnd_iff] at hc
    exact Nat.eq_of_beq_eq_true hc.2.1
  have e := CFSG.KS.Raw.siftK_eq chainOmP.1 (perm_of_head chainOmP.2.1) chainOmP.2.2.1 rfl hG
    (range_of_permOK hp)
  rw [omegaT, omegaQ, ← CFSG.ComponentClassification.J2Cover.ofArrays_mem_iff (by norm_num)
    omegaChain_ok.1 (CFSG.KS.Raw.Orb.rep_unpack hg)]
  exact e.trans hs

theorem p0_prep_tp {T : CFSG.Sporadic.Th.Native.Table} {X : ℕ}
    (e : CFSG.Sporadic.SmallOddCore.Native.natArr T = unpack 360 9 X) (hp : pm X = true) :
    CFSG.KS.Raw.Orb.PRep 360 9 X (CFSG.Sporadic.SmallOddCore.tp 360 T) := by
  have hT : CFSG.Sporadic.SmallOddCore.permOK 360 T = true := by
    unfold CFSG.Sporadic.SmallOddCore.permOK
    rw [e]
    exact isInvA_of hp
  have h := CFSG.Sporadic.SmallOddCore.co2Rep_natArr_iff.2 (CFSG.Sporadic.SmallOddCore.rep_tp hT)
  rw [e] at h
  exact CFSG.KS.Raw.Orb.prep_of_rep h

theorem p0_tab {F : ℕ → ℕ} {N : ℕ} (h : tabsK F N = true) {j : ℕ} (hj : j < N) :
    cn (F j) = true ∧ pm (F j) = true := by
  unfold tabsK at h
  have h1 := allN_spec h j hj
  simp only [bAnd_iff] at h1
  exact h1

theorem p0_tabs : tabsK P0H.F 3 = true ∧ tabsK K2H.F 2 = true ∧ tabsK L0H.F 5 = true ∧
    tabsK CJH.F 12 = true ∧ tabsK RPH.F 12 = true := by
  have h := ch17627_tabs
  simp only [bAnd_iff] at h
  exact h

theorem p0_sifts : (∀ j < 3, siftO (P0H.F j) = true) ∧ (∀ j < 12, siftO (CJH.F j) = true) ∧
    (∀ j < 5, siftO (L0H.F j) = true) ∧ ∀ j < 2, siftO (K2H.F j) = true := by
  have h := ch17627_sift
  simp only [bAnd_iff] at h
  exact ⟨allN_spec h.1, allN_spec h.2.1, allN_spec h.2.2.1, allN_spec h.2.2.2⟩

theorem p0_rho_parts : cn (AP.S 8) = true ∧ pm (AP.S 8) = true := by
  have h := kStrC
  simp only [bAnd_iff] at h
  exact ⟨allN_spec h.1 8 (by norm_num), h.2.1⟩

theorem p0_prep_rho :
    CFSG.KS.Raw.Orb.PRep 360 9 (AP.S 8) (gen 8) := by
  have h := rep_gen (i := 8) (by norm_num)
  rw [gen_get (by norm_num)] at h
  exact CFSG.KS.Raw.Orb.prep_of_rep h

theorem p0R_rho : p0R (AP.S 8) (gen 8) :=
  rep_tabT_unpack p0_prep_rho

theorem p0_t2_natArr :
    CFSG.Sporadic.SmallOddCore.Native.natArr (t2Tbl ()) = unpack 360 9 (RPH.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound RPH.all (by norm_num) 0 (by norm_num)
  rw [← RPH.eq] at h
  exact h

theorem p0R_t2 : p0R (RPH.F 0) p0T :=
  rep_tabT_unpack (p0_prep_tp p0_t2_natArr (p0_tab p0_tabs.2.2.2.2 (by norm_num)).2)

theorem p0_l0_tbl {i : ℕ} (hi : i < 5) : (l0Tbls ()).toArray[i]! =
    tblAt CFSG.HardMathSupport.Dickson.Bal207.D42TriData.l0Hex i := by
  rw [getElem!_pos _ i (by simp [l0Tbls]; omega)]
  simp [l0Tbls]

theorem p0_prep_l0 (i : Fin 5) : CFSG.KS.Raw.Orb.PRep 360 9 (L0H.F i) (p0L i) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound L0H.all (by norm_num) i.val i.2
  rw [← L0H.eq] at h
  unfold p0L
  rw [p0_l0_tbl i.2]
  exact p0_prep_tp h (p0_tab p0_tabs.2.2.1 i.2).2

noncomputable abbrev k2g (j : ℕ) : Perm (Fin 360) :=
  CFSG.Sporadic.SmallOddCore.tp 360 (tblAt CFSG.HardMathSupport.Dickson.Bal207.D42TriData.k2Hex j)

theorem p0_prep_k2 {j : ℕ} (hj : j < 2) : CFSG.KS.Raw.Orb.PRep 360 9 (K2H.F j) (k2g j) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound K2H.all (by norm_num) j hj
  rw [← K2H.eq] at h
  exact p0_prep_tp h (p0_tab p0_tabs.2.1 hj).2

theorem p0_k2_closure : CFSG.Sporadic.SmallOddCore.genOf 360 (k2Tbls ()) =
    Subgroup.closure (k2g '' {j | j < 2}) := by
  unfold CFSG.Sporadic.SmallOddCore.genOf
  congr 1
  ext z
  simp [k2Tbls, k2g]

theorem p0_rec {G GI F : ℕ → ℕ} {k cnt c R : ℕ} {T PL POS SRT SRI : ℕ → ℕ}
    {g : ℕ → Perm (Fin 360)} (h : recK G GI F k cnt c R T PL POS SRT SRI = true)
    (hg : ∀ j < k, p0R (F j) (g j)) :
    ∃ x : ℕ → Perm (Fin 360), x 0 = 1 ∧ (∀ i < cnt, p0R (T i) (x i) ∧ cn (T i) = true) ∧
      (∀ a < cnt, ∀ b < cnt, x a = x b → a = b) ∧
      (∀ y, y ∈ Subgroup.closure (g '' {j | j < k}) ↔ ∃ i < cnt, x i = y) ∧
      Nat.card (Subgroup.closure (g '' {j | j < k})) = cnt := by
  unfold recK at h
  simp only [bAnd_iff] at h
  obtain ⟨hc, hR, hh, hgen, hsl⟩ := h
  have e1 : c = cnt := Nat.eq_of_beq_eq_true hc
  have e2 : R = pid := Nat.eq_of_beq_eq_true hR
  rw [e1] at hh
  rw [e2] at hh
  rw [e1] at hsl
  have hp : ∀ i < cnt, penumPtK 360 9 (mask 9) (360 * 9) false G GI k cnt T PL POS SRT SRI i = true :=
    fun i hi => CFSG.KS.BaseMask.penumSl_spec hsl (Nat.zero_le i) (by omega) hi
  have hg' : ∀ j < k, canonK 360 9 (mask 9) (360 * 9) (G j) = true ∧
      CFSG.Sporadic.Th.Rep 360 (tabT (unpack 360 9 (G j))) (g j) := by
    intro j hj
    have h1 := allN_spec hgen j hj
    simp only [bAnd_iff] at h1
    refine ⟨h1.2.2.1, ?_⟩
    rw [Nat.eq_of_beq_eq_true h1.1]
    exact hg j hj
  obtain ⟨x, h0, hr, hi, hm, hcard⟩ := penumLeft_closure (n := 360) (w := 9) (k := k)
    (cnt := cnt) (cap := 512) rcCanon_parts.2.2 (by norm_num) hg' hh hp
  exact ⟨x, h0, fun i hi' => ⟨hr i hi', (penumPt_specH (hp i hi')).1⟩, hi, hm, hcard⟩

noncomputable abbrev p0Gen (j : ℕ) : Perm (Fin 360) := p0Perm (P0H.F j)

noncomputable abbrev p0Sub : Subgroup (Perm (Fin 360)) := Subgroup.closure (p0Gen '' {j | j < 3})

theorem p0R_gen {j : ℕ} (hj : j < 3) : p0R (P0H.F j) (p0Gen j) :=
  rep_tabT_unpack (p0_prep (p0_tab p0_tabs.1 hj).2)

structure P0Facts (x : ℕ → Perm (Fin 360)) : Prop where
  rep : ∀ i < 243, p0R (P0.T i) (x i) ∧ cn (P0.T i) = true
  inj : ∀ a < 243, ∀ b < 243, x a = x b → a = b
  mem : ∀ y, y ∈ p0Sub ↔ ∃ i < 243, x i = y

theorem exists_p0Facts : ∃ x, P0Facts x := by
  obtain ⟨x, -, hr, hi, hm, -⟩ := p0_rec ch17627_p0 (g := p0Gen) fun j hj => p0R_gen hj
  exact ⟨x, ⟨hr, hi, hm⟩⟩

theorem p0Sub_le : p0Sub ≤ omegaT := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have ht := p0_tab p0_tabs.1 hj
  exact p0_mem ht.1 ht.2 (p0_prep ht.2) (p0_sifts.1 j hj)

section Ext

variable {G : Type*} [Group G] (P : Subgroup G) (r : G)

theorem p0_conj_pow_mem (hn : ∀ p ∈ P, r * p * r⁻¹ ∈ P) :
    ∀ e : ℕ, ∀ p ∈ P, r ^ e * p * (r ^ e)⁻¹ ∈ P := by
  intro e
  induction e with
  | zero => intro p hp; simpa using hp
  | succ e ih =>
    intro p hp
    have h := ih _ (hn p hp)
    have e1 : r ^ (e + 1) * p * (r ^ (e + 1))⁻¹ = r ^ e * (r * p * r⁻¹) * (r ^ e)⁻¹ := by
      rw [pow_succ]
      group
    rw [e1]
    exact h

def extThree (h3 : r ^ 3 = 1) (hn : ∀ p ∈ P, r * p * r⁻¹ ∈ P) : Subgroup G where
  carrier := {y | ∃ e : ℕ, y * (r ^ e)⁻¹ ∈ P}
  one_mem' := ⟨0, by simp⟩
  mul_mem' := by
    rintro y1 y2 ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b + a, ?_⟩
    have e : y1 * y2 * (r ^ (b + a))⁻¹ =
        (y1 * (r ^ a)⁻¹) * (r ^ a * (y2 * (r ^ b)⁻¹) * (r ^ a)⁻¹) := by
      group
    rw [e]
    exact P.mul_mem ha (p0_conj_pow_mem P r hn a _ hb)
  inv_mem' := by
    rintro y ⟨a, ha⟩
    refine ⟨2 * a, ?_⟩
    have h3a : (r ^ a) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
    have e : y⁻¹ * (r ^ (2 * a))⁻¹ =
        ((r ^ a) ^ 3)⁻¹ * (r ^ (2 * a) * (y * (r ^ a)⁻¹)⁻¹ * (r ^ (2 * a))⁻¹) := by
      group
    rw [e, h3a, inv_one, one_mul]
    exact p0_conj_pow_mem P r hn (2 * a) _ (P.inv_mem ha)

variable {P r}

theorem p0_pow_mod (h3 : r ^ 3 = 1) (e : ℕ) : r ^ e = r ^ (e % 3) := by
  conv_lhs => rw [← Nat.div_add_mod e 3, pow_add, pow_mul, h3, one_pow, one_mul]

theorem mem_extThree {h3 : r ^ 3 = 1} {hn : ∀ p ∈ P, r * p * r⁻¹ ∈ P} {y : G} :
    y ∈ extThree P r h3 hn ↔ ∃ e < 3, ∃ p ∈ P, y = p * r ^ e := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e % 3, Nat.mod_lt _ (by norm_num), _, he, ?_⟩
    rw [← p0_pow_mod h3, inv_mul_cancel_right]
  · rintro ⟨e, -, p, hp, rfl⟩
    refine ⟨e, ?_⟩
    rw [mul_inv_cancel_right]
    exact hp

theorem p0_sq (h3 : r ^ 3 = 1) : r ^ 2 = r⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])

theorem p0_ext_eq (h3 : r ^ 3 = 1) (hr : r ∉ P) {e f : ℕ} (he : e < 3) (hf : f < 3)
    (hm : r ^ f * (r ^ e)⁻¹ ∈ P) : e = f := by
  have hr2 := p0_sq h3
  interval_cases e <;> interval_cases f
  · rfl
  · exact absurd (by simpa using hm) hr
  · exact absurd (by simpa [hr2] using hm) hr
  · exact absurd (by simpa using hm) hr
  · rfl
  · have e1 : r ^ 2 * (r ^ 1)⁻¹ = r := by group
    rw [e1] at hm
    exact absurd hm hr
  · exact absurd (by simpa [hr2] using hm) hr
  · have e1 : r ^ 1 * (r ^ 2)⁻¹ = r⁻¹ := by rw [hr2, inv_inv, pow_one, ← hr2, sq]
    rw [e1] at hm
    exact absurd (P.inv_mem_iff.1 hm) hr
  · rfl

theorem card_extThree {h3 : r ^ 3 = 1} {hn : ∀ p ∈ P, r * p * r⁻¹ ∈ P} {cnt : ℕ}
    {x : ℕ → G} (hmem : ∀ y, y ∈ P ↔ ∃ i < cnt, x i = y)
    (hinj : ∀ a < cnt, ∀ b < cnt, x a = x b → a = b) (hr : r ∉ P) :
    Nat.card (extThree P r h3 hn) = 3 * cnt := by
  have hc : 0 < cnt := by
    obtain ⟨i, hi, -⟩ := (hmem 1).1 P.one_mem
    omega
  refine card_of_mem_iff (x := fun m => x (m % cnt) * r ^ (m / cnt)) (fun y => ?_) ?_
  · rw [mem_extThree]
    constructor
    · rintro ⟨e, he, p, hp, rfl⟩
      obtain ⟨i, hi, rfl⟩ := (hmem p).1 hp
      have hle := Nat.mul_le_mul_left cnt (show e ≤ 2 by omega)
      refine ⟨i + cnt * e, by omega, ?_⟩
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.add_mul_div_left _ _ hc,
        Nat.div_eq_of_lt hi, zero_add]
    · rintro ⟨m, hm, rfl⟩
      refine ⟨m / cnt, ?_, _, (hmem _).2 ⟨m % cnt, Nat.mod_lt _ hc, rfl⟩, rfl⟩
      exact (Nat.div_lt_iff_lt_mul hc).2 (by omega)
  · intro a ha b hb hab
    have hea : a / cnt < 3 := (Nat.div_lt_iff_lt_mul hc).2 (by omega)
    have heb : b / cnt < 3 := (Nat.div_lt_iff_lt_mul hc).2 (by omega)
    have hm : r ^ (b / cnt) * (r ^ (a / cnt))⁻¹ ∈ P := by
      have e : r ^ (b / cnt) * (r ^ (a / cnt))⁻¹ = (x (b % cnt))⁻¹ * x (a % cnt) := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, ← hab, mul_inv_cancel_right]
      rw [e]
      exact P.mul_mem (P.inv_mem ((hmem _).2 ⟨_, Nat.mod_lt _ hc, rfl⟩))
        ((hmem _).2 ⟨_, Nat.mod_lt _ hc, rfl⟩)
    have hef := p0_ext_eq h3 hr hea heb hm
    rw [hef] at hab
    have hi := hinj _ (Nat.mod_lt _ hc) _ (Nat.mod_lt _ hc) (mul_right_cancel hab)
    rw [← Nat.div_add_mod a cnt, ← Nat.div_add_mod b cnt, hef, hi]

end Ext

theorem p0_conj_mem_of_three_index {G : Type*} [Group G] [Finite G] {C P : Subgroup G}
    (hPC : P ≤ C) {e : ℕ} (hPcard : Nat.card P = 3 ^ e)
    (hidx : ¬ 3 ∣ Nat.card C / Nat.card P) {x : G} (hx : x ∈ C)
    (hx3 : ∃ k : ℕ, x ^ 3 ^ k = 1) : ∃ c ∈ C, c * x * c⁻¹ ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P' : Subgroup C := P.subgroupOf C with hP'
  have hP'card : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv
  have hP'p : IsPGroup 3 P' := IsPGroup.of_card (by rw [hP'card, hPcard])
  have hindex : P'.index = Nat.card C / Nat.card P := by
    have h := P'.card_mul_index
    rw [hP'card] at h
    have hpos : 0 < Nat.card P := Nat.card_pos
    rw [← h, Nat.mul_div_cancel_left _ hpos]
  have hnd : ¬ 3 ∣ P'.index := hindex ▸ hidx
  let x' : C := ⟨x, hx⟩
  have hX : IsPGroup 3 (Subgroup.zpowers x') := by
    obtain ⟨k, hk⟩ := hx3
    have hk' : x' ^ 3 ^ k = 1 := Subtype.ext (by simpa [x'] using hk)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk')
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q, hQ⟩ := hX.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C (hP'p.toSylow hnd) Q
  have h1 : x' ∈ (Q : Subgroup C) := hQ (Subgroup.mem_zpowers x')
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.inv_def, MulAut.conj_symm_apply, IsPGroup.toSylow_coe, hP',
    Subgroup.mem_subgroupOf] at h1
  refine ⟨((g⁻¹ : C) : G), (g⁻¹ : C).2, ?_⟩
  simpa [x'] using h1

theorem p0_norm_parts : (∀ j < 3, r32 P0NI j < 243 ∧
      Nat.beq (pq (AP.S 8) (P0H.F j)) (pq (P0.T (r32 P0NI j)) (AP.S 8)) = true) ∧
    Nat.beq (pq (AP.S 8) (pq (AP.S 8) (AP.S 8))) pid = true ∧
    ∀ i < 243, nq (P0.T i) (AP.S 8) = true := by
  have h := ch17627_norm
  simp only [bAnd_iff] at h
  refine ⟨fun j hj => ?_, h.2.1, allN_spec h.2.2⟩
  have h1 := allN_spec h.1 j hj
  simp only [p0_strictB, bAnd_iff, Nat.blt_eq] at h1
  exact h1

theorem p0_rho3 : gen 8 ^ 3 = 1 := by
  have hc := p0_rho_parts.1
  have h := (p0R_beq (p0_cn hc (p0_cn hc hc)) p0_cn_pid
    (p0R_mul hc (p0_cn hc hc) p0R_rho (p0R_mul hc hc p0R_rho p0R_rho)) p0R_pid).1
    p0_norm_parts.2.1
  rw [pow_three]
  exact h

theorem p0_norm {x : ℕ → Perm (Fin 360)} (hx : P0Facts x) :
    ∀ p ∈ p0Sub, gen 8 * p * (gen 8)⁻¹ ∈ p0Sub := by
  have hle : p0Sub ≤ p0Sub.comap (MulAut.conj (gen 8)).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    obtain ⟨hq, hb⟩ := p0_norm_parts.1 j hj
    have hc := p0_rho_parts.1
    obtain ⟨hxq, hcq⟩ := hx.rep _ hq
    have hgc := (p0_tab p0_tabs.1 hj).1
    have e := (p0R_beq (p0_cn hc hgc) (p0_cn hcq hc) (p0R_mul hc hgc p0R_rho (p0R_gen hj))
      (p0R_mul hcq hc hxq p0R_rho)).1 hb
    rw [e, mul_inv_cancel_right]
    exact (hx.mem _).2 ⟨_, hq, rfl⟩
  intro p hp
  have := hle hp
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem p0_rho_not_mem {x : ℕ → Perm (Fin 360)} (hx : P0Facts x) :
    gen 8 ∉ p0Sub := by
  intro h
  obtain ⟨i, hi, e⟩ := (hx.mem _).1 h
  obtain ⟨hxi, hci⟩ := hx.rep i hi
  rw [e] at hxi
  exact p0_nq (p0_norm_parts.2.2 i hi) (eq_of_rep_eq hci p0_rho_parts.1 hxi p0R_rho)

theorem p0_conj_of_check {W Rr : ℕ} {ω r : Perm (Fin 360)}
    (hW : cn W = true) (hR : cn Rr = true) (hω : p0R W ω) (hr : p0R Rr r)
    (h : strictB (pq W Rr) (fun x => bIf(Nat.beq x (pq (AP.S 8) W), true,
      Nat.beq x (pq (RPH.F 0) W))) = true) :
    ω * r * ω⁻¹ = gen 8 ∨ ω * r * ω⁻¹ = p0T := by
  rw [p0_strictB] at h
  have hc := p0_rho_parts.1
  have ht := (p0_tab p0_tabs.2.2.2.2 (by norm_num : 0 < 12)).1
  rcases p0_bIf h with ⟨h1, -⟩ | ⟨-, h1⟩
  · have e := (p0R_beq (p0_cn hW hR) (p0_cn hc hW) (p0R_mul hW hR hω hr)
      (p0R_mul hc hW p0R_rho hω)).1 h1
    left
    rw [e, mul_inv_cancel_right]
  · have e := (p0R_beq (p0_cn hW hR) (p0_cn ht hW) (p0R_mul hW hR hω hr)
      (p0R_mul ht hW p0R_t2 hω)).1 h1
    right
    rw [e, mul_inv_cancel_right]

theorem p0_reps : ∀ j < 13, ∃ r ω : Perm (Fin 360),
    p0R (rpK j) r ∧ cn (rpK j) = true ∧ ω ∈ omegaT ∧
      (ω * r * ω⁻¹ = gen 8 ∨ ω * r * ω⁻¹ = p0T) := by
  intro j hj
  have hchk := allN_spec ch17627_reps j hj
  rcases j with _ | j
  · have e1 : rpK 0 = AP.S 8 := rfl
    have e2 : cjK 0 = pid := rfl
    rw [e1, e2] at hchk
    rw [e1]
    exact ⟨gen 8, 1, p0R_rho, p0_rho_parts.1, omegaT.one_mem,
      p0_conj_of_check p0_cn_pid p0_rho_parts.1 p0R_pid p0R_rho hchk⟩
  · have e1 : rpK (j + 1) = RPH.F j := rfl
    have e2 : cjK (j + 1) = CJH.F j := rfl
    rw [e1, e2] at hchk
    rw [e1]
    have hjc := p0_tab p0_tabs.2.2.2.1 (by omega : j < 12)
    have hjr := p0_tab p0_tabs.2.2.2.2 (by omega : j < 12)
    have hω := p0_prep hjc.2
    have hr := p0_prep hjr.2
    exact ⟨_, _, rep_tabT_unpack hr, hjr.1, p0_mem hjc.1 hjc.2 hω (p0_sifts.2.1 j (by omega)),
      p0_conj_of_check hjc.1 hjr.1 (rep_tabT_unpack hω) (rep_tabT_unpack hr) hchk⟩

theorem p0_coset {x : ℕ → Perm (Fin 360)} (hx : P0Facts x)
    {i : ℕ} (hi : i < 243) (h3 : (x i * gen 8) ^ 3 = 1) :
    ∃ z, (z = x i * gen 8 ∨ z = (x i * gen 8)⁻¹) ∧
      ∃ g ∈ omegaT, g * z * g⁻¹ = gen 8 ∨ g * z * g⁻¹ = p0T := by
  have hc := p0_rho_parts.1
  obtain ⟨hxi, hci⟩ := hx.rep i hi
  have hV := p0R_mul hci hc hxi p0R_rho
  have hVc := p0_cn hci hc
  have hcube := (p0R_beq (p0_cn hVc (p0_cn hVc hVc)) p0_cn_pid
    (p0R_mul hVc (p0_cn hVc hVc) hV (p0R_mul hVc hVc hV hV)) p0R_pid).2
    ((pow_three _).symm.trans h3)
  have h1 := allN_spec ch17627_coset i hi
  rw [p0_strictB, hcube] at h1
  have h2 : ch17627Row i (pq (P0.T i) (AP.S 8)) = true := h1
  unfold ch17627Row at h2
  simp only [p0_strictB, bAnd_iff, Nat.blt_eq] at h2
  obtain ⟨hcc, hck, hrow⟩ := h2
  have hj : Nat.div (r32 P0CK i) 2 < 13 := by
    change r32 P0CK i / 2 < 13
    omega
  obtain ⟨r, ω, hrR, hrc, hωO, hωr⟩ := p0_reps _ hj
  obtain ⟨hxc, hcc'⟩ := hx.rep _ hcc
  have hxcO : x (r32 P0CC i) ∈ omegaT :=
    p0Sub_le ((hx.mem _).2 ⟨_, hcc, rfl⟩)
  rcases p0_bIf hrow with ⟨-, hb⟩ | ⟨-, hb⟩
  · have e := (p0R_beq (p0_cn hcc' hVc) (p0_cn hrc hcc') (p0R_mul hcc' hVc hxc hV)
      (p0R_mul hrc hcc' hrR hxc)).1 hb
    refine ⟨_, Or.inl rfl, ω * x (r32 P0CC i), omegaT.mul_mem hωO hxcO, ?_⟩
    have e2 : ω * x (r32 P0CC i) * (x i * gen 8) * (ω * x (r32 P0CC i))⁻¹ = ω * r * ω⁻¹ := by
      calc ω * x (r32 P0CC i) * (x i * gen 8) * (ω * x (r32 P0CC i))⁻¹ =
            ω * (x (r32 P0CC i) * (x i * gen 8)) * (x (r32 P0CC i))⁻¹ * ω⁻¹ := by group
        _ = ω * (r * x (r32 P0CC i)) * (x (r32 P0CC i))⁻¹ * ω⁻¹ := by rw [e]
        _ = ω * r * ω⁻¹ := by group
    rw [e2]
    exact hωr
  · have e := (p0R_beq (p0_cn hrc (p0_cn hcc' hVc)) hcc'
      (p0R_mul hrc (p0_cn hcc' hVc) hrR (p0R_mul hcc' hVc hxc hV)) hxc).1 hb
    refine ⟨_, Or.inr rfl, ω * x (r32 P0CC i), omegaT.mul_mem hωO hxcO, ?_⟩
    have hr : r = x (r32 P0CC i) * (x i * gen 8)⁻¹ * (x (r32 P0CC i))⁻¹ := by
      calc r = r * (x (r32 P0CC i) * (x i * gen 8)) * (x (r32 P0CC i) * (x i * gen 8))⁻¹ := by
            group
        _ = x (r32 P0CC i) * (x (r32 P0CC i) * (x i * gen 8))⁻¹ := by rw [e]
        _ = x (r32 P0CC i) * (x i * gen 8)⁻¹ * (x (r32 P0CC i))⁻¹ := by group
    have e2 : ω * x (r32 P0CC i) * (x i * gen 8)⁻¹ * (ω * x (r32 P0CC i))⁻¹ = ω * r * ω⁻¹ := by
      rw [hr]
      group
    rw [e2]
    exact hωr

theorem p0_conj {a : Perm (Fin 360)} (ha : a ∈ autT)
    (h3 : a ^ 3 = 1) (hout : a ∉ omegaT) :
    ∃ y, (y = a ∨ y = a⁻¹) ∧ ∃ g ∈ autT, g * y * g⁻¹ = gen 8 ∨ g * y * g⁻¹ = p0T := by
  obtain ⟨x, hx⟩ := exists_p0Facts
  have hρ3 := p0_rho3
  have hn := p0_norm hx
  have hr := p0_rho_not_mem hx
  have hP1A : extThree p0Sub (gen 8) hρ3 hn ≤ autT := by
    intro y hy
    obtain ⟨e, -, p, hp, rfl⟩ := mem_extThree.1 hy
    exact autT.mul_mem (omegaT_le_autT (p0Sub_le hp)) (autT.pow_mem (gen_mem_autT (by norm_num)) _)
  have hcard : Nat.card (extThree p0Sub (gen 8) hρ3 hn) = 729 := by
    rw [card_extThree hx.mem hx.inj hr]
  obtain ⟨c, hcA, hcP⟩ := p0_conj_mem_of_three_index hP1A (e := 6)
    (by rw [hcard]; norm_num) (by rw [card_autT, hcard]; norm_num) ha ⟨1, by simpa using h3⟩
  obtain ⟨b, hb⟩ : ∃ b, b = c * a * c⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hcP
  have hb3 : b ^ 3 = 1 := by rw [hb, conj_pow, h3, mul_one, mul_inv_cancel]
  have hbO : b ∉ omegaT := fun h => hout ((conj_mem_omegaT hcA).2 (hb ▸ h))
  obtain ⟨e, he, p, hp, hbe⟩ := mem_extThree.1 hcP
  obtain ⟨i, hi, rfl⟩ := (hx.mem p).1 hp
  have key : ∃ z, (z = b ∨ z = b⁻¹) ∧
      ∃ g ∈ omegaT, g * z * g⁻¹ = gen 8 ∨ g * z * g⁻¹ = p0T := by
    interval_cases e
    · exfalso
      rw [pow_zero, mul_one] at hbe
      exact hbO (hbe ▸ p0Sub_le ((hx.mem _).2 ⟨i, hi, rfl⟩))
    · rw [pow_one] at hbe
      rw [hbe]
      exact p0_coset hx hi (hbe ▸ hb3)
    · have hm : gen 8 * (x i)⁻¹ * (gen 8)⁻¹ ∈ p0Sub :=
        hn _ (p0Sub.inv_mem ((hx.mem _).2 ⟨i, hi, rfl⟩))
      obtain ⟨k, hk, hxk⟩ := (hx.mem _).1 hm
      have hbi : b⁻¹ = x k * gen 8 := by
        rw [hxk, hbe, mul_inv_rev, p0_sq hρ3, inv_inv]
        group
      have hk3 : (x k * gen 8) ^ 3 = 1 := by rw [← hbi, inv_pow, hb3, inv_one]
      obtain ⟨z, hz, hzg⟩ := p0_coset hx hk hk3
      refine ⟨z, ?_, hzg⟩
      rw [← hbi, inv_inv] at hz
      exact hz.symm
  obtain ⟨z, hz, g, hgO, hg⟩ := key
  rcases hz with rfl | rfl
  · refine ⟨a, Or.inl rfl, g * c, autT.mul_mem (omegaT_le_autT hgO) hcA, ?_⟩
    have e1 : g * c * a * (g * c)⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by group
    rw [e1, ← hb]
    exact hg
  · refine ⟨a⁻¹, Or.inr rfl, g * c, autT.mul_mem (omegaT_le_autT hgO) hcA, ?_⟩
    have e1 : g * c * a⁻¹ * (g * c)⁻¹ = g * (c * a * c⁻¹)⁻¹ * g⁻¹ := by group
    rw [e1, ← hb]
    exact hg

theorem p0_l0_parts : (∀ j < 5,
      Nat.beq (pq (L0H.F j) (AP.S 8)) (pq (AP.S 8) (L0H.F j)) = true) ∧
    CFSG.Quasithin.u33PresRels.all (fun w => Nat.beq (ch17627RelK w) pid) = true ∧
    nq (L0H.F 0) pid = true := by
  have h := ch17627_l0
  simp only [bAnd_iff] at h
  exact ⟨allN_spec h.1, h.2⟩

theorem p0_l0 (i : Fin 5) :
    p0L i ∈ omegaT ∧ p0L i * gen 8 = gen 8 * p0L i := by
  have ht := p0_tab p0_tabs.2.2.1 i.2
  have hc := p0_rho_parts.1
  have hl := rep_tabT_unpack (p0_prep_l0 i)
  refine ⟨p0_mem ht.1 ht.2 (p0_prep_l0 i) (p0_sifts.2.2.1 i i.2), ?_⟩
  exact (p0R_beq (p0_cn ht.1 hc) (p0_cn hc ht.1) (p0R_mul ht.1 hc hl p0R_rho)
    (p0R_mul hc ht.1 p0R_rho hl)).1 (p0_l0_parts.1 i i.2)

theorem p0_fold {L : Fin 5 × Bool → ℕ} {f : Fin 5 × Bool → Perm (Fin 360)}
    (hL : ∀ l, CFSG.KS.Raw.Orb.PRep 360 9 (L l) (f l)) (w : List (Fin 5 × Bool)) :
    ∀ (acc : ℕ) (a : Perm (Fin 360)), CFSG.KS.Raw.Orb.PRep 360 9 acc a →
      CFSG.KS.Raw.Orb.PRep 360 9 (w.foldl (fun acc l => pq acc (L l)) acc) (a * (w.map f).prod) := by
  induction w with
  | nil => intro acc a h; simpa using h
  | cons l w ih =>
    intro acc a h
    rw [List.foldl_cons, List.map_cons, List.prod_cons, ← mul_assoc]
    exact ih _ _ (CFSG.KS.Raw.Orb.prep_pcomp (by norm_num) h (hL l))

theorem p0_l0_rel : ∀ r ∈ CFSG.Quasithin.u33PresRels,
    FreeGroup.lift p0L (FreeGroup.mk r) = 1 := by
  intro w hw
  have hL : ∀ l : Fin 5 × Bool, CFSG.KS.Raw.Orb.PRep 360 9
      (nIf(l.2, L0H.F l.1.val, pinv (L0H.F l.1.val))) (cond l.2 (p0L l.1) (p0L l.1)⁻¹) := by
    rintro ⟨i, b⟩
    cases b
    · exact CFSG.KC.CommBase.prep_inv_of_permOK (p0_prep_l0 i) (p0_tab p0_tabs.2.2.1 i.2).2
    · exact p0_prep_l0 i
  have h : CFSG.KS.Raw.Orb.PRep 360 9 (ch17627RelK w)
      (w.map fun l => cond l.2 (p0L l.1) (p0L l.1)⁻¹).prod := by
    have h1 := p0_fold hL w pid 1 p0_prep_pid
    rw [one_mul] at h1
    exact h1
  have e : ch17627RelK w = pid := Nat.eq_of_beq_eq_true (List.all_eq_true.1 p0_l0_parts.2.1 w hw)
  rw [e] at h
  rw [FreeGroup.lift_mk]
  exact CFSG.KC.CommBase.prep_unique h p0_prep_pid

theorem p0_l0_ne : p0L 0 ≠ 1 := by
  intro h1
  have hl := rep_tabT_unpack (p0_prep_l0 0)
  rw [h1] at hl
  exact p0_nq p0_l0_parts.2.2 (eq_of_rep_eq (p0_tab p0_tabs.2.2.1 (by norm_num : 0 < 5)).1
    p0_cn_pid hl p0R_pid)

theorem p0R_k2 {j : ℕ} (hj : j < 2) : p0R (K2H.F j) (k2g j) := rep_tabT_unpack (p0_prep_k2 hj)

theorem p0_k2 :
    CFSG.Sporadic.SmallOddCore.genOf 360 (k2Tbls ()) ≤
        CFSG.Sporadic.Schreier.centralizerIn omegaT p0T ∧
      Nat.card (CFSG.Sporadic.SmallOddCore.genOf 360 (k2Tbls ())) = 216 := by
  obtain ⟨x, -, -, -, -, hcard⟩ := p0_rec ch17627_k2 (g := k2g) fun j hj => p0R_k2 hj
  rw [p0_k2_closure]
  refine ⟨?_, hcard⟩
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have ht := p0_tab p0_tabs.2.1 hj
  have htc := (p0_tab p0_tabs.2.2.2.2 (by norm_num : 0 < 12)).1
  refine CFSG.Sporadic.Schreier.mem_centralizerIn.2
    ⟨p0_mem ht.1 ht.2 (p0_prep_k2 hj) (p0_sifts.2.2.2 j hj), ?_⟩
  exact (p0R_beq (p0_cn ht.1 htc) (p0_cn htc ht.1) (p0R_mul ht.1 htc (p0R_k2 hj) p0R_t2)
    (p0R_mul htc ht.1 p0R_t2 (p0R_k2 hj))).1 (allN_spec ch17627_k2c j hj)

theorem p0_k2_nine : ∀ g ∈ CFSG.Sporadic.SmallOddCore.genOf 360 (k2Tbls ()),
    g ^ 9 = 1 → g ^ 3 = 1 := by
  obtain ⟨x, -, hr, -, hm, -⟩ := p0_rec ch17627_k2 (g := k2g) fun j hj => p0R_k2 hj
  intro g hg h9
  rw [p0_k2_closure] at hg
  obtain ⟨i, hi, rfl⟩ := (hm _).1 hg
  obtain ⟨hxi, hci⟩ := hr i hi
  have hU := p0R_mul hci (p0_cn hci hci) hxi (p0R_mul hci hci hxi hxi)
  have hUc : cn (cubeK (K2.T i)) = true := p0_cn hci (p0_cn hci hci)
  have h1 := allN_spec ch17627_k2n i hi
  rw [p0_strictB] at h1
  have e9 : x i * (x i * x i) * (x i * (x i * x i) * (x i * (x i * x i))) = 1 := by
    rw [← pow_three, ← pow_three, ← pow_mul]
    exact h9
  have hc9 := (p0R_beq (p0_cn hUc (p0_cn hUc hUc)) p0_cn_pid
    (p0R_mul hUc (p0_cn hUc hUc) hU (p0R_mul hUc hUc hU hU)) p0R_pid).2 e9
  rcases p0_bIf h1 with ⟨-, h2⟩ | ⟨h2, -⟩
  · rw [pow_three]
    exact (p0R_beq hUc p0_cn_pid hU p0R_pid).1 h2
  · exact absurd (h2.symm.trans hc9) Bool.false_ne_true

end CertificateChecks.KernelD42Tri

end
