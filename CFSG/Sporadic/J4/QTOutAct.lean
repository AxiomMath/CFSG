module

public import CFSG.Sporadic.J4.QTOutNorm
public import CFSG.Sporadic.J4.QTOutActCheck
public import CFSG.Sporadic.J4.QTOutMatCheck
public import CFSG.Sporadic.J4.QTRankWitProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native
open scoped Pointwise

theorem lenOK_powT {t : List ℕ} (ht : lenOK t = true) : ∀ n, lenOK (powT t n) = true
  | 0 => lenOK_idT
  | n + 1 => lenOK_compT ht (lenOK_powT ht n)

theorem actT_powT_add {t : List ℕ} (ht : lenOK t = true) (a b : ℕ) (c : ℕ) :
    actT (powT t (a + b)) c = actT (powT t a) (actT (powT t b) c) ∨ ¬ c < 2 ^ 11 := by
  by_cases hc : c < 2 ^ 11
  · left
    induction a with
    | zero =>
      rw [zero_add]
      show actT (powT t b) c = actT idT (actT (powT t b) c)
      rw [actT_idT (actT_lt (lenOK_powT ht b) c)]
    | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 by omega]
      show actT (compT t (powT t (a + b))) c = actT (compT t (powT t a)) (actT (powT t b) c)
      rw [actT_comp, actT_comp, ih]
  · right; exact hc

theorem actT_powT_add' {t : List ℕ} (ht : lenOK t = true) (a b : ℕ) {c : ℕ} (hc : c < 2 ^ 11) :
    actT (powT t (a + b)) c = actT (powT t a) (actT (powT t b) c) :=
  (actT_powT_add ht a b c).resolve_right (not_not.2 hc)

theorem lenOK_t0 : lenOK t0 = true := letterTab_ok 1 (by decide)

theorem lenOK_tp (n : ℕ) : lenOK (tp n) = true := lenOK_powT lenOK_t0 n

theorem actT_tp_mod (n : ℕ) {c : ℕ} (hc : c < 2 ^ 11) :
    actT (tp n) c = actT (tp (n % 23)) c := by
  have key : ∀ q r : ℕ, actT (tp (23 * q + r)) c = actT (tp r) c := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show 23 * (q + 1) + r = 23 + (23 * q + r) by ring]
      have h1 := actT_powT_add' (t := t0) lenOK_t0 23 (23 * q + r) hc
      have h2 : actT (powT t0 (23 * q + r)) c < 2 ^ 11 := actT_lt (lenOK_powT lenOK_t0 _) c
      have h3 := tp_period _ h2
      show actT (powT t0 (23 + (23 * q + r))) c = _
      rw [h1]
      have h4 : actT (powT t0 23) (actT (powT t0 (23 * q + r)) c) =
          actT (powT t0 (23 * q + r)) c := h3
      rw [h4]
      exact ih r
  have := key (n / 23) (n % 23)
  rwa [Nat.div_add_mod] at this

theorem Acts_pow {g : J} {t : List ℕ} (h : Acts g t) : ∀ n : ℕ, Acts (g ^ n) (powT t n)
  | 0 => by simpa [powT] using Acts.one
  | n + 1 => by
    have := h.mul (Acts_pow h n)
    rwa [pow_succ']

theorem Acts_xJ_zero (hM : MatFacts) : Acts (xJ 0) t0 := by
  have := Acts_XJ hM (ℓ := 1) (by decide)
  rwa [XJ_one] at this

section AMap

variable (hM : MatFacts) (α : MulAut J) (hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11)
include hM hE

theorem exists_amap (c : ℕ) (_hc : c < 2 ^ 11) :
    ∃ d < 2 ^ 11, α (eta uJ 11 c) = eta uJ 11 d :=
  (mem_Eg_iff (elem_uJ hM)).1 ((hE _).2 (eta_mem_Eg 11 le_rfl c))

noncomputable def amap (c : ℕ) : ℕ :=
  if h : c < 2 ^ 11 then Classical.choose (exists_amap hM α hE c h) else 0

theorem amap_spec {c : ℕ} (hc : c < 2 ^ 11) :
    amap hM α hE c < 2 ^ 11 ∧ α (eta uJ 11 c) = eta uJ 11 (amap hM α hE c) := by
  unfold amap
  simp only [hc, dite_true]
  exact Classical.choose_spec (exists_amap hM α hE c hc)

theorem amap_lt {c : ℕ} (hc : c < 2 ^ 11) : amap hM α hE c < 2 ^ 11 := (amap_spec hM α hE hc).1

theorem amap_eta {c : ℕ} (hc : c < 2 ^ 11) :
    α (eta uJ 11 c) = eta uJ 11 (amap hM α hE c) := (amap_spec hM α hE hc).2

theorem amap_xor {c d : ℕ} (hc : c < 2 ^ 11) (hd : d < 2 ^ 11) :
    amap hM α hE (c ^^^ d) = amap hM α hE c ^^^ amap hM α hE d := by
  have h1 := amap_eta hM α hE (lt_xor hc hd)
  rw [eta_xor (elem_uJ hM) le_rfl, map_mul, amap_eta hM α hE hc, amap_eta hM α hE hd,
    ← eta_xor (elem_uJ hM) le_rfl] at h1
  exact (eta_inj hM _ (amap_lt hM α hE (lt_xor hc hd)) _
    (lt_xor (amap_lt hM α hE hc) (amap_lt hM α hE hd)) h1.symm)

theorem amap_zero : amap hM α hE 0 = 0 := by
  have h1 := amap_eta hM α hE (c := 0) (Nat.two_pow_pos 11)
  rw [eta_zero, map_one] at h1
  have := eta_inj hM 0 (Nat.two_pow_pos 11) _ (amap_lt hM α hE (Nat.two_pow_pos 11)) (by
    rw [eta_zero]; exact h1)
  exact this.symm

theorem amap_inj {c d : ℕ} (hc : c < 2 ^ 11) (hd : d < 2 ^ 11)
    (h : amap hM α hE c = amap hM α hE d) : c = d := by
  have h1 := amap_eta hM α hE hc
  have h2 := amap_eta hM α hE hd
  rw [h, ← h2] at h1
  exact eta_inj hM c hc d hd (α.injective h1)

theorem amap_surj {d : ℕ} (hd : d < 2 ^ 11) : ∃ c < 2 ^ 11, amap hM α hE c = d := by
  have hE' : α.symm (eta uJ 11 d) ∈ Eg uJ 11 := by
    rw [← hE, MulEquiv.apply_symm_apply]
    exact eta_mem_Eg 11 le_rfl d
  obtain ⟨c, hc, hcd⟩ := (mem_Eg_iff (elem_uJ hM)).1 hE'
  refine ⟨c, hc, ?_⟩
  have h1 := amap_eta hM α hE hc
  rw [← hcd, MulEquiv.apply_symm_apply] at h1
  exact (eta_inj hM d hd _ (amap_lt hM α hE hc) h1).symm

end AMap

@[expose] def Cl (c d : ℕ) : Prop := ∃ h ∈ Hj, h * eta uJ 11 c * h⁻¹ = eta uJ 11 d

theorem cl_refl (c : ℕ) : Cl c c := ⟨1, Hj.one_mem, by simp⟩

theorem cl_symm {c d : ℕ} (h : Cl c d) : Cl d c := by
  obtain ⟨g, hg, e⟩ := h
  refine ⟨g⁻¹, Hj.inv_mem hg, ?_⟩
  rw [← e]
  group

theorem cl_trans {c d e : ℕ} (h1 : Cl c d) (h2 : Cl d e) : Cl c e := by
  obtain ⟨g, hg, e1⟩ := h1
  obtain ⟨g', hg', e2⟩ := h2
  refine ⟨g' * g, Hj.mul_mem hg' hg, ?_⟩
  rw [← e2, ← e1]
  group

theorem orbits_get_mem {i : ℕ} (hi : i < 2) : orbits.getD i (0, [], []) ∈ orbits := by
  rw [List.getD_eq_getElem _ _ (by rw [orbits_shape.1]; exact hi)]
  exact List.getElem_mem _

section Orbits

variable (hM : MatFacts)
include hM

theorem closure_orbit {S : List ℕ} (hS : ∀ c ∈ S, ∀ ℓ ∈ letters, act ℓ c ∈ S) :
    ∀ h ∈ Hj, ∀ c ∈ S, ∃ d ∈ S, h * eta uJ 11 c * h⁻¹ = eta uJ 11 d := by
  have key : ∀ h : J, h ∈ Subgroup.closure (XJ '' {ℓ | ℓ ∈ letters}) →
      ∀ c ∈ S, ∃ d ∈ S, h * eta uJ 11 c * h⁻¹ = eta uJ 11 d := by
    intro h hh'
    induction hh' using Subgroup.closure_induction_right with
    | one => intro c hc; exact ⟨c, hc, by simp⟩
    | mul_right x hx y hy ih =>
      obtain ⟨ℓ, hℓ, rfl⟩ := hy
      intro c hc
      obtain ⟨d, hd, e⟩ := ih (act ℓ c) (hS c hc ℓ hℓ)
      refine ⟨d, hd, ?_⟩
      have h1 := hX_all hM hℓ c
      calc x * XJ ℓ * eta uJ 11 c * (x * XJ ℓ)⁻¹
          = x * (XJ ℓ * eta uJ 11 c * (XJ ℓ)⁻¹) * x⁻¹ := by group
        _ = eta uJ 11 d := by rw [h1, e]
    | mul_inv_cancel x hx y hy ih =>
      obtain ⟨ℓ, hℓ, rfl⟩ := hy
      intro c hc
      obtain ⟨hℓ', hXinv⟩ := XJ_inv hℓ
      obtain ⟨d, hd, e⟩ := ih (act (-ℓ) c) (hS c hc (-ℓ) hℓ')
      refine ⟨d, hd, ?_⟩
      have h1 := hX_all hM hℓ' c
      rw [hXinv] at h1
      calc x * (XJ ℓ)⁻¹ * eta uJ 11 c * (x * (XJ ℓ)⁻¹)⁻¹
          = x * ((XJ ℓ)⁻¹ * eta uJ 11 c * ((XJ ℓ)⁻¹)⁻¹) * x⁻¹ := by group
        _ = eta uJ 11 d := by rw [h1, e]
  intro h hh
  exact key h (Hj_le_closure hh)

theorem cl_of_orbit {o : ℕ × List (ℕ × List ℤ) × List (List ℕ)} (ho : o ∈ orbits)
    {p : ℕ × List ℤ} (hp : p ∈ o.2.1) : Cl o.1 p.1 := by
  obtain ⟨hlet, hfold⟩ := orbit_words o ho p hp
  refine ⟨(p.2.map XJ).prod, ?_, ?_⟩
  · have : (p.2.map XJ).prod = wordProd xJ p.2 := rfl
    rw [this]
    exact wordProd_mem_Hj hlet
  · rw [word_conj XJ act p.2 (fun ℓ hℓ c => hX_all hM (hlet ℓ hℓ) c), hfold]

theorem cl_iff_orbit {o : ℕ × List (ℕ × List ℤ) × List (List ℕ)} (ho : o ∈ orbits) {r : ℕ}
    (hr : o.1 = r) {S : List ℕ} (hSdef : S = o.2.1.map Prod.fst) (hroot : r ∈ S)
    (hS : ∀ c ∈ S, ∀ ℓ ∈ letters, act ℓ c ∈ S) (hlt : ∀ c ∈ S, c < 2 ^ 11)
    {d : ℕ} (hd : d < 2 ^ 11) : Cl r d ↔ d ∈ S := by
  constructor
  · rintro ⟨h, hh, e⟩
    obtain ⟨d', hd', e'⟩ := closure_orbit hM hS h hh r hroot
    rw [e] at e'
    have := eta_inj hM d hd d' (hlt d' hd') e'
    rw [this]; exact hd'
  · intro hdS
    rw [hSdef, List.mem_map] at hdS
    obtain ⟨p, hp, rfl⟩ := hdS
    have := cl_of_orbit hM ho hp
    rwa [hr] at this

end Orbits

theorem cl_iff_o1 (hM : MatFacts) {d : ℕ} (hd : d < 2 ^ 11) : Cl 1 d ↔ d ∈ o1 :=
  cl_iff_orbit hM (orbits_get_mem (by norm_num)) orbits_shape.2.1 rfl o_roots.1 o_closed.1
    (fun c hc => (o_lt c (List.mem_append_left _ hc)).1) hd

theorem cl_iff_o2 (hM : MatFacts) {d : ℕ} (hd : d < 2 ^ 11) : Cl 3 d ↔ d ∈ o2 :=
  cl_iff_orbit hM (orbits_get_mem (by norm_num)) orbits_shape.2.2 rfl o_roots.2 o_closed.2
    (fun c hc => (o_lt c (List.mem_append_right _ hc)).1) hd


section Pres

variable (hM : MatFacts) (α : MulAut J) (hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11)
  (hH : ∀ x, α x ∈ Hj ↔ x ∈ Hj)
include hM hE hH

theorem amap_cl {c d : ℕ} (hc : c < 2 ^ 11) (hd : d < 2 ^ 11) :
    Cl c d ↔ Cl (amap hM α hE c) (amap hM α hE d) := by
  constructor
  · rintro ⟨h, hh, e⟩
    refine ⟨α h, (hH h).2 hh, ?_⟩
    rw [← amap_eta hM α hE hc, ← amap_eta hM α hE hd, ← e, ← map_mul, ← map_inv, ← map_mul]
  · rintro ⟨h, hh, e⟩
    refine ⟨α.symm h, (hH _).1 (by simpa using hh), ?_⟩
    apply α.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, amap_eta hM α hE hc, e,
      amap_eta hM α hE hd]

theorem amap_o1 : ∀ c ∈ o1, amap hM α hE c ∈ o1 := by
  intro c hc
  have hc_lt := (o_lt c (List.mem_append_left _ hc)).1
  have h1lt : (1 : ℕ) < 2 ^ 11 := by norm_num
  have ha1lt := amap_lt hM α hE h1lt
  have ha1ne : amap hM α hE 1 ≠ 0 := by
    intro h0
    have := amap_inj hM α hE h1lt (Nat.two_pow_pos 11) (by rw [h0, amap_zero hM α hE])
    exact absurd this (by norm_num)
  rcases o_cover _ ha1lt ha1ne with h1 | h2
  · have c1 : Cl 1 c := (cl_iff_o1 hM hc_lt).2 hc
    have e1 := (amap_cl hM α hE hH h1lt hc_lt).1 c1
    have e2 := cl_trans ((cl_iff_o1 hM ha1lt).2 h1) e1
    exact (cl_iff_o1 hM (amap_lt hM α hE hc_lt)).1 e2
  · exfalso
    have hsurj : Set.SurjOn (amap hM α hE) (↑o1.toFinset) (↑o2.toFinset) := by
      intro d hd
      have hd2 : d ∈ o2 := by simpa using hd
      have hdlt := (o_lt d (List.mem_append_right _ hd2)).1
      obtain ⟨c', hc', rfl⟩ := amap_surj hM α hE hdlt
      refine ⟨c', ?_, rfl⟩
      have e1 : Cl 3 (amap hM α hE 1) := (cl_iff_o2 hM ha1lt).2 h2
      have e2 : Cl 3 (amap hM α hE c') := (cl_iff_o2 hM hdlt).2 hd2
      have e3 : Cl (amap hM α hE 1) (amap hM α hE c') := cl_trans (cl_symm e1) e2
      have e4 := (amap_cl hM α hE hH h1lt hc').2 e3
      simpa using (cl_iff_o1 hM hc').1 e4
    have := Finset.card_le_card_of_surjOn (amap hM α hE) hsurj
    rw [List.toFinset_card_of_nodup o2_len.2, List.toFinset_card_of_nodup o1_len.2, o1_len.1,
      o2_len.1] at this
    omega

end Pres

theorem exists_conj_pow_of_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcard : (Nat.card G).factorization p = 1) {x y : G} (hx : orderOf x = p)
    (hy : orderOf y = p) : ∃ g : G, ∃ k : ℕ, y = g * x ^ k * g⁻¹ := by
  have hpx : Nat.card (Subgroup.zpowers x) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hx, hcard, pow_one]
  have hpy : Nat.card (Subgroup.zpowers y) = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_zpowers, hy, hcard, pow_one]
  let P : Sylow p G := Sylow.ofCard (Subgroup.zpowers x) hpx
  let Q : Sylow p G := Sylow.ofCard (Subgroup.zpowers y) hpy
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hQ : (Q : Subgroup G) = MulAut.conj g • Subgroup.zpowers x := by
    rw [← hg, Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
  have hyQ : y ∈ (Q : Subgroup G) := by
    rw [Sylow.coe_ofCard]
    exact Subgroup.mem_zpowers y
  rw [hQ] at hyQ
  obtain ⟨t, ht, hty⟩ := (Subgroup.mem_smul_pointwise_iff_exists y (MulAut.conj g) _).1 hyQ
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨g, (n % (p : ℤ)).toNat, ?_⟩
  have hn : x ^ n = x ^ ((n % (p : ℤ)).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne'), ← hx, zpow_mod_orderOf]
  rw [← hn, ← hty]
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem card_Hj_factorization (hF : J4Facts) : (Nat.card Hj).factorization 23 = 1 := by
  rw [card_Hj hF]
  have h : (501397585920 : ℕ) = 23 * 21799895040 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_self (by norm_num : Nat.Prime 23),
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem xJ0_pow (hM : MatFacts) : xJ 0 ^ 23 = 1 :=
  pow_eq_one_of_rows (g := xJ 0) (R := xRowsOf 1)
    (by rw [← XJ_one]; exact Mx_XJ hM 1) x0_pow

theorem xJ0_ne (hM : MatFacts) : xJ 0 ≠ 1 := by
  intro h
  have h1 : Mx (xJ 0) = rowsMatrix (xRowsOf 1) := by rw [← XJ_one]; exact Mx_XJ hM 1
  rw [h, map_one, ← rowsMatrix_idRows] at h1
  obtain ⟨hs, hw⟩ := wfRows_spec x0_wf
  exact rowsMatrix_ne_of_eqRows_false hs idRows_size hw idRows_wf x0_ne h1.symm

theorem xJ0_order (hM : MatFacts) : orderOf (xJ 0) = 23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact orderOf_eq_prime (xJ0_pow hM) (xJ0_ne hM)

theorem lin_rowsXor {A : ℕ → ℕ}
    (hxor : ∀ c d, c < 2 ^ 11 → d < 2 ^ 11 → A (c ^^^ d) = A c ^^^ A d) (hzero : A 0 = 0)
    {r : ℕ → ℕ} (hr : ∀ j < 11, r j < 2 ^ 11) :
    ∀ m ≤ 11, ∀ c, A (rowsXor r m c) = rowsXor (fun j => A (r j)) m c := by
  intro m
  induction m with
  | zero => intro _ c; simp [rowsXor_zero, hzero]
  | succ m ih =>
    intro hm c
    rw [rowsXor_succ, rowsXor_succ]
    have hlt' : rowsXor r m c < 2 ^ 11 := rowsXor_lt (fun j hj => hr j (by omega)) (by omega) c
    by_cases hb : c.testBit m
    · simp only [hb, ite_true]
      rw [hxor _ _ hlt' (hr m (by omega)), ih (by omega)]
    · simp only [hb, Bool.false_eq_true, ite_false, Nat.xor_zero]
      rw [ih (by omega)]

theorem eq_actT_of_basis {A : ℕ → ℕ}
    (hxor : ∀ c d, c < 2 ^ 11 → d < 2 ^ 11 → A (c ^^^ d) = A c ^^^ A d) (hzero : A 0 = 0)
    {t : List ℕ} (hbasis : ∀ j < 11, A (2 ^ j) = t.getD j 0) :
    ∀ c < 2 ^ 11, A c = actT t c := by
  intro c hc
  have hr : ∀ j < 11, 2 ^ j < 2 ^ 11 := fun j hj => Nat.pow_lt_pow_right (by norm_num) hj
  have h1 := lin_rowsXor hxor hzero hr 11 le_rfl c
  rw [rowsXor_pow_two, Nat.mod_eq_of_lt hc] at h1
  rw [h1]
  unfold actT
  apply rowsXor_congr
  intro j hj
  exact hbasis j hj

theorem tpL_getD {n : ℕ} (hn : n < 23) : tpL.getD n [] = tp n := by
  unfold tpL
  rw [List.getD_eq_getElem _ _ (by simpa using hn)]
  simp

theorem kvec_lt {i : ℕ} : kvec i < 2 ^ 11 := actT_lt (lenOK_tp i) 1

theorem eq_candTab {A : ℕ → ℕ} (hlt : ∀ c < 2 ^ 11, A c < 2 ^ 11)
    (hxor : ∀ c d, c < 2 ^ 11 → d < 2 ^ 11 → A (c ^^^ d) = A c ^^^ A d) (hzero : A 0 = 0)
    {k : ℕ} (hcomm : ∀ c < 2 ^ 11, A (actT t0 c) = actT (tp k) (A c)) :
    ∀ c < 2 ^ 11, A c = actT (candTab (k % 23) (A 1)) c := by
  have hw : A 1 < 2 ^ 11 := hlt 1 (by norm_num)
  have hkv : ∀ i, A (kvec i) = actT (tp (k * i)) (A 1) := by
    intro i
    induction i with
    | zero =>
      have e1 : kvec 0 = 1 := by
        show actT idT 1 = 1
        exact actT_idT (by norm_num)
      rw [e1, Nat.mul_zero]
      show A 1 = actT idT (A 1)
      rw [actT_idT hw]
    | succ i ih =>
      have e1 : kvec (i + 1) = actT t0 (kvec i) := by
        show actT (compT t0 (tp i)) 1 = actT t0 (actT (tp i) 1)
        rw [actT_comp]
      rw [e1, hcomm _ kvec_lt, ih]
      have := actT_powT_add' (t := t0) lenOK_t0 k (k * i) hw
      rw [show k * (i + 1) = k + k * i by ring]
      exact this.symm
  apply eq_actT_of_basis hxor hzero
  intro j hj
  have hc : 2 ^ j < 2 ^ 11 := Nat.pow_lt_pow_right (by norm_num) hj
  obtain ⟨hk1, hk2⟩ := kcomb_kinv _ hc
  have hrk : ∀ i < 11, kvec i < 2 ^ 11 := fun i _ => kvec_lt
  have h1 := lin_rowsXor hxor hzero hrk 11 le_rfl (kinv.getD (2 ^ j) 0)
  have h2 : A (2 ^ j) = rowsXor (fun i => A (kvec i)) 11 (kinv.getD (2 ^ j) 0) := by
    conv_lhs => rw [← hk1]
    exact h1
  rw [h2]
  unfold candTab
  simp only []
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]
  apply rowsXor_congr
  intro i hi
  rw [hkv i]
  have e : k * i % 23 = (k % 23) * i % 23 := ((Nat.mod_modEq k 23).mul_right i).symm
  have hmod : actT (tp (k * i)) (A 1) = actT (tp ((k % 23) * i % 23)) (A 1) := by
    rw [actT_tp_mod _ hw, e]
  rw [hmod, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]
  rw [tpL_getD (Nat.mod_lt _ (by norm_num))]

@[expose] noncomputable def twistAut (g : J) (α : MulAut J) : MulAut J := MulAut.conj g⁻¹ * α

theorem twistAut_apply (g : J) (α : MulAut J) (x : J) : twistAut g α x = g⁻¹ * α x * g := by
  simp [twistAut]

theorem twist_mem_Eg (hM : MatFacts) {g : J} (hg : g ∈ Hj) (y : J) :
    g⁻¹ * y * g ∈ Eg uJ 11 ↔ y ∈ Eg uJ 11 := by
  constructor
  · intro h
    have := Hj_normalizes_Eg hM g hg _ h
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  · intro h
    have := Hj_normalizes_Eg hM g⁻¹ (Hj.inv_mem hg) _ h
    simpa using this

theorem twist_mem_Hj {g : J} (hg : g ∈ Hj) (y : J) : g⁻¹ * y * g ∈ Hj ↔ y ∈ Hj := by
  constructor
  · intro h
    have := Hj.mul_mem (Hj.mul_mem hg h) (Hj.inv_mem hg)
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  · intro h
    exact Hj.mul_mem (Hj.mul_mem (Hj.inv_mem hg) h) hg

theorem exists_inner_twist (hF : J4Facts) (α : MulAut J)
    (hE : ∀ x, α x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11) (hH : ∀ x, α x ∈ Hj ↔ x ∈ Hj) :
    ∃ g ∈ Hj, ∀ c < 2 ^ 11, g⁻¹ * α (eta uJ 11 c) * g = eta uJ 11 c := by
  have hM := hF.mat
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  let x0 : Hj := ⟨xJ 0, xJ_mem (by norm_num)⟩
  let y0 : Hj := ⟨α (xJ 0), (hH _).2 (xJ_mem (by norm_num))⟩
  have hx0 : orderOf x0 = 23 := by
    rw [← Subgroup.orderOf_coe]
    exact xJ0_order hM
  have hy0 : orderOf y0 = 23 := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (α (xJ 0)) = 23
    rw [MulEquiv.orderOf_eq]
    exact xJ0_order hM
  obtain ⟨g1, k, hg1⟩ := exists_conj_pow_of_sylow (card_Hj_factorization hF) hx0 hy0
  have hα1 : α (xJ 0) = (g1 : J) * xJ 0 ^ k * (g1 : J)⁻¹ := by
    have := congrArg Subtype.val hg1
    simpa using this
  have hh1 : (g1 : J) ∈ Hj := g1.2
  obtain ⟨α1, hα1apply⟩ : ∃ α1 : MulAut J, ∀ x, α1 x = (g1 : J)⁻¹ * α x * (g1 : J) :=
    ⟨twistAut (g1 : J) α, fun x => twistAut_apply _ _ x⟩
  have hE1 : ∀ x, α1 x ∈ Eg uJ 11 ↔ x ∈ Eg uJ 11 := fun x => by
    rw [hα1apply, twist_mem_Eg hM hh1, hE]
  have hH1 : ∀ x, α1 x ∈ Hj ↔ x ∈ Hj := fun x => by
    rw [hα1apply, twist_mem_Hj hh1, hH]
  have hx0k : α1 (xJ 0) = xJ 0 ^ k := by
    rw [hα1apply, hα1]
    group
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → ℕ, A = amap hM α1 hE1 := ⟨_, rfl⟩
  have hAlt : ∀ c < 2 ^ 11, A c < 2 ^ 11 := fun c hc => by
    rw [hAdef]; exact amap_lt hM α1 hE1 hc
  have hAxor : ∀ c d, c < 2 ^ 11 → d < 2 ^ 11 → A (c ^^^ d) = A c ^^^ A d :=
    fun c d hc hd => by rw [hAdef]; exact amap_xor hM α1 hE1 hc hd
  have hAzero : A 0 = 0 := by rw [hAdef]; exact amap_zero hM α1 hE1
  have hAeta : ∀ c < 2 ^ 11, α1 (eta uJ 11 c) = eta uJ 11 (A c) := fun c hc => by
    rw [hAdef]; exact amap_eta hM α1 hE1 hc
  have hAcomm : ∀ c < 2 ^ 11, A (actT t0 c) = actT (tp k) (A c) := by
    intro c hc
    have hx := Acts_xJ_zero hM
    have hxk : Acts (xJ 0 ^ k) (tp k) := Acts_pow hx k
    have e1 := hx.2 c hc
    have e2 := congrArg α1 e1
    rw [map_mul, map_mul, map_inv, hx0k, hAeta c hc, hAeta _ (actT_lt hx.1 c)] at e2
    rw [hxk.2 _ (hAlt c hc)] at e2
    have h3 := eta_inj hM (A (actT t0 c)) (hAlt _ (actT_lt hx.1 c)) (actT (tp k) (A c))
      (actT_lt (lenOK_tp k) _) e2.symm
    exact h3
  have hAeq := eq_candTab hAlt hAxor hAzero hAcomm
  have hs0 : k % 23 ≠ 0 := by
    intro h
    have h1 : xJ 0 ^ k = 1 := by
      rw [← Nat.mod_add_div k 23, h, zero_add, pow_mul, xJ0_pow hM, one_pow]
    rw [h1] at hx0k
    exact xJ0_ne hM (α1.injective (by rw [hx0k, map_one]))
  have hAo1 : ∀ c ∈ o1, A c ∈ o1 := fun c hc => by
    rw [hAdef]; exact amap_o1 hM α1 hE1 hH1 c hc
  have hw : A 1 ∈ o1 := hAo1 1 o_roots.1
  have hsurv : survOK (k % 23) (A 1) = true := by
    unfold survOK
    rw [List.all_eq_true]
    intro c hc
    have hclt := (o_lt c (List.mem_append_left _ hc)).1
    rw [← hAeq c hclt]
    exact List.contains_iff_mem.2 (hAo1 c hc)
  have hin := surv_all (k % 23) (Nat.mod_lt _ (by norm_num)) hs0 (A 1) hw hsurv
  unfold survIn at hin
  have hin' := List.contains_iff_mem.1 hin
  unfold fTabs at hin'
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hin'
  obtain ⟨i, hi, j, hj, hij⟩ := hin'
  have hEl := Acts_wordProd hM hWord hWord_letters
  have hElH : wordProd xJ hWord ∈ Hj := wordProd_mem_Hj hWord_letters
  have hh0 : (xJ 0) ^ i * (wordProd xJ hWord) ^ j ∈ Hj :=
    Hj.mul_mem (Hj.pow_mem (xJ_mem (by norm_num)) i) (Hj.pow_mem hElH j)
  have hAct : Acts ((xJ 0) ^ i * (wordProd xJ hWord) ^ j) (candTab (k % 23) (A 1)) := by
    rw [← hij]
    exact (Acts_pow (Acts_xJ_zero hM) i).mul (Acts_pow hEl j)
  refine ⟨(g1 : J) * ((xJ 0) ^ i * (wordProd xJ hWord) ^ j), Hj.mul_mem hh1 hh0, fun c hc => ?_⟩
  obtain ⟨h0, hh0def⟩ : ∃ h0 : J, h0 = (xJ 0) ^ i * (wordProd xJ hWord) ^ j := ⟨_, rfl⟩
  rw [← hh0def] at hAct ⊢
  have e1 : h0 * eta uJ 11 c * h0⁻¹ = eta uJ 11 (A c) := by
    have := hAct.2 c hc
    rw [this, ← hAeq c hc]
  have e2 : α1 (eta uJ 11 c) = h0 * eta uJ 11 c * h0⁻¹ := by
    rw [e1]; exact hAeta c hc
  have e3 : (g1 : J)⁻¹ * α (eta uJ 11 c) * (g1 : J) = h0 * eta uJ 11 c * h0⁻¹ := by
    rw [← hα1apply]; exact e2
  have e4 : α (eta uJ 11 c) = (g1 : J) * (h0 * eta uJ 11 c * h0⁻¹) * (g1 : J)⁻¹ := by
    rw [← e3]; group
  rw [e4]
  group

end CFSG.Sporadic.J4.QT
