module

public import Certificates.Kernel.E16.Hall
public import CFSG.Certificates.Kernel.Kc3E16TSound

set_option maxRecDepth 100000

public section

namespace CFSG.KD.E16L

open CFSG.KC.Kc3K CFSG.KC.Enum CFSG.KD.E16
open CFSG.QuasithinUnique.K1.SporadicPerm

structure LChecks (D : Data) (Q : Nat → Nat) : Prop where
  hB : ∀ p ∈ D.B, p < D.n
  hn : D.n ≤ 2 ^ D.w
  gs_lt : ∀ g ∈ D.gs, g < D.NN
  e0_lt : D.e0 < D.NE
  el : ∀ k < D.NE, elK D.w D.m D.NN D.NE D.M D.TF D.B D.gs D.eu D.ev D.ky D.iv D.kv D.tg k = true
  ivc : ∀ i < D.M, ivK D.w D.m D.NE D.M D.R D.TF D.B D.eu D.ev D.ky D.kv D.vu D.vv D.rt D.cj D.RI
    D.FR D.FL D.FM i = true
  rtc : ∀ ρ < D.R, rtK D.w D.m D.n D.M D.TF D.vu D.vv D.RI D.FR ρ = true
  prc : ∀ i < D.M, prK D.w D.m D.M D.TF D.B D.ky D.kv D.vu D.vv D.pr D.ct D.FL D.FM i = true
  nbc : ∀ i < D.M, nbK D.M D.pr D.NB D.NM i = true
  one : D.B.all (fun p => exK D.w D.m D.TF (D.eu D.e0) (D.ev D.e0) p == p) = true
  par : ∀ k < D.NE, elQ D.NE D.e0 D.gs.length D.ky D.tg Q k = true
  ivx : ∀ i < D.M, ivX D.w D.m D.TF D.B D.vu D.vv i = true

variable {D : Data} {Q : Nat → Nat}

theorem nb_spec (h : LChecks D Q) {i : Nat} (hi : i < D.M) (j : Nat) :
    j ∈ D.NB i ↔ j < D.M ∧ D.pr i j < D.M := by
  rw [(nbK_spec (h.nbc i hi)).1, List.mem_filter, List.mem_range, decide_eq_true_eq]

section Group

variable {Γ : Type} [Group Γ] [MulAction Γ (Fin D.n)] {E : Nat → Γ}

theorem eq_of_base (c : Ctx D E) (h : LChecks D Q) {g g' : Γ}
    (hg : ∀ p ∈ D.B, act D.n g p = act D.n g' p) : g = g' := by
  have h1 := c.base (g⁻¹ * g') fun p hp => by
    rw [act_mul _ _ (h.hB p hp), ← hg p hp, act_inv_act _ (h.hB p hp)]
  exact inv_mul_eq_one.1 h1

theorem eq_of_key (c : Ctx D E) (h : LChecks D Q) {g g' : Γ}
    (hk : packL D.w (D.B.map (act D.n g)) = packL D.w (D.B.map (act D.n g'))) : g = g' := by
  refine eq_of_base c h (eq_of_packL (fun p hp => ?_) (fun p hp => ?_) hk)
  · exact lt_of_lt_of_le (act_lt g (h.hB p hp)) h.hn
  · exact lt_of_lt_of_le (act_lt g' (h.hB p hp)) h.hn

theorem act_X (c : Ctx D E) (h : LChecks D Q) {k : Nat} (hk : k < D.NE) {p : Nat} (hp : p < D.n) :
    act D.n (X E D k) p = exK D.w D.m D.TF (D.eu k) (D.ev k) p := by
  obtain ⟨hu, hv, -⟩ := elK_spec (h.el k hk)
  have h1 := act_lt (E (D.ev k)) hp
  unfold X exK
  rw [act_mul _ _ hp, c.actE _ hu _ h1, c.actE _ hv _ hp]

theorem key_X (c : Ctx D E) (h : LChecks D Q) {k : Nat} (hk : k < D.NE) :
    D.ky k = packL D.w (D.B.map (act D.n (X E D k))) := by
  rw [(elK_spec (h.el k hk)).2.2.1]
  exact key_map fun p hp => (act_X c h hk (h.hB p hp)).symm

theorem X_tg (c : Ctx D E) (h : LChecks D Q) {k : Nat} (hk : k < D.NE) {i : Nat}
    (hi : i < D.gs.length) :
    D.tg i k < D.NE ∧ X E D (D.tg i k) = E (D.gs.getD i 0) * X E D k := by
  obtain ⟨-, -, -, ht, -⟩ := elK_spec (h.el k hk)
  obtain ⟨hlt, hkey⟩ := ht i hi
  refine ⟨hlt, eq_of_key c h ?_⟩
  rw [← key_X c h hlt, hkey]
  have hg : D.gs.getD i 0 < D.NN := by
    rw [List.getD_eq_getElem _ _ hi]
    exact h.gs_lt _ (List.getElem_mem hi)
  refine key_map fun p hp => ?_
  rw [act_mul _ _ (h.hB p hp), c.actE _ hg _ (act_lt _ (h.hB p hp)), act_X c h hk (h.hB p hp)]

theorem X_one (c : Ctx D E) (h : LChecks D Q) : X E D D.e0 = 1 := by
  refine eq_of_base c h fun p hp => ?_
  rw [act_X c h h.e0_lt (h.hB p hp), act_one (h.hB p hp)]
  exact beq_iff_eq.1 (List.all_eq_true.1 h.one p hp)

theorem mem_X [Finite Γ] (c : Ctx D E) (h : LChecks D Q) {g : Γ} (hg : g ∈ RX E D) :
    ∃ k < D.NE, X E D k = g := by
  have hstep : ∀ s ∈ {y | y ∈ D.gs.map E}, ∀ k < D.NE, ∃ k' < D.NE,
      X E D k' = s * X E D k := by
    intro s hs k hk
    rw [Set.mem_setOf_eq] at hs
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨h1, h2⟩ := X_tg c h hk hi
    rw [List.getD_eq_getElem _ _ hi] at h2
    exact ⟨_, h1, h2⟩
  refine Subgroup.closure_induction_left (p := fun g _ => ∃ k < D.NE, X E D k = g)
    ⟨D.e0, h.e0_lt, X_one c h⟩ ?_ ?_ hg
  · rintro s hs y - ⟨k, hk, rfl⟩
    exact hstep s hs k hk
  · rintro s hs y - ⟨k, hk, rfl⟩
    have hpow : ∀ n : Nat, ∃ k' < D.NE, X E D k' = s ^ n * X E D k := by
      intro n
      induction n with
      | zero => exact ⟨k, hk, by rw [pow_zero, one_mul]⟩
      | succ n ih =>
        obtain ⟨k1, hk1, e1⟩ := ih
        obtain ⟨k2, hk2, e2⟩ := hstep s hs k1 hk1
        exact ⟨k2, hk2, by rw [e2, e1, pow_succ', mul_assoc]⟩
    have hinv : s⁻¹ = s ^ (orderOf s - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [pow_sub_one_mul (orderOf_pos s).ne', pow_orderOf_eq_one]
    rw [hinv]
    exact hpow _

theorem X_mem (c : Ctx D E) (h : LChecks D Q) {k : Nat} (hk : k < D.NE) : X E D k ∈ RX E D := by
  have key : ∀ d, ∀ k < D.NE, Nat.shiftRight (Q k) 12 = d → X E D k ∈ RX E D := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hk hd
      rcases (elQ_spec (h.par k hk)).2 with h1 | ⟨hp, hc, ht, hdep⟩
      · rw [h1, X_one c h]
        exact (RX E D).one_mem
      · have hpm := ih _ (hd ▸ hdep) _ hp rfl
        obtain ⟨-, e⟩ := X_tg c h hp hc
        rw [ht] at e
        rw [e]
        refine (RX E D).mul_mem (Subgroup.subset_closure ?_) hpm
        rw [Set.mem_setOf_eq, List.getD_eq_getElem _ _ hc]
        exact List.mem_map.2 ⟨_, List.getElem_mem hc, rfl⟩
  exact key _ k hk rfl

theorem X_inj (c : Ctx D E) (h : LChecks D Q) {i j : Nat} (hi : i < D.NE) (hj : j < D.NE)
    (he : X E D i = X E D j) : i = j := by
  have hstrict : ∀ a b, a < b → b < D.NE → D.ky a < D.ky b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
      · exact Nat.lt_trans (ih h' (by omega)) ((elQ_spec (h.par b (by omega))).1 hb)
      · exact (elQ_spec (h.par a (by omega))).1 hb
  have e : D.ky i = D.ky j := by rw [key_X c h hi, key_X c h hj, he]
  rcases Nat.lt_trichotomy i j with h' | h' | h'
  · exact absurd e (Nat.ne_of_lt (hstrict i j h' hj))
  · exact h'
  · exact absurd e.symm (Nat.ne_of_lt (hstrict j i h' hi))

theorem card_RX [Finite Γ] (c : Ctx D E) (h : LChecks D Q) : Nat.card (RX E D) = D.NE := by
  classical
  have hbij : Function.Bijective (fun k : Fin D.NE => (⟨X E D k, X_mem c h k.2⟩ : RX E D)) := by
    refine ⟨fun a b hab => Fin.ext (X_inj c h a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := mem_X c h hg
    exact ⟨⟨k, hk⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem V_spec (h : LChecks D Q) {i : Nat} (hi : i < D.M) :
    D.kv i < D.NE ∧ D.vu i = D.eu (D.kv i) ∧ D.vv i = D.ev (D.kv i) := by
  obtain ⟨h1, h2, h3, -⟩ := ivK_spec (h.ivc i hi)
  exact ⟨h1, h2, h3⟩

theorem act_V (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) {p : Nat} (hp : p < D.n) :
    act D.n (V E D i) p = exK D.w D.m D.TF (D.vu i) (D.vv i) p := by
  obtain ⟨h1, h2, h3⟩ := V_spec h hi
  rw [h2, h3]
  exact act_X c h h1 hp

theorem key_V (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) :
    D.ky (D.kv i) = packL D.w (D.B.map (act D.n (V E D i))) := key_X c h (V_spec h hi).1

theorem key_lt (h : LChecks D Q) {i j : Nat} (hij : i < j) (hj : j < D.M) :
    D.ky (D.kv i) < D.ky (D.kv j) := by
  induction j, hij using Nat.le_induction with
  | base => exact (ivK_spec (h.ivc i (by omega))).2.2.2.1 hj
  | succ n hn ih =>
    exact lt_trans (ih (by omega)) ((ivK_spec (h.ivc n (by omega))).2.2.2.1 hj)

theorem V_inj (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) {j : Nat} (hj : j < D.M)
    (he : V E D i = V E D j) : i = j := by
  have e : D.ky (D.kv i) = D.ky (D.kv j) := by rw [key_V c h hi, key_V c h hj, he]
  rcases lt_trichotomy i j with hij | hij | hij
  · exact absurd e (key_lt h hij hj).ne
  · exact hij
  · exact absurd e (key_lt h hij hi).ne'

theorem V_sq (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) : V E D i * V E D i = 1 := by
  refine eq_of_base c h fun p hp => ?_
  have hq := act_lt (V E D i) (h.hB p hp)
  rw [act_mul _ _ (h.hB p hp), act_one (h.hB p hp), act_V c h hi hq, act_V c h hi (h.hB p hp)]
  exact (ivX_spec (h.ivx i hi)).1 p hp

theorem V_ne_one (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) : V E D i ≠ 1 := by
  intro he
  obtain ⟨p, hp, hne⟩ := (ivX_spec (h.ivx i hi)).2
  apply hne
  rw [← act_V c h hi (h.hB p hp), he, act_one (h.hB p hp)]

theorem V_list [Finite Γ] (c : Ctx D E) (h : LChecks D Q) {x : Γ} (hx : x ∈ RX E D)
    (hxx : x * x = 1) (hx1 : x ≠ 1) : ∃ i < D.M, V E D i = x := by
  obtain ⟨k, hk, rfl⟩ := mem_X c h hx
  have hsq : ∀ p ∈ D.B,
      exK D.w D.m D.TF (D.eu k) (D.ev k) (exK D.w D.m D.TF (D.eu k) (D.ev k) p) = p := by
    intro p hp
    have e : act D.n (X E D k * X E D k) p = act D.n (1 : Γ) p := by rw [hxx]
    rw [act_mul _ _ (h.hB p hp), act_X c h hk (act_lt _ (h.hB p hp)), act_X c h hk (h.hB p hp),
      act_one (h.hB p hp)] at e
    exact e
  have hmv : ∃ p ∈ D.B, exK D.w D.m D.TF (D.eu k) (D.ev k) p ≠ p := by
    by_contra! hn
    exact hx1 (c.base _ fun p hp => by rw [act_X c h hk (h.hB p hp)]; exact hn p hp)
  obtain ⟨hlt, he⟩ := (elK_spec (h.el k hk)).2.2.2.2 hsq hmv
  exact ⟨D.iv k, hlt, by unfold V; rw [he]⟩

theorem V_pr_lt (c : Ctx D E) (h : LChecks D Q) {i j : Nat} (hij : i < j) (hj : j < D.M)
    (hc : V E D i * V E D j = V E D j * V E D i) :
    D.pr i j < D.M ∧ V E D (D.pr i j) = V E D i * V E D j := by
  have hi : i < D.M := by omega
  obtain ⟨-, hr⟩ := prK_spec (h.prc i hi) j hj
  obtain ⟨hlt, hge⟩ := hr hij
  have hp : D.pr i j < D.M := by
    by_contra hn
    obtain ⟨p, hp, hne⟩ := hge hn
    apply hne
    have e : act D.n (V E D i * V E D j) p = act D.n (V E D j * V E D i) p := by rw [hc]
    rw [act_mul _ _ (h.hB p hp), act_mul _ _ (h.hB p hp), act_V c h hi (act_lt _ (h.hB p hp)),
      act_V c h hj (h.hB p hp), act_V c h hj (act_lt _ (h.hB p hp)), act_V c h hi (h.hB p hp)] at e
    exact e
  refine ⟨hp, eq_of_key c h ?_⟩
  rw [← key_V c h hp, (hlt hp).1]
  refine key_map fun p hp => ?_
  rw [act_mul _ _ (h.hB p hp), act_V c h hi (act_lt _ (h.hB p hp)), act_V c h hj (h.hB p hp)]

theorem V_pr (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) {j : Nat} (hj : j < D.M)
    (hij : i ≠ j) (hc : V E D i * V E D j = V E D j * V E D i) :
    D.pr i j < D.M ∧ V E D (D.pr i j) = V E D i * V E D j := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact V_pr_lt c h hlt hj hc
  · have e := ((prK_spec (h.prc i hi) j hj).1)
    obtain ⟨h1, h2⟩ := V_pr_lt c h hlt hi hc.symm
    rw [e, h2, hc]
    exact ⟨h1, rfl⟩

theorem comm_of_sq {a b : Γ} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * (a * b) = 1) :
    a * b = b * a := by
  have e := eq_inv_of_mul_eq_one_left hab
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at e
  exact e

theorem V_mul_lt (c : Ctx D E) (h : LChecks D Q) {i j : Nat} (hij : i < j) (hj : j < D.M)
    (hp : D.pr i j < D.M) :
    V E D (D.pr i j) = V E D i * V E D j ∧ V E D i * V E D j = V E D j * V E D i := by
  have hi : i < D.M := by omega
  obtain ⟨-, hr⟩ := prK_spec (h.prc i hi) j hj
  obtain ⟨hlt, -⟩ := hr hij
  have e : V E D (D.pr i j) = V E D i * V E D j := by
    refine eq_of_key c h ?_
    rw [← key_V c h hp, (hlt hp).1]
    refine key_map fun p hp => ?_
    rw [act_mul _ _ (h.hB p hp), act_V c h hi (act_lt _ (h.hB p hp)), act_V c h hj (h.hB p hp)]
  refine ⟨e, comm_of_sq (V_sq c h hi) (V_sq c h hj) ?_⟩
  rw [← e]
  exact V_sq c h hp

theorem V_mul (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) {j : Nat} (hj : j < D.M)
    (hij : i ≠ j) (hp : D.pr i j < D.M) :
    V E D (D.pr i j) = V E D i * V E D j ∧ V E D i * V E D j = V E D j * V E D i := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · exact V_mul_lt c h hlt hj hp
  · have e := (prK_spec (h.prc i hi) j hj).1
    rw [e] at hp ⊢
    obtain ⟨h1, h2⟩ := V_mul_lt c h hlt hi hp
    rw [h1]
    exact ⟨h2, h2.symm⟩

theorem NB_spec (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) {j : Nat} (hj : j < D.M)
    (hij : i ≠ j) (hc : V E D i * V E D j = V E D j * V E D i) : j ∈ D.NB i :=
  (nb_spec h hi j).2 ⟨hj, (V_pr c h hi hj hij hc).1⟩

theorem NM_spec (h : LChecks D Q) {i : Nat} (hi : i < D.M) {j : Nat} (hj : j ∈ D.NB i) :
    (D.NM i).testBit j = true := by
  rw [(nbK_spec (h.nbc i hi)).2, testBit_maskL]
  exact hj

theorem FR_spec (c : Ctx D E) (h : LChecks D Q) {ρ : Nat} (hρ : ρ < D.R) :
    D.RI ρ < D.M ∧ (D.FR ρ).Nodup ∧ (∀ p ∈ D.FR ρ, p < D.n) ∧
      ∀ p < D.n, p ∈ D.FR ρ ↔ act D.n (V E D (D.RI ρ)) p = p := by
  obtain ⟨hr, hs, hf, hc⟩ := rtK_spec (h.rtc ρ hρ)
  have hnd : (D.FR ρ).Nodup := hs.imp (fun h => h.ne)
  let F := (List.range D.n).filter fun p => exK D.w D.m D.TF (D.vu (D.RI ρ)) (D.vv (D.RI ρ)) p == p
  have hsub : (D.FR ρ).toFinset ⊆ F.toFinset := by
    intro p hp
    rw [List.mem_toFinset] at hp ⊢
    obtain ⟨h1, h2⟩ := hf p hp
    exact List.mem_filter.2 ⟨List.mem_range.2 h1, beq_iff_eq.2 h2⟩
  have heq : (D.FR ρ).toFinset = F.toFinset := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hnd, List.toFinset_card_of_nodup
      ((List.nodup_range).filter _), hc])
  refine ⟨hr, hnd, fun p hp => (hf p hp).1, fun p hp => ?_⟩
  rw [act_V c h hr hp, ← List.mem_toFinset, heq, List.mem_toFinset, List.mem_filter,
    List.mem_range, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

theorem FL_spec (c : Ctx D E) (h : LChecks D Q) {i : Nat} (hi : i < D.M) :
    (D.FL i).Nodup ∧ (∀ p ∈ D.FL i, p < D.n) ∧
      ∀ p < D.n, p ∈ D.FL i ↔ act D.n (V E D i) p = p := by
  obtain ⟨-, -, -, -, hrt, -, hcj, hconj, hFL, -⟩ := ivK_spec (h.ivc i hi)
  obtain ⟨hr, hnd, hlt, hfix⟩ := FR_spec c h hrt
  set y := X E D (D.cj i)
  set r := D.RI (D.rt i)
  have hy : ∀ p < D.n, exK D.w D.m D.TF (D.eu (D.cj i)) (D.ev (D.cj i)) p = act D.n y p :=
    fun p hp => (act_X c h hcj hp).symm
  have hVi : V E D i = y * V E D r * y⁻¹ := by
    have e : V E D i * y = y * V E D r := eq_of_base c h fun p hp => by
      have hq : exK D.w D.m D.TF (D.vu r) (D.vv r) p < D.n := by
        rw [← act_V c h hr (h.hB p hp)]
        exact act_lt _ (h.hB p hp)
      have hq' : exK D.w D.m D.TF (D.eu (D.cj i)) (D.ev (D.cj i)) p < D.n := by
        rw [hy p (h.hB p hp)]
        exact act_lt _ (h.hB p hp)
      rw [act_mul _ _ (h.hB p hp), act_mul _ _ (h.hB p hp), ← hy p (h.hB p hp), act_V c h hi hq',
        act_V c h hr (h.hB p hp), ← hy _ hq]
      exact hconj p hp
    rw [← e, mul_inv_cancel_right]
  have hFL' : D.FL i = (D.FR (D.rt i)).map (act D.n y) := by
    rw [hFL]
    exact List.map_congr_left fun p hp => hy p (hlt p hp)
  refine ⟨?_, ?_, fun p hp => ?_⟩
  · rw [hFL']
    refine hnd.map_on fun p hp q hq e => ?_
    rw [← act_inv_act y (hlt p hp), e, act_inv_act y (hlt q hq)]
  · rw [hFL']
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact act_lt y (hlt q hq)
  · have hp' := act_lt y⁻¹ hp
    rw [hFL', hVi, act_mul _ _ hp, act_mul _ _ (act_lt _ hp)]
    constructor
    · intro hm
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm
      rw [act_inv_act y (hlt q hq), (hfix q (hlt q hq)).1 hq]
    · intro he
      have e2 : act D.n (V E D r) (act D.n y⁻¹ p) = act D.n y⁻¹ p := by
        have := congrArg (act D.n y⁻¹) he
        rwa [act_inv_act y (act_lt _ hp')] at this
      exact List.mem_map.2 ⟨_, (hfix _ hp').2 e2, act_act_inv y hp⟩

end Group

end CFSG.KD.E16L

end
