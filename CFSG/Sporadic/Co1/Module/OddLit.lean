
module

public import CFSG.Sporadic.Co1.Module.OddLitBase
public import CFSG.Sporadic.Co1.Module.OddCount

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.Odd73
  CFSG.KD.Co1Odd

section Grp

variable {G : Type*} [Group G]

theorem conj_of_odd73 {x y : G} (hx : x * x = 1) (hy : y * y = 1) {m : ℕ}
    (hm : orderOf (x * y) = 2 * m + 1) : (x * y) ^ m * x * ((x * y) ^ m)⁻¹ = y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hxu : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    calc x * (x * y) * x⁻¹ = (x * x) * y * x⁻¹ := by group
      _ = y⁻¹ * x⁻¹ := by rw [hx, one_mul, hyi]
      _ = (x * y)⁻¹ := by rw [_root_.mul_inv_rev]
  have hpow : x * (x * y) ^ m * x⁻¹ = ((x * y) ^ m)⁻¹ := by
    rw [← conj_pow, hxu, inv_pow]
  have hord : (x * y) ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  have h2m : (x * y) ^ (2 * m) = (x * y)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hord]
  calc (x * y) ^ m * x * ((x * y) ^ m)⁻¹ = (x * y) ^ m * x * (x * (x * y) ^ m * x⁻¹) := by
        rw [hpow]
    _ = (x * y) ^ m * (x * x) * (x * y) ^ m * x⁻¹ := by group
    _ = (x * y) ^ (2 * m) * x⁻¹ := by rw [hx, mul_one, ← pow_add, two_mul]
    _ = y := by rw [h2m, _root_.mul_inv_rev, hxi, hyi, mul_assoc, hx, mul_one]

theorem orderOf_mul_conj73 {c ρ s : G} (hc : c * ρ = ρ * c) :
    orderOf (ρ * (c * s * c⁻¹)) = orderOf (ρ * s) := by
  have : ρ * (c * s * c⁻¹) = c * (ρ * s) * c⁻¹ := by
    calc ρ * (c * s * c⁻¹) = (ρ * c) * s * c⁻¹ := by group
      _ = (c * ρ) * s * c⁻¹ := by rw [hc]
      _ = c * (ρ * s) * c⁻¹ := by group
  rw [this]
  exact (MulAut.conj c).orderOf_eq (ρ * s)

theorem sq_of_conj73 {x y : G} (hx : x * x = 1) (h : IsConj x y) : y * y = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  rw [← hc]
  calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
    _ = 1 := by rw [hx, mul_one, mul_inv_cancel]

theorem conj_in_of_odd73 (K : Subgroup G) {x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hx : x * x = 1)
    (hy : y * y = 1) (h : Odd (orderOf (x * y))) : ∃ w ∈ K, y = w * x * w⁻¹ := by
  obtain ⟨m, hm⟩ := h
  exact ⟨(x * y) ^ m, K.pow_mem (K.mul_mem hxK hyK) m, (conj_of_odd73 hx hy (by omega)).symm⟩

theorem card_conj73 [Finite G] (K : Subgroup G) (a : G) :
    Nat.card ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) *
      {y : G | ∃ n ∈ K, y = n * a * n⁻¹}.ncard = Nat.card ↥K := by
  have h := card_stabilizer_pair_mul_ncard_orbit K a a
  rw [inf_assoc, inf_idem] at h
  have e : {p : G × G | ∃ n ∈ K, p = (n * a * n⁻¹, n * a * n⁻¹)} =
      (fun y : G => (y, y)) '' {y : G | ∃ n ∈ K, y = n * a * n⁻¹} := by
    ext p
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨n, hn, rfl⟩
  rw [e, Set.ncard_image_of_injective _ (fun y z h => (Prod.mk.inj h).1)] at h
  exact h

theorem card_ge_conj73 [Finite G] (K : Subgroup G) (s : G) (I : Set ℕ) (m : ℕ) (g z : ℕ → G)
    (hg : ∀ i ∈ I, ∃ c ∈ K, g i = c * s * c⁻¹)
    (hginj : ∀ i ∈ I, ∀ j ∈ I, g i = g j → i = j)
    (hz : ∀ j < m, z j ∈ K ⊓ Subgroup.centralizer ({s} : Set G))
    (hzinj : ∀ i < m, ∀ j < m, z i = z j → i = j) :
    I.ncard * m ≤ Nat.card ↥K := by
  classical
  choose! c hcK hcg using hg
  let Φ : ℕ × ℕ → G := fun p => c p.1 * z p.2
  have hzK : ∀ j < m, z j ∈ K := fun j hj => (Subgroup.mem_inf.1 (hz j hj)).1
  have hzs : ∀ j < m, z j * s = s * z j := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hz j hj)).2
  have hmaps : ∀ p ∈ I ×ˢ Set.Iio m, Φ p ∈ (K : Set G) := by
    rintro ⟨i, j⟩ ⟨hi, hj⟩
    exact K.mul_mem (hcK i hi) (hzK j hj)
  have hinj : Set.InjOn Φ (I ×ˢ Set.Iio m) := by
    rintro ⟨i, j⟩ ⟨hi, hj⟩ ⟨i', j'⟩ ⟨hi', hj'⟩ e
    have e1 : c i * z j = c i' * z j' := e
    have hconj : ∀ (a b : ℕ), a ∈ I → b < m → (c a * z b) * s * (c a * z b)⁻¹ = g a := by
      intro a b ha hb
      calc (c a * z b) * s * (c a * z b)⁻¹ = c a * (z b * s * (z b)⁻¹) * (c a)⁻¹ := by group
        _ = c a * s * (c a)⁻¹ := by rw [hzs b hb]; group
        _ = g a := (hcg a ha).symm
    have hgg : g i = g i' := by
      rw [← hconj i j hi hj, ← hconj i' j' hi' hj', e1]
    have hii : i = i' := hginj i hi i' hi' hgg
    subst hii
    have : z j = z j' := mul_left_cancel e1
    have hjj : j = j' := hzinj j hj j' hj' this
    rw [hjj]
  have hle := Set.ncard_le_ncard_of_injOn Φ hmaps hinj (Set.toFinite _)
  rw [Set.ncard_prod, Set.ncard_Iio_nat] at hle
  have e : Nat.card ↥K = (K : Set G).ncard := Nat.card_coe_set_eq (K : Set G)
  rw [e]
  exact hle

omit [Group G] in
theorem eq_image_of_card73 [Finite G] {A : Set G} {x : ℕ → G} {I : Set ℕ}
    (hx : ∀ i ∈ I, x i ∈ A) (hinj : Set.InjOn x I) (hA : A.ncard ≤ I.ncard) : x '' I = A := by
  have hsub : x '' I ⊆ A := by
    rintro _ ⟨i, hi, rfl⟩
    exact hx i hi
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [hinj.ncard_image]
  exact hA

end Grp

structure OddHyp73 (H : Subgroup NativeSporadic.Co1) : Prop where
  ρ_sq : reg 27 * reg 27 = 1
  ρ_mem : reg 27 ∈ H
  t₁_mem : reg 86 ∈ H
  t₁_conj : IsConj (reg 27) (reg 86)
  s_mem : ∀ k < 3, reg (getL 0 J73 k) ∈ H
  s_conj : ∀ k < 3, IsConj (reg 27) (reg (getL 0 J73 k))
  s_odd : ∀ k < 3, Odd (orderOf (reg 27 * reg (getL 0 J73 k)))
  gen_mem : ∀ l < 10, reg (getL 0 I73 l) ∈ H
  gen_inv : ∀ l < 10, reg (getL 0 Ii73 l) = (reg (getL 0 I73 l))⁻¹
  bray : ∀ l < 8, reg (getL 0 I73 l) * reg 27 = reg 27 * reg (getL 0 I73 l)
  z0 : ∀ i ∈ [77, 78, 79, 80], reg i ∈ H ⊓ Subgroup.centralizer {reg 27} ⊓
    Subgroup.centralizer {reg (getL 0 J73 0)}
  z1 : ∀ i ∈ [81, 82], reg i ∈ H ⊓ Subgroup.centralizer {reg 27} ⊓
    Subgroup.centralizer {reg (getL 0 J73 1)}
  z2 : ∀ i ∈ [83, 84], reg i ∈ H ⊓ Subgroup.centralizer {reg 27} ⊓
    Subgroup.centralizer {reg (getL 0 J73 2)}

@[expose] def Sem73 (H : Subgroup NativeSporadic.Co1) (c : ℕ)
    (x : NativeSporadic.Co1) : Prop :=
  (c = 0 ∧ (∃ n ∈ H, x = n * reg 27 * n⁻¹) ∧ ¬ Odd (orderOf (reg 27 * x))) ∨
  (c = 1 ∧ x = reg 27) ∨
  (∃ k < 3, c = k + 2 ∧ ∃ g ∈ H ⊓ Subgroup.centralizer {reg 27}, x = g * reg (getL 0 J73 k) * g⁻¹) ∨
  (c = 5 ∧ (∃ n ∈ H, x = n * reg 86 * n⁻¹) ∧ x * reg 86 = reg 86 * x)

section Main

variable {W : OddW} (hW : OddOK W) {H : Subgroup NativeSporadic.Co1}
  (hH : OddHyp73 H)
include hW hH

omit hW in
theorem sk_conj73 {k : ℕ} (hk : k < 3) : ∃ w ∈ H, reg (getL 0 J73 k) = w * reg 27 * w⁻¹ :=
  conj_in_of_odd73 H hH.ρ_mem (hH.s_mem k hk) hH.ρ_sq (sq_of_conj73 hH.ρ_sq (hH.s_conj k hk))
    (hH.s_odd k hk)

omit hW in
theorem sem73_conj {c : ℕ} {x : NativeSporadic.Co1} (h : Sem73 H c x) (hc : c ≠ 5) :
    ∃ n ∈ H, x = n * reg 27 * n⁻¹ := by
  rcases h with ⟨-, h, -⟩ | ⟨-, rfl⟩ | ⟨k, hk, -, g, hg, rfl⟩ | ⟨rfl, -⟩
  · exact h
  · exact ⟨1, H.one_mem, by group⟩
  · obtain ⟨w, hw, e⟩ := sk_conj73 hH hk
    refine ⟨g * w, H.mul_mem (Subgroup.mem_inf.1 hg).1 hw, ?_⟩
    rw [e]
    group
  · exact absurd rfl hc

omit hH in
theorem pm73_letter {l : ℕ} (hl : l < 10) : PM73 (reg (getL 0 I73 l)) (getL 0 W.R (getL 0 I73 l)) :=
  pm73_reg hW (by interval_cases l <;> decide)

omit hH in
theorem pm73_letteri {l : ℕ} (hl : l < 10) :
    PM73 (reg (getL 0 Ii73 l)) (getL 0 W.R (getL 0 Ii73 l)) :=
  pm73_reg hW (by interval_cases l <;> decide)

omit hH in
theorem pm73_jump {k : ℕ} (hk : k < 4) : PM73 (reg (getL 0 J73 k)) (getL 0 W.R (getL 0 J73 k)) :=
  pm73_reg hW (by interval_cases k <;> decide)

omit hW hH in
theorem comm73 {x y : NativeSporadic.Co1} {X Y : ℕ} (hx : PM73 x X) (hy : PM73 y Y)
    (h : mulF 24 X Y = mulF 24 Y X) : x * y = y * x := by
  have h1 := pm73_mul hx hy
  have h2 := pm73_mul hy hx
  rw [h] at h1
  exact pm73_inj h1 h2

omit hW hH in
theorem sem73_bray {b x : NativeSporadic.Co1} (hbH : b ∈ H) (hbρ : b * reg 27 = reg 27 * b)
    {c : ℕ} (h : Sem73 H c x) (h5 : c = 5 → b * x * b⁻¹ * reg 86 = reg 86 * (b * x * b⁻¹)) :
    Sem73 H c (b * x * b⁻¹) := by
  have hbC : b ∈ H ⊓ Subgroup.centralizer {reg 27} :=
    Subgroup.mem_inf.2 ⟨hbH, Subgroup.mem_centralizer_singleton_iff.2 hbρ⟩
  rcases h with ⟨h0, ⟨n, hn', e⟩, hodd⟩ | ⟨h1, e⟩ | ⟨k, hk, hck, g, hg, e⟩ | ⟨hc, ⟨n, hn', e⟩, -⟩
  · refine Or.inl ⟨h0, ⟨b * n, H.mul_mem hbH hn', ?_⟩, ?_⟩
    · rw [e]
      group
    · have ho : orderOf (reg 27 * (b * x * b⁻¹)) = orderOf (reg 27 * x) :=
        @orderOf_mul_conj73 NativeSporadic.Co1 _ b (reg 27) x hbρ
      rw [ho]
      exact hodd
  · refine Or.inr (Or.inl ⟨h1, ?_⟩)
    rw [e, hbρ, mul_inv_cancel_right]
  · refine Or.inr (Or.inr (Or.inl ⟨k, hk, hck, b * g, Subgroup.mul_mem _ hbC hg, ?_⟩))
    rw [e]
    group
  · refine Or.inr (Or.inr (Or.inr ⟨hc, ⟨b * n, H.mul_mem hbH hn', ?_⟩, h5 hc⟩))
    rw [e]
    group

omit hW in
theorem sem73_n {b x : NativeSporadic.Co1} (hbH : b ∈ H) {c : ℕ} (h : Sem73 H c x) (hc : c ≠ 5)
    (hodd : ¬ Odd (orderOf (reg 27 * (b * x * b⁻¹)))) : Sem73 H 0 (b * x * b⁻¹) := by
  obtain ⟨n, hn', e⟩ := sem73_conj hH h hc
  refine Or.inl ⟨rfl, ⟨b * n, H.mul_mem hbH hn', ?_⟩, hodd⟩
  rw [e]
  group

omit hW hH in
theorem sem73_n5 {b x : NativeSporadic.Co1} (hbH : b ∈ H) (h : Sem73 H 5 x)
    (h5 : b * x * b⁻¹ * reg 86 = reg 86 * (b * x * b⁻¹)) : Sem73 H 5 (b * x * b⁻¹) := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, h, -⟩ | ⟨-, ⟨n, hn', e⟩, -⟩
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · omega
  · refine Or.inr (Or.inr (Or.inr ⟨rfl, ⟨b * n, H.mul_mem hbH hn', ?_⟩, h5⟩))
    rw [e]
    group

theorem step73 {g vp v L c cp o : ℕ} (hL : L ≠ 0) (hg : g < 14) (hact : act73 W.R g vp = v)
    (hrule : ruleOK W.R v L g c o cp = true) {xp : NativeSporadic.Co1} (hxp : PM73 xp vp)
    (hsp : Sem73 H cp xp) : ∃ x, PM73 x v ∧ Sem73 H c x := by
  have h86 : PM73 (reg 86) (W.reg 86) := pm73_reg hW (by norm_num)
  have h27 : PM73 (reg 27) (W.reg 27) := pm73_reg hW (by norm_num)
  obtain ⟨-, hc5, -, hbray, hn, hj, ht⟩ := ruleOK73_spec hrule
  have hcomm : c = 5 → ∀ x, PM73 x v → x * reg 86 = reg 86 * x :=
    fun h5 x hx => comm73 hx h86 (hc5 h5)
  by_cases hg10 : g < 10
  · have hb := pm73_letter hW hg10
    have hbi : PM73 (reg (getL 0 I73 g))⁻¹ (getL 0 W.R (getL 0 Ii73 g)) := by
      have := pm73_letteri hW hg10
      rwa [hH.gen_inv g hg10] at this
    have hX : PM73 (reg (getL 0 I73 g) * xp * (reg (getL 0 I73 g))⁻¹) v := by
      rw [← hact, act73_lt hg10]
      exact pm73_conj hxp hb hbi
    have hbH := hH.gen_mem g hg10
    refine ⟨_, hX, ?_⟩
    by_cases hg8 : g < 8
    · rw [hbray hL hg8]
      exact sem73_bray hbH (hH.bray g hg8) hsp
        (fun h5 => hcomm (by rw [hbray hL hg8]; exact h5) _ hX)
    · obtain ⟨hn5, hn0⟩ := hn hL (by omega) hg10
      by_cases hcp : cp = 5
      · rw [hn5 hcp]
        rw [hcp] at hsp
        exact sem73_n5 hbH hsp (hcomm (hn5 hcp) _ hX)
      · obtain ⟨h0, ho, hoe, hok⟩ := hn0 hcp
        rw [h0]
        refine sem73_n hH hbH hsp hcp ?_
        rw [orderOf_eq73 (pm73_mul h27 hX) ho hok, Nat.not_odd_iff_even, Nat.even_iff]
        exact hoe
  · have hgv := act73_ge (R := W.R) hg10 vp
    rw [hact] at hgv
    by_cases hg13 : g < 13
    · have hx := pm73_jump hW (k := g - 10) (by omega)
      rw [← hgv] at hx
      refine ⟨_, hx, Or.inr (Or.inr (Or.inl ⟨g - 10, by omega, ?_, 1, Subgroup.one_mem _, ?_⟩))⟩
      · rw [hj hL (by omega) hg13]
        omega
      · group
    · have hg13' : g = 13 := by omega
      have hx : PM73 (reg 86) v := by
        rw [hgv, hg13']
        exact h86
      have h5 := ht hL (by omega)
      rw [h5]
      refine ⟨reg 86, hx, Or.inr (Or.inr (Or.inr ⟨rfl, ⟨1, H.one_mem, ?_⟩, hcomm h5 _ hx⟩))⟩
      group

theorem rec73_sem : ∀ i < nS, ∃ x, PM73 x (val73 W i) ∧ Sem73 H (clsA (W.aux i)) x := by
  suffices key : ∀ L i, i < nS → levF 576 W.T.wl (W.T.tab i) ≤ L →
      ∃ x, PM73 x (val73 W i) ∧ Sem73 H (clsA (W.aux i)) x from
    fun i hi => key _ i hi le_rfl
  have h86 : PM73 (reg 86) (W.reg 86) := pm73_reg hW (by norm_num)
  have h27 : PM73 (reg 27) (W.reg 27) := pm73_reg hW (by norm_num)
  intro L
  induction L with
  | zero =>
    intro i hi hL
    have hL0 : levF 576 W.T.wl (W.T.tab i) = 0 := by omega
    have hrule := aux73_spec hW hi
    unfold auxOK73 at hrule
    rw [andB73] at hrule
    obtain ⟨-, -, h0, -⟩ := ruleOK73_spec hrule.2
    refine ⟨reg 27, ?_, Or.inr (Or.inl ⟨h0 hL0, rfl⟩)⟩
    rw [(rec73_spec hW hi).1 hL0]
    exact h27
  | succ L ih =>
    intro i hi hL
    by_cases hL0 : levF 576 W.T.wl (W.T.tab i) = 0
    · exact ih i hi (by omega)
    obtain ⟨hp, hg, hlev, hact⟩ := (rec73_spec hW hi).2 hL0
    obtain ⟨xp, hxp, hsp⟩ := ih _ hp (by omega)
    have hrule := aux73_spec hW hi
    unfold auxOK73 at hrule
    rw [andB73] at hrule
    exact step73 hW hH hL0 hg hact hrule.2 hxp hsp

omit hH in
theorem canon73_val {i : ℕ} (hi : i < nS) : Canon73 (val73 W i) := by
  by_cases hL0 : levF 576 W.T.wl (W.T.tab i) = 0
  · rw [(rec73_spec hW hi).1 hL0]
    exact canon73_reg hW (by norm_num)
  · obtain ⟨-, hg, -, hact⟩ := (rec73_spec hW hi).2 hL0
    rw [← hact]
    by_cases hg10 : letF 576 W.T.wl W.T.wp (W.T.tab i) < 10
    · rw [act73_lt hg10]
      exact canon73_mulF _ _
    · rw [act73_ge hg10]
      have hk : letF 576 W.T.wl W.T.wp (W.T.tab i) - 10 < 4 := by omega
      have := canon73_reg hW (i := getL 0 J73 (letF 576 W.T.wl W.T.wp (W.T.tab i) - 10))
        (by interval_cases (letF 576 W.T.wl W.T.wp (W.T.tab i) - 10) <;> decide)
      exact this

theorem recs73 : ∃ x : ℕ → NativeSporadic.Co1, (∀ i < nS, PM73 (x i) (val73 W i) ∧
    Sem73 H (clsA (W.aux i)) (x i)) ∧ ∀ i < nS, ∀ j < nS, x i = x j → i = j := by
  choose! x hx using rec73_sem hW hH
  refine ⟨x, hx, fun i hi j hj e => val73_inj hW hi hj ?_⟩
  exact pm73_eq (hx i hi).1 (hx j hj).1 (canon73_val hW hi) (canon73_val hW hj) e

omit hH in
theorem pre73 : ∀ i ≤ nS, ∀ c < 4,
    preA (W.aux i) c = ((Finset.range i).filter (fun j => clsA (W.aux j) = c + 2)).card := by
  intro i
  induction i with
  | zero =>
    intro _ c hc
    have := beq_iff.1 (allN73.1 hW.aux0 c hc)
    simpa using this
  | succ i ih =>
    intro hi c hc
    have hrule := aux73_spec hW (show i < nS by omega)
    unfold auxOK73 at hrule
    rw [andB73] at hrule
    rw [preOK73_spec hrule.1 hc, ih (by omega) c hc, Finset.range_add_one, Finset.filter_insert]
    by_cases h : clsA (W.aux i) = c + 2
    · simp only [h, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
    · simp only [h, ↓reduceIte, Nat.add_zero]

omit hH in
theorem cnt73 {c : ℕ} (hc : c < 4) :
    {i | i < nS ∧ clsA (W.aux i) = c + 2}.ncard = getL 0 [7168, 2048, 28672, 759] c := by
  have h1 := beq_iff.1 (allN73.1 hW.auxN c hc)
  rw [pre73 hW nS le_rfl c hc] at h1
  have e : {i | i < nS ∧ clsA (W.aux i) = c + 2} =
      ↑((Finset.range nS).filter (fun j => clsA (W.aux j) = c + 2)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  rw [← h1, e, Set.ncard_coe_finset]

omit hW hH in
theorem treeOK71_facts73 {G P par lab : List ℕ} {n : ℕ} (hT : treeOK71 G P par lab n = true) :
    P.length = n ∧ P.getD 0 0 = idF 24 ∧ ∀ i < n, i = 0 ∨ ((par.getD i 0 < i ∧
      lab.getD i 0 < G.length) ∧ P.getD i 0 = mulF 24 (P.getD (par.getD i 0) 0)
        (G.getD (lab.getD i 0) 0)) := by
  unfold treeOK71 ptsOK71 at hT
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hT
  obtain ⟨⟨⟨⟨h1, -⟩, -⟩, h0⟩, hall⟩ := hT
  refine ⟨h1, h0, fun i hi => ?_⟩
  have h := hall i (List.mem_range'_1.2 ⟨Nat.zero_le _, by omega⟩)
  unfold ptOK71 at h
  simpa only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] using h

omit hW hH in
theorem tree73 {G P par lab : List ℕ} {n : ℕ} (hT : treeOK71 G P par lab n = true)
    (hd : distinctL P = true) (hc : canonL P = true)
    (gens : ℕ → NativeSporadic.Co1) (hg : ∀ l < G.length, PM73 (gens l) (G.getD l 0))
    (K : Subgroup NativeSporadic.Co1) (hK : ∀ l < G.length, gens l ∈ K) :
    ∃ z : ℕ → NativeSporadic.Co1, (∀ i < n, z i ∈ K ∧ PM73 (z i) (P.getD i 0)) ∧
      ∀ i < n, ∀ j < n, z i = z j → i = j := by
  obtain ⟨hlen, h0, hall⟩ := treeOK71_facts73 hT
  have key : ∀ i < n, ∃ x ∈ K, PM73 x (P.getD i 0) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases hall i hi with h | ⟨⟨hp, hl⟩, he⟩
      · subst h
        exact ⟨1, K.one_mem, by rw [h0]; exact pm73_one⟩
      · obtain ⟨x, hxK, hx⟩ := ih _ hp (lt_trans hp hi)
        refine ⟨x * gens (lab.getD i 0), K.mul_mem hxK (hK _ hl), ?_⟩
        rw [he]
        exact pm73_mul hx (hg _ hl)
  choose! z hz using key
  refine ⟨z, fun i hi => hz i hi, fun i hi j hj e => ?_⟩
  have hPe := pm73_eq (hz i hi).2 (hz j hj).2 (canonL73 hc (by omega)) (canonL73 hc (by omega)) e
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at hPe
  exact (List.Nodup.getElem_inj_iff (distinctL73 P hd)).1 hPe

theorem zTree0_73 : ∃ z : ℕ → NativeSporadic.Co1, (∀ i < 384, z i ∈ H ⊓
    Subgroup.centralizer {reg 27} ⊓ Subgroup.centralizer {reg (getL 0 J73 0)} ∧
      PM73 (z i) (W.Z0P.getD i 0)) ∧ ∀ i < 384, ∀ j < 384, z i = z j → i = j := by
  have hl : W.Z0G.length = 4 := by rw [hW.z0G]; rfl
  refine tree73 hW.z0 hW.z0d hW.z0c (fun l => reg (77 + l)) (fun l hl' => ?_) _ (fun l hl' => ?_)
  · rw [hl] at hl'
    rw [hW.z0G]
    interval_cases l
    · exact pm73_reg hW (by norm_num)
    · exact pm73_reg hW (by norm_num)
    · exact pm73_reg hW (by norm_num)
    · exact pm73_reg hW (by norm_num)
  · rw [hl] at hl'
    exact hH.z0 _ (by interval_cases l <;> simp)

theorem zTree1_73 : ∃ z : ℕ → NativeSporadic.Co1, (∀ i < 1344, z i ∈ H ⊓
    Subgroup.centralizer {reg 27} ⊓ Subgroup.centralizer {reg (getL 0 J73 1)} ∧
      PM73 (z i) (Z1P.getD i 0)) ∧ ∀ i < 1344, ∀ j < 1344, z i = z j → i = j := by
  have hl : Z1G.length = 2 := by rw [hW.z1G]; rfl
  refine tree73 hW.z1 hW.z1d hW.z1c (fun l => reg (81 + l)) (fun l hl' => ?_) _ (fun l hl' => ?_)
  · rw [hl] at hl'
    rw [hW.z1G]
    interval_cases l
    · exact pm73_reg hW (by norm_num)
    · exact pm73_reg hW (by norm_num)
  · rw [hl] at hl'
    exact hH.z1 _ (by interval_cases l <;> simp)

theorem zTree2_73 : ∃ z : ℕ → NativeSporadic.Co1, (∀ i < 96, z i ∈ H ⊓
    Subgroup.centralizer {reg 27} ⊓ Subgroup.centralizer {reg (getL 0 J73 2)} ∧
      PM73 (z i) (Z2P.getD i 0)) ∧ ∀ i < 96, ∀ j < 96, z i = z j → i = j := by
  have hl : Z2G.length = 2 := by rw [hW.z2G]; rfl
  refine tree73 hW.z2 hW.z2d hW.z2c (fun l => reg (83 + l)) (fun l hl' => ?_) _ (fun l hl' => ?_)
  · rw [hl] at hl'
    rw [hW.z2G]
    interval_cases l
    · exact pm73_reg hW (by norm_num)
    · exact pm73_reg hW (by norm_num)
  · rw [hl] at hl'
    exact hH.z2 _ (by interval_cases l <;> simp)

omit hW hH in
theorem finite73 : Finite NativeSporadic.Co1 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)

theorem card_CH_ge73 : 2752512 ≤ Nat.card ↥(H ⊓ Subgroup.centralizer {reg 27}) := by
  have := finite73
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  obtain ⟨z, hz, hzinj⟩ := zTree0_73 hW hH
  have hI : {i | i < nS ∧ clsA (W.aux i) = 0 + 2}.ncard = 7168 := cnt73 hW (by norm_num)
  have key := card_ge_conj73 (H ⊓ Subgroup.centralizer {reg 27}) (reg (getL 0 J73 0))
    {i | i < nS ∧ clsA (W.aux i) = 0 + 2} 384 x z
    (fun i ⟨hi, hc⟩ => by
      rcases (hx i hi).2 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, h, g, hg, e⟩ | ⟨h, -⟩
      · omega
      · omega
      · obtain rfl : k = 0 := by omega
        exact ⟨g, hg, e⟩
      · omega)
    (fun i hi j hj e => hinj i hi.1 j hj.1 e) (fun j hj => (hz j hj).1) hzinj
  rw [hI] at key
  omega

omit hH in
theorem cntR73 : {i | i < nS ∧ clsA (W.aux i) ≠ 5}.ncard = 182160 := by
  have e2 := cnt73 hW (c := 3) (by norm_num)
  have e3 : {i | i < nS ∧ clsA (W.aux i) = 3 + 2} =
      ↑((Finset.range nS).filter (fun j => clsA (W.aux j) = 5)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  have e1 : {i | i < nS ∧ clsA (W.aux i) ≠ 5} =
      ↑((Finset.range nS).filter (fun j => ¬ clsA (W.aux j) = 5)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range, ne_eq]
  have e4 : getL 0 [7168, 2048, 28672, 759] 3 = 759 := rfl
  rw [e3, Set.ncard_coe_finset, e4] at e2
  rw [e1, Set.ncard_coe_finset]
  have := Finset.card_filter_add_card_filter_not (s := Finset.range nS)
    (p := fun j => clsA (W.aux j) = 5)
  rw [Finset.card_range] at this
  have hn : nS = 182919 := rfl
  omega

@[expose] def Cl73 (H : Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1 :=
  {y | ∃ n ∈ H, y = n * reg 27 * n⁻¹}

@[expose] def S73 (H : Subgroup NativeSporadic.Co1) : Set NativeSporadic.Co1 :=
  {t | t ∈ H ∧ IsConj (reg 27) t}

section Count

variable (hHc : Nat.card H = 501397585920)
include hHc

theorem cl73_eq {x : ℕ → NativeSporadic.Co1}
    (hx : ∀ i < nS, PM73 (x i) (val73 W i) ∧ Sem73 H (clsA (W.aux i)) (x i))
    (hinj : ∀ i < nS, ∀ j < nS, x i = x j → i = j) :
    x '' {i | i < nS ∧ clsA (W.aux i) ≠ 5} = Cl73 H ∧
      Nat.card ↥(H ⊓ Subgroup.centralizer {reg 27}) = 2752512 := by
  have := finite73
  have h := card_conj73 H (reg 27)
  have h2 := card_CH_ge73 hW hH
  rw [hHc] at h
  change Nat.card ↥(H ⊓ Subgroup.centralizer {reg 27}) * (Cl73 H).ncard = 501397585920 at h
  have hle : (Cl73 H).ncard ≤ 182160 := by
    by_contra hc
    have hc' : 182161 ≤ (Cl73 H).ncard := Nat.lt_of_not_le hc
    have := Nat.mul_le_mul h2 hc'
    omega
  have heq := eq_image_of_card73 (A := Cl73 H) (x := x) (I := {i | i < nS ∧ clsA (W.aux i) ≠ 5})
    (fun i hi => sem73_conj hH (hx i hi.1).2 hi.2) (fun i hi j hj e => hinj i hi.1 j hj.1 e)
    (by rw [cntR73 hW]; exact hle)
  refine ⟨heq, ?_⟩
  have hc : (Cl73 H).ncard = 182160 := by
    rw [← heq, Set.InjOn.ncard_image (fun i hi j hj e => hinj i hi.1 j hj.1 e), cntR73 hW]
  rw [hc] at h
  omega

omit hH hHc in
theorem t1rec73 {x : ℕ → NativeSporadic.Co1}
    (hx : ∀ i < nS, PM73 (x i) (val73 W i) ∧ Sem73 H (clsA (W.aux i)) (x i)) :
    W.t1i < nS ∧ x W.t1i = reg 86 ∧ clsA (W.aux W.t1i) = 5 := by
  have h := hW.t1
  rw [andB73, andB73] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlt : W.t1i < nS := blt_iff.1 h1
  have hv : val73 W W.t1i = W.reg 86 := beq_iff.1 h2
  refine ⟨hlt, ?_, beq_iff.1 h3⟩
  have hp := (hx _ hlt).1
  rw [hv] at hp
  exact pm73_inj hp (pm73_reg hW (by norm_num))

omit hW hHc in
theorem s73_sub {x : ℕ → NativeSporadic.Co1}
    (hx : ∀ i < nS, PM73 (x i) (val73 W i) ∧ Sem73 H (clsA (W.aux i)) (x i)) :
    ∀ i ∈ Set.Iio nS, x i ∈ S73 H := by
  intro i hi
  by_cases h5 : clsA (W.aux i) = 5
  · have hs := (hx i hi).2
    rw [h5] at hs
    rcases hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, h, -⟩ | ⟨-, ⟨n, hn, e⟩, -⟩
    · omega
    · omega
    · omega
    · refine ⟨?_, hH.t₁_conj.trans (isConj_iff.2 ⟨n, e.symm⟩)⟩
      rw [e]
      exact H.mul_mem (H.mul_mem hn hH.t₁_mem) (H.inv_mem hn)
  · obtain ⟨n, hn, e⟩ := sem73_conj hH (hx i hi).2 h5
    refine ⟨?_, isConj_iff.2 ⟨n, e.symm⟩⟩
    rw [e]
    exact H.mul_mem (H.mul_mem hn hH.ρ_mem) (H.inv_mem hn)

variable (hS : (S73 H).ncard = 182919)
include hS

omit hW hHc in
theorem s73_eq {x : ℕ → NativeSporadic.Co1}
    (hx : ∀ i < nS, PM73 (x i) (val73 W i) ∧ Sem73 H (clsA (W.aux i)) (x i))
    (hinj : ∀ i < nS, ∀ j < nS, x i = x j → i = j) : x '' Set.Iio nS = S73 H := by
  have := finite73
  exact eq_image_of_card73 (s73_sub hH hx) (fun i hi j hj e => hinj i hi j hj e)
    (by rw [hS, Set.ncard_Iio_nat]; rfl)

omit hS in
theorem t1_not73 {x : ℕ → NativeSporadic.Co1}
    (hx : ∀ i < nS, PM73 (x i) (val73 W i) ∧ Sem73 H (clsA (W.aux i)) (x i))
    (hinj : ∀ i < nS, ∀ j < nS, x i = x j → i = j) : reg 86 ∉ Cl73 H := by
  intro h
  rw [← (cl73_eq hW hH hHc hx hinj).1] at h
  obtain ⟨j, ⟨hj, h5⟩, e⟩ := h
  obtain ⟨ht, hxt, hc⟩ := t1rec73 hW hx
  have := hinj j hj _ ht (e.trans hxt.symm)
  rw [this] at h5
  exact h5 hc

omit hHc in
theorem S_cover73 : ∀ t ∈ S73 H, ∃ n ∈ H, t = n * reg 86 * n⁻¹ ∨ t = n * reg 27 * n⁻¹ := by
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  intro t ht
  rw [← s73_eq hH hS hx hinj] at ht
  obtain ⟨i, hi, rfl⟩ := ht
  by_cases h5 : clsA (W.aux i) = 5
  · have hs := (hx i hi).2
    rw [h5] at hs
    rcases hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, h, -⟩ | ⟨-, ⟨n, hn, e⟩, -⟩
    · omega
    · omega
    · omega
    · exact ⟨n, hn, Or.inl e⟩
  · obtain ⟨n, hn, e⟩ := sem73_conj hH (hx i hi).2 h5
    exact ⟨n, hn, Or.inr e⟩

theorem scan73 : ∀ t ∈ S73 H, t ≠ reg 86 → ¬ Odd (orderOf (reg 86 * t)) := by
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  intro t ht hne hodd
  have ht1 : reg 86 * reg 86 = 1 :=
    @sq_of_conj73 NativeSporadic.Co1 _ (reg 27) (reg 86) hH.ρ_sq hH.t₁_conj
  have htt : t * t = 1 := @sq_of_conj73 NativeSporadic.Co1 _ (reg 27) t hH.ρ_sq ht.2
  obtain ⟨w, hw, e⟩ :=
    @conj_in_of_odd73 NativeSporadic.Co1 _ H (reg 86) t hH.t₁_mem ht.1 ht1 htt hodd
  have ht' := ht
  rw [← s73_eq hH hS hx hinj] at ht'
  obtain ⟨i, hi, rfl⟩ := ht'
  by_cases h5 : clsA (W.aux i) = 5
  · have hs := (hx i hi).2
    rw [h5] at hs
    rcases hs with ⟨h, -⟩ | ⟨h, -⟩ | ⟨k, hk, h, -⟩ | ⟨-, -, hc⟩
    · omega
    · omega
    · omega
    · have hsq : (reg 86 * x i) ^ 2 = 1 := by
        rw [pow_two]
        calc reg 86 * x i * (reg 86 * x i) = reg 86 * (x i * reg 86) * x i := by group
          _ = reg 86 * (reg 86 * x i) * x i := by rw [hc]
          _ = (reg 86 * reg 86) * (x i * x i) := by group
          _ = 1 := by rw [ht1, htt, one_mul]
      have hd : orderOf (reg 86 * x i) ∣ 2 :=
        @orderOf_dvd_of_pow_eq_one NativeSporadic.Co1 _ (reg 86 * x i) 2 hsq
      obtain ⟨m, hm⟩ := hodd
      have hle := Nat.le_of_dvd (by norm_num) hd
      have h1 : orderOf (reg 86 * x i) = 1 := by omega
      have h1' : reg 86 * x i = 1 :=
        (@orderOf_eq_one_iff NativeSporadic.Co1 _ (reg 86 * x i)).1 h1
      apply hne
      calc x i = reg 86 * (reg 86 * x i) := by rw [← mul_assoc, ht1, one_mul]
        _ = reg 86 := by rw [h1', mul_one]
  · obtain ⟨n, hn, e'⟩ := sem73_conj hH (hx i hi).2 h5
    apply t1_not73 hW hH hHc hx hinj
    refine ⟨w⁻¹ * n, H.mul_mem (H.inv_mem hw) hn, ?_⟩
    calc reg 86 = w⁻¹ * (w * reg 86 * w⁻¹) * w := by group
      _ = w⁻¹ * (n * reg 27 * n⁻¹) * w := by rw [← e, e']
      _ = w⁻¹ * n * reg 27 * (w⁻¹ * n)⁻¹ := by group

omit hS in
theorem partner73 : ∀ t ∈ S73 H, t ≠ reg 27 → Odd (orderOf (reg 27 * t)) →
    ∃ k < 3, ∃ c ∈ H ⊓ Subgroup.centralizer {reg 27}, t = c * reg (getL 0 J73 k) * c⁻¹ := by
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  intro t ht hne hodd
  have htt : t * t = 1 := @sq_of_conj73 NativeSporadic.Co1 _ (reg 27) t hH.ρ_sq ht.2
  obtain ⟨w, hw, e⟩ :=
    @conj_in_of_odd73 NativeSporadic.Co1 _ H (reg 27) t hH.ρ_mem ht.1 hH.ρ_sq htt hodd
  have hcl : t ∈ Cl73 H := ⟨w, hw, e⟩
  rw [← (cl73_eq hW hH hHc hx hinj).1] at hcl
  obtain ⟨i, ⟨hi, h5⟩, rfl⟩ := hcl
  rcases (hx i hi).2 with ⟨-, -, hev⟩ | ⟨-, h⟩ | ⟨k, hk, -, c, hc, e⟩ | ⟨h, -⟩
  · exact absurd hodd hev
  · exact absurd h hne
  · exact ⟨k, hk, c, hc, e⟩
  · exact absurd h h5

omit hS in
theorem Z_le73 {k : ℕ} (hk : k < 3) :
    Nat.card ↥(H ⊓ Subgroup.centralizer {reg 27} ⊓ Subgroup.centralizer {reg (getL 0 J73 k)}) *
      getL 0 [7168, 2048, 28672, 759] k ≤ 2752512 := by
  have := finite73
  obtain ⟨x, hx, hinj⟩ := recs73 hW hH
  have hC := (cl73_eq hW hH hHc hx hinj).2
  have h := card_conj73 (H ⊓ Subgroup.centralizer {reg 27}) (reg (getL 0 J73 k))
  rw [hC] at h
  have hI := cnt73 hW (c := k) (by omega)
  have hsub : ∀ i ∈ {i | i < nS ∧ clsA (W.aux i) = k + 2}, x i ∈
      {y | ∃ n ∈ H ⊓ Subgroup.centralizer {reg 27}, y = n * reg (getL 0 J73 k) * n⁻¹} := by
    rintro i ⟨hi, hc⟩
    rcases (hx i hi).2 with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨k', hk', hc', c, hcm, e⟩ | ⟨h5, -⟩
    · omega
    · omega
    · obtain rfl : k' = k := by omega
      exact ⟨c, hcm, e⟩
    · omega
  have hle := Set.ncard_le_ncard_of_injOn x hsub (fun i hi j hj e => hinj i hi.1 j hj.1 e)
    (Set.toFinite _)
  rw [hI] at hle
  calc Nat.card ↥(H ⊓ Subgroup.centralizer {reg 27} ⊓ Subgroup.centralizer {reg (getL 0 J73 k)}) *
        getL 0 [7168, 2048, 28672, 759] k ≤ Nat.card ↥(H ⊓ Subgroup.centralizer {reg 27} ⊓
          Subgroup.centralizer {reg (getL 0 J73 k)}) *
        {y | ∃ n ∈ H ⊓ Subgroup.centralizer {reg 27}, y = n * reg (getL 0 J73 k) * n⁻¹}.ncard :=
        Nat.mul_le_mul_left _ hle
    _ = 2752512 := h

end Count

omit hH in
theorem faith73 {r : ℕ} (hr : r < 94) {P V : List ℕ}
    (hf : faithK (trK 24 (W.reg 27)) (trK 24 (W.reg r)) P V = true)
    {z : NativeSporadic.Co1} {i : ℕ} (hi : i < P.length) (hz : PM73 z (P.getD i 0))
    (hfix : ∀ v : Vec24, co1Act (reg 27) v = v → co1Act (reg r) v = v → co1Act z v = v) :
    z = 1 := by
  unfold faithK at hf
  rw [andB73] at hf
  have h := allN73.1 hf.2 i (by rw [lenL73]; exact hi)
  rw [orB73] at h
  rw [getL73] at h
  rcases h with h | h
  · rw [beq_iff.1 h] at hz
    exact pm73_inj hz pm73_one
  · simp only [andB73, notB73, blt_iff, beq_iff] at h
    obtain ⟨hv, h1, h2, h3⟩ := h
    set v := getL 0 V i
    have hv' : v < 2 ^ 24 := by
      have e : CFSG.KLie.CT.pw2 24 = 2 ^ 24 := Nat.one_shiftLeft 24
      rw [← e]
      exact hv
    exfalso
    have e1 : co1Act (reg 27) (toVecD 24 v) = toVecD 24 v := by
      rw [pm73_act (pm73_reg hW (by norm_num)), h1]
    have e2 : co1Act (reg r) (toVecD 24 v) = toVecD 24 v := by
      rw [pm73_act (pm73_reg hW hr), h2]
    have e3 := hfix _ e1 e2
    rw [pm73_act hz] at e3
    have h4 := beq_iff.2 (toVecD_injective (CFSG.KC.F2W.vmF_lt 24 _ v) hv' e3)
    rw [h3] at h4
    exact Bool.false_ne_true h4

end Main

end CFSG.Sporadic.Co1.Module.Odd

end
