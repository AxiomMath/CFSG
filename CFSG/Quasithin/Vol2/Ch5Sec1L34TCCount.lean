module

public import CFSG.Quasithin.Background.FixVZPowersMem
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.TorusComm

open CFSG.Quasithin

variable {W : Type*} [CommGroup W]

@[expose] def tr3 (g : MulAut W) : W →* W where
  toFun w := w * g w * g (g w)
  map_one' := by simp only [map_one, mul_one]
  map_mul' a b := by
    simp only [map_mul]
    ac_rfl

theorem tr3_apply (g : MulAut W) (w : W) : tr3 g w = w * g w * g (g w) := rfl

@[expose] def cm (g : MulAut W) : W →* W where
  toFun w := g w * w⁻¹
  map_one' := by simp only [map_one, inv_one, mul_one]
  map_mul' a b := by
    simp only [map_mul, mul_inv]
    ac_rfl

theorem cm_apply (g : MulAut W) (w : W) : cm g w = g w * w⁻¹ := rfl

theorem cm_eq_one_iff {g : MulAut W} {w : W} : cm g w = 1 ↔ g w = w := by
  rw [cm_apply, mul_inv_eq_one]

theorem mem_fixV_zpowers {g : MulAut W} {w : W} : w ∈ fixV (Subgroup.zpowers g) ↔ g w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem ker_cm (g : MulAut W) : (cm g).ker = fixV (Subgroup.zpowers g) := by
  ext w
  rw [MonoidHom.mem_ker, cm_eq_one_iff, mem_fixV_zpowers]

theorem index_fixV_eq (g : MulAut W) :
    (fixV (Subgroup.zpowers g)).index = Nat.card (cm g).range := by
  rw [← ker_cm, Subgroup.index_ker]

theorem apply_apply_of_comm {g h : MulAut W} (hgh : g * h = h * g) (w : W) :
    g (h w) = h (g w) := by
  show (g * h) w = (h * g) w
  rw [hgh]

theorem apply_three {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : g (g (g w)) = w := by
  have h := congrArg (fun f : MulAut W => f w) hg
  simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h

theorem apply_tr3 {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : g (tr3 g w) = tr3 g w := by
  simp only [tr3_apply, map_mul, apply_three hg]
  ac_rfl

theorem tr3_of_apply (h2 : ∀ w : W, w ^ 2 = 1) {g : MulAut W} {w : W} (hw : g w = w) :
    tr3 g w = w := by
  rw [tr3_apply, hw, hw, ← sq, h2, one_mul]

theorem apply_tr3_of_comm {g h : MulAut W} (hgh : g * h = h * g) (w : W) :
    h (tr3 g w) = tr3 g (h w) := by
  simp only [tr3_apply, map_mul, apply_apply_of_comm hgh.symm]

theorem tr3_apply_self {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : tr3 g (g w) = tr3 g w := by
  rw [← apply_tr3_of_comm rfl, apply_tr3 hg]

theorem tr3_cm {g : MulAut W} (hg : g ^ 3 = 1) (w : W) : tr3 g (cm g w) = 1 := by
  rw [cm_apply, map_mul, map_inv, tr3_apply_self hg, mul_inv_cancel]

theorem tr3_comm {g h : MulAut W} (hgh : g * h = h * g) (w : W) :
    tr3 g (tr3 h w) = tr3 h (tr3 g w) := by
  rw [tr3_apply h w, map_mul, map_mul, ← apply_tr3_of_comm hgh, ← apply_tr3_of_comm hgh,
    ← apply_tr3_of_comm hgh, tr3_apply h]

theorem pow_eq_one_of_dvd {p m : ℕ} (h : p ∣ 2 ^ m - 1) : (2 : ZMod p) ^ m = 1 := by
  have h1 := (ZMod.natCast_eq_zero_iff (2 ^ m - 1) p).mpr h
  rwa [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero] at h1

theorem six_le_of_dvd {p n k : ℕ} (hp : p.Prime) (hn : Odd n) (hpn : p ∣ 2 ^ n - 1)
    (hk : k ≠ 0) (h3 : 3 ∣ 2 ^ k - 1) (hpk : p ∣ 2 ^ k - 1) : 6 ≤ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hrn := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_dvd hpn)
  have hrk := orderOf_dvd_of_pow_eq_one (pow_eq_one_of_dvd hpk)
  have hr1 : orderOf (2 : ZMod p) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    intro h
    have h1 : (1 : ZMod p) = 0 := by linear_combination h
    exact one_ne_zero h1
  have hodd : Odd (orderOf (2 : ZMod p)) := hn.of_dvd_nat hrn
  have h2k : 2 ∣ k := by
    have ho : orderOf (2 : ZMod 3) = 2 := orderOf_eq_prime (by decide) (by decide)
    rw [← ho]
    exact orderOf_dvd_of_pow_eq_one (pow_eq_one_of_dvd h3)
  have hdvd : 2 * orderOf (2 : ZMod p) ∣ k :=
    (Nat.coprime_two_left.mpr hodd).mul_dvd_of_dvd_of_dvd h2k hrk
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdvd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem pow_apply_mem {g : MulAut W} {Z : Subgroup W} (hZ : ∀ z ∈ Z, g z ∈ Z) (m : ℕ) {z : W}
    (hz : z ∈ Z) : (g ^ m) z ∈ Z := by
  induction m with
  | zero => simpa using hz
  | succ m ih => rw [pow_succ', MulAut.mul_apply]; exact hZ _ ih

@[expose] def restr (g : MulAut W) {Z : Subgroup W} (hZ : ∀ z ∈ Z, g z ∈ Z) :
    Function.End ↥Z :=
  fun z => ⟨g z, hZ z z.2⟩

theorem coe_restr_pow (g : MulAut W) {Z : Subgroup W} (hZ : ∀ z ∈ Z, g z ∈ Z) (m : ℕ)
    (z : ↥Z) : (((restr g hZ) ^ m) z : W) = (g ^ m) z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, ← ih]
    rfl

@[expose] noncomputable def restrPerm [Finite W] (g : MulAut W) {Z : Subgroup W}
    (hZ : ∀ z ∈ Z, g z ∈ Z) : Equiv.Perm ↥Z :=
  Equiv.ofBijective (restr g hZ) (Finite.injective_iff_bijective.mp fun _ _ h =>
    Subtype.ext (g.injective (congrArg Subtype.val h)))

theorem coe_restrPerm_pow [Finite W] (g : MulAut W) {Z : Subgroup W} (hZ : ∀ z ∈ Z, g z ∈ Z)
    (m : ℕ) (z : ↥Z) : (((restrPerm g hZ) ^ m) z : W) = (g ^ m) z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, Equiv.Perm.mul_apply, ← ih]
    rfl

theorem card_fixedPoints_eq_one (g : MulAut W) {Z : Subgroup W} (hg : ∀ u ∈ Z, g u ∈ Z)
    (hgf : ∀ u ∈ Z, g u = u → u = 1) :
    Nat.card (Function.fixedPoints (restr g hg)) = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨1, Subtype.ext (map_one g)⟩, ?_⟩
  rintro ⟨u, hu⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hgf u u.2 (congrArg Subtype.val hu)

theorem two_pow_six_le_card [Finite W] (h2 : ∀ w : W, w ^ 2 = 1) {y d : MulAut W}
    (hy3 : y ^ 3 = 1) (hyd : y * d = d * y) {n : ℕ} (hn : Odd n) (hd : d ^ (2 ^ n - 1) = 1)
    {Z : Subgroup W} (hZy : ∀ z ∈ Z, y z ∈ Z) (hZd : ∀ z ∈ Z, d z ∈ Z)
    (hfy : ∀ z ∈ Z, y z = z → z = 1) (hfd : ∀ z ∈ Z, d z = z → z = 1) (hZ : Z ≠ ⊥) :
    2 ^ 6 ≤ Nat.card Z := by
  classical
  have := Fintype.ofFinite W
  set δ := restrPerm d hZd with hδ
  have hN0 : orderOf δ ≠ 0 := (orderOf_pos δ).ne'
  have hNd : orderOf δ ∣ 2 ^ n - 1 := by
    refine orderOf_dvd_of_pow_eq_one (Equiv.ext fun z => Subtype.ext ?_)
    rw [coe_restrPerm_pow, hd]
    rfl
  have hN1 : orderOf δ ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    intro h1
    apply hZ
    rw [eq_bot_iff]
    intro z hz
    have h := congrArg (fun f : Equiv.Perm ↥Z => (f ⟨z, hz⟩ : W)) h1
    exact hfd z hz h
  obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN1
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (2 ^ n - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hn.pos.ne'⟩) odd_one
  have hpn : p ∣ 2 ^ n - 1 := hpN.trans hNd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpn)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set f := d ^ (orderOf δ / p) with hf
  have hε : orderOf (δ ^ (orderOf δ / p)) = p := orderOf_pow_orderOf_div hN0 hpN
  have hfZ : ∀ z ∈ Z, f z ∈ Z := fun z hz => pow_apply_mem hZd _ hz
  have hfp : ∀ z ∈ Z, (f ^ p) z = z := by
    intro z hz
    have h := congrArg (fun g : Equiv.Perm ↥Z => (g ⟨z, hz⟩ : W))
      (pow_orderOf_eq_one (δ ^ (orderOf δ / p)))
    rw [hε, ← pow_mul, hδ, coe_restrPerm_pow, pow_mul] at h
    exact h
  have hf1 : ∃ z ∈ Z, f z ≠ z := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have h1 : δ ^ (orderOf δ / p) = 1 := Equiv.ext fun z => Subtype.ext (by
      rw [coe_restrPerm_pow]
      exact hcon z z.2)
    rw [h1, orderOf_one] at hε
    exact hp.one_lt.ne hε
  have hyf : y * f = f * y := (Commute.pow_right hyd (orderOf δ / p)).eq
  set Z₁ := Z.map (cm f) with hZ₁
  have hZ₁Z : ∀ u ∈ Z₁, u ∈ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact Z.mul_mem (hfZ z hz) (Z.inv_mem hz)
  have hZ₁f : ∀ u ∈ Z₁, f u ∈ Z₁ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨f z, hfZ z hz, ?_⟩
    rw [cm_apply, cm_apply, map_mul, map_inv]
  have hZ₁y : ∀ u ∈ Z₁, y u ∈ Z₁ := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨y z, hZy z hz, ?_⟩
    rw [cm_apply, cm_apply, map_mul, map_inv, apply_apply_of_comm hyf]
  have hfixf : ∀ u ∈ Z₁, f u = u → u = 1 := by
    rintro _ ⟨z, hz, rfl⟩ hu
    set u := cm f z with hu'
    have hfz : f z = u * z := by rw [hu', cm_apply, inv_mul_cancel_right]
    have hit : ∀ i : ℕ, (f ^ i) z = z * u ^ i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hu, hfz, pow_succ]
        ac_rfl
    have h1 := hit p
    rw [hfp z hz, left_eq_mul] at h1
    obtain ⟨m, hm⟩ := hpodd
    rw [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at h1
    exact h1
  have hZ₁ne : Z₁ ≠ ⊥ := by
    obtain ⟨z, hz, hfz⟩ := hf1
    intro hb
    have h1 : cm f z ∈ Z₁ := ⟨z, hz, rfl⟩
    rw [hb, Subgroup.mem_bot, cm_eq_one_iff] at h1
    exact hfz h1
  have hmodp : Nat.card ↥Z₁ ≡ 1 [MOD p] := by
    have h := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) (f := restr f hZ₁f)
      (funext fun u => Subtype.ext (by rw [pow_one, coe_restr_pow, hfp u (hZ₁Z u u.2)]; rfl))
    rwa [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      card_fixedPoints_eq_one f hZ₁f hfixf] at h
  have hmod3 : Nat.card ↥Z₁ ≡ 1 [MOD 3] := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) (f := restr y hZ₁y)
      (funext fun u => Subtype.ext (by rw [pow_one, coe_restr_pow, hy3]; rfl))
    rwa [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
      card_fixedPoints_eq_one y hZ₁y fun u hu => hfy u (hZ₁Z u hu)] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2Z₁ : IsPGroup 2 ↥Z₁ := fun u => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact h2 u)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2Z₁
  rw [hk] at hmodp hmod3
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hZ₁ne (Subgroup.eq_bot_of_card_eq _ hk)
  have h6 := six_le_of_dvd hp hn hpn hk0
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmod3.symm)
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hmodp.symm)
  calc 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h6
    _ = Nat.card Z₁ := hk.symm
    _ ≤ Nat.card Z := Subgroup.card_le_of_le fun u hu => hZ₁Z u hu

theorem mul_self_eq_one' (h2 : ∀ w : W, w ^ 2 = 1) (w : W) : w * w = 1 := by
  rw [← sq, h2]

theorem eq_of_mul_eq_one' (h2 : ∀ w : W, w ^ 2 = 1) {a b : W} (h : a * b = 1) : a = b := by
  have h1 := congrArg (· * b) h
  simp only [mul_assoc, mul_self_eq_one' h2, mul_one, one_mul] at h1
  exact h1

theorem eq_one_of_tr3 (h2 : ∀ w : W, w ^ 2 = 1) {y b : MulAut W} (hb3 : b ^ 3 = 1)
    (hyb : y * b = b * y) {u : W} (hy : tr3 y u = 1) (hb : tr3 b u = 1)
    (h3 : tr3 (y * b) u = 1) (h4 : tr3 (y * b * b) u = 1) : u = 1 := by
  have hs := mul_self_eq_one' h2
  have hyy : y (y u) = u * y u := by
    rw [tr3_apply] at hy
    exact (eq_of_mul_eq_one' h2 hy).symm
  have hbb : b (b u) = u * b u := by
    rw [tr3_apply] at hb
    exact (eq_of_mul_eq_one' h2 hb).symm
  have hyb' : ∀ v, b (y v) = y (b v) := apply_apply_of_comm hyb.symm
  have hyyb : y (y (b u)) = b u * y (b u) := by
    have h := apply_tr3_of_comm hyb u
    rw [hy, map_one, tr3_apply] at h
    exact (eq_of_mul_eq_one' h2 h.symm).symm
  have hbbb : b (b (b u)) = u := apply_three hb3 u
  have e3a : (y * b) u = y (b u) := rfl
  have e3b : (y * b) ((y * b) u) = u * y u * (b u * y (b u)) := by
    show y (b (y (b u))) = _
    rw [hyb', hbb, map_mul, map_mul, hyy, hyyb]
  have e3 : tr3 (y * b) u = y u * b u := by
    rw [tr3_apply, e3b, e3a]
    calc u * y (b u) * (u * y u * (b u * y (b u)))
        = (u * u) * (y (b u) * y (b u)) * (y u * b u) := by ac_rfl
      _ = y u * b u := by rw [hs, hs, one_mul, one_mul]
  have e4a : (y * b * b) u = y u * y (b u) := by
    show y (b (b u)) = _
    rw [hbb, map_mul]
  have e4b : (y * b * b) ((y * b * b) u) = b u * y (b u) := by
    show y (b (b (y (b (b u))))) = _
    rw [hyb', hyb', hbbb, hyyb]
  have e4 : tr3 (y * b * b) u = u * y u * b u := by
    rw [tr3_apply, e4b, e4a]
    calc u * (y u * y (b u)) * (b u * y (b u))
        = u * y u * b u * (y (b u) * y (b u)) := by ac_rfl
      _ = u * y u * b u := by rw [hs, mul_one]
  rw [e3] at h3
  rw [e4] at h4
  have hA : y u = b u := eq_of_mul_eq_one' h2 h3
  rw [hA, mul_assoc, hs, mul_one] at h4
  exact h4

@[expose] def ySub (y g : MulAut W) : Subgroup W := (fixV (Subgroup.zpowers g)).map (cm y)

theorem mem_ySub {y g : MulAut W} {u : W} : u ∈ ySub y g ↔ ∃ x, g x = x ∧ y x * x⁻¹ = u := by
  simp only [ySub, Subgroup.mem_map, mem_fixV_zpowers, cm_apply]

variable {y g : MulAut W}

theorem apply_of_mem_ySub (hyg : y * g = g * y) {u : W} (hu : u ∈ ySub y g) : g u = u := by
  obtain ⟨x, hx, rfl⟩ := mem_ySub.mp hu
  rw [map_mul, map_inv, apply_apply_of_comm hyg.symm, hx]

theorem tr3_of_mem_ySub (hy3 : y ^ 3 = 1) {u : W} (hu : u ∈ ySub y g) : tr3 y u = 1 := by
  obtain ⟨x, -, rfl⟩ := mem_ySub.mp hu
  exact tr3_cm hy3 x

theorem mem_ySub_of_comm {h : MulAut W} (hyh : y * h = h * y) (hgh : g * h = h * g) {u : W}
    (hu : u ∈ ySub y g) : h u ∈ ySub y g := by
  obtain ⟨x, hx, rfl⟩ := mem_ySub.mp hu
  refine mem_ySub.mpr ⟨h x, by rw [apply_apply_of_comm hgh, hx], ?_⟩
  rw [map_mul, map_inv, apply_apply_of_comm hyh]

theorem eq_one_of_mem_ySub (h2 : ∀ w : W, w ^ 2 = 1) (hy3 : y ^ 3 = 1) {u : W}
    (hu : u ∈ ySub y g) (hyu : y u = u) : u = 1 := by
  rw [← tr3_of_mem_ySub hy3 hu, tr3_of_apply h2 hyu]

theorem tr3_eq_one_of_mem_ySub (h2 : ∀ w : W, w ^ 2 = 1) (hy3 : y ^ 3 = 1) {g' : MulAut W}
    (hg3 : g ^ 3 = 1) (hyg : y * g = g * y) (hyg' : y * g' = g' * y) (hgg' : g * g' = g' * g)
    (hfix : ∀ w : W, g w = w → g' w = w → y w = w) {u : W} (hu : u ∈ ySub y g') :
    tr3 g u = 1 := by
  have h1 : g (tr3 g u) = tr3 g u := apply_tr3 hg3 u
  have h2' : g' (tr3 g u) = tr3 g u := by
    rw [apply_tr3_of_comm hgg', apply_of_mem_ySub hyg' hu]
  have h3 := hfix _ h1 h2'
  have h4 : tr3 y (tr3 g u) = 1 := by
    rw [tr3_comm hyg, tr3_of_mem_ySub hy3 hu, map_one]
  rwa [tr3_of_apply h2 h3] at h4

theorem two_pow_eighteen_le_index [Finite W] (h2 : ∀ w : W, w ^ 2 = 1) {b d : MulAut W}
    (hy3 : y ^ 3 = 1) (hb3 : b ^ 3 = 1) (hyb : y * b = b * y) (hyd : y * d = d * y)
    (hbd : b * d = d * b) {n : ℕ} (hn : Odd n) (hd : d ^ (2 ^ n - 1) = 1)
    (hfd : ∀ w : W, d w = w → w = 1) (hy1 : y ≠ 1)
    (hc2 : Nat.card (fixV (Subgroup.zpowers b)) = Nat.card (fixV (Subgroup.zpowers y)))
    (hc3 : Nat.card (fixV (Subgroup.zpowers (y * b))) = Nat.card (fixV (Subgroup.zpowers y)))
    (hc4 : Nat.card (fixV (Subgroup.zpowers (y * b * b))) =
      Nat.card (fixV (Subgroup.zpowers y))) :
    2 ^ 18 ≤ (fixV (Subgroup.zpowers y)).index := by
  classical
  have hcy : Commute y b := hyb
  have hcyd : Commute y d := hyd
  have hcbd : Commute b d := hbd
  have hc3' : Commute (y * b) b := hcy.mul_left (Commute.refl b)
  have h33 : (y * b) ^ 3 = 1 := by rw [hcy.mul_pow, hy3, hb3, one_mul]
  have h43 : (y * b * b) ^ 3 = 1 := by rw [hc3'.mul_pow, h33, hb3, one_mul]
  have cy3 : Commute y (y * b) := (Commute.refl y).mul_right hcy
  have cy4 : Commute y (y * b * b) := cy3.mul_right hcy
  have cb3 : Commute b (y * b) := hcy.symm.mul_right (Commute.refl b)
  have cb4 : Commute b (y * b * b) := cb3.mul_right (Commute.refl b)
  have c34 : Commute (y * b) (y * b * b) := (Commute.refl (y * b)).mul_right hc3'
  have cd3 : Commute (y * b) d := hcyd.mul_left hcbd
  have cd4 : Commute (y * b * b) d := cd3.mul_left hcbd
  have ap3 : ∀ w, (y * b) w = y (b w) := fun w => rfl
  have ap4 : ∀ w, (y * b * b) w = y (b (b w)) := fun w => rfl
  have P1 : ∀ w : W, b w = w → (y * b) w = w → y w = w := by
    intro w h1 h2'
    rwa [ap3, h1] at h2'
  have P2 : ∀ w : W, b w = w → (y * b * b) w = w → y w = w := by
    intro w h1 h2'
    rwa [ap4, h1, h1] at h2'
  have P3 : ∀ w : W, (y * b) w = w → (y * b * b) w = w → y w = w := by
    intro w h1 h2'
    have hb : b w = w := by
      have : (y * b) (b w) = (y * b) w := by rw [h1]; exact h2'
      exact (y * b).injective this
    exact P1 w hb h1
  have key : ∀ g : MulAut W,
      (∀ w : W, y w = w → g w = w → b w = w ∧ (y * b) w = w ∧ (y * b * b) w = w) →
      Nat.card (fixV (Subgroup.zpowers g)) = Nat.card (fixV (Subgroup.zpowers y)) →
      ySub y g ≠ ⊥ := by
    intro g hF hcg hbot
    have hgy : ∀ w : W, g w = w → y w = w := by
      intro w hw
      have h1 : cm y w ∈ ySub y g := Subgroup.mem_map_of_mem _ (mem_fixV_zpowers.mpr hw)
      rw [hbot, Subgroup.mem_bot, cm_eq_one_iff] at h1
      exact h1
    have hrev : ∀ x : MulAut W, (∀ w : W, g w = w → x w = w) →
        Nat.card (fixV (Subgroup.zpowers x)) = Nat.card (fixV (Subgroup.zpowers y)) →
        ∀ w : W, x w = w → y w = w := by
      intro x hx hcx w hw
      have hle : fixV (Subgroup.zpowers g) ≤ fixV (Subgroup.zpowers x) := fun v hv =>
        mem_fixV_zpowers.mpr (hx v (mem_fixV_zpowers.mp hv))
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcx, hcg])
      have hw' : w ∈ fixV (Subgroup.zpowers g) := by
        rw [heq]
        exact mem_fixV_zpowers.mpr hw
      exact hgy w (mem_fixV_zpowers.mp hw')
    have hb' := hrev b (fun w hw => (hF w (hgy w hw) hw).1) hc2
    have h3' := hrev (y * b) (fun w hw => (hF w (hgy w hw) hw).2.1) hc3
    have h4' := hrev (y * b * b) (fun w hw => (hF w (hgy w hw) hw).2.2) hc4
    apply hy1
    refine MulEquiv.ext fun w => ?_
    rw [MulAut.one_apply, ← cm_eq_one_iff]
    have hu := tr3_cm hy3 w
    have hk : ∀ x : MulAut W, x ^ 3 = 1 → y * x = x * y → (∀ v : W, x v = v → y v = v) →
        tr3 x (cm y w) = 1 := by
      intro x hx3 hyx hxy
      have h1 := hxy _ (apply_tr3 hx3 (cm y w))
      have h2' : tr3 y (tr3 x (cm y w)) = 1 := by rw [tr3_comm hyx, hu, map_one]
      rwa [tr3_of_apply h2 h1] at h2'
    exact eq_one_of_tr3 h2 hb3 hyb hu (hk b hb3 hyb hb') (hk _ h33 cy3 h3') (hk _ h43 cy4 h4')
  have hne2 : ySub y b ≠ ⊥ := key b (fun w hy hb => by
    refine ⟨hb, ?_, ?_⟩
    · rw [ap3, hb, hy]
    · rw [ap4, hb, hb, hy]) hc2
  have hne3 : ySub y (y * b) ≠ ⊥ := key (y * b) (fun w hy h3 => by
    have hb : b w = w := by
      rw [ap3] at h3
      exact y.injective (h3.trans hy.symm)
    refine ⟨hb, h3, ?_⟩
    rw [ap4, hb, hb, hy]) hc3
  have hne4 : ySub y (y * b * b) ≠ ⊥ := key (y * b * b) (fun w hy h4 => by
    have hbb : b (b w) = w := by
      rw [ap4] at h4
      exact y.injective (h4.trans hy.symm)
    have hb : b w = w := by
      have := congrArg b hbb
      rw [apply_three hb3] at this
      exact this.symm
    refine ⟨hb, ?_, h4⟩
    rw [ap3, hb, hy]) hc4
  have hbig : ∀ g : MulAut W, Commute y g → Commute g d → ySub y g ≠ ⊥ →
      2 ^ 6 ≤ Nat.card (ySub y g) := by
    intro g hyg hgd hne
    exact two_pow_six_le_card h2 hy3 hyd hn hd
      (fun z hz => mem_ySub_of_comm rfl hyg.symm hz) (fun z hz => mem_ySub_of_comm hyd hgd hz)
      (fun z hz hyz => eq_one_of_mem_ySub h2 hy3 hz hyz) (fun z _ hdz => hfd z hdz) hne
  have hind : ∀ u₂ ∈ ySub y b, ∀ u₃ ∈ ySub y (y * b), ∀ u₄ ∈ ySub y (y * b * b),
      u₂ * u₃ * u₄ = 1 → u₂ = 1 ∧ u₃ = 1 := by
    intro u₂ h₂ u₃ h₃ u₄ h₄ h
    have e2 : tr3 b (u₂ * u₃ * u₄) = u₂ := by
      rw [map_mul, map_mul, tr3_of_apply h2 (apply_of_mem_ySub hyb h₂),
        tr3_eq_one_of_mem_ySub h2 hy3 hb3 hyb cy3 cb3 P1 h₃,
        tr3_eq_one_of_mem_ySub h2 hy3 hb3 hyb cy4 cb4 P2 h₄, mul_one, mul_one]
    have e3 : tr3 (y * b) (u₂ * u₃ * u₄) = u₃ := by
      rw [map_mul, map_mul, tr3_eq_one_of_mem_ySub h2 hy3 h33 cy3 hyb cb3.symm
          (fun w h1 h2' => P1 w h2' h1) h₂,
        tr3_of_apply h2 (apply_of_mem_ySub cy3 h₃),
        tr3_eq_one_of_mem_ySub h2 hy3 h33 cy3 cy4 c34 P3 h₄, one_mul, mul_one]
    rw [h, map_one] at e2 e3
    exact ⟨e2.symm, e3.symm⟩
  have hrange : ∀ g : MulAut W, ∀ u ∈ ySub y g, u ∈ (cm y).range := by
    intro g u hu
    obtain ⟨x, -, rfl⟩ := mem_ySub.mp hu
    exact ⟨x, rfl⟩
  let F : ↥(ySub y b) × ↥(ySub y (y * b)) × ↥(ySub y (y * b * b)) → ↥(cm y).range :=
    fun p => ⟨(p.1 : W) * p.2.1 * p.2.2, (cm y).range.mul_mem ((cm y).range.mul_mem
      (hrange _ _ p.1.2) (hrange _ _ p.2.1.2)) (hrange _ _ p.2.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨a₂, a₃, a₄⟩ ⟨c₂, c₃, c₄⟩ hac
    have h1 : (a₂ : W) * a₃ * a₄ = c₂ * c₃ * c₄ := congrArg Subtype.val hac
    have h0 : ((a₂ : W) * (c₂ : W)⁻¹) * ((a₃ : W) * (c₃ : W)⁻¹) *
        ((a₄ : W) * (c₄ : W)⁻¹) = 1 := by
      rw [show ((a₂ : W) * (c₂ : W)⁻¹) * ((a₃ : W) * (c₃ : W)⁻¹) * ((a₄ : W) * (c₄ : W)⁻¹) =
        ((a₂ : W) * a₃ * a₄) * ((c₂ : W) * c₃ * c₄)⁻¹ by
          simp only [mul_inv]
          ac_rfl, h1, mul_inv_cancel]
    obtain ⟨e2, e3⟩ := hind _ ((ySub y b).mul_mem a₂.2 ((ySub y b).inv_mem c₂.2)) _
      ((ySub y (y * b)).mul_mem a₃.2 ((ySub y (y * b)).inv_mem c₃.2)) _
      ((ySub y (y * b * b)).mul_mem a₄.2 ((ySub y (y * b * b)).inv_mem c₄.2)) h0
    rw [mul_inv_eq_one] at e2 e3
    have e4 : (a₄ : W) = c₄ := by
      rw [e2, e3] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext e2) (Prod.ext (Subtype.ext e3) (Subtype.ext e4))
  have hcard := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, Nat.card_prod] at hcard
  rw [index_fixV_eq]
  calc 2 ^ 18 = 2 ^ 6 * (2 ^ 6 * 2 ^ 6) := by norm_num
    _ ≤ Nat.card (ySub y b) * (Nat.card (ySub y (y * b)) * Nat.card (ySub y (y * b * b))) :=
      Nat.mul_le_mul (hbig b hcy hcbd hne2) (Nat.mul_le_mul (hbig _ cy3 cd3 hne3)
        (hbig _ cy4 cd4 hne4))
    _ ≤ Nat.card (cm y).range := hcard

end CFSG.Quasithin.H13.TorusComm
