module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CAZ1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

private def s168e3_cyc_pk (x : MulAut W) (k : ℕ) : W →* W :=
  (x ^ k).toMonoidHom

private lemma s168e3_cyc_pk_pow (x : MulAut W) (m n : ℕ) (w : W) :
    s168e3_cyc_pk x m (s168e3_cyc_pk x n w) = s168e3_cyc_pk x (m + n) w := by
  simp only [s168e3_cyc_pk, MulEquiv.coe_toMonoidHom, MulAut.mul_apply, pow_add]

private lemma s168e3_cyc_pk_zero (x : MulAut W) (w : W) :
    s168e3_cyc_pk x 0 w = w := by
  simp [s168e3_cyc_pk]

private lemma s168e3_cyc_pk_one (x : MulAut W) (w : W) :
    s168e3_cyc_pk x 1 w = x w := by
  simp [s168e3_cyc_pk]

private def s168e3_cyc_ph1 (x : MulAut W) : W →* W :=
  s168e3_cyc_pk x 3 * s168e3_cyc_pk x 1 * MonoidHom.id W

private def s168e3_cyc_ph2 (x : MulAut W) : W →* W :=
  s168e3_cyc_pk x 3 * s168e3_cyc_pk x 2 * MonoidHom.id W

private def s168e3_cyc_nrm (x : MulAut W) (w : W) : W :=
  s168e3_cyc_pk x 6 w * s168e3_cyc_pk x 5 w * s168e3_cyc_pk x 4 w *
    s168e3_cyc_pk x 3 w * s168e3_cyc_pk x 2 w * s168e3_cyc_pk x 1 w * s168e3_cyc_pk x 0 w

private lemma s168e3_cyc_sq_of (hW : ∀ w : W, w ^ 2 = 1) : ∀ a : W, a * a = 1 :=
  fun a => by simpa [pow_two] using hW a

private lemma s168e3_cyc_mmul (hsq : ∀ a : W, a * a = 1) (a b : W) :
    a * (a * b) = b := by
  rw [← mul_assoc, hsq, one_mul]

private lemma s168e3_cyc_ph1_ph2 (hW : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (w : W) :
    s168e3_cyc_ph1 x (s168e3_cyc_ph2 x w) = s168e3_cyc_nrm x w := by
  have hsq := s168e3_cyc_sq_of hW
  simp only [s168e3_cyc_ph1, s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply,
    map_mul, s168e3_cyc_pk_pow, s168e3_cyc_nrm]
  norm_num
  simp [s168e3_cyc_pk_zero, mul_assoc, mul_comm, mul_left_comm, hsq, s168e3_cyc_mmul hsq]

private lemma s168e3_cyc_ph2_ph1 (hW : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (w : W) :
    s168e3_cyc_ph2 x (s168e3_cyc_ph1 x w) = s168e3_cyc_nrm x w := by
  have hsq := s168e3_cyc_sq_of hW
  simp only [s168e3_cyc_ph1, s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply,
    map_mul, s168e3_cyc_pk_pow, s168e3_cyc_nrm]
  norm_num
  simp [s168e3_cyc_pk_zero, mul_assoc, mul_comm, mul_left_comm, hsq, s168e3_cyc_mmul hsq]

private lemma s168e3_cyc_ph_sum (hW : ∀ w : W, w ^ 2 = 1) (x : MulAut W) (w : W) :
    s168e3_cyc_ph2 x w * s168e3_cyc_pk x 1 (s168e3_cyc_ph2 x w) *
      s168e3_cyc_pk x 1 (s168e3_cyc_ph1 x w) = w := by
  have hsq := s168e3_cyc_sq_of hW
  simp only [s168e3_cyc_ph1, s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply,
    map_mul, s168e3_cyc_pk_pow]
  norm_num
  simp [s168e3_cyc_pk_zero, mul_assoc, mul_comm, mul_left_comm, hsq, s168e3_cyc_mmul hsq]

private lemma s168e3_cyc_nrm_pk_one {x : MulAut W} (hx7 : x ^ 7 = 1) (w : W) :
    s168e3_cyc_pk x 1 (s168e3_cyc_nrm x w) = s168e3_cyc_nrm x w := by
  have h70 : s168e3_cyc_pk x 7 w = s168e3_cyc_pk x 0 w := by
    simp only [s168e3_cyc_pk, hx7, pow_zero, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  simp only [s168e3_cyc_nrm, map_mul, s168e3_cyc_pk_pow]
  norm_num
  rw [h70]
  simp [mul_assoc, mul_comm, mul_left_comm]

private lemma s168e3_cyc_nrm_eq_one {x : MulAut W} (hx7 : x ^ 7 = 1)
    (hfpf : ∀ w : W, x w = w → w = 1) (w : W) : s168e3_cyc_nrm x w = 1 := by
  have h1 : s168e3_cyc_pk x 1 (s168e3_cyc_nrm x w) = s168e3_cyc_nrm x w :=
    s168e3_cyc_nrm_pk_one hx7 w
  exact hfpf _ (by simpa [s168e3_cyc_pk_one] using h1)

private lemma s168e3_cyc_conj_pow {x t : MulAut W} (hinv : t * x * t⁻¹ = x⁻¹) (k : ℕ) :
    t * x ^ k * t⁻¹ = (x ^ k)⁻¹ := by
  have h := map_pow (MulAut.conj t) x k
  rw [MulAut.conj_apply, MulAut.conj_apply, hinv] at h
  simpa [inv_pow] using h

private lemma s168e3_cyc_t_pk {x t : MulAut W} (hinv : t * x * t⁻¹ = x⁻¹) (k : ℕ) (w : W) :
    t (s168e3_cyc_pk x k w) = (x ^ k)⁻¹ (t w) := by
  have h := s168e3_cyc_conj_pow hinv k
  have hmul : t * x ^ k = (x ^ k)⁻¹ * t := by
    rw [← h, mul_assoc, inv_mul_cancel, mul_one]
  simp only [s168e3_cyc_pk, MulEquiv.coe_toMonoidHom]
  rw [← MulAut.mul_apply, hmul, MulAut.mul_apply]

private lemma s168e3_cyc_t_pk1 {x t : MulAut W} (hx7 : x ^ 7 = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) (w : W) :
    t (s168e3_cyc_pk x 1 w) = s168e3_cyc_pk x 6 (t w) := by
  have h16 : x⁻¹ = x ^ 6 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hx7)
  have h := s168e3_cyc_t_pk hinv 1 w
  simpa [s168e3_cyc_pk, pow_one, h16] using h

private lemma s168e3_cyc_t_pk3 {x t : MulAut W} (hx7 : x ^ 7 = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) (w : W) :
    t (s168e3_cyc_pk x 3 w) = s168e3_cyc_pk x 4 (t w) := by
  have h34 : (x ^ 3)⁻¹ = x ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add]; show x ^ 7 = 1; exact hx7)
  have h := s168e3_cyc_t_pk hinv 3 w
  simpa [s168e3_cyc_pk, h34] using h

private lemma s168e3_cyc_ph2_t {x t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hx7 : x ^ 7 = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) (w : W) :
    s168e3_cyc_ph2 x (t w) = s168e3_cyc_pk x 3 (t (s168e3_cyc_ph1 x w)) := by
  have h7 : s168e3_cyc_pk x 7 (t w) = t w := by
    simp only [s168e3_cyc_pk, hx7, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  have h9 : s168e3_cyc_pk x 9 (t w) = s168e3_cyc_pk x 2 (t w) := by
    have : x ^ 9 = x ^ 2 := by
      rw [show (9:ℕ) = 7 + 2 from rfl, pow_add, hx7, one_mul]
    simp only [s168e3_cyc_pk, this, MulEquiv.coe_toMonoidHom]
  simp only [s168e3_cyc_ph1, s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul,
    s168e3_cyc_pk_pow, s168e3_cyc_t_pk3 hx7 hinv, s168e3_cyc_t_pk1 hx7 hinv]
  rw [h7, h9]
  norm_num
  simp [mul_assoc, mul_comm, mul_left_comm]

private lemma s168e3_cyc_ph1_t {x t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1) (hx7 : x ^ 7 = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) (w : W) :
    s168e3_cyc_ph1 x (t w) = s168e3_cyc_pk x 3 (t (s168e3_cyc_ph2 x w)) := by
  have h7 : s168e3_cyc_pk x 7 (t w) = t w := by
    simp only [s168e3_cyc_pk, hx7, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  have h8 : s168e3_cyc_pk x 8 (t w) = s168e3_cyc_pk x 1 (t w) := by
    have : x ^ 8 = x ^ 1 := by
      rw [show (8:ℕ) = 7 + 1 from rfl, pow_add, hx7, one_mul]
    simp only [s168e3_cyc_pk, this, MulEquiv.coe_toMonoidHom]
  have h34 : (x ^ 3)⁻¹ = x ^ 4 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add]; show x ^ 7 = 1; exact hx7)
  have h25 : (x ^ 2)⁻¹ = x ^ 5 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_add]; show x ^ 7 = 1; exact hx7)
  have ht2 : t (s168e3_cyc_pk x 2 w) = s168e3_cyc_pk x 5 (t w) := by
    have h := s168e3_cyc_t_pk hinv 2 w
    simpa [s168e3_cyc_pk, h25] using h
  simp only [s168e3_cyc_ph1, s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul,
    s168e3_cyc_pk_pow, s168e3_cyc_t_pk3 hx7 hinv, ht2]
  rw [h7, h8]
  norm_num
  simp [mul_assoc, mul_comm, mul_left_comm]

private lemma s168e3_cyc_g_pk_comm {x g : MulAut W} (hgx : g * x = x * g) (k : ℕ) :
    g * x ^ k = x ^ k * g := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_assoc, hgx, mul_assoc]

private lemma s168e3_cyc_g_pk {x g : MulAut W} (hgx : g * x = x * g) (k : ℕ) (a : W) :
    g (s168e3_cyc_pk x k a) = s168e3_cyc_pk x k (g a) := by
  have h := s168e3_cyc_g_pk_comm hgx k
  simp only [s168e3_cyc_pk, MulEquiv.coe_toMonoidHom]
  rw [← MulAut.mul_apply, h, MulAut.mul_apply]

private lemma s168e3_cyc_ph1_g {x g : MulAut W} (hgx : g * x = x * g) (a : W) :
    s168e3_cyc_ph1 x (g a) = g (s168e3_cyc_ph1 x a) := by
  simp only [s168e3_cyc_ph1, MonoidHom.mul_apply, MonoidHom.id_apply]
  rw [← s168e3_cyc_g_pk hgx 3 a, ← s168e3_cyc_g_pk hgx 1 a, ← map_mul, ← map_mul]

private lemma s168e3_cyc_ph2_g {x g : MulAut W} (hgx : g * x = x * g) (a : W) :
    s168e3_cyc_ph2 x (g a) = g (s168e3_cyc_ph2 x a) := by
  simp only [s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply]
  rw [← s168e3_cyc_g_pk hgx 3 a, ← s168e3_cyc_g_pk hgx 2 a, ← map_mul, ← map_mul]

private lemma s168e3_cyc_ph1_pk (x : MulAut W) (k : ℕ) (a : W) :
    s168e3_cyc_ph1 x (s168e3_cyc_pk x k a) = s168e3_cyc_pk x k (s168e3_cyc_ph1 x a) := by
  simp only [s168e3_cyc_ph1, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul,
    s168e3_cyc_pk_pow]
  rw [Nat.add_comm 3 k, Nat.add_comm 1 k]

private lemma s168e3_cyc_ph2_pk (x : MulAut W) (k : ℕ) (a : W) :
    s168e3_cyc_ph2 x (s168e3_cyc_pk x k a) = s168e3_cyc_pk x k (s168e3_cyc_ph2 x a) := by
  simp only [s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply, map_mul,
    s168e3_cyc_pk_pow]
  rw [Nat.add_comm 3 k, Nat.add_comm 2 k]

private lemma s168e3_cyc_pk_mem {x : MulAut W} {U : Subgroup W}
    (hU : ∀ u ∈ U, x u ∈ U) (k : ℕ) {u : W} (hu : u ∈ U) :
    s168e3_cyc_pk x k u ∈ U := by
  induction k generalizing u with
  | zero => simpa [s168e3_cyc_pk_zero] using hu
  | succ k ih =>
      have hstep : s168e3_cyc_pk x (k + 1) u = s168e3_cyc_pk x k (x u) := by
        simp only [s168e3_cyc_pk, MulEquiv.coe_toMonoidHom, pow_succ, MulAut.mul_apply]
      rw [hstep]
      exact ih (hU u hu)

private lemma s168e3_cyc_ph1_mem {x : MulAut W} {U : Subgroup W}
    (hU : ∀ u ∈ U, x u ∈ U) {u : W} (hu : u ∈ U) : s168e3_cyc_ph1 x u ∈ U := by
  simp only [s168e3_cyc_ph1, MonoidHom.mul_apply, MonoidHom.id_apply]
  exact mul_mem (mul_mem (s168e3_cyc_pk_mem hU 3 hu) (s168e3_cyc_pk_mem hU 1 hu)) hu

private lemma s168e3_cyc_ph2_mem {x : MulAut W} {U : Subgroup W}
    (hU : ∀ u ∈ U, x u ∈ U) {u : W} (hu : u ∈ U) : s168e3_cyc_ph2 x u ∈ U := by
  simp only [s168e3_cyc_ph2, MonoidHom.mul_apply, MonoidHom.id_apply]
  exact mul_mem (mul_mem (s168e3_cyc_pk_mem hU 3 hu) (s168e3_cyc_pk_mem hU 2 hu)) hu

private lemma s168e3_cyc_mem_ker_ph1_x {x : MulAut W} {a : W}
    (ha : s168e3_cyc_ph1 x a = 1) : s168e3_cyc_ph1 x (x a) = 1 := by
  rw [← s168e3_cyc_pk_one x a, s168e3_cyc_ph1_pk, ha, map_one]

private lemma s168e3_cyc_mem_ker_ph2_x {x : MulAut W} {a : W}
    (ha : s168e3_cyc_ph2 x a = 1) : s168e3_cyc_ph2 x (x a) = 1 := by
  rw [← s168e3_cyc_pk_one x a, s168e3_cyc_ph2_pk, ha, map_one]

private lemma s168e3_cyc_ph1_a1 (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W} (hx7 : x ^ 7 = 1)
    (hfpf : ∀ w : W, x w = w → w = 1) (u : W) :
    s168e3_cyc_ph1 x
      (s168e3_cyc_ph2 x u * s168e3_cyc_pk x 1 (s168e3_cyc_ph2 x u)) = 1 := by
  rw [map_mul, s168e3_cyc_ph1_ph2 hW, s168e3_cyc_ph1_pk, s168e3_cyc_ph1_ph2 hW,
    s168e3_cyc_nrm_eq_one hx7 hfpf, map_one, mul_one]

private lemma s168e3_cyc_ph2_a2 (hW : ∀ w : W, w ^ 2 = 1) {x : MulAut W} (hx7 : x ^ 7 = 1)
    (hfpf : ∀ w : W, x w = w → w = 1) (u : W) :
    s168e3_cyc_ph2 x (s168e3_cyc_pk x 1 (s168e3_cyc_ph1 x u)) = 1 := by
  rw [s168e3_cyc_ph2_pk, s168e3_cyc_ph2_ph1 hW, s168e3_cyc_nrm_eq_one hx7 hfpf, map_one]

private lemma s168e3_cyc_div_eight_mod_seven {n : ℕ} (hdvd : n ∣ 8) (hmod : n % 7 = 1) :
    n = 1 ∨ n = 8 := by
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  omega

private lemma s168e3_cyc_card_map (t : MulAut W) (H : Subgroup W) :
    Nat.card ↥(H.map t.toMonoidHom) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (f := t.toMonoidHom) (fun _ _ h => t.injective h)

theorem s168e3_cyc7_blocks [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 6)
    {x t : MulAut W} (hx7 : x ^ 7 = 1) (hfpf : ∀ w : W, x w = w → w = 1)
    (hinv : t * x * t⁻¹ = x⁻¹) :
    ∃ W₁ W₂ : Subgroup W, Nat.card ↥W₁ = 8 ∧ Nat.card ↥W₂ = 8 ∧ W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = ⊤ ∧
      W₁.map t.toMonoidHom = W₂ ∧ W₂.map t.toMonoidHom = W₁ ∧
      (∀ U : Subgroup W, (∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = W₁ ∨ U = W₂ ∨ U = ⊤) ∧
      ∀ g : MulAut W, g * x = x * g →
        W₁.map g.toMonoidHom = W₁ ∧ W₂.map g.toMonoidHom = W₂ := by
  classical
  let W₁ : Subgroup W := (s168e3_cyc_ph1 x).ker
  let W₂ : Subgroup W := (s168e3_cyc_ph2 x).ker
  have hmem₁ : ∀ {a : W}, a ∈ W₁ ↔ s168e3_cyc_ph1 x a = 1 := fun {a} => MonoidHom.mem_ker
  have hmem₂ : ∀ {a : W}, a ∈ W₂ ↔ s168e3_cyc_ph2 x a = 1 := fun {a} => MonoidHom.mem_ker
  have hinf : W₁ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    have hu1 : s168e3_cyc_ph1 x u = 1 := hmem₁.1 hu.1
    have hu2 : s168e3_cyc_ph2 x u = 1 := hmem₂.1 hu.2
    have h := s168e3_cyc_ph_sum hW x u
    rw [hu1, hu2] at h
    simpa [s168e3_cyc_pk] using h.symm
  have hsup : W₁ ⊔ W₂ = ⊤ := by
    rw [eq_top_iff]
    intro u _
    rw [Subgroup.mem_sup]
    refine ⟨s168e3_cyc_ph2 x u * s168e3_cyc_pk x 1 (s168e3_cyc_ph2 x u), ?_,
      s168e3_cyc_pk x 1 (s168e3_cyc_ph1 x u), ?_, s168e3_cyc_ph_sum hW x u⟩
    · rw [hmem₁]
      exact s168e3_cyc_ph1_a1 hW hx7 hfpf u
    · rw [hmem₂]
      exact s168e3_cyc_ph2_a2 hW hx7 hfpf u
  have hmap₁ : W₁.map t.toMonoidHom ≤ W₂ := by
    intro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    change s168e3_cyc_ph2 x (t a) = 1
    rw [s168e3_cyc_ph2_t hW hx7 hinv a, hmem₁.1 ha]
    simp [s168e3_cyc_pk]
  have hmap₂ : W₂.map t.toMonoidHom ≤ W₁ := by
    intro u hu
    rw [Subgroup.mem_map] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    change s168e3_cyc_ph1 x (t a) = 1
    rw [s168e3_cyc_ph1_t hW hx7 hinv a, hmem₂.1 ha]
    simp [s168e3_cyc_pk]
  have hcard₁₂ : Nat.card ↥W₁ = Nat.card ↥W₂ := by
    have h₁ : Nat.card ↥W₁ ≤ Nat.card ↥W₂ := by
      have := Subgroup.card_le_of_le hmap₁
      rwa [s168e3_cyc_card_map t W₁] at this
    have h₂ : Nat.card ↥W₂ ≤ Nat.card ↥W₁ := by
      have := Subgroup.card_le_of_le hmap₂
      rwa [s168e3_cyc_card_map t W₂] at this
    exact le_antisymm h₁ h₂
  have hcardW₁ : Nat.card ↥W₁ = 8 := by
    have hprod := card_sup_mul_card_inf W₁ W₂
    rw [hsup, hinf, Subgroup.card_top, Subgroup.card_bot, hcard] at hprod
    have hsq : Nat.card ↥W₁ * Nat.card ↥W₁ = 2 ^ 6 := by
      have h := hprod.symm
      rw [mul_one, ← hcard₁₂] at h
      exact h
    have hpos : 0 < Nat.card ↥W₁ := Nat.card_pos
    nlinarith
  have hcardW₂ : Nat.card ↥W₂ = 8 := by rw [← hcard₁₂, hcardW₁]
  have ht₁ : W₁.map t.toMonoidHom = W₂ := by
    apply Subgroup.eq_of_le_of_card_ge hmap₁
    rw [s168e3_cyc_card_map t W₁, hcardW₁, hcardW₂]
  have ht₂ : W₂.map t.toMonoidHom = W₁ := by
    apply Subgroup.eq_of_le_of_card_ge hmap₂
    rw [s168e3_cyc_card_map t W₂, hcardW₂, hcardW₁]
  have hclass : ∀ U : Subgroup W, (∀ u ∈ U, x u ∈ U) → U = ⊥ ∨ U = W₁ ∨ U = W₂ ∨ U = ⊤ := by
    intro U hU
    have hU₁ : ∀ u ∈ U ⊓ W₁, x u ∈ U ⊓ W₁ := by
      rintro u ⟨huU, huW⟩
      exact ⟨hU u huU, hmem₁.2 (s168e3_cyc_mem_ker_ph1_x (hmem₁.1 huW))⟩
    have hU₂ : ∀ u ∈ U ⊓ W₂, x u ∈ U ⊓ W₂ := by
      rintro u ⟨huU, huW⟩
      exact ⟨hU u huU, hmem₂.2 (s168e3_cyc_mem_ker_ph2_x (hmem₂.1 huW))⟩
    have hmod₁ : Nat.card ↥(U ⊓ W₁) % 7 = 1 :=
      CFSG.OddStandard.HigherRank.YamadaG23.y7c_card_invariant_mod_seven hx7 hfpf hU₁
    have hmod₂ : Nat.card ↥(U ⊓ W₂) % 7 = 1 :=
      CFSG.OddStandard.HigherRank.YamadaG23.y7c_card_invariant_mod_seven hx7 hfpf hU₂
    have hdiv₁ : Nat.card ↥(U ⊓ W₁) ∣ 8 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : U ⊓ W₁ ≤ W₁)
      rwa [hcardW₁] at this
    have hdiv₂ : Nat.card ↥(U ⊓ W₂) ∣ 8 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : U ⊓ W₂ ≤ W₂)
      rwa [hcardW₂] at this
    have hcase₁ : U ⊓ W₁ = ⊥ ∨ U ⊓ W₁ = W₁ := by
      rcases s168e3_cyc_div_eight_mod_seven hdiv₁ hmod₁ with h1 | h8
      · exact Or.inl (Subgroup.eq_bot_of_card_eq (U ⊓ W₁) h1)
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge inf_le_right
          (Nat.le_of_eq (by rw [hcardW₁, h8])))
    have hcase₂ : U ⊓ W₂ = ⊥ ∨ U ⊓ W₂ = W₂ := by
      rcases s168e3_cyc_div_eight_mod_seven hdiv₂ hmod₂ with h1 | h8
      · exact Or.inl (Subgroup.eq_bot_of_card_eq (U ⊓ W₂) h1)
      · exact Or.inr (Subgroup.eq_of_le_of_card_ge inf_le_right
          (Nat.le_of_eq (by rw [hcardW₂, h8])))
    have hUeq : U = (U ⊓ W₁) ⊔ (U ⊓ W₂) := by
      apply le_antisymm
      · intro u hu
        rw [Subgroup.mem_sup]
        refine ⟨s168e3_cyc_ph2 x u * s168e3_cyc_pk x 1 (s168e3_cyc_ph2 x u), ?_,
          s168e3_cyc_pk x 1 (s168e3_cyc_ph1 x u), ?_, s168e3_cyc_ph_sum hW x u⟩
        · refine ⟨?_, hmem₁.2 (s168e3_cyc_ph1_a1 hW hx7 hfpf u)⟩
          exact mul_mem (s168e3_cyc_ph2_mem hU hu)
            (s168e3_cyc_pk_mem hU 1 (s168e3_cyc_ph2_mem hU hu))
        · refine ⟨?_, hmem₂.2 (s168e3_cyc_ph2_a2 hW hx7 hfpf u)⟩
          exact s168e3_cyc_pk_mem hU 1 (s168e3_cyc_ph1_mem hU hu)
      · exact sup_le inf_le_left inf_le_left
    rcases hcase₁ with h1 | h1 <;> rcases hcase₂ with h2 | h2
    · left; rw [hUeq, h1, h2]; simp
    · right; right; left; rw [hUeq, h1, h2]; simp
    · right; left; rw [hUeq, h1, h2]; simp
    · right; right; right; rw [hUeq, h1, h2, hsup]
  have hstab : ∀ g : MulAut W, g * x = x * g →
      W₁.map g.toMonoidHom = W₁ ∧ W₂.map g.toMonoidHom = W₂ := by
    intro g hgx
    have hle₁ : W₁.map g.toMonoidHom ≤ W₁ := by
      intro u hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨a, ha, rfl⟩ := hu
      change s168e3_cyc_ph1 x (g a) = 1
      rw [s168e3_cyc_ph1_g hgx a, hmem₁.1 ha, map_one]
    have hle₂ : W₂.map g.toMonoidHom ≤ W₂ := by
      intro u hu
      rw [Subgroup.mem_map] at hu
      obtain ⟨a, ha, rfl⟩ := hu
      change s168e3_cyc_ph2 x (g a) = 1
      rw [s168e3_cyc_ph2_g hgx a, hmem₂.1 ha, map_one]
    have hcm₁ := s168e3_cyc_card_map g W₁
    have hcm₂ := s168e3_cyc_card_map g W₂
    exact ⟨Subgroup.eq_of_le_of_card_ge hle₁ (Nat.le_of_eq hcm₁.symm),
      Subgroup.eq_of_le_of_card_ge hle₂ (Nat.le_of_eq hcm₂.symm)⟩
  exact ⟨W₁, W₂, hcardW₁, hcardW₂, hinf, hsup, ht₁, ht₂, hclass, hstab⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
