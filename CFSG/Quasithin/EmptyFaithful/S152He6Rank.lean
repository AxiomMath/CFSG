module

public import CFSG.Dihedral.Glauberman.DicksonMaxExist
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Fix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic

public section

namespace CFSG.Quasithin.He6

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1
open scoped MatrixGroups

theorem exists_prime_ge_five_dvd_four_pow_add_one {k : ℕ} (hk : 1 ≤ k) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 4 ^ k + 1 := by
  have hn : 4 ^ k + 1 ≠ 1 := by
    have : 0 < 4 ^ k := by positivity
    omega
  refine ⟨(4 ^ k + 1).minFac, Nat.minFac_prime hn, ?_, Nat.minFac_dvd _⟩
  have hp := Nat.minFac_prime hn
  have hd := Nat.minFac_dvd (4 ^ k + 1)
  have h2 : (4 ^ k + 1).minFac ≠ 2 := by
    intro h
    rw [h] at hd
    have : (4 : ℕ) ^ k % 2 = 0 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
    omega
  have h3 : (4 ^ k + 1).minFac ≠ 3 := by
    intro h
    rw [h] at hd
    have : (4 : ℕ) ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    omega
  have h2le := hp.two_le
  have h4 : (4 ^ k + 1).minFac ≠ 4 := by
    intro h
    rw [h] at hp
    exact absurd hp (by decide)
  omega

theorem three_pow_add_one_ne_two_pow {b c : ℕ} (hb : 2 ≤ b) : 3 ^ b + 1 ≠ 2 ^ c := by
  intro h
  have h9 : 9 ∣ 3 ^ b := by
    have : 3 ^ 2 ∣ 3 ^ b := pow_dvd_pow 3 hb
    simpa using this
  have hmod9 : 2 ^ c % 9 = 1 := by omega
  have h6 : c % 6 = 0 := by
    have hc : 2 ^ c % 9 = 2 ^ (c % 6) % 9 := by
      conv_lhs => rw [← Nat.div_add_mod c 6, pow_add, pow_mul]
      rw [Nat.mul_mod, Nat.pow_mod]
      norm_num
    have hlt : c % 6 < 6 := Nat.mod_lt _ (by norm_num)
    interval_cases hc6 : c % 6 <;> simp_all
  have hmod7 : 2 ^ c % 7 = 1 := by
    conv_lhs => rw [← Nat.div_add_mod c 6, h6, add_zero, pow_mul]
    rw [Nat.pow_mod]
    norm_num
  have h7 : 7 ∣ 3 ^ b := by omega
  have := (Nat.prime_iff.mp (by norm_num : Nat.Prime 7)).dvd_of_dvd_pow h7
  omega

theorem exists_prime_ge_five_dvd_of_mod_four {p : ℕ} (hp3 : p % 4 = 3) (hp11 : 11 ≤ p) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ (r ∣ (p - 1) / 2 ∨ r ∣ (p + 1) / 2) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ : ∃ j, p = 4 * j + 3 := ⟨p / 4, by omega⟩
  have hm : (p - 1) / 2 = 2 * j + 1 := by omega
  have hm1 : (p + 1) / 2 = 2 * j + 2 := by omega
  have hj2 : 2 ≤ j := by omega
  have hA : ∀ {d : ℕ}, d.Prime → d ∣ 2 * j + 1 → d = 3 := by
    intro d hd hdvd
    have h2 : d ≠ 2 := by
      rintro rfl
      omega
    have hd5 : ¬ 5 ≤ d := fun h5 => (hcon d hd h5).1 (by rw [hm]; exact hdvd)
    have := hd.two_le
    have h4 : d ≠ 4 := by
      rintro rfl
      exact absurd hd (by decide)
    omega
  have hApow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : 2 * j + 1 ≠ 0) hA
  set b := (2 * j + 1).primeFactorsList.length with hb
  have hb2 : 2 ≤ b := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ b ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3dvd : 3 ∣ 2 * j + 1 := by
    rw [hApow]
    exact dvd_pow_self 3 (by omega)
  have hB : ∀ {d : ℕ}, d.Prime → d ∣ 2 * j + 2 → d = 2 := by
    intro d hd hdvd
    have h3 : d ≠ 3 := by
      rintro rfl
      omega
    have hd5 : ¬ 5 ≤ d := fun h5 => (hcon d hd h5).2 (by rw [hm1]; exact hdvd)
    have := hd.two_le
    have h4 : d ≠ 4 := by
      rintro rfl
      exact absurd hd (by decide)
    omega
  have hBpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : 2 * j + 2 ≠ 0) hB
  apply three_pow_add_one_ne_two_pow hb2 (c := (2 * j + 2).primeFactorsList.length)
  rw [← hApow, ← hBpow]

theorem three_le_orderOf_two {r : ℕ} [Fact r.Prime] (hr5 : 5 ≤ r) : 3 ≤ orderOf (2 : ZMod r) := by
  have hr : r.Prime := Fact.out
  have h20 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hfin : IsOfFinOrder (2 : ZMod r) :=
    isOfFinOrder_iff_pow_eq_one.2
      ⟨r - 1, by have := hr.one_lt; omega, ZMod.pow_card_sub_one_eq_one h20⟩
  have hpos : 0 < orderOf (2 : ZMod r) := hfin.orderOf_pos
  by_contra hlt
  push Not at hlt
  have hone := pow_orderOf_eq_one (2 : ZMod r)
  interval_cases hk : orderOf (2 : ZMod r)
  · rw [pow_one] at hone
    have h' : ((1 : ℕ) : ZMod r) = 0 := by
      have : (2 : ZMod r) - 1 = 0 := by rw [hone]; ring
      simpa using (by linear_combination this : (1 : ZMod r) = 0)
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · have h' : ((3 : ℕ) : ZMod r) = 0 := by
      have : (2 : ZMod r) ^ 2 - 1 = 0 := by rw [hone]; ring
      push_cast
      linear_combination this
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega

theorem not_transvection {P : Type*} [Group P] {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (ρ : P →* MulAut W) (hρ : Function.Injective ρ)
    (hconj : ∀ x y : P, orderOf x = 2 → orderOf y = 2 → IsConj x y)
    (hgood : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ∃ b c : P, b * b = 1 ∧ c * c = 1 ∧ orderOf (b * c) = r)
    {x : P} (hx : orderOf x = 2) : (fixV (Subgroup.zpowers (ρ x))).index ≠ 2 := by
  obtain ⟨r, hr, hr5, b, c, hb, hc, hbc⟩ := hgood
  have : Fact r.Prime := ⟨hr⟩
  have hsq : ∀ y : P, y * y = 1 → y ≠ 1 → orderOf y = 2 := fun y hy hy1 =>
    orderOf_eq_prime (by rw [sq]; exact hy) hy1
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [one_mul] at hbc
    have h1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hc)
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [mul_one] at hbc
    have h1 : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hb)
    have := Nat.le_of_dvd (by norm_num) h1
    omega
  intro h2
  have hDconj : ∀ y : P, orderOf y = 2 → (fixV (Subgroup.zpowers (ρ y))).index = 2 := by
    intro y hy
    obtain ⟨g, hg⟩ := isConj_iff.1 (hconj x y hx hy)
    rw [← hg, map_mul, map_mul, map_inv]
    exact (index_fixV_conj (ρ g) (ρ x)).trans h2
  have hDb := hDconj b (hsq b hb hb1)
  have hDc := hDconj c (hsq c hc hc1)
  have hprod := index_fixV_mul_le (ρ b) (ρ c)
  rw [hDb, hDc] at hprod
  have hord : orderOf (ρ b * ρ c) = r := by
    rw [← map_mul, orderOf_injective ρ hρ]
    exact hbc
  have hlow := two_pow_orderOf_le_index_fixV hW (p := r) (by omega) hord
  have h3 := three_le_orderOf_two hr5
  have h4 : 2 ^ 3 ≤ 2 ^ orderOf (2 : ZMod r) := Nat.pow_le_pow_right (by norm_num) h3
  omega

theorem dihedral_pair_of_equiv {G : Type*} [Group G] {H : Subgroup G} {r : ℕ}
    (e : H ≃* DihedralGroup r) :
    ∃ b c : G, b * b = 1 ∧ c * c = 1 ∧ orderOf (b * c) = r := by
  refine ⟨(e.symm (DihedralGroup.sr 0) : G), (e.symm (DihedralGroup.sr 1) : G), ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one]; rfl
  · rw [← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_self, map_one]; rfl
  · rw [← Subgroup.coe_mul, ← map_mul, DihedralGroup.sr_mul_sr, Subgroup.orderOf_coe,
      MulEquiv.orderOf_eq]
    simp

theorem exists_involution_pair_of_sq {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    {i : K} (hi : -1 = i * i) :
    ∃ b c : PSL(2, K), b * b = 1 ∧ c * c = 1 ∧ orderOf (b * c) = p := by
  have hdet_t : (!![i, 0; 0, -i] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hi
  have hdet_u : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  let t : SL(2, K) := ⟨!![i, 0; 0, -i], hdet_t⟩
  let u : SL(2, K) := ⟨!![1, 1; 0, 1], hdet_u⟩
  have hcenter : ∀ g : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) = !![-1, 0; 0, -1] →
      (QuotientGroup.mk g : PSL(2, K)) = 1 := by
    intro g hg
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [hg]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  have htt : (QuotientGroup.mk (t * t) : PSL(2, K)) = 1 := by
    apply hcenter
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show !![i, 0; 0, -i] * !![i, 0; 0, -i] = _
    ext a b
    fin_cases a <;> fin_cases b <;> simp <;> linear_combination (-1 : K) * hi
  have htu : (QuotientGroup.mk ((t * u) * (t * u)) : PSL(2, K)) = 1 := by
    apply hcenter
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    show (!![i, 0; 0, -i] * !![1, 1; 0, 1]) * (!![i, 0; 0, -i] * !![1, 1; 0, 1]) = _
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (-1 : K) * hi
  have hupow : ∀ n : ℕ, ((u ^ n : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      !![1, (n : K); 0, 1] := by
    intro n
    induction n with
    | zero =>
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    | succ n ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
      show !![1, (n : K); 0, 1] * !![1, 1; 0, 1] = _
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
  have hup : (QuotientGroup.mk u : PSL(2, K)) ^ p = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨1, by norm_num, ?_⟩
    rw [hupow]
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  have hu1 : (QuotientGroup.mk u : PSL(2, K)) ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hr
    simp [u] at this
  refine ⟨QuotientGroup.mk t, QuotientGroup.mk (t * u), ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul]; exact htt
  · rw [← QuotientGroup.mk_mul]; exact htu
  · have : (QuotientGroup.mk t : PSL(2, K)) * QuotientGroup.mk (t * u) =
        QuotientGroup.mk u := by
      rw [← QuotientGroup.mk_mul, show t * (t * u) = (t * t) * u by group, QuotientGroup.mk_mul,
        htt, one_mul]
    rw [this]
    exact orderOf_eq_prime hup hu1

theorem exists_involution_pair_zmod {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ b c : PSL(2, ZMod p), b * b = 1 ∧ c * c = 1 ∧ orderOf (b * c) = p := by
  obtain ⟨i, hi⟩ : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
  exact exists_involution_pair_of_sq hi

theorem exists_involution_psl2 (K : Type*) [Field K] : ∃ x : PSL(2, K), x * x = 1 ∧ x ≠ 1 := by
  have hdet : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]
    ring
  let w : SL(2, K) := ⟨!![0, 1; -1, 0], hdet⟩
  refine ⟨QuotientGroup.mk w, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show _ = !![0, 1; -1, 0] * !![0, 1; -1, 0]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    rw [QuotientGroup.eq_one_iff, Matrix.SpecialLinearGroup.mem_center_iff] at h
    obtain ⟨r, -, hr⟩ := h
    have := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hr
    simp [w] at this

theorem goodPair_gf_two {f : ℕ} (hfe : Even f) (hf : 2 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ∃ b c : PSL(2, GaloisField 2 f), b * b = 1 ∧ c * c = 1 ∧
      orderOf (b * c) = r := by
  obtain ⟨k, hk⟩ := hfe
  have hk1 : 1 ≤ k := by omega
  obtain ⟨r, hr, hr5, hdvd⟩ := exists_prime_ge_five_dvd_four_pow_add_one hk1
  have h2f : 2 ^ f = 4 ^ k := by
    rw [hk, ← two_mul, pow_mul]
    norm_num
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hgcd : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have hodd : Odd (2 ^ f - 1) := by
      have hpos : 0 < 2 ^ f := by positivity
      have heven : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      exact Nat.Even.sub_odd hpos heven odd_one
    exact (Nat.coprime_two_left.2 hodd)
  have hz : r ∣ (2 ^ f + 1) / Nat.gcd 2 (2 ^ f - 1) := by
    rw [hgcd, Nat.div_one, h2f]
    exact hdvd
  obtain ⟨H, ⟨e⟩⟩ := CFSG.Glauberman.Dickson.exists_dihedral_subgroup
    (F := GaloisField 2 f) (p := 2) (f := f) hcard (z := r) (Or.inl hz)
  exact ⟨r, hr, hr5, dihedral_pair_of_equiv e⟩

theorem goodPair_zmod {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hp7 : p ≠ 7) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ ∃ b c : PSL(2, ZMod p), b * b = 1 ∧ c * c = 1 ∧
      orderOf (b * c) = r := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · omega
    · exact h
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h4 with h1 | h3
  · exact ⟨p, hp.out, hp5, exists_involution_pair_zmod h1⟩
  · have hp11 : 11 ≤ p := by
      by_contra hlt
      have : p = 7 := by omega
      exact hp7 this
    obtain ⟨r, hr, hr5, hrd⟩ := exists_prime_ge_five_dvd_of_mod_four h3 hp11
    have hcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
    have hgcd : Nat.gcd 2 (p ^ 1 - 1) = 2 := by
      rw [pow_one]
      exact Nat.gcd_eq_left (by omega)
    have hz : r ∣ (p ^ 1 + 1) / Nat.gcd 2 (p ^ 1 - 1) ∨ r ∣ (p ^ 1 - 1) / Nat.gcd 2 (p ^ 1 - 1) := by
      rw [hgcd, pow_one]
      exact hrd.symm
    obtain ⟨H, ⟨e⟩⟩ := CFSG.Glauberman.Dickson.exists_dihedral_subgroup
      (F := ZMod p) (p := p) (f := 1) hcard (z := r) hz
    exact ⟨r, hr, hr5, dihedral_pair_of_equiv e⟩

theorem no_transvection_gf_two {f : ℕ} (hfe : Even f) (hf : 2 ≤ f) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) (ρ : PSL(2, GaloisField 2 f) →* MulAut W)
    (hρ : Function.Injective ρ) {x : PSL(2, GaloisField 2 f)} (hx : orderOf x = 2) :
    (fixV (Subgroup.zpowers (ρ x))).index ≠ 2 :=
  not_transvection hW ρ hρ
    (fun _ _ hx hy => CFSG.Walter.psl2_even_isConj_of_orderOf_eq_two hf hx hy)
    (goodPair_gf_two hfe hf) hx

theorem no_transvection_zmod {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp7 : p ≠ 7) {W : Type}
    [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (ρ : PSL(2, ZMod p) →* MulAut W)
    (hρ : Function.Injective ρ) {x : PSL(2, ZMod p)} (hx : orderOf x = 2) :
    (fixV (Subgroup.zpowers (ρ x))).index ≠ 2 := by
  have hodd : Odd p := by
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · omega
    · exact h
  have hcard : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  exact not_transvection hW ρ hρ
    (fun _ _ hx hy => CFSG.Walter.psl2_isConj_of_orderOf_eq_two (ZMod p) hcard hodd one_pos hx hy)
    (goodPair_zmod hp5 hp7) hx

theorem no_transvection_of_l2 {A : Type} [Group A] {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1)
    (hA : (∃ f : ℕ, Even f ∧ 2 ≤ f ∧ Nonempty (A ≃* PSL(2, GaloisField 2 f))) ∨
      (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ≠ 7 ∧ Nonempty (A ≃* PSL(2, ZMod p))))
    (ρ : A →* MulAut W) (hρ : Function.Injective ρ) {x : A} (hx : orderOf x = 2) :
    (fixV (Subgroup.zpowers (ρ x))).index ≠ 2 := by
  rcases hA with ⟨f, hfe, hf, ⟨e⟩⟩ | ⟨p, hp, hp5, hp7, ⟨e⟩⟩
  · have := no_transvection_gf_two hfe hf hW (ρ.comp e.symm.toMonoidHom)
      (hρ.comp e.symm.injective) (x := e x) (by rw [MulEquiv.orderOf_eq]; exact hx)
    simpa using this
  · have : Fact p.Prime := ⟨hp⟩
    have := no_transvection_zmod hp5 hp7 hW (ρ.comp e.symm.toMonoidHom)
      (hρ.comp e.symm.injective) (x := e x) (by rw [MulEquiv.orderOf_eq]; exact hx)
    simpa using this

end CFSG.Quasithin.He6
