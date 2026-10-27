module

public import CFSG.Walter.Ree.Thompson1.Basic
public import CFSG.Walter.Ree.Thompson1.Coord

public section

namespace CFSG.Walter.Ree.Thompson1

open scoped IsMulCommutative

structure IsCoord {N K : Type*} [Group N] [Field K] (S T : Subgroup N) (θ : N → K) : Prop where
  add : ∀ x ∈ S, ∀ y ∈ S, θ (x * y) = θ x + θ y
  ker : ∀ x ∈ S, θ x = 0 ↔ x ∈ T
  surj : ∀ a : K, ∃ x ∈ S, θ x = a

section CoordLemmas

variable {N K : Type*} [Group N] [Field K] {S T : Subgroup N} {θ : N → K}

theorem IsCoord.one (hθ : IsCoord S T θ) : θ 1 = 0 := (hθ.ker 1 S.one_mem).2 T.one_mem

theorem IsCoord.inv (hθ : IsCoord S T θ) {x : N} (hx : x ∈ S) : θ x⁻¹ = -θ x := by
  have h1 := hθ.add x hx x⁻¹ (S.inv_mem hx)
  rw [mul_inv_cancel, hθ.one] at h1
  linear_combination -h1

theorem IsCoord.pow (hθ : IsCoord S T θ) {x : N} (hx : x ∈ S) (n : ℕ) : θ (x ^ n) = n * θ x := by
  induction n with
  | zero => simp [hθ.one]
  | succ n ih => rw [pow_succ, hθ.add _ (S.pow_mem hx n) _ hx, ih]; push_cast; ring

theorem IsCoord.zpow (hθ : IsCoord S T θ) {x : N} (hx : x ∈ S) (n : ℤ) :
    θ (x ^ n) = n * θ x := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [zpow_natCast, hθ.pow hx]; push_cast; ring
  · rw [zpow_neg, zpow_natCast, hθ.inv (S.pow_mem hx k), hθ.pow hx]; push_cast; ring

theorem IsCoord.eq_iff (hθ : IsCoord S T θ) {x y : N} (hx : x ∈ S) (hy : y ∈ S) :
    θ x = θ y ↔ y⁻¹ * x ∈ T := by
  rw [← hθ.ker _ (S.mul_mem (S.inv_mem hy) hx), hθ.add _ (S.inv_mem hy) _ hx, hθ.inv hy,
    neg_add_eq_zero, eq_comm]

end CoordLemmas

section Center

variable {N : Type*} [Group N] {P : Subgroup N}

@[expose] def toCenter {n : N} (hn : n ∈ zc P) : Subgroup.center P :=
  ⟨⟨n, (mem_zc.1 hn).1⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ((mem_zc.1 hn).2 g.1 g.2)⟩

theorem toCenter_mul {x y : N} (hx : x ∈ zc P) (hy : y ∈ zc P) :
    toCenter ((zc P).mul_mem hx hy) = toCenter hx * toCenter hy := rfl

end Center

variable {N : Type*} [Group N] [Finite N] {q : ℕ} {P R : Subgroup N}
  (h : ThompsonIConditions q P R) {K : Type*} [Field K] [Fintype K] [CharP K 3]
  (hK : Fintype.card K = q)
include h hK

theorem exists_theta3 : ∃ θ : N → K, IsCoord (zc P) ⊥ θ := by
  classical
  have hel := h.elementary_center
  have h3 : ∀ a : Subgroup.center P, a ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 _)
  obtain ⟨e⟩ := exists_addEquiv_of_exponent_three (K := K) h3 (by rw [h.card_center, hK])
  refine ⟨fun n => if hn : n ∈ zc P then e (Additive.ofMul (toCenter hn)) else 0, ⟨?_, ?_, ?_⟩⟩
  · intro x hx y hy
    simp only [hx, hy, (zc P).mul_mem hx hy, dite_true, toCenter_mul, ofMul_mul, map_add]
  · intro x hx
    simp only [hx, dite_true, Subgroup.mem_bot]
    constructor
    · intro h0
      have : toCenter hx = 1 := by
        have := e.injective (h0.trans e.map_zero.symm)
        exact this
      exact congrArg (fun w : Subgroup.center P => w.1.1) this
    · intro h1
      subst h1
      have : toCenter hx = 1 := rfl
      rw [this, ofMul_one, map_zero]
  · intro a
    obtain ⟨v, rfl⟩ := e.surjective a
    refine ⟨(Additive.toMul v).1.1, ⟨(Additive.toMul v).1, (Additive.toMul v).2, rfl⟩, ?_⟩
    have hmem : (Additive.toMul v).1.1 ∈ zc P :=
      ⟨(Additive.toMul v).1, (Additive.toMul v).2, rfl⟩
    simp only [hmem, dite_true]
    congr 1

omit [CharP K 3] in
theorem exists_theta1 {θ₃ : N → K} (h₃ : IsCoord (zc P) ⊥ θ₃) (hq1 : 1 < q) :
    ∃ y₀ ∈ ⁅P, P⁆, y₀ ∉ zc P ∧ IsCoord P ⁅P, P⁆ (fun x => θ₃ (tc y₀ x)) := by
  obtain ⟨y₀, hy₀, hy₀Z⟩ : ∃ y₀ ∈ ⁅P, P⁆, y₀ ∉ zc P := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (H := ⁅P, P⁆) (K := zc P) hcon
    rw [h.card_commutator, card_zc h] at this
    nlinarith
  have hadd : ∀ x ∈ P, ∀ x' ∈ P, θ₃ (tc y₀ (x * x')) = θ₃ (tc y₀ x) + θ₃ (tc y₀ x') :=
    fun x hx x' hx' => by
      rw [tc_mul_right_of_mem h hy₀ hx hx', h₃.add _ (tc_mem_zc h hy₀ hx) _ (tc_mem_zc h hy₀ hx')]
  have hker : ∀ x ∈ P, θ₃ (tc y₀ x) = 0 ↔ x ∈ ⁅P, P⁆ := fun x hx => by
    rw [h₃.ker _ (tc_mem_zc h hy₀ hx), Subgroup.mem_bot, tc_eq_one_iff,
      ← h.centralizer_of_mem_commutator y₀ hy₀ hy₀Z, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h' => ⟨hx, h'.symm⟩, fun h' => h'.2.symm⟩
  refine ⟨y₀, hy₀, hy₀Z, hadd, hker, surjective_of_card (commutator_le h) _ hadd hker ?_⟩
  rw [h.card_P, h.card_commutator, hK]
  ring

omit [Fintype K] [CharP K 3] hK in
theorem exists_x0 {J : N} (hJ : J ∈ R)
    (hJ2 : orderOf J = 2) {x : N} (hx : x ∈ P) (hxP2 : x ∉ ⁅P, P⁆) :
    x⁻¹ * (J⁻¹ * x * J) ∈ P ∧ x⁻¹ * (J⁻¹ * x * J) ∉ ⁅P, P⁆ ∧
      J⁻¹ * (x⁻¹ * (J⁻¹ * x * J)) * J = (x⁻¹ * (J⁻¹ * x * J))⁻¹ := by
  have hJ1 : J ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hJ2; exact absurd hJ2 (by norm_num)
  refine ⟨P.mul_mem (P.inv_mem hx) (conj_mem_P h hx), fun hmem => hxP2 ?_,
    invol_conj_inverted hJ2 x⟩
  exact fixed_L1 h hJ hJ2 hJ hJ1 hx hmem

omit [Finite N] [Fintype K] hK in
theorem cube_mem_zc_of_coord {θ₁ : N → K} (h₁ : IsCoord P ⁅P, P⁆ θ₁) {J : N} (hJ : J ∈ R)
    (hJ2 : orderOf J = 2) {x : N} (hx : x ∈ P) (hinv : J⁻¹ * x * J = x⁻¹) : x ^ 3 ∈ zc P := by
  refine cube_mem_zc h hJ hJ2 hinv ((h₁.ker _ (P.pow_mem hx 3)).1 ?_)
  rw [h₁.pow hx]
  have h3 : ((3 : ℕ) : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  rw [h3, zero_mul]

omit [Finite N] [Fintype K] hK in
theorem centralizer_inf_commutator {θ₁ : N → K} (h₁ : IsCoord P ⁅P, P⁆ θ₁) {x y : N}
    (hx : x ∈ P) (hxP2 : x ∉ ⁅P, P⁆) (hx3 : x ^ 3 ∈ zc P) (hy : y ∈ ⁅P, P⁆)
    (hyx : y * x = x * y) : y ∈ zc P := by
  have hyC : y ∈ P ⊓ Subgroup.centralizer {x} :=
    ⟨commutator_le h hy, Subgroup.mem_centralizer_singleton_iff.2 hyx⟩
  rw [h.centralizer_of_notMem_commutator x hx hxP2] at hyC
  have hyC' : y ∈ Subgroup.zpowers x ⊔ zc P := hyC
  have := zc_normal' h
  obtain ⟨w, hw, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hyC'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have hθx : θ₁ x ≠ 0 := fun h0 => hxP2 ((h₁.ker x hx).1 h0)
  have hk : θ₁ (x ^ k) = 0 := by
    have h1 : x ^ k = (x ^ k * z) * z⁻¹ := by group
    have h2 : x ^ k * z * z⁻¹ ∈ ⁅P, P⁆ :=
      (⁅P, P⁆ : Subgroup N).mul_mem hy ((⁅P, P⁆ : Subgroup N).inv_mem (zc_le_commutator h hz))
    rw [h1]
    exact (h₁.ker _ (commutator_le h h2)).2 h2
  rw [h₁.zpow hx] at hk
  have hk0 : (k : K) = 0 := (mul_eq_zero.1 hk).resolve_right hθx
  obtain ⟨j, rfl⟩ := (CharP.intCast_eq_zero_iff K 3 k).1 hk0
  refine (zc P).mul_mem ?_ hz
  rw [zpow_mul]
  exact (zc P).zpow_mem (by exact_mod_cast hx3) j

theorem exists_theta2 {θ₃ : N → K} (h₃ : IsCoord (zc P) ⊥ θ₃) {θ₁ : N → K}
    (h₁ : IsCoord P ⁅P, P⁆ θ₁) {x₀ : N} (hx₀ : x₀ ∈ P) (hx₀P2 : x₀ ∉ ⁅P, P⁆)
    (hx₀3 : x₀ ^ 3 ∈ zc P) : IsCoord ⁅P, P⁆ (zc P) (fun y => θ₃ (tc y x₀)) := by
  have hadd : ∀ y ∈ ⁅P, P⁆, ∀ y' ∈ ⁅P, P⁆, θ₃ (tc (y * y') x₀) = θ₃ (tc y x₀) + θ₃ (tc y' x₀) :=
    fun y hy y' hy' => by
      rw [tc_mul_left_of_mem h hy (commutator_le h hy') hx₀,
        h₃.add _ (tc_mem_zc h hy hx₀) _ (tc_mem_zc h hy' hx₀)]
  have hker : ∀ y ∈ ⁅P, P⁆, θ₃ (tc y x₀) = 0 ↔ y ∈ zc P := fun y hy => by
    rw [h₃.ker _ (tc_mem_zc h hy hx₀), Subgroup.mem_bot, tc_eq_one_iff]
    exact ⟨centralizer_inf_commutator h h₁ hx₀ hx₀P2 hx₀3 hy,
      fun hz => zc_comm hz hx₀⟩
  refine ⟨hadd, hker, surjective_of_card (zc_le_commutator h) _ hadd hker ?_⟩
  rw [h.card_commutator, card_zc h, hK]
  ring

theorem exists_eigen_coords {m : ℕ} (hq : q = 3 ^ m) (hm : 1 ≤ m) {J : N} (hJ : J ∈ R)
    (hJ2 : orderOf J = 2) :
    ∃ ℓ₁ ℓ₂ ℓ₃ : N → K, IsCoord P ⁅P, P⁆ ℓ₁ ∧ IsCoord ⁅P, P⁆ (zc P) ℓ₂ ∧
      IsCoord (zc P) ⊥ ℓ₃ ∧ ∃ ρ₁ ρ₂ ρ₃ : R →* Kˣ,
        (∀ r : R, ∀ x ∈ P, ℓ₁ (r.1⁻¹ * x * r.1) = ρ₁ r * ℓ₁ x) ∧
        (∀ r : R, ∀ y ∈ ⁅P, P⁆, ℓ₂ (r.1⁻¹ * y * r.1) = ρ₂ r * ℓ₂ y) ∧
        (∀ r : R, ∀ z ∈ zc P, ℓ₃ (r.1⁻¹ * z * r.1) = ρ₃ r * ℓ₃ z) := by
  have hq1 : 1 < q := by rw [hq]; exact Nat.one_lt_pow (by omega) (by norm_num)
  have hRc : Nat.card R = Fintype.card K - 1 := by rw [h.card_R, hK]
  have hRcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' = r' * r := fun r hr r' hr' => R_comm h hr hr'
  have := h.isCyclic_R
  have hinv : ∀ r ∈ R, r ^ 2 = 1 → r = 1 ∨ r = J := by
    intro r hr hr2
    by_cases hr1 : r = 1
    · exact Or.inl hr1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Or.inr (invol_unique h hr (orderOf_eq_prime hr2 hr1) hJ hJ2)
  obtain ⟨θ₃, h₃⟩ := exists_theta3 h hK
  obtain ⟨ℓ₃, h3a, h3k, h3s, ρ₃, h3ρ⟩ := exists_eigen_layer (R := R) bot_le
    (fun r _ z hz => conj_mem_zc h hz) (fun r _ z hz => by
      rw [Subgroup.mem_bot] at hz ⊢; rw [hz]; group) h₃.add h₃.ker hRc hRcomm h₃.surj
    (fun H hH => irreducible_of_fixed bot_le (fun r _ z hz => conj_mem_zc h hz)
      (fun r _ z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz]; group) h₃.add h₃.ker hRc
      (fun r hr hr1 z hz hfix => by
        have e := (h₃.eq_iff (conj_mem_zc h hz) hz).1 hfix
        rw [Subgroup.mem_bot, inv_mul_eq_one] at e
        rw [Subgroup.mem_bot]
        exact fixed_zc h hJ hJ2 hr hr1 hz e.symm) h₃.surj H hH)
  obtain ⟨y₀, hy₀, hy₀Z, h₁⟩ := exists_theta1 h hK h₃ hq1
  obtain ⟨ℓ₁, h1a, h1k, h1s, ρ₁, h1ρ⟩ := exists_eigen_layer (R := R) (commutator_le h)
    (fun r _ x hx => conj_mem_P h hx) (fun r _ x hx => conj_mem_commutator h hx) h₁.add h₁.ker
    hRc hRcomm h₁.surj
    (fun H hH => irreducible_of_fixed (commutator_le h) (fun r _ x hx => conj_mem_P h hx)
      (fun r _ x hx => conj_mem_commutator h hx) h₁.add h₁.ker hRc
      (fun r hr hr1 x hx hfix => fixed_L1 h hJ hJ2 hr hr1 hx
        ((h₁.eq_iff (conj_mem_P h hx) hx).1 hfix)) h₁.surj H hH)
  have hc₁ : IsCoord P ⁅P, P⁆ ℓ₁ := ⟨h1a, h1k, h1s⟩
  obtain ⟨x₁, hx₁, hx₁1⟩ := hc₁.surj 1
  have hx₁P2 : x₁ ∉ ⁅P, P⁆ := fun hm' => one_ne_zero (hx₁1 ▸ (hc₁.ker x₁ hx₁).2 hm')
  obtain ⟨hx₀, hx₀P2, hx₀inv⟩ := exists_x0 h hJ hJ2 hx₁ hx₁P2
  set x₀ := x₁⁻¹ * (J⁻¹ * x₁ * J)
  have hx₀3 := cube_mem_zc_of_coord h h₁ hJ hJ2 hx₀ hx₀inv
  have h₂ := exists_theta2 h hK h₃ h₁ hx₀ hx₀P2 hx₀3
  obtain ⟨ℓ₂, h2a, h2k, h2s, ρ₂, h2ρ⟩ := exists_eigen_layer (R := R) (zc_le_commutator h)
    (fun r _ y hy => conj_mem_commutator h hy) (fun r _ z hz => conj_mem_zc h hz) h₂.add
    h₂.ker hRc hRcomm h₂.surj
    (fun H hH => irreducible_of_fixed₂ (zc_le_commutator h)
      (fun r _ y hy => conj_mem_commutator h hy) (fun r _ z hz => conj_mem_zc h hz) h₂.add
      h₂.ker (by rw [hK, hq]) hRc hJ hinv
      (fun r hr hr2 y hy hfix => by
        have hE := (h₂.eq_iff (conj_mem_commutator h hy) hy).1 hfix
        obtain ⟨c, hc, z, hz, rfl⟩ := decomp h hJ hJ2 hy
        have hcP : c ∈ P := (mem_P0.1 hc).1
        have hrJ : r * J = J * r := hRcomm r hr J hJ
        have hc' : r⁻¹ * c * r ∈ P ⊓ Subgroup.centralizer {J} := by
          refine mem_P0.2 ⟨conj_mem_P h hcP, ?_⟩
          have e1 : J⁻¹ * (r⁻¹ * c * r) * J = r⁻¹ * (J⁻¹ * c * J) * r := by
            have : J⁻¹ * r⁻¹ = r⁻¹ * J⁻¹ := by
              rw [← mul_inv_rev, ← mul_inv_rev, hrJ]
            calc J⁻¹ * (r⁻¹ * c * r) * J = (J⁻¹ * r⁻¹) * c * (r * J) := by group
              _ = (r⁻¹ * J⁻¹) * c * (J * r) := by rw [this, hrJ]
              _ = r⁻¹ * (J⁻¹ * c * J) * r := by group
          rw [e1, (mem_P0.1 hc).2]
        set d := c⁻¹ * (r⁻¹ * c * r) with hd
        have hdP0 : d ∈ P ⊓ Subgroup.centralizer {J} :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hc'
        have hdZ : d ∈ zc P := by
          have e2 : d = z * ((c * z)⁻¹ * (r⁻¹ * (c * z) * r)) * (r⁻¹ * z * r)⁻¹ := by
            rw [hd]; group
          rw [e2]
          exact (zc P).mul_mem ((zc P).mul_mem hz hE) ((zc P).inv_mem (conj_mem_zc h hz))
        have hd1 : d ∈ (P ⊓ Subgroup.centralizer {J}) ⊓ zc P := ⟨hdP0, hdZ⟩
        rw [P0_inf_zc h hJ hJ2, Subgroup.mem_bot, hd, inv_mul_eq_one] at hd1
        have hc1 := fixed_P h hr hr2 hcP hd1.symm
        rw [hc1, one_mul]
        exact hz) h₂.surj H hH)
  exact ⟨ℓ₁, ℓ₂, ℓ₃, hc₁, ⟨h2a, h2k, h2s⟩, ⟨h3a, h3k, h3s⟩, ρ₁, ρ₂, ρ₃, h1ρ, h2ρ, h3ρ⟩

section Brackets

variable {ℓ₁ ℓ₂ ℓ₃ : N → K} (h1 : IsCoord P ⁅P, P⁆ ℓ₁) (h2 : IsCoord ⁅P, P⁆ (zc P) ℓ₂)
  (h3 : IsCoord (zc P) ⊥ ℓ₃)

omit [Finite N] [Fintype K] [CharP K 3] hK in
include h2 in
theorem B_left {x w y : N} (hx : x ∈ P) (hw : w ∈ ⁅P, P⁆) (hy : y ∈ P) :
    ℓ₂ (tc (x * w) y) = ℓ₂ (tc x y) := by
  have hxy := tc_mem_commutator hx hy
  rw [tc_mul_left', tc_commutator h hxy hw, mul_one,
    h2.add _ hxy _ (zc_le_commutator h (tc_mem_zc h hw hy)),
    (h2.ker _ (zc_le_commutator h (tc_mem_zc h hw hy))).2 (tc_mem_zc h hw hy), add_zero]

omit [Finite N] [Fintype K] [CharP K 3] hK in
include h2 in
theorem B_right {x y w : N} (hx : x ∈ P) (hy : y ∈ P) (hw : w ∈ ⁅P, P⁆) :
    ℓ₂ (tc x (y * w)) = ℓ₂ (tc x y) := by
  have hxy := tc_mem_commutator hx hy
  have hxw := tc_mem_zc' h hx hw
  have e : w⁻¹ * tc x y * w = tc x y := by
    rw [mul_assoc, commutator_comm h hxy hw, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [tc_mul_right, e, h2.add _ (zc_le_commutator h hxw) _ hxy,
    (h2.ker _ (zc_le_commutator h hxw)).2 hxw, zero_add]

omit [Finite N] [Fintype K] [CharP K 3] hK in
include h2 in
theorem B_add_left {x x' y : N} (hx : x ∈ P) (hx' : x' ∈ P) (hy : y ∈ P) :
    ℓ₂ (tc (x * x') y) = ℓ₂ (tc x y) + ℓ₂ (tc x' y) := by
  have hxy := tc_mem_commutator hx hy
  have hm := tc_mem_zc h hxy hx'
  rw [tc_mul_left', h2.add _ ((⁅P, P⁆ : Subgroup N).mul_mem hxy (zc_le_commutator h hm)) _
    (tc_mem_commutator hx' hy), h2.add _ hxy _ (zc_le_commutator h hm),
    (h2.ker _ (zc_le_commutator h hm)).2 hm, add_zero]

omit [Finite N] [Fintype K] [CharP K 3] hK in
include h2 in
theorem B_add_right {x y y' : N} (hx : x ∈ P) (hy : y ∈ P) (hy' : y' ∈ P) :
    ℓ₂ (tc x (y * y')) = ℓ₂ (tc x y) + ℓ₂ (tc x y') := by
  have hxy := tc_mem_commutator hx hy
  have hm := tc_mem_zc h hxy hy'
  rw [tc_mul_right, conj_eq_mul_tc, h2.add _ (tc_mem_commutator hx hy') _
    ((⁅P, P⁆ : Subgroup N).mul_mem hxy (zc_le_commutator h hm)),
    h2.add _ hxy _ (zc_le_commutator h hm), (h2.ker _ (zc_le_commutator h hm)).2 hm, add_zero,
    add_comm]

omit [Finite N] [Field K] [Fintype K] [CharP K 3] hK in
theorem tc_mul_commutator_right {y x w : N} (hy : y ∈ ⁅P, P⁆) (hx : x ∈ P)
    (hw : w ∈ ⁅P, P⁆) : tc y (x * w) = tc y x := by
  have e : w⁻¹ * tc y x * w = tc y x := by
    rw [mul_assoc, zc_comm (tc_mem_zc h hy hx) (commutator_le h hw), ← mul_assoc, inv_mul_cancel,
      one_mul]
  rw [tc_mul_right, tc_commutator h hy hw, one_mul, e]

omit [Finite N] [Fintype K] [CharP K 3] hK in
include h1 h2 in
theorem B_wd {x y x' y' : N} (hx : x ∈ P) (hy : y ∈ P) (hx' : x' ∈ P) (hy' : y' ∈ P)
    (hxx : ℓ₁ x = ℓ₁ x') (hyy : ℓ₁ y = ℓ₁ y') : ℓ₂ (tc x y) = ℓ₂ (tc x' y') := by
  have hw : x⁻¹ * x' ∈ ⁅P, P⁆ := (h1.eq_iff hx' hx).1 hxx.symm
  have hw' : y⁻¹ * y' ∈ ⁅P, P⁆ := (h1.eq_iff hy' hy).1 hyy.symm
  have e1 : x' = x * (x⁻¹ * x') := by group
  have e2 : y' = y * (y⁻¹ * y') := by group
  rw [e1, e2, B_left h h2 hx hw (P.mul_mem hy (commutator_le h hw')), B_right h h2 hx hy hw']

omit [Finite N] [Fintype K] [CharP K 3] hK in
include h1 h2 in
theorem C_wd {x y x' y' : N} (hy : y ∈ ⁅P, P⁆) (hx : x ∈ P) (hy' : y' ∈ ⁅P, P⁆) (hx' : x' ∈ P)
    (hyy : ℓ₂ y = ℓ₂ y') (hxx : ℓ₁ x = ℓ₁ x') : ℓ₃ (tc y x) = ℓ₃ (tc y' x') := by
  have hz : y⁻¹ * y' ∈ zc P := (h2.eq_iff hy' hy).1 hyy.symm
  have hw : x⁻¹ * x' ∈ ⁅P, P⁆ := (h1.eq_iff hx' hx).1 hxx.symm
  have e1 : y' = y * (y⁻¹ * y') := by group
  have e2 : x' = x * (x⁻¹ * x') := by group
  rw [e1, e2, tc_mul_zc_left (commutator_le h hy) hz (P.mul_mem hx (commutator_le h hw)),
    tc_mul_commutator_right h hy hx hw]

end Brackets

end CFSG.Walter.Ree.Thompson1

namespace CFSG.Walter.Ree.Thompson1

variable {N : Type*} [Group N] {K : Type*} [Field K]

structure NormalCoords (P R : Subgroup N) (σ : K ≃+* K) (r : Kˣ →* N) (ℓ₁ ℓ₂ ℓ₃ : N → K) :
    Prop where
  fix : ∀ x : K, σ x = x → x = 0 ∨ x = 1 ∨ x = -1
  r_mem : ∀ κ, r κ ∈ R
  r_surj : ∀ x ∈ R, ∃ κ, r κ = x
  r_inj : Function.Injective r
  c1 : IsCoord P ⁅P, P⁆ ℓ₁
  c2 : IsCoord ⁅P, P⁆ (zc P) ℓ₂
  c3 : IsCoord (zc P) ⊥ ℓ₃
  eq1 : ∀ (κ : Kˣ) (x : N), x ∈ P → ℓ₁ ((r κ)⁻¹ * x * r κ) = κ * ℓ₁ x
  eq2 : ∀ (κ : Kˣ) (y : N), y ∈ ⁅P, P⁆ → ℓ₂ ((r κ)⁻¹ * y * r κ) = κ * σ κ * ℓ₂ y
  eq3 : ∀ (κ : Kˣ) (z : N), z ∈ zc P → ℓ₃ ((r κ)⁻¹ * z * r κ) = κ ^ 2 * σ κ * ℓ₃ z
  br1 : ∀ x y : N, x ∈ P → y ∈ P → ℓ₂ (tc x y) = σ (ℓ₁ x) * ℓ₁ y - ℓ₁ x * σ (ℓ₁ y)
  br2 : ∀ y x : N, y ∈ ⁅P, P⁆ → x ∈ P → ℓ₃ (tc y x) = ℓ₂ y * ℓ₁ x

end CFSG.Walter.Ree.Thompson1
