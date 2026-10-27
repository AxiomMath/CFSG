module

public import CFSG.RankThree.PartTwo.Sec8.Hering418RCrit
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem NoCommute37.of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : NoCommute37 T) : NoCommute37 S := by
  intro y z hy hz hyz
  refine h (e y) (e z) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq, hy]
  · rw [MulEquiv.orderOf_eq, hz]
  · rw [← map_mul, ← map_mul, hyz]

theorem NoCommute37.of_le {S : Type*} [Group S] (H : Subgroup S) (h : NoCommute37 S) :
    NoCommute37 H := by
  intro y z hy hz hyz
  refine h (y : S) (z : S) ?_ ?_ ?_
  · rw [Subgroup.orderOf_coe, hy]
  · rw [Subgroup.orderOf_coe, hz]
  · exact congrArg Subtype.val hyz

private lemma lift_pow_aux {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] {m : ℕ}
    (hm : ∀ x ∈ Z, x ^ m = 1) (g : G) (n k : ℕ) (hn : orderOf (g : G ⧸ Z) = n)
    (hmk : m ∣ k) (hk : k % n = 1) :
    (g ^ k) ^ n = 1 ∧ ((g ^ k : G) : G ⧸ Z) = (g : G ⧸ Z) := by
  have hpow : ∀ j : ℕ, ((g ^ j : G) : G ⧸ Z) = (g : G ⧸ Z) ^ j :=
    fun j => QuotientGroup.mk_pow Z g j
  have hgn : g ^ n ∈ Z := by
    apply (QuotientGroup.eq_one_iff (g ^ n)).mp
    rw [hpow, ← hn]
    exact pow_orderOf_eq_one _
  have hgnm : (g ^ n) ^ m = 1 := hm _ hgn
  constructor
  · have h : (g ^ k) ^ n = (g ^ n) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [h]
    obtain ⟨t, rfl⟩ := hmk
    rw [pow_mul, hgnm, one_pow]
  · have hmod := pow_mod_orderOf (g : G ⧸ Z) k
    rw [hn, hk, pow_one] at hmod
    rw [hpow]
    exact hmod.symm

private lemma exists_lift_pow {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal] {m : ℕ}
    (hm : ∀ x ∈ Z, x ^ m = 1) {n : ℕ} (hcop : Nat.Coprime m n) (hn : 1 < n)
    (y : G ⧸ Z) (hy : orderOf y = n) : ∃ a : G, a ^ n = 1 ∧ (a : G ⧸ Z) = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨j, -, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn
  obtain ⟨h1, h2⟩ := lift_pow_aux Z hm g n (m * j) hy (dvd_mul_right m j) hj
  exact ⟨g ^ (m * j), h1, h2⟩

theorem exists_commuting_of_quotient {G : Type*} [Group G] (Z : Subgroup G) [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) {m : ℕ} (hm : ∀ x ∈ Z, x ^ m = 1)
    (h7 : Nat.Coprime m 7) (h3 : Nat.Coprime m 3)
    (y w : G ⧸ Z) (hy : orderOf y = 7) (hw : orderOf w = 3) (hyw : y * w = w * y) :
    ∃ a b : G, orderOf a = 7 ∧ orderOf b = 3 ∧ a * b = b * a := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha7, ha⟩ := exists_lift_pow Z hm h7 (by norm_num) y hy
  obtain ⟨b, hb3, hb⟩ := exists_lift_pow Z hm h3 (by norm_num) w hw
  obtain ⟨ζ, hζ_def⟩ : ∃ ζ : G, ζ = a * b * a⁻¹ * b⁻¹ := ⟨_, rfl⟩
  have hζZ : ζ ∈ Z := by
    rw [hζ_def, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ha, hb, hyw]
    group
  have hζc : ∀ g : G, g * ζ = ζ * g := Subgroup.mem_center_iff.mp (hZ hζZ)
  have hab : a * b * a⁻¹ = ζ * b := by
    rw [hζ_def]
    group
  have hconj : (a * b * a⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hb3, mul_one, mul_inv_cancel]
  have hcube : (ζ * b) ^ 3 = ζ ^ 3 := by
    have hc : Commute ζ b := (hζc b).symm
    rw [hc.mul_pow, hb3, mul_one]
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hcube, ← hab]
    exact hconj
  have hζ1 : ζ = 1 := by
    have h : ζ ^ Nat.gcd m 3 = 1 := pow_gcd_eq_one.mpr ⟨hm ζ hζZ, hζ3⟩
    have h3' : Nat.gcd m 3 = 1 := h3
    rw [h3', pow_one] at h
    exact h
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, QuotientGroup.mk_one] at ha
    rw [← ha, orderOf_one] at hy
    norm_num at hy
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, QuotientGroup.mk_one] at hb
    rw [← hb, orderOf_one] at hw
    norm_num at hw
  refine ⟨a, b, orderOf_eq_prime ha7 ha1, orderOf_eq_prime hb3 hb1, ?_⟩
  have h0 : a * b * a⁻¹ * b⁻¹ = 1 := by
    rw [← hζ_def]
    exact hζ1
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h0, one_mul]


section LinAlg

theorem natCard_modEq_inf_ker {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Module.Finite F V] [Finite V] (Z : Module.End F V) {p k : ℕ} [hp : Fact p.Prime]
    (hZ : Z ^ p ^ k = 1) (U : Submodule F V) (hU : ∀ u ∈ U, Z u ∈ U) :
    Nat.card U ≡ Nat.card (U ⊓ LinearMap.ker (Z - 1) : Submodule F V) [MOD p] := by
  classical
  haveI : Fintype U := Fintype.ofFinite U
  let f : Function.End U := fun u => ⟨Z u, hU u u.2⟩
  have hfpow : ∀ (m : ℕ) (u : U), ((f ^ m) u : V) = (Z ^ m) u := by
    intro m
    induction m with
    | zero => intro u; rfl
    | succ m ih =>
      intro u
      rw [pow_succ', pow_succ', Module.End.mul_apply]
      show Z ((f ^ m) u : V) = Z ((Z ^ m) u)
      rw [ih u]
  have hf : f ^ p ^ k = 1 := by
    funext u
    apply Subtype.ext
    have h := hfpow (p ^ k) u
    rw [hZ, Module.End.one_apply] at h
    exact h
  have h1 := Equiv.Perm.card_fixedPoints_modEq (p := p) (n := k) hf
  have hmem : ∀ x : U, x ∈ Function.fixedPoints f ↔ (x : V) ∈ LinearMap.ker (Z - 1) := by
    intro x
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      have h' : f x = x := h
      exact congrArg Subtype.val h'
    · intro h
      show f x = x
      exact Subtype.ext h
  let e : Function.fixedPoints f ≃ (U ⊓ LinearMap.ker (Z - 1) : Submodule F V) :=
    { toFun := fun x => ⟨(x.1 : V), Submodule.mem_inf.2 ⟨x.1.2, (hmem x.1).1 x.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (Submodule.mem_inf.1 y.2).1⟩,
        (hmem ⟨y.1, (Submodule.mem_inf.1 y.2).1⟩).2 (Submodule.mem_inf.1 y.2).2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  have hfix : Nat.card (Function.fixedPoints f) =
      Nat.card (U ⊓ LinearMap.ker (Z - 1) : Submodule F V) :=
    Nat.card_congr e
  rw [← hfix, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h1

theorem three_dvd_of_nine_pow_mod_seven {a : ℕ} (h : 9 ^ a % 7 = 1) : 3 ∣ a := by
  have key : ∀ q r : ℕ, 9 ^ (3 * q + r) % 7 = 9 ^ r % 7 := by
    intro q r
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod (9 ^ 3) q 7]
    norm_num
  have h2 : 9 ^ a % 7 = 9 ^ (a % 3) % 7 := by
    have := key (a / 3) (a % 3)
    rwa [Nat.div_add_mod] at this
  rw [h] at h2
  have hr : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  apply Nat.dvd_of_mod_eq_zero
  obtain ⟨r, hr_eq⟩ : ∃ r, a % 3 = r := ⟨_, rfl⟩
  rw [hr_eq] at h2 hr ⊢
  interval_cases r
  · rfl
  · exact absurd h2 (by norm_num)
  · exact absurd h2 (by norm_num)

theorem inf_range_ker_eq_bot {F V : Type*} [Field F] [CharP F 3] [AddCommGroup V] [Module F V]
    (Z : Module.End F V) (hZ : Z ^ 7 = 1) :
    LinearMap.range (Z - 1) ⊓ LinearMap.ker (Z - 1) = ⊥ := by
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h7 : (7 : F) = 1 := by linear_combination 2 * h3
  have hS : (∑ i ∈ Finset.range 7, Z ^ i) * (Z - 1) = 0 := by
    rw [geom_sum_mul, hZ, sub_self]
  have aux : ∀ w : V, Z w = w → (∑ i ∈ Finset.range 7, Z ^ i) w = w := by
    intro w hw
    have hpow : ∀ i : ℕ, (Z ^ i) w = w := fun i => by
      rw [Module.End.pow_apply]
      exact Function.iterate_fixed hw i
    rw [LinearMap.sum_apply]
    simp only [hpow, Finset.sum_const, Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul F, Nat.cast_ofNat, h7, one_smul]
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨⟨x, rfl⟩, hk⟩ := hv
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hk
  have h0 : (∑ i ∈ Finset.range 7, Z ^ i) ((Z - 1) x) = 0 := by
    rw [← Module.End.mul_apply, hS, LinearMap.zero_apply]
  rw [Submodule.mem_bot]
  exact (aux _ hk).symm.trans h0

theorem three_dvd_finrank_of_inf_ker_eq_bot {F V : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 9) [AddCommGroup V] [Module F V] [Module.Finite F V] [Finite V]
    (Z : Module.End F V) (hZ : Z ^ 7 = 1) (U : Submodule F V) (hU : ∀ u ∈ U, Z u ∈ U)
    (hK : U ⊓ LinearMap.ker (Z - 1) = ⊥) : 3 ∣ Module.finrank F U := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := natCard_modEq_inf_ker Z (p := 7) (k := 1) (by simpa using hZ) U hU
  have hU' : Nat.card U = 9 ^ Module.finrank F U := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF]
  have hbot : Nat.card (⊥ : Submodule F V) = 1 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF, finrank_bot, pow_zero]
  rw [hU', hK, hbot] at h
  have h' : 9 ^ Module.finrank F U % 7 = 1 := h
  exact three_dvd_of_nine_pow_mod_seven h'

theorem fix_of_finrank_le_one {F V : Type*} [Field F] [Finite F] (hF : Nat.card F = 9)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (K : Submodule F V)
    (hK : Module.finrank F K ≤ 1) (C : Module.End F V) (hC3 : C ^ 3 = 1)
    (hCK : ∀ v ∈ K, C v ∈ K) : ∀ v ∈ K, C v = v := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 9 := by rw [← hF, Nat.card_eq_fintype_card]
  have hcube : ∀ l : F, l ^ 3 = 1 → l = 1 := by
    intro l hl
    have h9 : l ^ 9 = l := by
      rw [← hcard]
      exact FiniteField.pow_card l
    calc l = l ^ 9 := h9.symm
      _ = (l ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hl, one_pow]
  by_cases hbot : K = ⊥
  · intro v hv
    rw [hbot, Submodule.mem_bot] at hv
    subst hv
    exact map_zero C
  · obtain ⟨k0, hk0K, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hspan : Submodule.span F {k0} = K := by
      apply Submodule.eq_of_le_of_finrank_le
      · exact (Submodule.span_singleton_le_iff_mem k0 K).2 hk0K
      · rw [finrank_span_singleton hk0]
        exact hK
    intro v hv
    rw [← hspan] at hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hCk0 : C k0 ∈ Submodule.span F {k0} := by
      rw [hspan]
      exact hCK k0 hk0K
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 hCk0
    have e1 : C (C k0) = l • (l • k0) := by
      rw [← hl, map_smul, hl]
    have e2 : C (C (C k0)) = l • (l • (l • k0)) := by
      rw [e1, map_smul, map_smul, hl]
    have hC3k0 : C (C (C k0)) = k0 := by
      have h := hC3
      rw [pow_three] at h
      have := congrArg (fun g : Module.End F V => g k0) h
      simpa [Module.End.mul_apply] using this
    have h4 : (l ^ 3) • k0 = k0 := by
      rw [pow_three, mul_smul, mul_smul]
      exact e2.symm.trans hC3k0
    have h5 : (l ^ 3 - 1) • k0 = 0 := by
      rw [sub_smul, one_smul, h4, sub_self]
    have hl3 : l ^ 3 = 1 := by
      rcases smul_eq_zero.1 h5 with h6 | h6
      · exact sub_eq_zero.1 h6
      · exact absurd h6 hk0
    have hl1 : l = 1 := hcube l hl3
    rw [map_smul, ← hl, hl1, one_smul]

theorem core_linear {F : Type*} [Field F] [Finite F] [CharP F 3] (hF : Nat.card F = 9) {n : ℕ}
    (hn : n = 3 ∨ n = 4) (Z C : Module.End F (Fin n → F)) (hZ7 : Z ^ 7 = 1) (hC3 : C ^ 3 = 1)
    (hZC : Z * C = C * Z) (hZ1 : Z ≠ 1) : C = 1 := by
  have hfin : Module.finrank F (Fin n → F) = n := by simp
  have hcomm : ∀ y, C (Z y) = Z (C y) := fun y => by
    have := congrArg (fun g : Module.End F (Fin n → F) => g y) hZC
    simp only [Module.End.mul_apply] at this
    exact this.symm
  obtain ⟨W, hWdef⟩ : ∃ W : Submodule F (Fin n → F), W = LinearMap.range (Z - 1) :=
    ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Submodule F (Fin n → F), K = LinearMap.ker (Z - 1) :=
    ⟨_, rfl⟩
  have memW : ∀ v, v ∈ W ↔ ∃ x, (Z - 1) x = v := fun v => by
    rw [hWdef]
    exact LinearMap.mem_range
  have memK : ∀ v, v ∈ K ↔ Z v = v := fun v => by
    rw [hKdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have hWZ : ∀ w ∈ W, Z w ∈ W := by
    intro w hw
    obtain ⟨x, rfl⟩ := (memW _).1 hw
    refine (memW _).2 ⟨Z x, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  have hWC : ∀ w ∈ W, C w ∈ W := by
    intro w hw
    obtain ⟨x, rfl⟩ := (memW _).1 hw
    refine (memW _).2 ⟨C x, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub, hcomm]
  have hKC : ∀ v ∈ K, C v ∈ K := by
    intro v hv
    rw [memK] at hv ⊢
    rw [← hcomm, hv]
  have hWK : W ⊓ K = ⊥ := by
    rw [hWdef, hKdef]
    exact inf_range_ker_eq_bot Z hZ7
  have hrank : Module.finrank F W + Module.finrank F K = n := by
    have h := LinearMap.finrank_range_add_finrank_ker (Z - 1)
    rw [hfin] at h
    rw [hWdef, hKdef]
    exact h
  have hW3 : 3 ∣ Module.finrank F W :=
    three_dvd_finrank_of_inf_ker_eq_bot hF Z hZ7 W hWZ (by rw [← hKdef]; exact hWK)
  have hWne : Module.finrank F W ≠ 0 := by
    intro h0
    rw [Submodule.finrank_eq_zero, hWdef, LinearMap.range_eq_bot] at h0
    exact hZ1 (sub_eq_zero.1 h0)
  have hW3' : Module.finrank F W = 3 := by omega
  have hK1 : Module.finrank F K ≤ 1 := by omega
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule F (Fin n → F), U = W ⊓ LinearMap.ker (C - 1) :=
    ⟨_, rfl⟩
  have memU : ∀ v, v ∈ U ↔ v ∈ W ∧ C v = v := fun v => by
    rw [hUdef, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
  have hWcount := natCard_modEq_inf_ker C (p := 3) (k := 1) (by simpa using hC3) W hWC
  rw [← hUdef] at hWcount
  have hUne : Module.finrank F U ≠ 0 := by
    intro h0
    have hc1 : Nat.card U = 1 := by
      rw [Module.natCard_eq_pow_finrank (K := F), hF, h0, pow_zero]
    have hc2 : Nat.card W = 729 := by
      rw [Module.natCard_eq_pow_finrank (K := F), hF, hW3']
      norm_num
    rw [hc1, hc2] at hWcount
    have h' : 729 % 3 = 1 % 3 := hWcount
    norm_num at h'
  have hUZ : ∀ u ∈ U, Z u ∈ U := by
    intro u hu
    obtain ⟨huW, huC⟩ := (memU u).1 hu
    refine (memU _).2 ⟨hWZ u huW, ?_⟩
    rw [hcomm, huC]
  have hUK : U ⊓ LinearMap.ker (Z - 1) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    have hvK : v ∈ K := by
      rw [hKdef]
      exact hv.2
    have hv' : v ∈ W ⊓ K := Submodule.mem_inf.2 ⟨((memU v).1 hv.1).1, hvK⟩
    rw [hWK] at hv'
    exact hv'
  have hU3 : 3 ∣ Module.finrank F U :=
    three_dvd_finrank_of_inf_ker_eq_bot hF Z hZ7 U hUZ hUK
  have hUW_le : U ≤ W := fun v hv => ((memU v).1 hv).1
  have hUle : Module.finrank F U ≤ Module.finrank F W := Submodule.finrank_mono hUW_le
  have hUW : U = W := by
    apply Submodule.eq_of_le_of_finrank_eq hUW_le
    omega
  have hWfix : ∀ w ∈ W, C w = w := by
    intro w hw
    have hwU : w ∈ U := by
      rw [hUW]
      exact hw
    exact ((memU w).1 hwU).2
  have hKfix : ∀ v ∈ K, C v = v := fix_of_finrank_le_one hF K hK1 C hC3 hKC
  have hKW : K ⊓ W = ⊥ := by
    rw [inf_comm]
    exact hWK
  have hsup : K ⊔ W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq K W
    rw [hKW, finrank_bot] at h
    rw [hfin]
    omega
  apply LinearMap.ext
  intro v
  have hv : v ∈ K ⊔ W := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, Module.End.one_apply, hKfix y hy, hWfix w hw]

theorem eq_one_of_commute_seven_three {F : Type} [Field F] [Fintype F] [CharP F 3]
    (hF : Fintype.card F = 9) {n : ℕ} (hn : n = 3 ∨ n = 4) (z c : GL (Fin n) F)
    (hz : z ^ 7 = 1) (hc : c ^ 3 = 1) (hzc : z * c = c * z) : z = 1 ∨ c = 1 := by
  have hF9 : Nat.card F = 9 := by rw [Nat.card_eq_fintype_card, hF]
  have hinj := (Matrix.toLinAlgEquiv' :
    Matrix (Fin n) (Fin n) F ≃ₐ[F] Module.End F (Fin n → F)).injective
  by_cases hz1 : z = 1
  · exact Or.inl hz1
  right
  have hZ7 : Matrix.toLinAlgEquiv' (z : Matrix (Fin n) (Fin n) F) ^ 7 = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]
  have hC3 : Matrix.toLinAlgEquiv' (c : Matrix (Fin n) (Fin n) F) ^ 3 = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
  have hZC : Matrix.toLinAlgEquiv' (z : Matrix (Fin n) (Fin n) F) *
      Matrix.toLinAlgEquiv' (c : Matrix (Fin n) (Fin n) F) =
      Matrix.toLinAlgEquiv' (c : Matrix (Fin n) (Fin n) F) *
      Matrix.toLinAlgEquiv' (z : Matrix (Fin n) (Fin n) F) := by
    rw [← map_mul, ← map_mul, ← Units.val_mul, ← Units.val_mul, hzc]
  have hZ1 : Matrix.toLinAlgEquiv' (z : Matrix (Fin n) (Fin n) F) ≠ 1 := by
    intro h
    apply hz1
    apply Units.ext
    rw [Units.val_one]
    apply hinj
    rw [map_one]
    exact h
  have hC := core_linear hF9 hn _ _ hZ7 hC3 hZC hZ1
  apply Units.ext
  rw [Units.val_one]
  apply hinj
  rw [map_one]
  exact hC

end LinAlg

section Groups

theorem noCommute37_projGenLin {F : Type} [Field F] [Fintype F] [CharP F 3]
    (hF : Fintype.card F = 9) {n : ℕ} (hn : n = 3 ∨ n = 4) :
    NoCommute37 (Matrix.ProjGenLinGroup (Fin n) F) := by
  classical
  intro y z hy hz hyz
  have hm : ∀ x ∈ Subgroup.center (GL (Fin n) F), x ^ 8 = 1 := by
    intro x hx
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hx
    obtain ⟨u, rfl⟩ := hx
    have hu : u ^ 8 = 1 := by
      have := pow_card_eq_one (G := Fˣ) (x := u)
      rwa [Fintype.card_units, hF] at this
    rw [← map_pow, hu, map_one]
  obtain ⟨a, b, ha, hb, hab⟩ := exists_commuting_of_quotient
    (Subgroup.center (GL (Fin n) F)) le_rfl hm (by norm_num) (by norm_num) z y hz hy hyz.symm
  have ha7 : a ^ 7 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  rcases eq_one_of_commute_seven_three hF hn a b ha7 hb3 hab with h | h
  · rw [h, orderOf_one] at ha
    norm_num at ha
  · rw [h, orderOf_one] at hb
    norm_num at hb

theorem noCommute37_projSL_three_nine : NoCommute37 (projSL 3 (GaloisField 3 2)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype (GaloisField 3 2) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 3 2) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 2 (by norm_num)]
    norm_num
  exact NoCommute37.of_le _ (noCommute37_projGenLin hF (Or.inl rfl))

theorem noCommute37_projSU_four_three : NoCommute37 (projSU 4 3 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype (GaloisField 3 (2 * 1)) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  exact NoCommute37.of_le _ (noCommute37_projGenLin hF (Or.inr rfl))

end Groups

end CFSG.RankThree.PartTwo.Sec8.Hering418
