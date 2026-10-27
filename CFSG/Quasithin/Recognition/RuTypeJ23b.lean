module

public import CFSG.Quasithin.Recognition.RuTypeJ23a
public import CFSG.Quasithin.Recognition.RuTypeSL3c

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type*} [Group G]

theorem exists_fixed_mem_coset {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x y : G} {N : Subgroup G} (hx : x ^ p = 1) (hxN : ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hy : y⁻¹ * (x * y * x⁻¹) ∈ N) (hN : ¬ p ∣ Nat.card N) :
    ∃ n ∈ N, x * (y * n) * x⁻¹ = y * n := by
  classical
  have hmem : ∀ n : N, y⁻¹ * (x * (y * n) * x⁻¹) ∈ N := fun n => by
    have e : y⁻¹ * (x * (y * n) * x⁻¹) = (y⁻¹ * (x * y * x⁻¹)) * (x * n * x⁻¹) := by group
    rw [e]
    exact N.mul_mem hy (hxN _ n.2)
  let f : N → N := fun n => ⟨_, hmem n⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h : y⁻¹ * (x * (y * a) * x⁻¹) = y⁻¹ * (x * (y * b) * x⁻¹) := congrArg Subtype.val hab
    apply Subtype.ext
    simpa using h
  have : Fintype N := Fintype.ofFinite N
  let σ : Equiv.Perm N := Equiv.ofBijective f hf.bijective_of_finite
  have hσk : ∀ (k : ℕ) (n : N), ((σ ^ k) n : G) = y⁻¹ * (x ^ k * (y * n) * (x ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => intro n; simp
    | succ k ih =>
      intro n
      rw [pow_succ', Equiv.Perm.mul_apply]
      show y⁻¹ * (x * (y * ((σ ^ k) n : G)) * x⁻¹) = _
      rw [ih n]
      group
  have hσp : σ ^ p ^ 1 = 1 := by
    rw [pow_one]
    refine Equiv.ext fun n => Subtype.ext ?_
    rw [hσk p n, hx]
    simp
  obtain ⟨n, hn⟩ := Equiv.Perm.exists_fixed_point_of_prime
    (by rwa [← Nat.card_eq_fintype_card]) hσp
  refine ⟨n, n.2, ?_⟩
  have h : y⁻¹ * (x * (y * n) * x⁻¹) = n := congrArg Subtype.val hn
  calc x * (y * n) * x⁻¹ = y * (y⁻¹ * (x * (y * n) * x⁻¹)) := by group
    _ = y * n := by rw [h]

theorem orderOf_conj_eq (a x : G) : orderOf (a * x * a⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq a (show a * x = a * x * a⁻¹ * a by group)).symm

theorem exists_nat_zpow {x : G} {n : ℕ} (hn : 0 < n) (hx : x ^ n = 1) (k : ℤ) :
    ∃ m : ℕ, x ^ k = x ^ m := by
  have hx' : x ^ (n : ℤ) = 1 := by rw [zpow_natCast, hx]
  refine ⟨(k % n).toNat, ?_⟩
  rw [zpow_eq_zpow_emod k hx', ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

namespace RuDataM

variable (M : RuDataM G) [Finite G]

omit [Finite G] in
theorem pow_S_eq_one {s : G} (hs : s ∈ ruS M.L) : s ^ (2 ^ 11) = 1 := by
  have h := orderOf_dvd_natCard (⟨s, hs⟩ : ruS M.L)
  rw [M.toRuData.card_S] at h
  have := orderOf_dvd_iff_pow_eq_one.mp h
  simpa using congrArg Subtype.val this

omit [Finite G] in
theorem exists_lift {g : SL(3, ZMod 2)} {n : ℕ} (hgn : g ^ n = 1) (hn : 2 ^ 12 % n = 1) :
    ∃ l : M.L, M.θ l = g ∧ (l : G) ^ n = 1 := by
  obtain ⟨l₀, hl₀⟩ := M.θ_surj g
  have hk : l₀ ^ n ∈ M.θ.ker := by rw [MonoidHom.mem_ker, map_pow, hl₀, hgn]
  rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
  have hS := M.pow_S_eq_one hk
  refine ⟨l₀ ^ (2 ^ 12), ?_, ?_⟩
  · rw [map_pow, hl₀]
    have : 2 ^ 12 = n * (2 ^ 12 / n) + 1 := by
      have := Nat.div_add_mod (2 ^ 12) n
      omega
    rw [this, pow_succ, pow_mul, hgn, one_pow, one_mul]
  · simp only [Subgroup.coe_pow]
    rw [← pow_mul, mul_comm, pow_mul, show 2 ^ 12 = 2 ^ 11 * 2 by norm_num, pow_mul]
    simp only [Subgroup.coe_pow] at hS
    rw [hS, one_pow]

abbrev Y7 : Subgroup G := pullL M.L M.θ (Subgroup.zpowers SL3.c0)

omit [Finite G] in
theorem card_Y7 : Nat.card M.Y7 = 2 ^ 11 * 7 := by
  rw [M.card_pullL, Nat.card_zpowers]
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [orderOf_eq_prime SL3.c0_pow_seven SL3.c0_ne_one]

theorem exists_conj_Y7 {P P' : Subgroup G} (hP : P ≤ M.Y7) (hP' : P' ≤ M.Y7)
    (h7 : Nat.card P = 7) (h7' : Nat.card P' = 7) :
    ∃ y ∈ M.Y7, ∀ x ∈ P, y * x * y⁻¹ ∈ P' := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfact : (Nat.card M.Y7).factorization 7 = 1 := by
    rw [M.card_Y7, Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_pow]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 2 by norm_num),
      Nat.Prime.factorization_self (show Nat.Prime 7 by norm_num)]
  let S1 : Sylow 7 M.Y7 := Sylow.ofCard (P.subgroupOf M.Y7) (by
    rw [card_subgroupOf_of_le hP, h7, hfact, pow_one])
  let S2 : Sylow 7 M.Y7 := Sylow.ofCard (P'.subgroupOf M.Y7) (by
    rw [card_subgroupOf_of_le hP', h7', hfact, pow_one])
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq M.Y7 S1 S2
  refine ⟨y, y.2, fun x hx => ?_⟩
  have hmem : (⟨x, hP hx⟩ : M.Y7) ∈ (S1 : Subgroup M.Y7) := Subgroup.mem_subgroupOf.mpr hx
  have : y * ⟨x, hP hx⟩ * y⁻¹ ∈ ((y • S1 : Sylow 7 M.Y7) : Subgroup M.Y7) := by
    rw [Sylow.coe_subgroup_smul]
    exact ⟨_, hmem, rfl⟩
  rw [hy] at this
  exact Subgroup.mem_subgroupOf.mp this

omit [Finite G] in
theorem zpow_mem_Y7 {l : M.L} (hl : M.θ l ∈ Subgroup.zpowers SL3.c0) (k : ℤ) :
    (l : G) ^ k ∈ M.Y7 := by
  refine mem_pullL.mpr ⟨(l ^ k).2, ?_⟩
  rw [show (⟨(l : G) ^ k, (l ^ k).2⟩ : M.L) = l ^ k from rfl, map_zpow]
  exact Subgroup.zpow_mem _ hl k

omit [Finite G] in
theorem zpowers_le_Y7 {l : M.L} (hl : M.θ l ∈ Subgroup.zpowers SL3.c0) :
    Subgroup.zpowers (l : G) ≤ M.Y7 := by
  rintro _ ⟨k, rfl⟩
  exact M.zpow_mem_Y7 hl k

theorem exists_B_B7 : ∃ (b c : M.L), M.θ b = SL3.b0 ∧ M.θ c = SL3.c0 ∧ (b : G) ^ 3 = 1 ∧
    (c : G) ^ 7 = 1 ∧ ∀ k : ℤ, (b : G) * c ^ k * (b : G)⁻¹ ∈ Subgroup.zpowers (c : G) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hc, hc7⟩ := M.exists_lift SL3.c0_pow_seven (by norm_num)
  obtain ⟨b₁, hb₁, -⟩ := M.exists_lift SL3.b0_pow_three (by norm_num)
  have hc1 : (c : G) ≠ 1 := fun h => SL3.c0_ne_one (by
    rw [← hc, show c = 1 from Subtype.ext h, map_one])
  have hcθ : M.θ c ∈ Subgroup.zpowers SL3.c0 := hc ▸ Subgroup.mem_zpowers _
  set c' : M.L := b₁ * c * b₁⁻¹
  have hc'θ : M.θ c' ∈ Subgroup.zpowers SL3.c0 := by
    show M.θ (b₁ * c * b₁⁻¹) ∈ _
    rw [map_mul, map_mul, map_inv, hb₁, hc, SL3.b0_c0]
    exact Subgroup.npow_mem_zpowers _ 2
  have hord : orderOf (c : G) = 7 := orderOf_eq_prime hc7 hc1
  have hcard : Nat.card (Subgroup.zpowers (c : G)) = 7 := by rw [Nat.card_zpowers, hord]
  have hcard' : Nat.card (Subgroup.zpowers (c' : G)) = 7 := by
    rw [Nat.card_zpowers]
    show orderOf ((b₁ : G) * c * (b₁ : G)⁻¹) = 7
    rw [orderOf_conj_eq, hord]
  obtain ⟨y, hyY, hy⟩ := M.exists_conj_Y7 (M.zpowers_le_Y7 hc'θ) (M.zpowers_le_Y7 hcθ) hcard'
    hcard
  obtain ⟨hyL, hyθ⟩ := mem_pullL.mp hyY
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hyθ
  set s : M.L := c ^ (-i) * ⟨y, hyL⟩
  have hsS : (s : G) ∈ ruS M.L := by
    have : s ∈ M.θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_zpow, hc, ← hi, zpow_neg, inv_mul_cancel]
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at this
    exact this
  set b₂ : M.L := s * b₁
  have hb₂θ : M.θ b₂ = SL3.b0 := by
    rw [map_mul, hb₁]
    have : s ∈ M.θ.ker := by
      rw [M.θ_ker, Subgroup.mem_subgroupOf]
      exact hsS
    rw [MonoidHom.mem_ker.mp this, one_mul]
  have hb₂c : (b₂ : G) * c * (b₂ : G)⁻¹ ∈ Subgroup.zpowers (c : G) := by
    have h1 := hy (c' : G) (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have e : (b₂ : G) * c * (b₂ : G)⁻¹ = (c : G) ^ (-i) * (y * c' * y⁻¹) * (c : G) ^ i := by
      simp only [b₂, s, c', Subgroup.coe_mul, Subgroup.coe_zpow, Subgroup.coe_inv]
      group
    rw [e, ← hk]
    group
  have hb₂ck : ∀ k : ℤ, (b₂ : G) * c ^ k * (b₂ : G)⁻¹ ∈ Subgroup.zpowers (c : G) := by
    intro k
    have : (b₂ : G) * c ^ k * (b₂ : G)⁻¹ = ((b₂ : G) * c * (b₂ : G)⁻¹) ^ k := by
      rw [conj_zpow]
    rw [this]
    exact Subgroup.zpow_mem _ hb₂c k
  refine ⟨b₂ ^ (2 ^ 12), c, ?_, hc, ?_, hc7, ?_⟩
  · rw [map_pow, hb₂θ]
    rw [show 2 ^ 12 = 3 * 1365 + 1 by norm_num, pow_succ, pow_mul, SL3.b0_pow_three, one_pow,
      one_mul]
  · have hk : b₂ ^ 3 ∈ M.θ.ker := by rw [MonoidHom.mem_ker, map_pow, hb₂θ, SL3.b0_pow_three]
    rw [M.θ_ker, Subgroup.mem_subgroupOf] at hk
    have hS := M.pow_S_eq_one hk
    simp only [Subgroup.coe_pow] at hS ⊢
    rw [← pow_mul, mul_comm, pow_mul, show 2 ^ 12 = 2 ^ 11 * 2 by norm_num, pow_mul, hS,
      one_pow]
  · intro k
    have key : ∀ n : ℕ, ∀ k : ℤ, ((b₂ : G) ^ n) * c ^ k * ((b₂ : G) ^ n)⁻¹ ∈
        Subgroup.zpowers (c : G) := by
      intro n
      induction n with
      | zero => intro k; simp only [pow_zero, one_mul, inv_one, mul_one]; exact
          Subgroup.zpow_mem_zpowers _ k
      | succ n ih =>
        intro k
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (ih k)
        have e : (b₂ : G) ^ (n + 1) * c ^ k * ((b₂ : G) ^ (n + 1))⁻¹ =
            (b₂ : G) * ((b₂ : G) ^ n * c ^ k * ((b₂ : G) ^ n)⁻¹) * (b₂ : G)⁻¹ := by group
        rw [e, ← hm]
        exact hb₂ck m
    simp only [Subgroup.coe_pow]
    exact key (2 ^ 12) k

@[expose] noncomputable def bel : M.L := M.exists_B_B7.choose

@[expose] noncomputable def cel : M.L := M.exists_B_B7.choose_spec.choose

theorem θ_bel : M.θ M.bel = SL3.b0 := M.exists_B_B7.choose_spec.choose_spec.1

theorem θ_cel : M.θ M.cel = SL3.c0 := M.exists_B_B7.choose_spec.choose_spec.2.1

theorem bel_pow_three : (M.bel : G) ^ 3 = 1 := M.exists_B_B7.choose_spec.choose_spec.2.2.1

theorem cel_pow_seven : (M.cel : G) ^ 7 = 1 := M.exists_B_B7.choose_spec.choose_spec.2.2.2.1

theorem bel_conj_cel (k : ℤ) :
    (M.bel : G) * (M.cel : G) ^ k * (M.bel : G)⁻¹ ∈ Subgroup.zpowers (M.cel : G) :=
  M.exists_B_B7.choose_spec.choose_spec.2.2.2.2 k

noncomputable abbrev B : Subgroup G := Subgroup.zpowers (M.bel : G)

noncomputable abbrev B7 : Subgroup G := Subgroup.zpowers (M.cel : G)

theorem cel_ne_one : (M.cel : G) ≠ 1 := fun h => SL3.c0_ne_one (by
  rw [← M.θ_cel, show M.cel = 1 from Subtype.ext h, map_one])

theorem bel_ne_one : (M.bel : G) ≠ 1 := fun h => SL3.b0_ne_one (by
  rw [← M.θ_bel, show M.bel = 1 from Subtype.ext h, map_one])

theorem orderOf_cel : orderOf (M.cel : G) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime M.cel_pow_seven M.cel_ne_one

theorem orderOf_bel : orderOf (M.bel : G) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime M.bel_pow_three M.bel_ne_one

theorem card_B7 : Nat.card M.B7 = 7 := by rw [Nat.card_zpowers, M.orderOf_cel]

theorem card_B : Nat.card M.B = 3 := by rw [Nat.card_zpowers, M.orderOf_bel]

theorem bel_mem_H : (M.bel : G) ∈ ruH M.T := by
  have : (M.bel : G) ∈ M.LT1 := mem_pullL.mpr ⟨M.bel.2, by rw [M.θ_bel]; exact SL3.b0_mem_Stab0⟩
  rw [← M.L_inf_H] at this
  exact this.2

theorem bel_inv_conj_cel (k : ℤ) :
    (M.bel : G)⁻¹ * (M.cel : G) ^ k * (M.bel : G) ∈ Subgroup.zpowers (M.cel : G) := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (M.bel_conj_cel k)
  obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp (M.bel_conj_cel m)
  have hb : (M.bel : G)⁻¹ = (M.bel : G) * (M.bel : G) := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three, M.bel_pow_three]
  have hb2 : (M.bel : G)⁻¹ * (M.bel : G)⁻¹ = M.bel := by
    calc (M.bel : G)⁻¹ * (M.bel : G)⁻¹ = (M.bel * M.bel) * (M.bel : G)⁻¹ := by rw [← hb]
      _ = M.bel := by group
  refine Subgroup.mem_zpowers_iff.mpr ⟨m', ?_⟩
  calc (M.cel : G) ^ m' = M.bel * (M.cel : G) ^ m * (M.bel : G)⁻¹ := hm'
    _ = M.bel * (M.bel * (M.cel : G) ^ k * (M.bel : G)⁻¹) * (M.bel : G)⁻¹ := by rw [hm]
    _ = (M.bel * M.bel) * (M.cel : G) ^ k * ((M.bel : G)⁻¹ * (M.bel : G)⁻¹) := by group
    _ = (M.bel : G)⁻¹ * (M.cel : G) ^ k * M.bel := by rw [← hb, hb2]

abbrev S0 : Subgroup G := ruS M.L ⊓ Subgroup.centralizer (M.B7 : Set G)

theorem mem_S0 {x : G} : x ∈ M.S0 ↔ x ∈ ruS M.L ∧ (M.cel : G) * x = x * M.cel := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, h _ (Subgroup.mem_zpowers _)⟩
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left h k).eq

theorem conj_cel_V (v : ruV M.L) :
    (M.cel : G) * v * (M.cel : G)⁻¹ = v ↔
      natAct3 SL3.c0 (Multiplicative.toAdd (M.ψV v)) = Multiplicative.toAdd (M.ψV v) := by
  rw [← M.θ_cel]
  exact M.toRuData.conj_eq_iff M.cel v

theorem eq_one_of_mem_S0_V {x : G} (hx : x ∈ M.S0) (hxV : x ∈ ruV M.L) : x = 1 := by
  obtain ⟨-, hc⟩ := M.mem_S0.mp hx
  have h : (M.cel : G) * (⟨x, hxV⟩ : ruV M.L) * (M.cel : G)⁻¹ = (⟨x, hxV⟩ : ruV M.L) := by
    show (M.cel : G) * x * (M.cel : G)⁻¹ = x
    rw [hc, mul_inv_cancel_right]
  have h0 := SL3.c0_fix_vec _ ((M.conj_cel_V ⟨x, hxV⟩).mp h)
  have : M.ψV ⟨x, hxV⟩ = 1 := Multiplicative.toAdd.injective h0
  have := congrArg Subtype.val (M.ψV.injective (this.trans (map_one M.ψV).symm))
  exact this

theorem χ_S0 {x : G} (hx : x ∈ M.S0) :
    Multiplicative.toAdd (M.χ ⟨x, (M.mem_S0.mp hx).1⟩) ∈ SL3.fixC0List := by
  obtain ⟨hxS, hc⟩ := M.mem_S0.mp hx
  have e := M.χ_equiv M.cel ⟨x, hxS⟩ ⟨x, hxS⟩ (by
    show x = (M.cel : G) * x * (M.cel : G)⁻¹
    rw [hc, mul_inv_cancel_right])
  rw [M.θ_cel] at e
  have := congrArg Multiplicative.toAdd e
  rw [toAdd_ofAdd] at this
  exact (SL3.fix_c0_iff _ (M.χ_trace _)).mp this.symm

theorem χ_S0_inj {x y : G} (hx : x ∈ M.S0) (hy : y ∈ M.S0)
    (h : M.χ ⟨x, (M.mem_S0.mp hx).1⟩ = M.χ ⟨y, (M.mem_S0.mp hy).1⟩) : x = y := by
  have hk : (⟨x, (M.mem_S0.mp hx).1⟩ : ruS M.L)⁻¹ * ⟨y, (M.mem_S0.mp hy).1⟩ ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h]
    exact inv_mul_cancel _
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  have h1 := M.eq_one_of_mem_S0_V (M.S0.mul_mem (M.S0.inv_mem hx) hy) hk
  rw [inv_mul_eq_one] at h1
  exact h1

theorem exists_S0_χ {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A ∈ SL3.fixC0List) :
    ∃ x, ∃ hx : x ∈ M.S0, Multiplicative.toAdd (M.χ ⟨x, (M.mem_S0.mp hx).1⟩) = A := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hA0, hAc, -⟩ := SL3.fixC0_props A hA
  obtain ⟨s, hs⟩ := M.χ_surj A hA0
  have hcs : (M.cel : G) * s * (M.cel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.cel.2) s).mp s.2
  have hsV : (s : G)⁻¹ * ((M.cel : G) * s * (M.cel : G)⁻¹) ∈ ruV M.L := by
    have e := M.χ_equiv M.cel s ⟨_, hcs⟩ rfl
    rw [M.θ_cel, hs, toAdd_ofAdd, hAc, ← hs] at e
    have hk : s⁻¹ * ⟨_, hcs⟩ ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, e]
      exact inv_mul_cancel _
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have hcV : ∀ v ∈ ruV M.L, (M.cel : G) * v * (M.cel : G)⁻¹ ∈ ruV M.L := fun v hv =>
    M.toRuData.conj_mem_V M.cel.2 hv
  have h7 : ¬ 7 ∣ Nat.card (ruV M.L) := by rw [M.toRuData.card_V]; norm_num
  obtain ⟨v, hv, hfix⟩ := exists_fixed_mem_coset M.cel_pow_seven hcV hsV h7
  have hsv : (s : G) * v ∈ ruS M.L := mul_mem s.2 (M.toRuData.V_le_S hv)
  have hmem : (s : G) * v ∈ M.S0 := M.mem_S0.mpr ⟨hsv, by
    calc (M.cel : G) * (s * v) = (M.cel : G) * (s * v) * (M.cel : G)⁻¹ * M.cel := by group
      _ = s * v * M.cel := by rw [hfix]⟩
  refine ⟨_, hmem, ?_⟩
  have e : (⟨(s : G) * v, (M.mem_S0.mp hmem).1⟩ : ruS M.L) = s * ⟨v, M.toRuData.V_le_S hv⟩ :=
    rfl
  have hv1 : M.χ ⟨v, M.toRuData.V_le_S hv⟩ = 1 := by
    have : (⟨v, M.toRuData.V_le_S hv⟩ : ruS M.L) ∈ M.χ.ker := by
      rw [M.χ_ker, Subgroup.mem_subgroupOf]
      exact hv
    exact this
  rw [e, map_mul, hv1, mul_one, hs, toAdd_ofAdd]

theorem card_S0 : Nat.card M.S0 = 4 := by
  classical
  let f : M.S0 → {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // A ∈ SL3.fixC0List} := fun x =>
    ⟨_, M.χ_S0 x.2⟩
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => ?_, fun A => ?_⟩
    · have h' := congrArg Subtype.val h
      exact Subtype.ext (M.χ_S0_inj x.2 y.2 (Multiplicative.toAdd.injective h'))
    · obtain ⟨x, hx, hxA⟩ := M.exists_S0_χ A.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxA⟩
  rw [Nat.card_eq_of_bijective f hf, Nat.card_eq_fintype_card]
  decide +kernel

theorem S0_elem : IsElemAbelian 2 M.S0 := by
  have hsq : ∀ x ∈ M.S0, x ^ 2 = 1 := by
    intro x hx
    have hxS := (M.mem_S0.mp hx).1
    have hx2 : x ^ 2 ∈ M.S0 := M.S0.pow_mem hx 2
    refine M.eq_one_of_mem_S0_V hx2 ?_
    have hk : (⟨x, hxS⟩ : ruS M.L) ^ 2 ∈ M.χ.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [pow_two, M.toAdd_χ_mul, toAdd_one]
      ext i j
      have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
      exact h2 _
    rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, hsq⟩
  have hx := x.2
  have hy := y.2
  have hxy : (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ M.S0 :=
    M.S0.mul_mem (M.S0.mul_mem (M.S0.mul_mem hx hy) (M.S0.inv_mem hx)) (M.S0.inv_mem hy)
  have h1 := M.eq_one_of_mem_S0_V hxy (M.comm_mem_V (M.mem_S0.mp hx).1 (M.mem_S0.mp hy).1)
  show (x : G) * y = y * x
  calc (x : G) * y = (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem bel_conj_S0 {x : G} (hx : x ∈ M.S0) : (M.bel : G) * x * (M.bel : G)⁻¹ ∈ M.S0 := by
  obtain ⟨hxS, hc⟩ := M.mem_S0.mp hx
  refine M.mem_S0.mpr ⟨(Subgroup.mem_normalizer_iff.mp
    (le_normalizer_pCoreOf 2 M.L M.bel.2) x).mp hxS, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (M.bel_inv_conj_cel 1)
  have hck : (M.cel : G) ^ k * x = x * (M.cel : G) ^ k := (Commute.zpow_left hc k).eq
  rw [zpow_one] at hk
  have e : (M.cel : G) = (M.bel : G) * (M.cel : G) ^ k * (M.bel : G)⁻¹ := by
    rw [hk]
    group
  rw [e]
  calc (M.bel : G) * (M.cel : G) ^ k * (M.bel : G)⁻¹ * ((M.bel : G) * x * (M.bel : G)⁻¹)
      = (M.bel : G) * ((M.cel : G) ^ k * x) * (M.bel : G)⁻¹ := by group
    _ = (M.bel : G) * (x * (M.cel : G) ^ k) * (M.bel : G)⁻¹ := by rw [hck]
    _ = (M.bel : G) * x * (M.bel : G)⁻¹ * ((M.bel : G) * (M.cel : G) ^ k * (M.bel : G)⁻¹) := by
        group

theorem eq_one_of_bel_fix {x : G} (hx : x ∈ M.S0) (hb : (M.bel : G) * x * (M.bel : G)⁻¹ = x) :
    x = 1 := by
  have hxS := (M.mem_S0.mp hx).1
  have e := M.χ_equiv M.bel ⟨x, hxS⟩ ⟨x, hxS⟩ hb.symm
  rw [M.θ_bel] at e
  have h := congrArg Multiplicative.toAdd e
  rw [toAdd_ofAdd] at h
  have h0 := (SL3.fixC0_props _ (M.χ_S0 hx)).2.2.2 h.symm
  refine M.eq_one_of_mem_S0_V hx ?_
  have hk : (⟨x, hxS⟩ : ruS M.L) ∈ M.χ.ker := by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
  rw [M.χ_ker, Subgroup.mem_subgroupOf] at hk
  exact hk

theorem commutator_S0_B : ⁅M.S0, M.B⁆ = M.S0 := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hbk : ∀ n : ℕ, ∀ y ∈ M.S0, (M.bel : G) ^ n * y * ((M.bel : G) ^ n)⁻¹ ∈ M.S0 := by
      intro n
      induction n with
      | zero => intro y hy; simpa using hy
      | succ n ih =>
        intro y hy
        have := M.bel_conj_S0 (ih y hy)
        rw [pow_succ']
        convert this using 1
        group
    obtain ⟨n, hn⟩ := exists_nat_zpow (by norm_num) M.bel_pow_three k
    have hmem := hbk n x⁻¹ (M.S0.inv_mem hx)
    rw [← hn] at hmem
    show x * (M.bel : G) ^ k * x⁻¹ * ((M.bel : G) ^ k)⁻¹ ∈ M.S0
    have e : x * (M.bel : G) ^ k * x⁻¹ * ((M.bel : G) ^ k)⁻¹ =
        x * ((M.bel : G) ^ k * x⁻¹ * ((M.bel : G) ^ k)⁻¹) := by group
    rw [e]
    exact M.S0.mul_mem hx hmem
  ·
    classical
    have hmem : ∀ x : M.S0, ⁅(x : G), (M.bel : G)⁆ ∈ M.S0 := fun x => by
      rw [commutatorElement_def]
      have e : (x : G) * M.bel * (x : G)⁻¹ * (M.bel : G)⁻¹ =
          (x : G) * ((M.bel : G) * (x : G)⁻¹ * (M.bel : G)⁻¹) := by group
      rw [e]
      exact M.S0.mul_mem x.2 (M.bel_conj_S0 (M.S0.inv_mem x.2))
    let f : M.S0 → M.S0 := fun x => ⟨_, hmem x⟩
    have hf : Function.Injective f := by
      intro x y h
      have h' : ⁅(x : G), (M.bel : G)⁆ = ⁅(y : G), (M.bel : G)⁆ := congrArg Subtype.val h
      rw [commutatorElement_def, commutatorElement_def] at h'
      have h2 : (x : G) * M.bel * (x : G)⁻¹ = (y : G) * M.bel * (y : G)⁻¹ := by
        have := congrArg (· * (M.bel : G)) h'
        simpa using this
      have hfix : (M.bel : G) * ((y : G)⁻¹ * x) * (M.bel : G)⁻¹ = (y : G)⁻¹ * x := by
        calc (M.bel : G) * ((y : G)⁻¹ * x) * (M.bel : G)⁻¹
            = (y : G)⁻¹ * ((y : G) * M.bel * (y : G)⁻¹) * x * (M.bel : G)⁻¹ := by group
          _ = (y : G)⁻¹ * ((x : G) * M.bel * (x : G)⁻¹) * x * (M.bel : G)⁻¹ := by rw [h2]
          _ = (y : G)⁻¹ * x := by group
      have := M.eq_one_of_bel_fix (M.S0.mul_mem (M.S0.inv_mem y.2) x.2) hfix
      rw [inv_mul_eq_one] at this
      exact Subtype.ext this.symm
    intro x hx
    obtain ⟨y, hy⟩ := Finite.surjective_of_injective hf ⟨x, hx⟩
    have : ⁅(y : G), (M.bel : G)⁆ = x := congrArg Subtype.val hy
    rw [← this]
    exact Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers _)

theorem lemma_J23_1 : ⁅M.S0, M.B⁆ = M.S0 ∧ Nat.card M.S0 = 4 ∧ IsElemAbelian 2 M.S0 :=
  ⟨M.commutator_S0_B, M.card_S0, M.S0_elem⟩

theorem lemma_J23_2 (g : G) : g * M.z * g⁻¹ ∉ M.S0 := by
  intro h
  obtain ⟨-, hc⟩ := M.mem_S0.mp h
  have hH : (g⁻¹ * M.cel * g : G) ∈ ruH M.T := by
    rw [M.mem_H_iff_comm]
    have e : M.z = g⁻¹ * (g * M.z * g⁻¹) * g := by group
    rw [e]
    calc g⁻¹ * (g * M.z * g⁻¹) * g * (g⁻¹ * M.cel * g)
        = g⁻¹ * ((g * M.z * g⁻¹) * M.cel) * g := by group
      _ = g⁻¹ * (M.cel * (g * M.z * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * M.cel * g * (g⁻¹ * (g * M.z * g⁻¹) * g) := by group
  have hdvd := Subgroup.orderOf_dvd_natCard (ruH M.T) hH
  have hord : orderOf (g⁻¹ * (M.cel : G) * g) = 7 := by
    rw [show g⁻¹ * (M.cel : G) * g = g⁻¹ * (M.cel : G) * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq,
      M.orderOf_cel]
  rw [hord, M.toRuData.card_H] at hdvd
  norm_num at hdvd

end RuDataM

end CFSG.Quasithin.RuType
