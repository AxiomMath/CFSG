module

public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofModel
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public section

namespace CFSG.RankThree.PartTwo.Sec14.ONLoc

open CFSG CFSG.RankThree

theorem false_of_commute_seven
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X Blueprint.NativeSporadic.ON) {w h : X} {k : ℕ}
    (hw : w ^ 3 ^ k = 1) (hwZ : w ∉ Subgroup.center X) (hh : orderOf h = 7)
    (hc : w * h = h * w) : False := by
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  have hw3 : w ^ 3 = 1 := Sec13.ON134.pow_three_eq_one ψ hw
  obtain ⟨K, hC, hinf, -, ρ, -, hρ⟩ := Sec15.Proof156Res4.exists_centralizer_eq ψ hw3 hwZ
  have hhC : h ∈ Subgroup.centralizer ({w} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.symm
  have hKC : K ≤ Subgroup.centralizer ({w} : Set X) := hC ▸ le_sup_right
  have hcomm : ∀ x ∈ K, x * w = w * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hKC hx)
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (K : Set X) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hcomm x hx, mul_inv_cancel_right]
      exact hx
    · intro hx
      have h1 := hcomm _ hx
      have e : x = w * x * w⁻¹ := by
        calc x = w⁻¹ * (w * x * w⁻¹) * w := by group
          _ = w⁻¹ * (w * (w * x * w⁻¹)) := by rw [mul_assoc, h1]
          _ = w * x * w⁻¹ := by group
      rw [e]
      exact hx
  rw [hC, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hwN] at hhC
  obtain ⟨a, ha, x, hx, rfl⟩ := Set.mem_mul.mp hhC
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hax : Commute (w ^ i) x := ((Commute.zpow_left (hcomm x hx).symm i))
  have h7 : (w ^ i * x) ^ 7 = 1 := by rw [← hh, pow_orderOf_eq_one]
  rw [hax.mul_pow] at h7
  have hx7 : x ^ 7 = 1 := by
    have hmem : x ^ 7 ∈ Subgroup.zpowers w ⊓ K := by
      refine Subgroup.mem_inf.mpr ⟨?_, pow_mem hx 7⟩
      have e : x ^ 7 = ((w ^ i) ^ 7)⁻¹ := eq_inv_of_mul_eq_one_right h7
      rw [e]
      exact inv_mem (pow_mem (Subgroup.zpow_mem_zpowers w i) 7)
    rw [hinf] at hmem
    exact hmem
  have hwi7 : (w ^ i) ^ 7 = 1 := by rw [hx7, mul_one] at h7; exact h7
  have hwi3 : (w ^ i) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
  have hwi : w ^ i = 1 := by
    calc w ^ i = (w ^ i) ^ 7 * ((w ^ i) ^ 3)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hwi7, hwi3, inv_one, one_pow, one_mul]
  have hρx : ρ ⟨x, hx⟩ = 1 := by
    have h1 : ρ ⟨x, hx⟩ ^ 7 = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : ↥K) ^ 7 = 1 := Subtype.ext hx7
      rw [this, map_one]
    have h2 : orderOf (ρ ⟨x, hx⟩) ∣ 7 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (ρ ⟨x, hx⟩) ∣ 720 := by
      have := orderOf_dvd_natCard (ρ ⟨x, hx⟩)
      rwa [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    have h4 : orderOf (ρ ⟨x, hx⟩) = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h2 with h | h
      · exact h
      · rw [h] at h3
        norm_num at h3
    exact orderOf_eq_one_iff.mp h4
  have hxZ : x ∈ Subgroup.center X := (hρ ⟨x, hx⟩).mp hρx
  have hx3 : x ^ 3 = 1 := by
    have h1 : (⟨x, hxZ⟩ : Subgroup.center X) ^ Nat.card (Subgroup.center X) = 1 :=
      pow_card_eq_one'
    rw [hT.1] at h1
    exact congrArg Subtype.val h1
  have hx1 : x = 1 := by
    calc x = x ^ 7 * (x ^ 3)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hx7, hx3, inv_one, one_pow, one_mul]
  rw [hwi, hx1, mul_one, orderOf_one] at hh
  norm_num at hh

theorem exists_seven_of_isTripleCover {Q : Type*} [Group Q]
    (htc : Sec4.IsTripleCover Q (alternatingGroup (Fin 7))) :
    ∃ v g : Q, v ^ 7 = 1 ∧ v ≠ 1 ∧ g * v * g⁻¹ = v ^ 2 := by
  obtain ⟨hZ3, ⟨θ⟩⟩ := htc
  have hZ : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : Subgroup.center Q) ^ Nat.card (Subgroup.center Q) = 1 :=
      pow_card_eq_one'
    rw [hZ3] at h1
    exact congrArg Subtype.val h1
  set c : alternatingGroup (Fin 7) := ⟨finRotate 7, Equiv.Perm.mem_alternatingGroup.mpr
    (by decide)⟩ with hc
  set t : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 1 2 * Equiv.swap 2 4 * Equiv.swap 3 6 * Equiv.swap 6 5,
      Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩ with ht
  have hc7 : c ^ 7 = 1 := Subtype.ext (by decide)
  have hc1 : c ≠ 1 := fun h0 => by
    have := congrArg Subtype.val h0
    revert this
    decide
  have htc' : t * c * t⁻¹ = c ^ 2 := Subtype.ext (by decide)
  have hc15 : c ^ 15 = c := by
    rw [show 15 = 7 * 2 + 1 by rfl, pow_succ, pow_mul, hc7, one_pow, one_mul]
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective (θ.symm c)
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (θ.symm t)
  have hz : x₀ ^ 7 ∈ Subgroup.center Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx₀, ← map_pow, hc7, map_one]
  set v := x₀ ^ 15 with hvdef
  have hv : (v : Q ⧸ Subgroup.center Q) = θ.symm c := by
    rw [hvdef, QuotientGroup.mk_pow, hx₀, ← map_pow, hc15]
  have hv7 : v ^ 7 = 1 := by
    rw [hvdef, ← pow_mul, show 15 * 7 = 7 * 3 * 5 by rfl, pow_mul, pow_mul, hZ _ hz, one_pow]
  have hv1 : v ≠ 1 := by
    intro h1
    apply hc1
    apply θ.symm.injective
    rw [← hv, h1, QuotientGroup.mk_one, map_one]
  refine ⟨v, g, hv7, hv1, ?_⟩
  set y := g * v * g⁻¹ with hy
  have hy7 : y ^ 7 = 1 := by rw [hy, conj_pow, hv7, mul_one, mul_inv_cancel]
  have hzy : (v ^ 2)⁻¹ * y ∈ Subgroup.center Q := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, hy, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hg, hv, ← map_inv, ← map_mul, ← map_mul, htc', ← map_pow,
      ← map_inv, ← map_mul, inv_mul_cancel, map_one]
  set z := (v ^ 2)⁻¹ * y with hzdef
  have hyz : y = v ^ 2 * z := by rw [hzdef]; group
  have hzc : ∀ q : Q, q * z = z * q := Subgroup.mem_center_iff.mp hzy
  have hz7 : z ^ 7 = 1 := by
    have h1 : y ^ 7 = (v ^ 2) ^ 7 * z ^ 7 := by
      rw [hyz]
      exact (show Commute (v ^ 2) z from hzc (v ^ 2)).mul_pow 7
    rw [hy7, ← pow_mul, show 2 * 7 = 7 * 2 by rfl, pow_mul, hv7, one_pow, one_mul] at h1
    exact h1.symm
  have hz1 : z = 1 := by
    have h2 := hZ z hzy
    calc z = z ^ 7 * (z ^ 3)⁻¹ ^ 2 := by group
      _ = 1 := by rw [hz7, h2, inv_one, one_pow, one_mul]
  rw [hyz, hz1, mul_one]

theorem exists_conj_mem_zpowers_seven {Q : Type*} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 7560) {v w : Q} (hv7 : v ^ 7 = 1) (hv1 : v ≠ 1) (hw7 : w ^ 7 = 1)
    (hw1 : w ≠ 1) : ∃ q : Q, q * w * q⁻¹ ∈ Subgroup.zpowers v := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hov : orderOf v = 7 := orderOf_eq_prime hv7 hv1
  have how : orderOf w = 7 := orderOf_eq_prime hw7 hw1
  have hpv : IsPGroup 7 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hov, pow_one])
  have hpw : IsPGroup 7 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, how, pow_one])
  have hidx : ∀ x : Q, orderOf x = 7 → ¬ 7 ∣ (Subgroup.zpowers x).index := by
    intro x hx
    have h := (Subgroup.zpowers x).index_mul_card
    rw [Nat.card_zpowers, hx, hQ] at h
    have h1 : (Subgroup.zpowers x).index = 1080 := by omega
    rw [h1]
    norm_num
  set Sv : Sylow 7 Q := hpv.toSylow (hidx v hov) with hSv
  set Sw : Sylow 7 Q := hpw.toSylow (hidx w how) with hSw
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq Q Sw Sv
  refine ⟨q, ?_⟩
  have hSv' : (Sv : Subgroup Q) = Subgroup.zpowers v := rfl
  have hSw' : (Sw : Subgroup Q) = Subgroup.zpowers w := rfl
  have h1 : (MulAut.conj q).toMonoidHom w ∈ (Sv : Subgroup Q) := by
    rw [← hq, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact Subgroup.mem_map_of_mem _ (by rw [hSw']; exact Subgroup.mem_zpowers w)
  rw [hSv'] at h1
  exact h1

noncomputable def extendHom {X Q : Type*} [Group X] [Group Q] {M : Subgroup X} (π : ↥M →* Q)
    (x : X) : Q := by
  classical
  exact if h : x ∈ M then π ⟨x, h⟩ else 1

section Extend

variable {X Q : Type*} [Group X] [Group Q] {M : Subgroup X} (π : ↥M →* Q)

theorem extendHom_of_mem {x : X} (hx : x ∈ M) : extendHom π x = π ⟨x, hx⟩ := by
  classical
  simp [extendHom, hx]

theorem extendHom_mul {x y : X} (hx : x ∈ M) (hy : y ∈ M) :
    extendHom π (x * y) = extendHom π x * extendHom π y := by
  rw [extendHom_of_mem π (mul_mem hx hy), extendHom_of_mem π hx, extendHom_of_mem π hy, ← map_mul]
  rfl

theorem extendHom_inv {x : X} (hx : x ∈ M) : extendHom π x⁻¹ = (extendHom π x)⁻¹ := by
  rw [extendHom_of_mem π (inv_mem hx), extendHom_of_mem π hx, ← map_inv]
  rfl

theorem extendHom_pow {x : X} (hx : x ∈ M) (n : ℕ) :
    extendHom π (x ^ n) = extendHom π x ^ n := by
  rw [extendHom_of_mem π (pow_mem hx n), extendHom_of_mem π hx, ← map_pow]
  rfl

theorem extendHom_conj {m x : X} (hm : m ∈ M) (hx : x ∈ M) :
    extendHom π (m * x * m⁻¹) = extendHom π m * extendHom π x * (extendHom π m)⁻¹ := by
  rw [extendHom_mul π (mul_mem hm hx) (inv_mem hm), extendHom_mul π hm hx, extendHom_inv π hm]

theorem mem_map_ker_iff {x : X} (hx : x ∈ M) :
    x ∈ π.ker.map M.subtype ↔ extendHom π x = 1 := by
  rw [extendHom_of_mem π hx]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hm
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem map_ker_le : π.ker.map M.subtype ≤ M := by
  rintro _ ⟨m, -, rfl⟩
  exact m.2

theorem le_normalizer_map_ker :
    M ≤ Subgroup.normalizer ((π.ker.map M.subtype : Subgroup X) : Set X) := by
  intro m hm
  refine Subgroup.mem_normalizer_iff.mpr fun x => ?_
  constructor
  · intro hx
    have hxM : x ∈ M := map_ker_le π hx
    have hc : m * x * m⁻¹ ∈ M := mul_mem (mul_mem hm hxM) (inv_mem hm)
    rw [mem_map_ker_iff π hc, extendHom_conj π hm hxM, (mem_map_ker_iff π hxM).mp hx, mul_one,
      mul_inv_cancel]
  · intro hx
    have hc : m * x * m⁻¹ ∈ M := map_ker_le π hx
    have hxM : x ∈ M := by
      have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hm) hc) hm
    rw [mem_map_ker_iff π hxM]
    have h1 := (mem_map_ker_iff π hc).mp hx
    rw [extendHom_conj π hm hxM] at h1
    have h2 : extendHom π x = (extendHom π m)⁻¹ * (extendHom π m * extendHom π x *
        (extendHom π m)⁻¹) * extendHom π m := by group
    rw [h2, h1, mul_one, inv_mul_cancel]

theorem extendHom_conj_congr {y x₁ x₂ : X} (hyM : y ∈ Subgroup.normalizer (M : Set X))
    (hyN : y ∈ Subgroup.normalizer ((π.ker.map M.subtype : Subgroup X) : Set X))
    (hx₁ : x₁ ∈ M) (hx₂ : x₂ ∈ M) (h : extendHom π x₁ = extendHom π x₂) :
    extendHom π (y * x₁ * y⁻¹) = extendHom π (y * x₂ * y⁻¹) := by
  have h12 : x₂⁻¹ * x₁ ∈ π.ker.map M.subtype := by
    rw [mem_map_ker_iff π (mul_mem (inv_mem hx₂) hx₁), extendHom_mul π (inv_mem hx₂) hx₁,
      extendHom_inv π hx₂, h, inv_mul_cancel]
  have hy12 : y * (x₂⁻¹ * x₁) * y⁻¹ ∈ π.ker.map M.subtype :=
    (Subgroup.mem_normalizer_iff.mp hyN _).mp h12
  have hc₂ : y * x₂ * y⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hyM _).mp hx₂
  have hcM : y * (x₂⁻¹ * x₁) * y⁻¹ ∈ M := map_ker_le π hy12
  have e : y * x₁ * y⁻¹ = y * x₂ * y⁻¹ * (y * (x₂⁻¹ * x₁) * y⁻¹) := by group
  rw [e, extendHom_mul π hc₂ hcM, (mem_map_ker_iff π hcM).mp hy12, mul_one]

end Extend

theorem conj_pow_two_pow {Q : Type*} [Group Q] {v g : Q} (hgv : g * v * g⁻¹ = v ^ 2) (i : ℕ) :
    g ^ i * v * (g ^ i)⁻¹ = v ^ 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc g ^ (i + 1) * v * (g ^ (i + 1))⁻¹ = g * (g ^ i * v * (g ^ i)⁻¹) * g⁻¹ := by group
      _ = g * v ^ 2 ^ i * g⁻¹ := by rw [ih]
      _ = (g * v * g⁻¹) ^ 2 ^ i := by rw [conj_pow]
      _ = v ^ 2 ^ (i + 1) := by rw [hgv, ← pow_mul, pow_succ, mul_comm]

theorem exists_two_pow_mul_sq_mod_seven {k : ℕ} (hk : k % 7 ≠ 0) :
    ∃ i : ℕ, 2 ^ i * (k * k) % 7 = 1 := by
  have key : ∀ r < 7, r ≠ 0 → ∃ i < 3, 2 ^ i * (r * r) % 7 = 1 := by decide
  obtain ⟨i, -, hi⟩ := key (k % 7) (Nat.mod_lt _ (by norm_num)) hk
  refine ⟨i, ?_⟩
  have hmod : 2 ^ i * (k * k) ≡ 2 ^ i * (k % 7 * (k % 7)) [MOD 7] :=
    Nat.ModEq.mul_left _ (Nat.ModEq.mul (Nat.mod_modEq k 7).symm (Nat.mod_modEq k 7).symm)
  rw [Nat.ModEq] at hmod
  rw [hmod, hi]

theorem pow_mul_inv_pow_mem {X : Type*} [Group X] {M : Subgroup X} {x y : X}
    (hx : x ∈ Subgroup.normalizer (M : Set X)) (hy : y * x⁻¹ ∈ M) (j : ℕ) :
    y ^ j * (x ^ j)⁻¹ ∈ M := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : y ^ (j + 1) * (x ^ (j + 1))⁻¹ = (y ^ j * (x ^ j)⁻¹) * (x ^ j * (y * x⁻¹) *
        (x ^ j)⁻¹) := by group
    rw [e]
    exact mul_mem ih ((Subgroup.mem_normalizer_iff.mp (pow_mem hx j) _).mp hy)

theorem mem_of_pow_mem_of_coprime {X : Type*} [Group X] {M : Subgroup X} {u : X} {s n : ℕ}
    (hu : u ^ 3 ^ s = 1) (hn : ¬ 3 ∣ n) (hun : u ^ n ∈ M) : u ∈ M := by
  have hdvd : orderOf u ∣ 3 ^ s := orderOf_dvd_of_pow_eq_one hu
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hcop : n.gcd (orderOf u) = 1 := by
    rw [ht]
    exact Nat.Coprime.pow_right t ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hn).symm
  have h1 : u ∈ Subgroup.zpowers (u ^ n) := mem_zpowers_pow_iff.mpr hcop
  exact Subgroup.zpowers_le.mpr hun h1

theorem mem_of_normalizes_seven {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    {M : Subgroup X} (π : ↥M →* Q) (hπ : Function.Surjective π)
    (hker : ¬ 3 ∣ Nat.card (π.ker.map M.subtype)) (hQ : Nat.card Q = 7560) {v g : Q}
    (hv7 : v ^ 7 = 1) (hv1 : v ≠ 1) (hgv : g * v * g⁻¹ = v ^ 2)
    (h21 : ∀ w h : X, w ∉ M → (∃ k : ℕ, w ^ 3 ^ k = 1) → orderOf h = 7 → w * h = h * w →
      False)
    {u : X} {s : ℕ} (hu : u ^ 3 ^ s = 1) (huM : u ∈ Subgroup.normalizer (M : Set X))
    (huN : u ∈ Subgroup.normalizer ((π.ker.map M.subtype : Subgroup X) : Set X)) : u ∈ M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  by_contra huM'
  set NM : Subgroup X := π.ker.map M.subtype with hNMdef
  set D : Subgroup X := Subgroup.normalizer (M : Set X) ⊓ Subgroup.normalizer (NM : Set X)
    with hDdef
  have hMD : M ≤ D := le_inf Subgroup.le_normalizer (le_normalizer_map_ker π)
  have huD : u ∈ D := ⟨huM, huN⟩
  have hconjM : ∀ y ∈ D, ∀ x ∈ M, y * x * y⁻¹ ∈ M := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp hy.1 x).mp hx
  have hcongr : ∀ y ∈ D, ∀ x₁ ∈ M, ∀ x₂ ∈ M, extendHom π x₁ = extendHom π x₂ →
      extendHom π (y * x₁ * y⁻¹) = extendHom π (y * x₂ * y⁻¹) := fun y hy x₁ hx₁ x₂ hx₂ h =>
    extendHom_conj_congr π hy.1 hy.2 hx₁ hx₂ h
  obtain ⟨v₀', hv₀'⟩ := hπ v
  obtain ⟨g₀', hg₀'⟩ := hπ g
  set v₀ : X := (v₀' : X) with hv₀def
  set g₀ : X := (g₀' : X) with hg₀def
  have hv₀M : v₀ ∈ M := v₀'.2
  have hg₀M : g₀ ∈ M := g₀'.2
  have hπv₀ : extendHom π v₀ = v := by rw [extendHom_of_mem π hv₀M]; exact hv₀'
  have hπg₀ : extendHom π g₀ = g := by rw [extendHom_of_mem π hg₀M]; exact hg₀'
  have huv₀M : u * v₀ * u⁻¹ ∈ M := hconjM u huD v₀ hv₀M
  have hv₀7 : v₀ ^ 7 ∈ NM := by
    rw [mem_map_ker_iff π (pow_mem hv₀M 7)]
    rw [extendHom_pow π hv₀M 7, hπv₀, hv7]
  have hw7 : extendHom π (u * v₀ * u⁻¹) ^ 7 = 1 := by
    rw [← extendHom_pow π huv₀M, conj_pow]
    have h1 : u * v₀ ^ 7 * u⁻¹ ∈ NM := (Subgroup.mem_normalizer_iff.mp huN _).mp hv₀7
    exact (mem_map_ker_iff π (map_ker_le π h1)).mp h1
  have hw1 : extendHom π (u * v₀ * u⁻¹) ≠ 1 := by
    intro h1
    have h2 : u * v₀ * u⁻¹ ∈ NM := (mem_map_ker_iff π huv₀M).mpr h1
    have h3 : v₀ ∈ NM := by
      have h4 := (Subgroup.mem_normalizer_iff.mp (inv_mem huN) _).mp h2
      rwa [show u⁻¹ * (u * v₀ * u⁻¹) * u⁻¹⁻¹ = v₀ by group] at h4
    apply hv1
    rw [← hπv₀]
    exact (mem_map_ker_iff π hv₀M).mp h3
  obtain ⟨q, hq⟩ := exists_conj_mem_zpowers_seven hQ hv7 hv1 hw7 hw1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, v ^ k = q * extendHom π (u * v₀ * u⁻¹) * q⁻¹ :=
    Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr hq)
  obtain ⟨m', hm'⟩ := hπ q
  set m : X := (m' : X) with hmdef
  have hmM : m ∈ M := m'.2
  have hπm : extendHom π m = q := by rw [extendHom_of_mem π hmM]; exact hm'
  set y : X := m * u with hydef
  have hyD : y ∈ D := mul_mem (hMD hmM) huD
  have hy : extendHom π (y * v₀ * y⁻¹) = v ^ k := by
    have e : y * v₀ * y⁻¹ = m * (u * v₀ * u⁻¹) * m⁻¹ := by rw [hydef]; group
    rw [e, extendHom_conj π hmM huv₀M, hπm, hk]
  have hk7 : k % 7 ≠ 0 := by
    intro h0
    have h1 : v ^ k = 1 := by
      rw [← pow_mod_orderOf, orderOf_eq_prime hv7 hv1, h0, pow_zero]
    rw [hk] at h1
    apply hw1
    have h2 : extendHom π (u * v₀ * u⁻¹) =
        q⁻¹ * (q * extendHom π (u * v₀ * u⁻¹) * q⁻¹) * q := by group
    rw [h2, h1, mul_one, inv_mul_cancel]
  have hyv₀M : y * v₀ * y⁻¹ ∈ M := hconjM y hyD v₀ hv₀M
  have hy2 : extendHom π ((y * y) * v₀ * (y * y)⁻¹) = v ^ (k * k) := by
    have e : (y * y) * v₀ * (y * y)⁻¹ = y * (y * v₀ * y⁻¹) * y⁻¹ := by group
    have h1 : extendHom π (y * v₀ * y⁻¹) = extendHom π (v₀ ^ k) := by
      rw [hy, show extendHom π (v₀ ^ k) = extendHom π v₀ ^ k from extendHom_pow π hv₀M k, hπv₀]
    rw [e, hcongr y hyD _ hyv₀M _ (pow_mem hv₀M k) h1, ← conj_pow,
      show extendHom π ((y * v₀ * y⁻¹) ^ k) = extendHom π (y * v₀ * y⁻¹) ^ k from
        extendHom_pow π hyv₀M k, hy,
      ← pow_mul]
  obtain ⟨i, hi⟩ := exists_two_pow_mul_sq_mod_seven hk7
  set y' : X := g₀ ^ i * (y * y) with hy'def
  have hy'D : y' ∈ D := mul_mem (hMD (pow_mem hg₀M i)) (mul_mem hyD hyD)
  have hyyM : (y * y) * v₀ * (y * y)⁻¹ ∈ M := hconjM (y * y) (mul_mem hyD hyD) v₀ hv₀M
  have hy' : extendHom π (y' * v₀ * y'⁻¹) = v := by
    have e : y' * v₀ * y'⁻¹ = g₀ ^ i * ((y * y) * v₀ * (y * y)⁻¹) * (g₀ ^ i)⁻¹ := by
      rw [hy'def]; group
    rw [e, extendHom_conj π (pow_mem hg₀M i) hyyM, hy2,
      show extendHom π (g₀ ^ i) = extendHom π g₀ ^ i from extendHom_pow π hg₀M i, hπg₀, ← conj_pow,
      conj_pow_two_pow hgv i, ← pow_mul, ← pow_mod_orderOf, orderOf_eq_prime hv7 hv1, hi,
      pow_one]
  have hpow : ∀ j : ℕ, y' ^ j * v₀ * (y' ^ j)⁻¹ ∈ M ∧
      extendHom π (y' ^ j * v₀ * (y' ^ j)⁻¹) = v := by
    intro j
    induction j with
    | zero => simp only [pow_zero, one_mul, inv_one, mul_one]; exact ⟨hv₀M, hπv₀⟩
    | succ j ih =>
      have e : y' ^ (j + 1) * v₀ * (y' ^ (j + 1))⁻¹ = y' * (y' ^ j * v₀ * (y' ^ j)⁻¹) * y'⁻¹ := by
        group
      rw [e]
      refine ⟨hconjM y' hy'D _ ih.1, ?_⟩
      rw [hcongr y' hy'D _ ih.1 _ hv₀M (ih.2.trans hπv₀.symm), hy']
  obtain ⟨a, n, hn3, horder⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y').ne' 3
    (by norm_num)
  set w₀ := y' ^ n with hw₀def
  have hw₀3 : w₀ ^ 3 ^ a = 1 := by
    rw [hw₀def, ← pow_mul, mul_comm, ← horder, pow_orderOf_eq_one]
  have hy'u : y' * (u * u)⁻¹ ∈ M := by
    have e : y' * (u * u)⁻¹ = g₀ ^ i * m * (u * m * u⁻¹) := by rw [hy'def, hydef]; group
    rw [e]
    exact mul_mem (mul_mem (pow_mem hg₀M i) hmM) (hconjM u huD m hmM)
  have hw₀M : w₀ ∉ M := by
    intro hw₀
    have h1 := pow_mul_inv_pow_mem (mul_mem huM huM) hy'u n
    have h2 : (u * u) ^ n ∈ M := by
      have e : (u * u) ^ n = (y' ^ n * ((u * u) ^ n)⁻¹)⁻¹ * y' ^ n := by group
      rw [e]
      exact mul_mem (inv_mem h1) hw₀
    rw [← pow_two, ← pow_mul] at h2
    exact huM' (mem_of_pow_mem_of_coprime hu (by omega) h2)
  have hpw₀ : ∀ j : ℕ, w₀ ^ j * v₀ * (w₀ ^ j)⁻¹ ∈ M ∧
      extendHom π (w₀ ^ j * v₀ * (w₀ ^ j)⁻¹) = v := by
    intro j
    rw [hw₀def, ← pow_mul]
    exact hpow (n * j)
  have hw₀D : w₀ ∈ D := pow_mem hy'D n
  have hp : IsPGroup 3 (Subgroup.zpowers w₀) :=
    IsPGroup.of_card (n := a) (by
      rw [Nat.card_zpowers]
      have h1 : orderOf w₀ ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hw₀3
      obtain ⟨b, hb, hb'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
      have h2 : orderOf y' = orderOf w₀ * n := by
        rw [hw₀def, orderOf_pow' y' (by omega : n ≠ 0)]
        have hg : (orderOf y').gcd n = n := Nat.gcd_eq_right ⟨3 ^ a, by rw [horder]; ring⟩
        rw [hg, Nat.div_mul_cancel ⟨3 ^ a, by rw [horder]; ring⟩]
      rw [horder, hb'] at h2
      have h3 : 3 ^ a = 3 ^ b := by
        have hn0 : 0 < n := by omega
        exact Nat.eq_of_mul_eq_mul_right hn0 h2
      rw [hb', h3])
  set α : ↥(Subgroup.zpowers w₀) →* MulAut X :=
    MulAut.conj.comp (Subgroup.zpowers w₀).subtype with hαdef
  have hinv : ∀ (b : ↥(Subgroup.zpowers w₀)) (x : X), x * v₀⁻¹ ∈ NM → α b x * v₀⁻¹ ∈ NM := by
    intro b x hx
    obtain ⟨j, hj⟩ : ∃ j : ℕ, w₀ ^ j = (b : X) :=
      Submonoid.mem_powers_iff _ _ |>.mp (mem_powers_iff_mem_zpowers.mpr b.2)
    have hxM : x ∈ M := by
      have e : x = x * v₀⁻¹ * v₀ := by group
      rw [e]
      exact mul_mem (map_ker_le π hx) hv₀M
    have hxv : extendHom π x = extendHom π v₀ := by
      have h1 := (mem_map_ker_iff π (mul_mem hxM (inv_mem hv₀M))).mp hx
      rw [extendHom_mul π hxM (inv_mem hv₀M), extendHom_inv π hv₀M] at h1
      exact mul_inv_eq_one.mp h1
    have hαb : α b x = w₀ ^ j * x * (w₀ ^ j)⁻¹ := by
      rw [hαdef, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply, hj]
    rw [hαb]
    have hw₀jD : w₀ ^ j ∈ D := pow_mem hw₀D j
    have hcM : w₀ ^ j * x * (w₀ ^ j)⁻¹ ∈ M := hconjM _ hw₀jD x hxM
    rw [mem_map_ker_iff π (mul_mem hcM (inv_mem hv₀M)), extendHom_mul π hcM (inv_mem hv₀M),
      extendHom_inv π hv₀M, hcongr _ hw₀jD x hxM v₀ hv₀M hxv, (hpw₀ j).2, hπv₀,
      mul_inv_cancel]
  obtain ⟨c, hcv, hcfix⟩ :=
    (Semidihedral.Principal.coprime_invariant_coset_fixed 3 hp α NM hker v₀).1 hinv
  have hcM : c ∈ M := by
    have e : c = c * v₀⁻¹ * v₀ := by group
    rw [e]
    exact mul_mem (map_ker_le π hcv) hv₀M
  have hπc : extendHom π c = v := by
    have h1 := (mem_map_ker_iff π (mul_mem hcM (inv_mem hv₀M))).mp hcv
    rw [extendHom_mul π hcM (inv_mem hv₀M), extendHom_inv π hv₀M, hπv₀] at h1
    exact mul_inv_eq_one.mp h1
  have h7c : 7 ∣ orderOf c := by
    have h1 : v ^ orderOf c = 1 := by
      rw [← hπc, ← extendHom_pow π hcM, pow_orderOf_eq_one]
      exact (mem_map_ker_iff π (one_mem M)).mp (one_mem _)
    rw [← orderOf_eq_prime hv7 hv1]
    exact orderOf_dvd_of_pow_eq_one h1
  set h := c ^ (orderOf c / 7) with hhdef
  have hh7 : orderOf h = 7 := orderOf_pow_orderOf_div (orderOf_pos c).ne' h7c
  have hcw : w₀ * c = c * w₀ := by
    have h1 := hcfix ⟨w₀, Subgroup.mem_zpowers w₀⟩
    rw [hαdef, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conj_apply] at h1
    calc w₀ * c = w₀ * c * w₀⁻¹ * w₀ := by group
      _ = c * w₀ := by rw [h1]
  have hhw : w₀ * h = h * w₀ := by
    rw [hhdef]
    exact (Commute.pow_right hcw _).eq
  exact h21 w₀ h hw₀M ⟨a, hw₀3⟩ hh7 hhw

end CFSG.RankThree.PartTwo.Sec14.ONLoc
