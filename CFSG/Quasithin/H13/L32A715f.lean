module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.H13.L32A714a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace Heis

variable {X : Type*} [Group X] (h : IsPOnePlusTwo 3 X)
include h

theorem fix_center_of_pow_odd (φ : MulAut X) {n : ℕ} (hn : Odd n) (hφ : φ ^ n = 1) :
    ∀ z ∈ Subgroup.center X, φ z = z := by
  rcases fix_or_inv_center h φ with hfix | hinv
  · exact hfix
  · intro z hz
    obtain ⟨k, rfl⟩ := hn
    have h2 : ∀ j : ℕ, (φ ^ (2 * j)) z = z := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, pow_succ, pow_succ]
        change (φ ^ (2 * j)) (φ (φ z)) = z
        rw [hinv z hz, map_inv, hinv z hz, inv_inv, ih]
    have h1 : (φ ^ (2 * k + 1)) z = z⁻¹ := by
      rw [pow_succ]
      change (φ ^ (2 * k)) (φ z) = z⁻¹
      rw [hinv z hz, map_inv, h2 k]
    rw [hφ] at h1
    have hz1 : z = 1 := eq_one_of_eq_inv h h1
    rw [hz1, map_one]

theorem eq_one_of_pow_prime {φ : MulAut X} {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hφ : φ ^ p ^ e = 1) : φ = 1 := by
  have := finite h
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ e) := (hp.odd_of_ne_two (by omega)).pow
  have hZ := fix_center_of_pow_odd h φ hodd hφ
  have hP : IsPGroup p ↥(Subgroup.zpowers φ) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨e, Subtype.ext ?_⟩
    change (φ ^ n) ^ p ^ e = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hφ, one_zpow]
  let F : Subgroup X :=
    { carrier := {x | φ x = x}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [map_mul, hx, hy]
      one_mem' := map_one φ
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [map_inv, hx] }
  have hFix : MulAction.fixedPoints ↥(Subgroup.zpowers φ) X = (F : Set X) := by
    ext x
    rw [MulAction.mem_fixedPoints]
    constructor
    · intro hx
      exact hx ⟨φ, Subgroup.mem_zpowers φ⟩
    · intro hx g
      have hle : Subgroup.zpowers φ ≤ MulAction.stabilizer (MulAut X) x :=
        (Subgroup.zpowers_le).mpr (MulAction.mem_stabilizer_iff.mpr hx)
      exact MulAction.mem_stabilizer_iff.mp (hle g.2)
  have hmod := hP.card_modEq_card_fixedPoints X
  rw [hFix, card_eq h] at hmod
  have hFcard : Nat.card ↥F = 27 := by
    have hdvd : Nat.card ↥F ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = Nat.card X by rw [card_eq h]; norm_num]
      exact Subgroup.card_subgroup_dvd_card F
    obtain ⟨k, hk, hkF⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hZF : Subgroup.center X ≤ F := fun z hz => hZ z hz
    have h3 : 3 ∣ Nat.card ↥F := card_center h ▸ Subgroup.card_dvd_of_le hZF
    change 27 ≡ Nat.card ↥F [MOD p] at hmod
    rw [hkF] at hmod h3 ⊢
    interval_cases k
    · norm_num at h3
    · exfalso
      have h24 : p ∣ 2 ^ 3 * 3 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
      rcases (Nat.Prime.dvd_mul hp).mp h24 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h2)
        omega
      · have := Nat.le_of_dvd (by norm_num) h3
        omega
    · exfalso
      have h18 : p ∣ 2 * 3 ^ 2 := (Nat.modEq_iff_dvd' (by norm_num)).mp hmod.symm
      rcases (Nat.Prime.dvd_mul hp).mp h18 with h2 | h3
      · have := Nat.le_of_dvd (by norm_num) h2
        omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h3)
        omega
    · norm_num
  have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F (by rw [hFcard, card_eq h])
  ext x
  have hx : x ∈ F := hFtop ▸ Subgroup.mem_top x
  exact hx

theorem exists_mem_fixMod_of_pow {φ : MulAut X} {m : ℕ} (hφ : φ ^ 3 ^ m = 1) :
    ∃ a : X, a ∉ Subgroup.center X ∧ φ a * a⁻¹ ∈ Subgroup.center X := by
  have := finite h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hI
  have hconj : ∀ (ψ : MulAut X) (a : X), ψ * MulAut.conj a * ψ⁻¹ = MulAut.conj (ψ a) := by
    intro ψ a
    ext x
    change ψ (a * ψ⁻¹ x * a⁻¹) = ψ a * x * (ψ a)⁻¹
    rw [map_mul, map_mul, map_inv]
    congr 2
    exact ψ.apply_symm_apply x
  have hIn : I.Normal := ⟨fun n hn ψ => by
    obtain ⟨a, rfl⟩ := hn
    exact ⟨ψ a, (hconj ψ a).symm⟩⟩
  have hX3 : IsPGroup 3 X := IsPGroup.of_card h.2.1
  have hI3 : IsPGroup 3 ↥I := by
    rw [hI, MonoidHom.range_eq_map]
    exact (hX3.to_subgroup ⊤).map _
  have hφ3 : IsPGroup 3 ↥(Subgroup.zpowers φ) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨m, Subtype.ext ?_⟩
    change (φ ^ n) ^ 3 ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hφ, one_zpow]
  set P := I ⊔ Subgroup.zpowers φ with hP
  have hP3 : IsPGroup 3 ↥P := hI3.to_sup_of_normal_left hφ3
  have : Group.IsNilpotent ↥P := hP3.isNilpotent
  set N := I.subgroupOf P with hN
  have : N.Normal := Subgroup.Normal.subgroupOf hIn P
  have hconj1 : ∀ a : X, MulAut.conj a = 1 → a ∈ Subgroup.center X := by
    intro a ha
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have h1 := congrArg (fun ψ : MulAut X => ψ g) ha
    change a * g * a⁻¹ = g at h1
    calc g * a = a * g * a⁻¹ * a := by rw [h1]
      _ = a * g := by group
  have hNne : N ≠ ⊥ := by
    obtain ⟨b, hb⟩ : ∃ b : X, b ∉ Subgroup.center X := by
      by_contra hno
      push Not at hno
      exact center_ne_top h (eq_top_iff.mpr fun x _ => hno x)
    intro hbot
    have hmem : (⟨MulAut.conj b, le_sup_left (a := I) ⟨b, rfl⟩⟩ : ↥P) ∈ N :=
      Subgroup.mem_subgroupOf.mpr ⟨b, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hb (hconj1 b (congrArg Subtype.val hmem))
  obtain ⟨⟨n, hnNZ⟩, hn1'⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hNne))
  have hn1 : n ≠ 1 := fun e => hn1' (Subtype.ext e)
  obtain ⟨hnN, hnZ⟩ := hnNZ
  obtain ⟨a, ha⟩ := Subgroup.mem_subgroupOf.mp hnN
  have hφP : φ ∈ P := le_sup_right (a := I) (Subgroup.mem_zpowers φ)
  refine ⟨a, fun haZ => ?_, ?_⟩
  · apply hn1
    apply Subtype.ext
    rw [Subgroup.coe_one, ← ha]
    ext x
    change a * x * a⁻¹ = x
    rw [(Subgroup.mem_center_iff.mp haZ x).symm, mul_inv_cancel_right]
  · have hcomm := Subgroup.mem_center_iff.mp hnZ ⟨φ, hφP⟩
    have h2 : φ * MulAut.conj a = MulAut.conj a * φ := by
      have := congrArg Subtype.val hcomm
      simp only [Subgroup.coe_mul] at this
      rw [ha]
      exact this
    have h3 : MulAut.conj (φ a) = MulAut.conj a := by
      rw [← hconj, h2, mul_inv_cancel_right]
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have h4 := congrArg (fun ψ : MulAut X => ψ (a⁻¹ * g * a)) h3
    change φ a * (a⁻¹ * g * a) * (φ a)⁻¹ = a * (a⁻¹ * g * a) * a⁻¹ at h4
    calc g * (φ a * a⁻¹) = a * (a⁻¹ * g * a) * a⁻¹ * (φ a * a⁻¹) := by group
      _ = φ a * (a⁻¹ * g * a) * (φ a)⁻¹ * (φ a * a⁻¹) := by rw [h4]
      _ = φ a * a⁻¹ * g := by group

theorem exists_conj_eq_mul {a : X} (ha : a ∉ Subgroup.center X) {w : X}
    (hw : w ∈ Subgroup.center X) : ∃ b : X, b * a * b⁻¹ = w * a := by
  obtain ⟨b₀, hb₀⟩ := exists_comm_ne_one_of_not_mem ha
  have hc : ⁅b₀, a⁆ ∈ Subgroup.center X := comm_mem_center h b₀ a
  have hc1 : ⁅b₀, a⁆ ≠ 1 := by
    rw [← commutatorElement_inv, ne_eq, inv_eq_one]
    exact hb₀
  have hpow : ∀ k : ℕ, ⁅b₀ ^ k, a⁆ = ⁅b₀, a⁆ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, comm_mul_left h, ih, pow_succ]
  have hwz : w ∈ Subgroup.zpowers ⁅b₀, a⁆ := (center_eq_zpowers h hc hc1).symm ▸ hw
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hwz
  obtain ⟨k, -, hk⟩ := exists_pow_lt_three_of_zpow (pow_three_eq h ⁅b₀, a⁆) n
  refine ⟨b₀ ^ k, ?_⟩
  have e := hpow k
  rw [← hk, hn] at e
  rw [← e, commutatorElement_def]
  group

end Heis

section Gen

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem conj_center_of_pow_odd {X : Subgroup Γ} [X.Normal] (hX : IsPOnePlusTwo 3 ↥X) {g : Γ}
    {n : ℕ} (hn : Odd n) (hg : g ^ n = 1) {z : Γ}
    (hz : z ∈ (Subgroup.center ↥X).map X.subtype) : g * z * g⁻¹ = z := by
  obtain ⟨z', hz', rfl⟩ := hz
  have h1 := Heis.fix_center_of_pow_odd hX (MulAut.conjNormal g : MulAut ↥X) hn
    (by rw [← map_pow, hg, map_one]) z' hz'
  have := congrArg Subtype.val h1
  rw [MulAut.conjNormal_apply] at this
  exact this

omit [Finite Γ] in
theorem comm_of_pow_prime {X : Subgroup Γ} [X.Normal] (hX : IsPOnePlusTwo 3 ↥X) {g : Γ}
    {p e : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hg : g ^ p ^ e = 1) :
    ∀ x ∈ X, g * x * g⁻¹ = x := by
  have h1 : (MulAut.conjNormal g : MulAut ↥X) = 1 :=
    Heis.eq_one_of_pow_prime hX hp hp5 (by rw [← map_pow, hg, map_one])
  intro x hx
  have := congrArg (fun φ : MulAut ↥X => ((φ ⟨x, hx⟩ : ↥X) : Γ)) h1
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
  exact this

omit [Finite Γ] in
theorem exists_comm_mul {X : Subgroup Γ} [X.Normal] (hX : IsPOnePlusTwo 3 ↥X) {y : Γ} {m : ℕ}
    (hy : y ^ 3 ^ m = 1) :
    ∃ a ∈ X, a ∉ (Subgroup.center ↥X).map X.subtype ∧ ∃ b ∈ X, b * y * a = a * (b * y) := by
  set φ : MulAut ↥X := MulAut.conjNormal y with hφ
  have hφ3 : φ ^ 3 ^ m = 1 := by rw [hφ, ← map_pow, hy, map_one]
  obtain ⟨a, haZ, hfa⟩ := Heis.exists_mem_fixMod_of_pow hX hφ3
  obtain ⟨b, hb⟩ := Heis.exists_conj_eq_mul hX haZ (Subgroup.inv_mem _ hfa)
  refine ⟨a, a.2, fun ⟨a', ha', he⟩ => haZ (Subtype.ext he ▸ ha'), b, b.2, ?_⟩
  have hya : ((φ a : ↥X) : Γ) = y * a * y⁻¹ := MulAut.conjNormal_apply y a
  have hbz : b * φ a * b⁻¹ = a := by
    have hzc : ∀ x : ↥X, x * (φ a * a⁻¹) = (φ a * a⁻¹) * x :=
      fun x => (Subgroup.mem_center_iff.mp hfa x)
    calc b * φ a * b⁻¹ = b * ((φ a * a⁻¹) * a) * b⁻¹ := by group
      _ = (φ a * a⁻¹) * (b * a * b⁻¹) := by
        rw [show b * ((φ a * a⁻¹) * a) * b⁻¹ = (b * (φ a * a⁻¹)) * a * b⁻¹ by group, hzc b]
        group
      _ = a := by rw [hb]; group
  have := congrArg Subtype.val hbz
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hya] at this
  calc (b : Γ) * y * a = (b : Γ) * (y * a * y⁻¹) * (b : Γ)⁻¹ * ((b : Γ) * y) := by group
    _ = a * ((b : Γ) * y) := by rw [this]

end Gen

end CFSG.Quasithin.H13.L32A
