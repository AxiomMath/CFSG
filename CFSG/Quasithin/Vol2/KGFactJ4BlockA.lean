module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.H13.Ch4.J4Blk

variable {Γ : Type*} [Group Γ]

@[reducible] noncomputable def conjActOn {P E : Subgroup Γ}
    (hPE : P ≤ Subgroup.normalizer (E : Set Γ)) : MulAction ↥P ↥E where
  smul p e := ⟨(p : Γ) * e * (p : Γ)⁻¹, (Subgroup.mem_normalizer_iff.mp (hPE p.2) e).mp e.2⟩
  one_smul e := Subtype.ext (by change (1 : Γ) * e * (1 : Γ)⁻¹ = e; group)
  mul_smul p q e := Subtype.ext (by
    change (p : Γ) * q * e * ((p : Γ) * q)⁻¹ = (p : Γ) * ((q : Γ) * e * (q : Γ)⁻¹) * (p : Γ)⁻¹
    group)

theorem card_fixedBy_eq {P E : Subgroup Γ} (hPE : P ≤ Subgroup.normalizer (E : Set Γ)) (p : ↥P) :
    letI := conjActOn hPE
    Nat.card (MulAction.fixedBy ↥E p) =
      Nat.card ↥(E ⊓ Subgroup.centralizer ({(p : Γ)} : Set Γ)) := by
  let _ : MulAction ↥P ↥E := conjActOn hPE
  refine Nat.card_congr ⟨fun e => ⟨e.1, e.1.2, ?_⟩, fun e => ⟨⟨e.1, e.2.1⟩, ?_⟩, fun _ => rfl,
    fun _ => rfl⟩
  · show (e.1 : Γ) ∈ Subgroup.centralizer ({(p : Γ)} : Set Γ)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val e.2
    change (p : Γ) * e.1 * (p : Γ)⁻¹ = e.1 at h
    calc (e.1 : Γ) * p = (p : Γ) * e.1 * (p : Γ)⁻¹ * p := by rw [h]
      _ = p * e.1 := by group
  · apply Subtype.ext
    change (p : Γ) * e.1 * (p : Γ)⁻¹ = e.1
    rw [(Subgroup.mem_centralizer_singleton_iff.mp e.2.2).symm]
    group

variable [Finite Γ]

theorem card_inf_centralizer_set_modEq {p : ℕ} [Fact p.Prime] {P E : Subgroup Γ}
    (hP : IsPGroup p ↥P) (hPE : P ≤ Subgroup.normalizer (E : Set Γ)) :
    Nat.card E ≡ Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set Γ)) [MOD p] := by
  let _ : MulAction ↥P ↥E := conjActOn hPE
  have h := hP.card_modEq_card_fixedPoints (α := ↥E)
  have heq : Nat.card ↥(MulAction.fixedPoints ↥P ↥E) =
      Nat.card ↥(E ⊓ Subgroup.centralizer (P : Set Γ)) := by
    refine Nat.card_congr ⟨fun e => ⟨e.1, e.1.2, ?_⟩,
      fun e => ⟨⟨e.1, e.2.1⟩, fun g => ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · show (e.1 : Γ) ∈ Subgroup.centralizer (P : Set Γ)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := congrArg Subtype.val (e.2 ⟨g, hg⟩)
      change g * e.1 * g⁻¹ = e.1 at h1
      calc g * (e.1 : Γ) = g * e.1 * g⁻¹ * g := by group
        _ = e.1 * g := by rw [h1]
    · apply Subtype.ext
      change (g : Γ) * e.1 * (g : Γ)⁻¹ = e.1
      rw [Subgroup.mem_centralizer_iff.mp e.2.2 g g.2, mul_inv_cancel_right]
  rw [← heq]
  exact h

theorem inf_centralizer_ne_bot {p : ℕ} [Fact p.Prime] {P E : Subgroup Γ} (hP : IsPGroup p ↥P)
    (hPE : P ≤ Subgroup.normalizer (E : Set Γ)) (hpE : p ∣ Nat.card E) :
    E ⊓ Subgroup.centralizer (P : Set Γ) ≠ ⊥ := by
  intro h
  have hmod := card_inf_centralizer_set_modEq hP hPE
  rw [h, Subgroup.card_bot] at hmod
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_zero_of_dvd hpE, Nat.mod_eq_of_lt (Fact.out : p.Prime).one_lt] at hmod
  exact zero_ne_one hmod

theorem card_inf_centralizer_modEq {E : Subgroup Γ} {x : Γ}
    (hx : IsPGroup 3 ↥(Subgroup.zpowers x))
    (hxE : x ∈ Subgroup.normalizer (E : Set Γ)) :
    Nat.card E ≡ Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set Γ)) [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set Γ) :=
    Subgroup.zpowers_le.mpr hxE
  let _ : MulAction ↥(Subgroup.zpowers x) ↥E := conjActOn hle
  have h := hx.card_modEq_card_fixedPoints (α := ↥E)
  have heq : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥E) =
      Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set Γ)) := by
    refine Nat.card_congr ⟨fun e => ⟨e.1, e.1.2, ?_⟩,
      fun e => ⟨⟨e.1, e.2.1⟩, fun g => ?_⟩, fun _ => rfl, fun _ => rfl⟩
    · show (e.1 : Γ) ∈ Subgroup.centralizer ({x} : Set Γ)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := congrArg Subtype.val (e.2 ⟨x, Subgroup.mem_zpowers x⟩)
      change x * e.1 * x⁻¹ = e.1 at h1
      calc (e.1 : Γ) * x = x * e.1 * x⁻¹ * x := by rw [h1]
        _ = x * e.1 := by group
    · obtain ⟨g, k, hk⟩ := g
      apply Subtype.ext
      change g * e.1 * g⁻¹ = e.1
      have hc : Commute x (e.1 : Γ) := (Subgroup.mem_centralizer_singleton_iff.mp e.2.2).symm
      rw [← hk, (hc.zpow_left k).eq, mul_inv_cancel_right]
  rw [← heq]
  exact h

theorem exists_four_le_card_inf_centralizer {P E : Subgroup Γ} (hP : IsPGroup 3 ↥P)
    (hPE : P ≤ Subgroup.normalizer (E : Set Γ)) {c : ℕ} (hc : Nat.card E % 3 = c) (hc0 : c ≠ 0)
    (hdvd : ¬ Nat.card P ∣ Nat.card E + (Nat.card P - 1) * c) :
    ∃ x ∈ P, x ≠ 1 ∧ 4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set Γ)) := by
  classical
  by_contra hne
  push Not at hne
  have hfix : ∀ x ∈ P, x ≠ 1 → Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set Γ)) = c := by
    intro x hx hx1
    have hxp : IsPGroup 3 ↥(Subgroup.zpowers x) := hP.to_le (Subgroup.zpowers_le.mpr hx)
    have hmod := card_inf_centralizer_modEq hxp (hPE hx)
    have hlt := hne x hx hx1
    have hpos : 0 < Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set Γ)) := Nat.card_pos
    unfold Nat.ModEq at hmod
    rw [hc] at hmod
    have hc3 : c < 3 := hc ▸ Nat.mod_lt _ (by norm_num)
    omega
  let _ : MulAction ↥P ↥E := conjActOn hPE
  have : Fintype ↥P := Fintype.ofFinite _
  have : Fintype ↥E := Fintype.ofFinite _
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (G := ↥P) (X := ↥E)
  have hsum : ∑ p : ↥P, Fintype.card (MulAction.fixedBy ↥E p) =
      Nat.card E + (Nat.card P - 1) * c := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : ↥P))]
    have h1 : Fintype.card (MulAction.fixedBy ↥E (1 : ↥P)) = Nat.card E := by
      have hu : MulAction.fixedBy ↥E (1 : ↥P) = Set.univ :=
        Set.eq_univ_of_forall fun e => MulAction.mem_fixedBy.mpr (one_smul _ e)
      rw [← Nat.card_eq_fintype_card, hu, Nat.card_univ]
    have h2 : ∀ p ∈ (Finset.univ : Finset ↥P).erase 1,
        Fintype.card (MulAction.fixedBy ↥E p) = c := by
      intro p hp
      have hp1 : p ≠ 1 := Finset.ne_of_mem_erase hp
      rw [← Nat.card_eq_fintype_card, card_fixedBy_eq hPE p]
      exact hfix p p.2 fun h => hp1 (Subtype.ext h)
    rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
  apply hdvd
  rw [← hsum, hB, Nat.card_eq_fintype_card]
  exact Dvd.intro_left _ rfl

theorem exists_orderOf_three_four_le_card {P E : Subgroup Γ} (hP : IsPGroup 3 ↥P)
    (hPE : P ≤ Subgroup.normalizer (E : Set Γ)) {c : ℕ} (hc : Nat.card E % 3 = c) (hc0 : c ≠ 0)
    (hdvd : ¬ Nat.card P ∣ Nat.card E + (Nat.card P - 1) * c) :
    ∃ x ∈ P, orderOf x = 3 ∧ 4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set Γ)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxP, hx1, h4⟩ := exists_four_le_card_inf_centralizer hP hPE hc hc0 hdvd
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hx1 hk
  have hdvd3 : 3 ∣ orderOf x := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  refine ⟨x ^ (orderOf x / 3), Subgroup.pow_mem _ hxP _,
    orderOf_pow_orderOf_div (orderOf_pos x).ne' hdvd3, h4.trans ?_⟩
  refine Nat.card_mono (Set.toFinite _) fun e he => ⟨he.1, ?_⟩
  show e ∈ Subgroup.centralizer ({x ^ (orderOf x / 3)} : Set Γ)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (show Commute e x from Subgroup.mem_centralizer_singleton_iff.mp he.2).pow_right _

end CFSG.Quasithin.H13.Ch4.J4Blk
