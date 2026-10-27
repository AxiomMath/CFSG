module

public import CFSG.Quasithin.Vol2.Ch3E213MKer
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.EmptyFaithful.S153XPgrp

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

namespace E214F

variable {Γ : Type} [Group Γ]

theorem mem_of_commutator_mem [Finite Γ] {P Z Y : Subgroup Γ} {x : Γ} (hZY : Z ≤ Y)
    (hYP : Y ≤ P) (hPZ : P ≤ Subgroup.normalizer (Z : Set Γ))
    (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) (hxY : ∀ y ∈ Y, x * y * x⁻¹ ∈ Y)
    (hfpf : ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ Z → p ∈ Z) {p : Γ} (hp : p ∈ P)
    (hpY : x * p * x⁻¹ * p⁻¹ ∈ Y) : p ∈ Y := by
  have hZconj : ∀ a ∈ P, ∀ z ∈ Z, a⁻¹ * z * a ∈ Z := fun a ha z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (hPZ (P.inv_mem ha)) z).mp hz
    simpa using this
  have hid : ∀ a b : Γ, x * (a⁻¹ * b) * x⁻¹ * (a⁻¹ * b)⁻¹ =
      a⁻¹ * ((x * a * x⁻¹ * a⁻¹)⁻¹ * (x * b * x⁻¹ * b⁻¹)) * a := fun a b => by group
  let N : Subgroup ↥Y := Z.subgroupOf Y
  let f : ↥Y → ↥Y := fun y =>
    ⟨x * (y : Γ) * x⁻¹ * (y : Γ)⁻¹, Y.mul_mem (hxY y y.2) (Y.inv_mem y.2)⟩
  have hfv : ∀ y : ↥Y, ((f y : ↥Y) : Γ) = x * (y : Γ) * x⁻¹ * (y : Γ)⁻¹ := fun _ => rfl
  have hf : ∀ a b : ↥Y, a⁻¹ * b ∈ N → (f a)⁻¹ * f b ∈ N := by
    intro a b hab
    rw [Subgroup.mem_subgroupOf] at hab ⊢
    have hab' : (a : Γ)⁻¹ * b ∈ Z := by simpa using hab
    have hxz := hxZ _ hab'
    have e : ((f b : ↥Y) : Γ) = f a := by
      rw [hfv, hfv]
      calc x * (b : Γ) * x⁻¹ * (b : Γ)⁻¹
          = x * (a : Γ) * x⁻¹ * (x * ((a : Γ)⁻¹ * b) * x⁻¹) * ((a : Γ)⁻¹ * b)⁻¹ *
              (a : Γ)⁻¹ := by group
        _ = x * (a : Γ) * x⁻¹ * (a : Γ)⁻¹ := by rw [hxz]; group
    have h1 : (f a)⁻¹ * f b = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e, inv_mul_cancel, Subgroup.coe_one]
    rw [h1]
    exact Z.one_mem
  let F : ↥Y ⧸ N → ↥Y ⧸ N := Quotient.map' f (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hf a b hab)
  have hFmk : ∀ a : ↥Y, F (a : ↥Y ⧸ N) = ((f a : ↥Y) : ↥Y ⧸ N) := fun _ => rfl
  have hFinj : Function.Injective F := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
    induction q₂ using QuotientGroup.induction_on with
    | H b =>
    rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 : (x * (a : Γ) * x⁻¹ * (a : Γ)⁻¹)⁻¹ * (x * (b : Γ) * x⁻¹ * (b : Γ)⁻¹) ∈ Z := by
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hfv] using hq
    have h2 : x * ((a : Γ)⁻¹ * b) * x⁻¹ * ((a : Γ)⁻¹ * b)⁻¹ ∈ Z := by
      rw [hid]
      exact hZconj a (hYP a.2) _ h1
    have h3 := hfpf _ (P.mul_mem (P.inv_mem (hYP a.2)) (hYP b.2)) h2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h3
  have : Finite (↥Y ⧸ N) := Finite.of_surjective _ (QuotientGroup.mk_surjective (s := N))
  obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.mp hFinj)
    ((⟨x * p * x⁻¹ * p⁻¹, hpY⟩ : ↥Y) : ↥Y ⧸ N)
  induction q using QuotientGroup.induction_on with
  | H a =>
  rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
  have h1 : (x * (a : Γ) * x⁻¹ * (a : Γ)⁻¹)⁻¹ * (x * p * x⁻¹ * p⁻¹) ∈ Z := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hfv] using hq
  have h2 : x * ((a : Γ)⁻¹ * p) * x⁻¹ * ((a : Γ)⁻¹ * p)⁻¹ ∈ Z := by
    rw [hid]
    exact hZconj a (hYP a.2) _ h1
  have h3 := hfpf _ (P.mul_mem (P.inv_mem (hYP a.2)) hp) h2
  have e : p = a * ((a : Γ)⁻¹ * p) := by group
  rw [e]
  exact Y.mul_mem a.2 (hZY h3)

theorem exists_fpf_of_pair [Finite Γ] {X P Z : Subgroup Γ} {v e : Γ} (hvX : v ∈ X)
    (heX : e ∈ X) (hv : v * v = 1) (he : e * e = 1) (hP2 : IsPGroup 2 P) (hPX : P ≤ X)
    (hXP : X ≤ Subgroup.normalizer (P : Set Γ)) (hZc : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z)
    (hve : ∀ p ∈ P, v * p * v⁻¹ * p⁻¹ ∈ Z → e * p * e⁻¹ * p⁻¹ ∈ Z → p ∈ Z) :
    ∃ x ∈ Subgroup.zpowers (v * e), Odd (orderOf x) ∧
      ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ Z → p ∈ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, x, hc, ha, hx, ⟨n, han⟩, hxo⟩ := E2.exists_two_part_odd_part (v * e)
  refine ⟨x, hx, hxo, ?_⟩
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hzpX : Subgroup.zpowers (v * e) ≤ X := Subgroup.zpowers_le.mpr (X.mul_mem hvX heX)
  have hxX : x ∈ X := hzpX hx
  have haX : a ∈ X := hzpX ha
  have hZfix : ∀ y ∈ X, ∀ z ∈ Z, y * z * y⁻¹ = z := fun y hy z hz => by
    rw [← hZc z hz y hy, mul_inv_cancel_right]
  have hXZ : X ≤ Subgroup.normalizer (Z : Set Γ) := fun y hy =>
    B6.mem_normalizer_of_forall_mem (fun z hz => by rw [hZfix y hy z hz]; exact hz)
      (fun z hz => by
        have := hZfix y⁻¹ (X.inv_mem hy) z hz
        rw [inv_inv] at this
        rw [this]
        exact hz)
  have hv1 : v * (v * e) * v⁻¹ = (v * e)⁻¹ := by
    rw [mul_inv_rev, hvinv, heinv]
    calc v * (v * e) * v = (v * v) * e * v := by group
      _ = e * v := by rw [hv, one_mul]
  have hvc : ∀ y ∈ Subgroup.zpowers (v * e), v * y * v⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 := map_zpow (MulAut.conj v) (v * e) j
    simp only [MulAut.conj_apply] at h1
    rw [h1, hv1, inv_zpow]
  have hvx : v * x * v⁻¹ = x⁻¹ := hvc x hx
  have hvx' : v⁻¹ * x * v⁻¹⁻¹ = x⁻¹ := by
    rw [inv_inv]
    have h := hvx
    rw [hvinv] at h ⊢
    exact h
  have hxa : x * a = a * x := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_zpow_self (v * e) i j).eq
  let U : Subgroup Γ :=
    { carrier := {p | p ∈ P ∧ x * p * x⁻¹ * p⁻¹ ∈ Z}
      mul_mem' := by
        rintro p q ⟨hp, hpx⟩ ⟨hq, hqx⟩
        refine ⟨P.mul_mem hp hq, ?_⟩
        have e1 : x * (p * q) * x⁻¹ * (p * q)⁻¹ =
            (x * p * x⁻¹ * p⁻¹) * (p * (x * q * x⁻¹ * q⁻¹) * p⁻¹) := by group
        rw [e1, hZfix p (hPX hp) _ hqx]
        exact Z.mul_mem hpx hqx
      one_mem' := ⟨P.one_mem, by simp⟩
      inv_mem' := by
        rintro p ⟨hp, hpx⟩
        refine ⟨P.inv_mem hp, ?_⟩
        have e1 : x * p⁻¹ * x⁻¹ * p⁻¹⁻¹ = p⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * p⁻¹⁻¹ := by group
        rw [e1, hZfix p⁻¹ (X.inv_mem (hPX hp)) _ (Z.inv_mem hpx)]
        exact Z.inv_mem hpx }
  have hUP : U ≤ P := fun p hp => hp.1
  have hconj : ∀ y ∈ X, (x * y = y * x ∨ x * y = y * x⁻¹) → ∀ p ∈ U, y * p * y⁻¹ ∈ U := by
    rintro y hy hxy p ⟨hp, hpx⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXP hy) p).mp hp, ?_⟩
    rcases hxy with hxy | hxy
    · have e1 : x * (y * p * y⁻¹) * x⁻¹ * (y * p * y⁻¹)⁻¹ =
          y * (x * p * x⁻¹ * p⁻¹) * y⁻¹ := by
        calc x * (y * p * y⁻¹) * x⁻¹ * (y * p * y⁻¹)⁻¹
            = (x * y) * p * (x * y)⁻¹ * (y * p⁻¹ * y⁻¹) := by group
          _ = (y * x) * p * (y * x)⁻¹ * (y * p⁻¹ * y⁻¹) := by rw [hxy]
          _ = y * (x * p * x⁻¹ * p⁻¹) * y⁻¹ := by group
      rw [e1, hZfix y hy _ hpx]
      exact hpx
    · have e1 : x * (y * p * y⁻¹) * x⁻¹ * (y * p * y⁻¹)⁻¹ =
          y * (x⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * x⁻¹⁻¹) * y⁻¹ := by
        calc x * (y * p * y⁻¹) * x⁻¹ * (y * p * y⁻¹)⁻¹
            = (x * y) * p * (x * y)⁻¹ * (y * p⁻¹ * y⁻¹) := by group
          _ = (y * x⁻¹) * p * (y * x⁻¹)⁻¹ * (y * p⁻¹ * y⁻¹) := by rw [hxy]
          _ = y * (x⁻¹ * (x * p * x⁻¹ * p⁻¹)⁻¹ * x⁻¹⁻¹) * y⁻¹ := by group
      rw [e1, hZfix x⁻¹ (X.inv_mem hxX) _ (Z.inv_mem hpx), hZfix y hy _ (Z.inv_mem hpx)]
      exact Z.inv_mem hpx
  have hxv : x * v = v * x⁻¹ := by
    calc x * v = v * (v⁻¹ * x * v⁻¹⁻¹) := by group
      _ = v * x⁻¹ := by rw [hvx']
  have hxv' : x * v⁻¹ = v⁻¹ * x⁻¹ := by
    calc x * v⁻¹ = v⁻¹ * (v * x * v⁻¹) := by group
      _ = v⁻¹ * x⁻¹ := by rw [hvx]
  have hxa' : x * a⁻¹ = a⁻¹ * x := by
    calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
      _ = a⁻¹ * (x * a) * a⁻¹ := by rw [hxa]
      _ = a⁻¹ * x := by group
  have hv2 : IsPGroup 2 (Subgroup.zpowers v) :=
    E2.isPGroup_zpowers_of_pow (k := 1) (by rw [pow_one, pow_two, hv])
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) := E2.isPGroup_zpowers_of_pow han
  have hva : ∀ j : ℤ, v * a ^ j * v⁻¹ = (a ^ j)⁻¹ := fun j =>
    hvc _ (Subgroup.zpow_mem _ ha j)
  have hvna : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers a : Set Γ) := by
    rw [Subgroup.zpowers_le]
    refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [hva j]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j)
    · obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h := hva j
      rw [hvinv] at h
      rw [hvinv, h]
      exact Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) j)
  set Q : Subgroup Γ := Subgroup.zpowers v ⊔ Subgroup.zpowers a with hQ
  have hQ2 : IsPGroup 2 Q := IsPGroup.to_sup_of_normal_right' hv2 ha2 hvna
  have hQX : Q ≤ X := sup_le (Subgroup.zpowers_le.mpr hvX) (Subgroup.zpowers_le.mpr haX)
  have hQU : Q ≤ Subgroup.normalizer (U : Set Γ) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact B6.mem_normalizer_of_forall_mem (hconj v hvX (Or.inr hxv))
        (fun p hp => by simpa using hconj v⁻¹ (X.inv_mem hvX) (Or.inr hxv') p hp)
    · exact B6.mem_normalizer_of_forall_mem (hconj a haX (Or.inl hxa))
        (fun p hp => by simpa using hconj a⁻¹ (X.inv_mem haX) (Or.inl hxa') p hp)
  set S : Subgroup Γ := Q ⊔ U with hS
  have hS2 : IsPGroup 2 S := IsPGroup.to_sup_of_normal_right' hQ2 (hP2.to_le hUP) hQU
  intro p hp hpx
  by_contra hpZ
  have hUZ : ¬ U ≤ Z := fun h => hpZ (h ⟨hp, hpx⟩)
  obtain ⟨u, hu, huZ, hfix⟩ := X1469.exists_fixed_mod hS2 le_sup_right
    (sup_le hQU Subgroup.le_normalizer) (sup_le (hQX.trans hXZ) ((hUP.trans hPX).trans hXZ)) hUZ
  have hfixS : ∀ y ∈ S, y * u * y⁻¹ * u⁻¹ ∈ Z := fun y hy => by
    have h := Z.inv_mem (hfix y hy)
    have e1 : (u * y * u⁻¹ * y⁻¹)⁻¹ = y * u * y⁻¹ * u⁻¹ := by group
    rwa [e1] at h
  have hmul : ∀ y₁ ∈ X, ∀ y₂ : Γ, y₁ * u * y₁⁻¹ * u⁻¹ ∈ Z → y₂ * u * y₂⁻¹ * u⁻¹ ∈ Z →
      (y₁ * y₂) * u * (y₁ * y₂)⁻¹ * u⁻¹ ∈ Z := by
    intro y₁ hy₁ y₂ h₁ h₂
    have e1 : (y₁ * y₂) * u * (y₁ * y₂)⁻¹ * u⁻¹ =
        (y₁ * (y₂ * u * y₂⁻¹ * u⁻¹) * y₁⁻¹) * (y₁ * u * y₁⁻¹ * u⁻¹) := by group
    rw [e1, hZfix y₁ hy₁ _ h₂]
    exact Z.mul_mem h₂ h₁
  have hvu := hfixS v ((le_sup_left : Q ≤ S) ((le_sup_left : Subgroup.zpowers v ≤ Q)
    (Subgroup.mem_zpowers v)))
  have hau := hfixS a ((le_sup_left : Q ≤ S) ((le_sup_right : Subgroup.zpowers a ≤ Q)
    (Subgroup.mem_zpowers a)))
  have hxu : x * u * x⁻¹ * u⁻¹ ∈ Z := hu.2
  have he' : e = v * (x * a) := by
    calc e = v * (v * e) := by rw [← mul_assoc, hv, one_mul]
      _ = v * (x * a) := by rw [hc]
  have heu : e * u * e⁻¹ * u⁻¹ ∈ Z := by
    rw [he']
    exact hmul v hvX _ hvu (hmul x hxX a hxu hau)
  exact huZ (hve u hu.1 hvu heu)

@[expose] def fixModSubgroup (X Z : Subgroup Γ) (hZc : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z)
    (u : Γ) : Subgroup Γ where
  carrier := {y | y ∈ X ∧ y * u * y⁻¹ * u⁻¹ ∈ Z}
  mul_mem' := by
    rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
    refine ⟨X.mul_mem hy₁ hy₂, ?_⟩
    have e1 : (y₁ * y₂) * u * (y₁ * y₂)⁻¹ * u⁻¹ =
        (y₁ * (y₂ * u * y₂⁻¹ * u⁻¹) * y₁⁻¹) * (y₁ * u * y₁⁻¹ * u⁻¹) := by group
    rw [e1, ← hZc _ h₂ y₁ hy₁, mul_inv_cancel_right]
    exact Z.mul_mem h₂ h₁
  one_mem' := ⟨X.one_mem, by simp⟩
  inv_mem' := by
    rintro y ⟨hy, h⟩
    refine ⟨X.inv_mem hy, ?_⟩
    have e1 : y⁻¹ * u * y⁻¹⁻¹ * u⁻¹ = y⁻¹ * (y * u * y⁻¹ * u⁻¹)⁻¹ * y := by group
    rw [e1, ← hZc _ (Z.inv_mem h) y⁻¹ (X.inv_mem hy), inv_mul_cancel_right]
    exact Z.inv_mem h

theorem fixed_of_sup [Finite Γ] {X P Z J L : Subgroup Γ} (hJ2 : IsPGroup 2 J) (hJX : J ≤ X)
    (hPJ : P ≤ J) (hXP : X ≤ Subgroup.normalizer (P : Set Γ))
    (hZc : ∀ z ∈ Z, ∀ y ∈ X, z * y = y * z)
    (hPab : ∀ p ∈ P, ∀ q ∈ P, p * q * p⁻¹ * q⁻¹ ∈ Z)
    (hJc : ∀ y ∈ X, ∀ j ∈ J, y * j * y⁻¹ * j⁻¹ ∈ P)
    (hfix : ∀ p ∈ P, (∀ y ∈ X, y * p * y⁻¹ * p⁻¹ ∈ Z) → p ∈ Z)
    (hLX : L ≤ X) (hgen : X ≤ L ⊔ J) :
    ∀ p ∈ P, (∀ l ∈ L, l * p * l⁻¹ * p⁻¹ ∈ Z) → p ∈ Z := by
  have hZfix : ∀ y ∈ X, ∀ z ∈ Z, y * z * y⁻¹ = z := fun y hy z hz => by
    rw [← hZc z hz y hy, mul_inv_cancel_right]
  have hXZ : X ≤ Subgroup.normalizer (Z : Set Γ) := fun y hy =>
    B6.mem_normalizer_of_forall_mem (fun z hz => by rw [hZfix y hy z hz]; exact hz)
      (fun z hz => by
        have := hZfix y⁻¹ (X.inv_mem hy) z hz
        rw [inv_inv] at this
        rw [this]
        exact hz)
  have hPX : P ≤ X := hPJ.trans hJX
  let U : Subgroup Γ :=
    { carrier := {p | p ∈ P ∧ ∀ l ∈ L, l * p * l⁻¹ * p⁻¹ ∈ Z}
      mul_mem' := by
        rintro p q ⟨hp, hpl⟩ ⟨hq, hql⟩
        refine ⟨P.mul_mem hp hq, fun l hl => ?_⟩
        have e1 : l * (p * q) * l⁻¹ * (p * q)⁻¹ =
            (l * p * l⁻¹ * p⁻¹) * (p * (l * q * l⁻¹ * q⁻¹) * p⁻¹) := by group
        rw [e1, hZfix p (hPX hp) _ (hql l hl)]
        exact Z.mul_mem (hpl l hl) (hql l hl)
      one_mem' := ⟨P.one_mem, fun l _ => by simp⟩
      inv_mem' := by
        rintro p ⟨hp, hpl⟩
        refine ⟨P.inv_mem hp, fun l hl => ?_⟩
        have e1 : l * p⁻¹ * l⁻¹ * p⁻¹⁻¹ = p⁻¹ * (l * p * l⁻¹ * p⁻¹)⁻¹ * p⁻¹⁻¹ := by group
        rw [e1, hZfix p⁻¹ (X.inv_mem (hPX hp)) _ (Z.inv_mem (hpl l hl))]
        exact Z.inv_mem (hpl l hl) }
  have hJU : ∀ j ∈ J, ∀ u ∈ U, j * u * j⁻¹ ∈ U := by
    rintro j hj u ⟨hu, hul⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXP (hJX hj)) u).mp hu, fun l hl => ?_⟩
    have hp₀P : j⁻¹ * l * j * l⁻¹ ∈ P := by
      have h := P.inv_mem (hJc l (hLX hl) j⁻¹ (J.inv_mem hj))
      have e1 : (l * j⁻¹ * l⁻¹ * j⁻¹⁻¹)⁻¹ = j⁻¹ * l * j * l⁻¹ := by group
      rwa [e1] at h
    set p₀ := j⁻¹ * l * j * l⁻¹ with hp₀
    have e1 : l * (j * u * j⁻¹) * l⁻¹ * (j * u * j⁻¹)⁻¹ =
        j * (p₀ * (l * u * l⁻¹ * u⁻¹) * p₀⁻¹ * (p₀ * u * p₀⁻¹ * u⁻¹)) * j⁻¹ := by
      rw [hp₀]; group
    rw [e1, hZfix p₀ (hPX hp₀P) _ (hul l hl)]
    have h2 := Z.mul_mem (hul l hl) (hPab p₀ hp₀P u hu)
    rw [hZfix j (hJX hj) _ h2]
    exact h2
  have hJN : J ≤ Subgroup.normalizer (U : Set Γ) := fun j hj =>
    B6.mem_normalizer_of_forall_mem (hJU j hj)
      (fun u hu => by simpa using hJU j⁻¹ (J.inv_mem hj) u hu)
  intro p hp hpl
  by_contra hpZ
  have hUZ : ¬ U ≤ Z := fun h => hpZ (h ⟨hp, hpl⟩)
  obtain ⟨u, hu, huZ, hfixu⟩ :=
    X1469.exists_fixed_mod (E := U) hJ2 (fun u hu => hPJ hu.1) hJN (hJX.trans hXZ) hUZ
  have hLF : L ≤ fixModSubgroup X Z hZc u := fun l hl => ⟨hLX hl, hu.2 l hl⟩
  have hJF : J ≤ fixModSubgroup X Z hZc u := fun j hj => by
    refine ⟨hJX hj, ?_⟩
    have h := Z.inv_mem (hfixu j hj)
    have e1 : (u * j * u⁻¹ * j⁻¹)⁻¹ = j * u * j⁻¹ * u⁻¹ := by group
    rwa [e1] at h
  have hXF : X ≤ fixModSubgroup X Z hZc u := hgen.trans (sup_le hLF hJF)
  exact huZ (hfix u hu.1 fun y hy => (hXF hy).2)

theorem mem_kerIn_of_forall_commutator_mem [Finite Γ] {I MI Y₁ Y₂ : Subgroup Γ}
    (hMI : MI ≤ I) (hJ2 : IsPGroup 2 (kerIn MI I))
    (hIY₁ : I ≤ Subgroup.normalizer (Y₁ : Set Γ)) (hIY₂ : I ≤ Subgroup.normalizer (Y₂ : Set Γ))
    {x : Γ} (hxI : x ∈ I) (hxo : Odd (orderOf x))
    (hN : ∀ N : Subgroup (E2.StarQuot MI I), N.Normal → N ≠ ⊥ → E2P.starMap MI I ⟨x, hxI⟩ ∈ N)
    (hx : ∃ y ∈ Y₁, x * y * x⁻¹ * y⁻¹ ∉ Y₂)
    {i : Γ} (hiI : i ∈ I) (hi : ∀ y ∈ Y₁, i * y * i⁻¹ * y⁻¹ ∈ Y₂) : i ∈ kerIn MI I := by
  let K : Subgroup Γ :=
    { carrier := {i | i ∈ I ∧ ∀ y ∈ Y₁, i * y * i⁻¹ * y⁻¹ ∈ Y₂}
      mul_mem' := by
        rintro i₁ i₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
        refine ⟨I.mul_mem h₁ h₂, fun y hy => ?_⟩
        have e1 : (i₁ * i₂) * y * (i₁ * i₂)⁻¹ * y⁻¹ =
            (i₁ * (i₂ * y * i₂⁻¹ * y⁻¹) * i₁⁻¹) * (i₁ * y * i₁⁻¹ * y⁻¹) := by group
        rw [e1]
        exact Y₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hIY₂ h₁) _).mp (k₂ y hy)) (k₁ y hy)
      one_mem' := ⟨I.one_mem, fun y _ => by simp⟩
      inv_mem' := by
        rintro i ⟨hi, k⟩
        refine ⟨I.inv_mem hi, fun y hy => ?_⟩
        have hy' : i⁻¹ * y * i⁻¹⁻¹ ∈ Y₁ :=
          (Subgroup.mem_normalizer_iff.mp (hIY₁ (I.inv_mem hi)) y).mp hy
        have e1 : i⁻¹ * y * i⁻¹⁻¹ * y⁻¹ =
            (i * (i⁻¹ * y * i⁻¹⁻¹) * i⁻¹ * (i⁻¹ * y * i⁻¹⁻¹)⁻¹)⁻¹ := by group
        rw [e1]
        exact Y₂.inv_mem (k _ hy') }
  have hKI : K ≤ I := fun i hi => hi.1
  have hIK : I ≤ Subgroup.normalizer (K : Set Γ) := by
    have key : ∀ j ∈ I, ∀ k ∈ K, j * k * j⁻¹ ∈ K := by
      rintro j hj k ⟨hk, hky⟩
      refine ⟨I.mul_mem (I.mul_mem hj hk) (I.inv_mem hj), fun y hy => ?_⟩
      have hy' : j⁻¹ * y * j⁻¹⁻¹ ∈ Y₁ :=
        (Subgroup.mem_normalizer_iff.mp (hIY₁ (I.inv_mem hj)) y).mp hy
      have e1 : j * k * j⁻¹ * y * (j * k * j⁻¹)⁻¹ * y⁻¹ =
          j * (k * (j⁻¹ * y * j⁻¹⁻¹) * k⁻¹ * (j⁻¹ * y * j⁻¹⁻¹)⁻¹) * j⁻¹ := by group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp (hIY₂ hj) _).mp (hky _ hy')
    exact fun j hj => B6.mem_normalizer_of_forall_mem (key j hj)
      (fun k hk => by simpa using key j⁻¹ (I.inv_mem hj) k hk)
  have hKn : (K.subgroupOf I).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).2 hIK
  set π := E2P.starMap MI I with hπ
  have hKs : ((K.subgroupOf I).map π).Normal := hKn.map π (E2P.starMap_surjective MI I)
  by_cases hbot : (K.subgroupOf I).map π = ⊥
  · have h1 : π ⟨i, hiI⟩ ∈ (K.subgroupOf I).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ⟨hiI, hi⟩)
    rw [hbot, Subgroup.mem_bot, hπ, E2P.starMap, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  · exfalso
    obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp (hN _ hKs hbot)
    rw [hπ, E2P.starMap, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hkx
    rw [Subgroup.mem_subgroupOf] at hk
    set j : Γ := (k : Γ)⁻¹ * x with hj
    have hjJ : j ∈ kerIn MI I := by simpa [hj] using hkx
    have hjI : j ∈ I := hMI (kerIn_le hjJ)
    obtain ⟨m, hm⟩ := hJ2 ⟨j, hjJ⟩
    have hjm : j ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hxkj : x = k * j := by rw [hj]; group
    have hpow : ∀ N : ℕ, ((k : Γ) * j) ^ N * (j ^ N)⁻¹ ∈ K := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have e1 : ((k : Γ) * j) ^ (N + 1) * (j ^ (N + 1))⁻¹ =
            (((k : Γ) * j) ^ N * (j ^ N)⁻¹) * (j ^ N * k * (j ^ N)⁻¹) := by
          rw [pow_succ, pow_succ]; group
        rw [e1]
        exact K.mul_mem ih ((Subgroup.mem_normalizer_iff.mp (hIK (I.pow_mem hjI N)) _).mp hk)
    have hxK : x ∈ K := by
      have h1 := hpow (2 ^ m)
      rw [hjm, inv_one, mul_one, ← hxkj] at h1
      exact B6.mem_of_pow_mem_of_coprime h1
        (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hxo))
    obtain ⟨y, hy, hxy⟩ := hx
    exact hxy (hxK.2 y hy)

theorem exists_relIndex_eq_two_pow [Finite Γ] {X : Subgroup Γ} (hX : IsPGroup 2 X)
    (U : Subgroup Γ) : ∃ a : ℕ, U.relIndex X = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := IsPGroup.iff_card.mp hX
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hv ▸ Subgroup.relIndex_dvd_card U X)
  exact ⟨a, ha⟩

theorem exists_dvd_two_pow_sub_one_le [Finite Γ] {Y₁ Y₂ : Subgroup Γ} {c : Γ} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hc : orderOf c = r) (hY₁2 : IsPGroup 2 Y₁) (hY : Y₂ ≤ Y₁)
    (hY₁Y₂ : Y₁ ≤ Subgroup.normalizer (Y₂ : Set Γ))
    (hcY₁ : c ∈ Subgroup.normalizer (Y₁ : Set Γ)) (hcY₂ : c ∈ Subgroup.normalizer (Y₂ : Set Γ))
    (hne : ∃ y ∈ Y₁, c * y * c⁻¹ * y⁻¹ ∉ Y₂) :
    ∃ m : ℕ, 0 < m ∧ r ∣ 2 ^ m - 1 ∧ m ≤ E3.mQuot Y₁ Y₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Subgroup Γ :=
    { carrier := {y | y ∈ Y₁ ∧ c * y * c⁻¹ * y⁻¹ ∈ Y₂}
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
        refine ⟨Y₁.mul_mem h₁ h₂, ?_⟩
        have e1 : c * (y₁ * y₂) * c⁻¹ * (y₁ * y₂)⁻¹ =
            (c * y₁ * c⁻¹ * y₁⁻¹) * (y₁ * (c * y₂ * c⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e1]
        exact Y₂.mul_mem k₁ ((Subgroup.mem_normalizer_iff.mp (hY₁Y₂ h₁) _).mp k₂)
      one_mem' := ⟨Y₁.one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨hy, k⟩
        refine ⟨Y₁.inv_mem hy, ?_⟩
        have e1 : c * y⁻¹ * c⁻¹ * y⁻¹⁻¹ = y⁻¹ * (c * y * c⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (hY₁Y₂ (Y₁.inv_mem hy)) _).mp (Y₂.inv_mem k) }
  have hY₂F : Y₂ ≤ F := fun y hy =>
    ⟨hY hy, Y₂.mul_mem ((Subgroup.mem_normalizer_iff.mp hcY₂ y).mp hy) (Y₂.inv_mem hy)⟩
  have hFY₁ : F ≤ Y₁ := fun y hy => hy.1
  have hzc : Subgroup.zpowers c ≤ Subgroup.normalizer (Y₁ : Set Γ) :=
    Subgroup.zpowers_le.mpr hcY₁
  have hzc₂ : Subgroup.zpowers c ≤ Subgroup.normalizer (Y₂ : Set Γ) :=
    Subgroup.zpowers_le.mpr hcY₂
  let ρ : ↥(Subgroup.zpowers c) →* MulAut ↥Y₁ :=
    Y₁.normalizerMonoidHom.comp (Subgroup.inclusion hzc)
  let _ : MulAction ↥(Subgroup.zpowers c) ↥Y₁ := MulAction.compHom ↥Y₁ ρ
  have hsmul : ∀ (k : ↥(Subgroup.zpowers c)) (y : ↥Y₁),
      ((k • y : ↥Y₁) : Γ) = (k : Γ) * y * (k : Γ)⁻¹ := fun k y => by
    show ((ρ k) y : Γ) = _
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  set C : Set ↥Y₁ := ((F.subgroupOf Y₁ : Subgroup ↥Y₁) : Set ↥Y₁) with hC
  have hCmem : ∀ y : ↥Y₁, y ∈ C ↔ (y : Γ) ∈ F := fun y => Subgroup.mem_subgroupOf
  have hdvd := Ch3E213M.card_dvd_card_sub_of_fixed_subset (K := ↥(Subgroup.zpowers c))
    (β := ↥Y₁) (C := C)
    (fun k y hy => by
      rw [hCmem] at hy ⊢
      obtain ⟨hy₁, hyc⟩ := hy
      refine ⟨by rw [hsmul]; exact (k • y).2, ?_⟩
      have hck : c * (k : Γ) = k * c := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp k.2
        rw [← hj]
        exact (Commute.self_zpow c j).eq
      rw [hsmul]
      have e1 : c * ((k : Γ) * y * (k : Γ)⁻¹) * c⁻¹ * ((k : Γ) * y * (k : Γ)⁻¹)⁻¹ =
          (k : Γ) * (c * y * c⁻¹ * (y : Γ)⁻¹) * (k : Γ)⁻¹ := by
        calc c * ((k : Γ) * y * (k : Γ)⁻¹) * c⁻¹ * ((k : Γ) * y * (k : Γ)⁻¹)⁻¹
            = (c * k) * y * (c * k)⁻¹ * ((k : Γ) * (y : Γ)⁻¹ * (k : Γ)⁻¹) := by group
          _ = (k * c) * y * (k * c)⁻¹ * ((k : Γ) * (y : Γ)⁻¹ * (k : Γ)⁻¹) := by rw [hck]
          _ = (k : Γ) * (c * y * c⁻¹ * (y : Γ)⁻¹) * (k : Γ)⁻¹ := by group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp (hzc₂ k.2) _).mp hyc)
    (fun k hk y hky => by
      rw [hCmem]
      have hk' : (k : Γ) ≠ 1 := fun h => hk (Subtype.ext h)
      have hcmem : c ^ r ^ 0 ∈ Subgroup.zpowers (k : Γ) :=
        Ch3E213M.pow_mem_zpowers_of_ne_one hr (by rw [hc, zero_add, pow_one]) k.2 hk'
      rw [pow_zero, pow_one] at hcmem
      have hkyc : (k : Γ) ∈ Subgroup.centralizer ({(y : Γ)} : Set Γ) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : (k : Γ) * y * (k : Γ)⁻¹ = y := by rw [← hsmul, hky]
        calc (k : Γ) * y = ((k : Γ) * y * (k : Γ)⁻¹) * k := by group
          _ = (y : Γ) * k := by rw [h1]
      have hcy : c ∈ Subgroup.centralizer ({(y : Γ)} : Set Γ) :=
        (Subgroup.zpowers_le.mpr hkyc) hcmem
      rw [Subgroup.mem_centralizer_singleton_iff] at hcy
      refine ⟨y.2, ?_⟩
      rw [hcy, mul_inv_cancel_right, mul_inv_cancel]
      exact Y₂.one_mem)
  rw [Nat.card_zpowers, hc] at hdvd
  have hCcard : Nat.card ↑C = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY₁).toEquiv
  rw [hCcard] at hdvd
  obtain ⟨e, he⟩ := exists_relIndex_eq_two_pow (hY₁2.to_le hFY₁) Y₂
  obtain ⟨f, hf⟩ := exists_relIndex_eq_two_pow hY₁2 F
  have hF : Nat.card F = 2 ^ e * Nat.card Y₂ := by
    have h1 := Subgroup.relIndex_mul_card Y₂ F
    rw [inf_eq_left.2 hY₂F, he] at h1
    exact h1.symm
  have hY₁ : Nat.card Y₁ = 2 ^ f * Nat.card F := by
    have h1 := Subgroup.relIndex_mul_card F Y₁
    rw [inf_eq_left.2 hFY₁, hf] at h1
    exact h1.symm
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hf
      obtain ⟨y, hy, hcy⟩ := hne
      exact hcy (Subgroup.relIndex_eq_one.mp hf hy).2
    · exact h0
  have hsub : Nat.card Y₁ - Nat.card F = (2 ^ f - 1) * Nat.card F := by
    rw [hY₁, Nat.sub_one_mul]
  rw [hsub] at hdvd
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hY₁2
  have hcop : Nat.Coprime r (Nat.card F) := by
    have h2N : Nat.Coprime r (2 ^ N) :=
      Nat.Coprime.pow_right N ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
    exact h2N.coprime_dvd_right (hN ▸ Subgroup.card_dvd_of_le hFY₁)
  refine ⟨f, hf0, hcop.dvd_of_dvd_mul_right hdvd, ?_⟩
  unfold E3.mQuot
  rw [← Subgroup.relIndex_mul_relIndex Y₂ F Y₁ hY₂F hFY₁, he, hf, ← pow_add,
    padicValNat.prime_pow]
  omega

theorem exists_conj_of_forall_involution {Y : Type*} [Group Y] [Finite Y] {v e : Y}
    (hv : v * v = 1) (he : e * e = 1)
    (hno : ∀ z : Y, z * z = 1 → z * v = v * z → z * e = e * z → z = 1) :
    ∃ y ∈ Subgroup.zpowers (v * e), y * v * y⁻¹ = e := by
  set c := v * e with hcdef
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hvc : v * c * v⁻¹ = c⁻¹ := by
    rw [hcdef, mul_inv_rev, hvinv, heinv]
    calc v * (v * e) * v = (v * v) * e * v := by group
      _ = e * v := by rw [hv, one_mul]
  have hec : e * c * e⁻¹ = c⁻¹ := by
    rw [hcdef, mul_inv_rev, hvinv, heinv]
    calc e * (v * e) * e = e * v * (e * e) := by group
      _ = e * v := by rw [he, mul_one]
  have hpow : ∀ w : Y, w * c * w⁻¹ = c⁻¹ → ∀ j : ℤ, w * c ^ j * w⁻¹ = (c ^ j)⁻¹ := by
    intro w hw j
    have h1 := map_zpow (MulAut.conj w) c j
    simp only [MulAut.conj_apply] at h1
    rw [h1, hw, inv_zpow]
  have hc0 : 0 < orderOf c := orderOf_pos c
  rcases Nat.even_or_odd (orderOf c) with ⟨m, hm⟩ | ⟨m, hm⟩
  · exfalso
    set z := c ^ (m : ℤ) with hz
    have hz2 : z * z = 1 := by
      rw [hz, ← zpow_add, ← Nat.cast_add, ← hm, zpow_natCast, pow_orderOf_eq_one]
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hzv : z * v = v * z := by
      have h := hpow v hvc m
      rw [← hz, hzinv] at h
      calc z * v = (v * z * v⁻¹) * v := by rw [h]
        _ = v * z := by group
    have hze : z * e = e * z := by
      have h := hpow e hec m
      rw [← hz, hzinv] at h
      calc z * e = (e * z * e⁻¹) * e := by rw [h]
        _ = e * z := by group
    have h1 := hno z hz2 hzv hze
    rw [hz, zpow_natCast] at h1
    have hm0 : 0 < m := by omega
    have := orderOf_le_of_pow_eq_one hm0 h1
    omega
  · refine ⟨c ^ (m : ℤ), Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) _, ?_⟩
    have h1 : v * (c ^ (m : ℤ))⁻¹ * v⁻¹ = c ^ (m : ℤ) := by
      have h := hpow v hvc (-(m : ℤ))
      rw [zpow_neg, inv_inv] at h
      exact h
    have h2 : c ^ (m : ℤ) * c ^ (m : ℤ) = c⁻¹ := by
      rw [← zpow_add, show (m : ℤ) + m = ((orderOf c : ℕ) : ℤ) - 1 by rw [hm]; push_cast; ring,
        zpow_sub_one, zpow_natCast, pow_orderOf_eq_one, one_mul]
    calc c ^ (m : ℤ) * v * (c ^ (m : ℤ))⁻¹
        = c ^ (m : ℤ) * (v * (c ^ (m : ℤ))⁻¹ * v⁻¹) * v := by group
      _ = c ^ (m : ℤ) * c ^ (m : ℤ) * v := by rw [h1]
      _ = c⁻¹ * v := by rw [h2]
      _ = e := by rw [hcdef, mul_inv_rev, inv_mul_cancel_right, heinv]

theorem conj_commute_iff {Y : Type*} [Group Y] (a b c : Y) :
    (c * a * c⁻¹) * (c * b * c⁻¹) = (c * b * c⁻¹) * (c * a * c⁻¹) ↔ a * b = b * a := by
  constructor
  · intro h1
    have h2 : c * (a * b) * c⁻¹ = c * (b * a) * c⁻¹ := by
      calc c * (a * b) * c⁻¹ = (c * a * c⁻¹) * (c * b * c⁻¹) := by group
        _ = (c * b * c⁻¹) * (c * a * c⁻¹) := h1
        _ = c * (b * a) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro h1
    calc (c * a * c⁻¹) * (c * b * c⁻¹) = c * (a * b) * c⁻¹ := by group
      _ = c * (b * a) * c⁻¹ := by rw [h1]
      _ = (c * b * c⁻¹) * (c * a * c⁻¹) := by group

theorem sup_zpowers_eq_top {Y : Type*} [Group Y] [Finite Y] {S : Subgroup Y} {h v : Y}
    (hW2 : ∀ w ∈ S ⊓ Subgroup.centralizer (S : Set Y), w * w = 1)
    (hgen : (S ⊓ Subgroup.centralizer (S : Set Y)) ⊔
      (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom = ⊤)
    (hv : v ∈ S ⊓ Subgroup.centralizer (S : Set Y))
    (hCv : Subgroup.centralizer ({v} : Set Y) ≤ S) (hcen : Subgroup.center Y = ⊥) :
    (S ⊓ Subgroup.centralizer (S : Set Y)) ⊔ Subgroup.zpowers (h⁻¹ * v * h) = ⊤ ∧
      (S ⊓ Subgroup.centralizer (S : Set Y)).map (MulAut.conj h⁻¹).toMonoidHom ⊔
        Subgroup.zpowers v = ⊤ := by
  set W := S ⊓ Subgroup.centralizer (S : Set Y) with hW
  set W' := W.map (MulAut.conj h⁻¹).toMonoidHom with hW'
  set e := h⁻¹ * v * h with he
  have hmemW' : ∀ w, w ∈ W' ↔ h * w * h⁻¹ ∈ W := by
    intro w
    rw [hW', Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hv2 : v * v = 1 := hW2 v hv
  have hhe : h * e * h⁻¹ = v := by rw [he]; group
  have he2 : e * e = 1 := by
    have h1 : h * (e * e) * h⁻¹ = 1 := by
      calc h * (e * e) * h⁻¹ = (h * e * h⁻¹) * (h * e * h⁻¹) := by group
        _ = 1 := by rw [hhe, hv2]
    calc e * e = h⁻¹ * (h * (e * e) * h⁻¹) * h := by group
      _ = 1 := by rw [h1]; group
  have hCvS : ∀ z, z * v = v * z ↔ z ∈ S := fun z =>
    ⟨fun hz => hCv (Subgroup.mem_centralizer_singleton_iff.mpr hz),
      fun hz => Subgroup.mem_centralizer_iff.mp hv.2 z hz⟩
  have hTI : ∀ z : Y, z ∈ S → h * z * h⁻¹ ∈ S → z = 1 := by
    intro z hzS hzS'
    have hWz : W ≤ Subgroup.centralizer ({z} : Set Y) := fun w hw => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hw.2 z hzS).symm
    have hW'z : W' ≤ Subgroup.centralizer ({z} : Set Y) := fun w hw => by
      rw [hmemW'] at hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((conj_commute_iff z w h).mp (Subgroup.mem_centralizer_iff.mp hw.2 _ hzS')).symm
    have hzc : z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro u
      have hu := (sup_le hWz hW'z) (hgen ▸ Subgroup.mem_top u : u ∈ W ⊔ W')
      exact Subgroup.mem_centralizer_singleton_iff.mp hu
    rw [hcen] at hzc
    exact hzc
  have hno : ∀ z : Y, z * z = 1 → z * v = v * z → z * e = e * z → z = 1 := by
    intro z _ hzv hze
    refine hTI z ((hCvS z).mp hzv) ((hCvS _).mp ?_)
    have h1 := (conj_commute_iff z e h).mpr hze
    rw [hhe] at h1
    exact h1
  obtain ⟨y, hy, hyv⟩ := exists_conj_of_forall_involution hv2 he2 hno
  have hyz : ∀ z, y * (y⁻¹ * z * y) * y⁻¹ = z := fun z => by group
  have key : ∀ z, h * z * h⁻¹ ∈ S ↔ y⁻¹ * z * y ∈ S := by
    intro z
    have h4 := conj_commute_iff z e h
    rw [hhe] at h4
    have h3 := conj_commute_iff (y⁻¹ * z * y) v y
    rw [hyz, hyv] at h3
    exact (hCvS _).symm.trans (h4.trans (h3.trans (hCvS _)))
  have keyW : ∀ w, h * w * h⁻¹ ∈ W ↔ y⁻¹ * w * y ∈ W := by
    intro w
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(key w).mp h1, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have hs : h * (y * t * y⁻¹) * h⁻¹ ∈ S := (key _).mpr (by
        have e1 : y⁻¹ * (y * t * y⁻¹) * y = t := by group
        rw [e1]
        exact ht)
      have h3 := (conj_commute_iff (y * t * y⁻¹) w h).mp (Subgroup.mem_centralizer_iff.mp h2 _ hs)
      have h5 := conj_commute_iff t (y⁻¹ * w * y) y
      rw [hyz] at h5
      exact h5.mp h3
    · rintro ⟨h1, h2⟩
      refine ⟨(key w).mpr h1, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
      have hz : y⁻¹ * (h⁻¹ * s * h) * y ∈ S := (key _).mp (by
        have e1 : h * (h⁻¹ * s * h) * h⁻¹ = s := by group
        rw [e1]
        exact hs)
      have h3 := conj_commute_iff (h⁻¹ * s * h) w y⁻¹
      rw [inv_inv] at h3
      have h5 := (conj_commute_iff (h⁻¹ * s * h) w h).mpr
        (h3.mp (Subgroup.mem_centralizer_iff.mp h2 _ hz))
      have e1 : h * (h⁻¹ * s * h) * h⁻¹ = s := by group
      rw [e1] at h5
      exact h5
  have hyvE : v * e ∈ W ⊔ Subgroup.zpowers e :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  have hyvE' : v * e ∈ W' ⊔ Subgroup.zpowers v :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
      (Subgroup.mem_sup_left ((hmemW' e).mpr (by rw [hhe]; exact hv)))
  have hy1 : y ∈ W ⊔ Subgroup.zpowers e := Subgroup.zpowers_le.mpr hyvE hy
  have hy2 : y ∈ W' ⊔ Subgroup.zpowers v := Subgroup.zpowers_le.mpr hyvE' hy
  constructor
  · refine eq_top_iff.mpr (hgen ▸ sup_le le_sup_left fun w hw => ?_)
    have h1 := (keyW w).mp ((hmemW' w).mp hw)
    rw [← hyz w]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy1 (Subgroup.mem_sup_left h1))
      (Subgroup.inv_mem _ hy1)
  · refine eq_top_iff.mpr (hgen ▸ sup_le (fun w hw => ?_) le_sup_left)
    have e1 : y⁻¹ * (y * w * y⁻¹) * y = w := by group
    have h1 : y * w * y⁻¹ ∈ W' := (hmemW' _).mpr ((keyW _).mpr (by rw [e1]; exact hw))
    rw [← e1]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy2) (Subgroup.mem_sup_left h1)) hy2

end E214F

end CFSG.Quasithin.SimsE2
