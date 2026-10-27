module

public import Mathlib.RepresentationTheory.Invariants

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open Module

private theorem finrank_le_two_mul_finrank_invariants_zpowers
    {E : Type} [Group E] (k : Type) [Field k] [CharP k 2]
    {C : Type} [AddCommGroup C] [Module k C] [Module.Finite k C]
    (ρ : Representation k E C) {x : E} (hx2 : x * x = 1) :
    Module.finrank k C ≤
      2 * Module.finrank k (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)) := by
  have hgen : ∀ y : ↥(Subgroup.zpowers x),
      y ∈ Subgroup.zpowers (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) := by
    intro y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hker : LinearMap.ker ((ρ x : Module.End k C) - 1) =
      Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype) := by
    ext v
    rw [LinearMap.mem_ker]
    show ρ x v - v = 0 ↔ v ∈ Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype)
    rw [sub_eq_zero]
    exact (Representation.mem_invariants_iff_of_forall_mem_zpowers (ρ := ρ.comp
      (Subgroup.zpowers x).subtype) ⟨x, Subgroup.mem_zpowers x⟩ hgen v).symm
  have hx2end : (ρ x) * (ρ x) = 1 := by rw [← map_mul, hx2, map_one]
  have hneg : ∀ w : C, -w = w := by
    intro w
    rw [neg_eq_iff_add_eq_zero, ← two_smul k w, CharTwo.two_eq_zero, zero_smul]
  have hfv : ∀ v : C, ((ρ x : Module.End k C) - 1) (((ρ x : Module.End k C) - 1) v) = 0 := by
    intro v
    have h1 : ρ x (ρ x v) = v := by
      have h2 : (ρ x * ρ x) v = (1 : Module.End k C) v := by rw [hx2end]
      simpa [Module.End.mul_apply] using h2
    have hsub : ∀ a b : C, a - b = a + b := fun a b => by rw [sub_eq_add_neg, hneg b]
    have hv0 : v + v = 0 := by rw [← two_smul k v, CharTwo.two_eq_zero, zero_smul]
    have hw0 : ρ x v + ρ x v = 0 := by
      rw [← two_smul k (ρ x v), CharTwo.two_eq_zero, zero_smul]
    change ρ x (ρ x v - v) - (ρ x v - v) = 0
    rw [map_sub, h1, hsub, hsub, hsub]
    calc v + ρ x v + (ρ x v + v) = (v + v) + (ρ x v + ρ x v) := by abel
      _ = 0 := by rw [hv0, hw0, add_zero]
  have hle : LinearMap.range ((ρ x : Module.End k C) - 1) ≤
      LinearMap.ker ((ρ x : Module.End k C) - 1) := by
    rintro y ⟨v, rfl⟩
    exact hfv v
  have hmono : Module.finrank k (LinearMap.range ((ρ x : Module.End k C) - 1)) ≤
      Module.finrank k (LinearMap.ker ((ρ x : Module.End k C) - 1)) :=
    Submodule.finrank_mono hle
  have hrank := LinearMap.finrank_range_add_finrank_ker ((ρ x : Module.End k C) - 1)
  rw [hker] at hrank hmono
  omega

private theorem finrank_invariants_quotientToInvariants
    {E : Type} [Group E] (k : Type) [Field k] [CharP k 2]
    {C : Type} [AddCommGroup C] [Module k C]
    (ρ : Representation k E C) (S : Subgroup E) [S.Normal] :
    Module.finrank k (Representation.invariants
        (Representation.quotientToInvariants ρ S)) =
      Module.finrank k (Representation.invariants ρ) := by
  have hWle : Representation.invariants ρ ≤
      Representation.invariants (ρ.comp S.subtype) := by
    intro v hv
    rw [Representation.mem_invariants] at hv ⊢
    intro s
    exact hv (s : E)
  have hEq : Representation.invariants
        (Representation.quotientToInvariants ρ S) =
      (Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype := by
    ext v
    rw [Submodule.mem_comap]
    constructor
    · intro hv
      rw [Representation.mem_invariants] at hv
      intro g
      have h := hv (QuotientGroup.mk g)
      rw [Representation.ofQuotient_coe_apply] at h
      simpa using congrArg Subtype.val h
    · intro hv
      rw [Representation.mem_invariants]
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [Representation.ofQuotient_coe_apply]
        refine Subtype.ext ?_
        exact (Representation.mem_invariants ρ (v := (v : C))).mp hv g
  rw [hEq]
  have hmap : ((Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype).map
        (Representation.invariants (ρ.comp S.subtype)).subtype =
      Representation.invariants ρ := by
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr hWle
  have hfr : Module.finrank k ↥(((Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype).map
        (Representation.invariants (ρ.comp S.subtype)).subtype) =
      Module.finrank k ↥((Representation.invariants ρ).comap
        (Representation.invariants (ρ.comp S.subtype)).subtype) :=
    Submodule.finrank_map_subtype_eq _ _
  rw [hmap] at hfr
  exact hfr.symm


private theorem quotient_zpowers_card_and_involutions
    {m : ℕ} {E : Type} [Group E] [Finite E] {x : E}
    (hsq : ∀ e : E, e * e = 1) (hx1 : x ≠ 1) (hcard : Nat.card E = 2 ^ (m + 1))
    [hSnorm : (Subgroup.zpowers x : Subgroup E).Normal] :
    Nat.card (E ⧸ Subgroup.zpowers x) = 2 ^ m ∧
      ∀ e : E ⧸ Subgroup.zpowers x, e * e = 1 := by
  have hScard : Nat.card (Subgroup.zpowers x : Subgroup E) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hsq x) hx1]
  constructor
  · have h := Subgroup.card_mul_index (Subgroup.zpowers x : Subgroup E)
    rw [hScard, hcard, pow_succ] at h
    rw [← Subgroup.index_eq_card]
    omega
  · intro e
    induction e using QuotientGroup.induction_on with
    | H g =>
      rw [← QuotientGroup.mk_mul, hsq g]
      exact QuotientGroup.mk_one _

private theorem finrank_le_two_pow_mul_finrank_invariants_aux :
    ∀ (m : ℕ) (E : Type) [Group E] [Finite E] (k : Type) [Field k] [CharP k 2]
      (C : Type) [AddCommGroup C] [Module k C] [Module.Finite k C]
      (ρ : Representation k E C), (∀ e : E, e * e = 1) → Nat.card E = 2 ^ m →
      Module.finrank k C ≤ 2 ^ m * Module.finrank k (Representation.invariants ρ) := by
  intro m
  induction m with
  | zero =>
    intro E _ _ k _ _ C _ _ _ ρ hsq hcard
    have h1 : Nat.card E = 1 := by simpa using hcard
    haveI : Subsingleton E := (Nat.card_eq_one_iff_unique.mp h1).1
    have htop : Representation.invariants ρ = ⊤ := by
      rw [eq_top_iff]
      intro v _
      rw [Representation.mem_invariants]
      intro g
      rw [Subsingleton.elim g 1, map_one]
      rfl
    rw [htop, finrank_top, pow_zero, one_mul]
  | succ m ih =>
    intro E _ _ k _ _ C _ _ _ ρ hsq hcard
    have hcard1 : 1 < Nat.card E := by rw [hcard]; exact Nat.one_lt_two_pow (by omega)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp hcard1
    obtain ⟨x, hx1⟩ := exists_ne (1 : E)
    have hx2 : x ^ 2 = 1 := by rw [pow_two]; exact hsq x
    have hcomm : ∀ a b : E, a * b = b * a := by
      intro a b
      have hab : (a * b)⁻¹ = a * b := by rw [inv_eq_iff_mul_eq_one]; exact hsq (a * b)
      rw [← hab, mul_inv_rev, inv_eq_iff_mul_eq_one.mpr (hsq b),
        inv_eq_iff_mul_eq_one.mpr (hsq a)]
    haveI hSnorm : (Subgroup.zpowers x : Subgroup E).Normal :=
      ⟨fun n hn g => by
        rw [show g * n * g⁻¹ = n by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]]
        exact hn⟩
    obtain ⟨hquotcard, hsq'⟩ := quotient_zpowers_card_and_involutions hsq hx1 hcard
    have hIH := ih (E ⧸ Subgroup.zpowers x) k
      (Representation.invariants (ρ.comp (Subgroup.zpowers x).subtype))
      (Representation.quotientToInvariants ρ (Subgroup.zpowers x)) hsq' hquotcard
    have hstep1 : Module.finrank k C ≤
        2 * Module.finrank k (Representation.invariants (ρ.comp
          (Subgroup.zpowers x).subtype)) :=
      finrank_le_two_mul_finrank_invariants_zpowers k ρ (by simpa [pow_two] using hx2)
    have hstep2 : Module.finrank k (Representation.invariants
          (Representation.quotientToInvariants ρ (Subgroup.zpowers x))) =
        Module.finrank k (Representation.invariants ρ) :=
      finrank_invariants_quotientToInvariants k ρ (Subgroup.zpowers x)
    calc Module.finrank k C
        ≤ 2 * Module.finrank k (Representation.invariants (ρ.comp
            (Subgroup.zpowers x).subtype)) := hstep1
      _ ≤ 2 * (2 ^ m * Module.finrank k (Representation.invariants
            (Representation.quotientToInvariants ρ (Subgroup.zpowers x)))) :=
          Nat.mul_le_mul_left 2 hIH
      _ = 2 * (2 ^ m * Module.finrank k (Representation.invariants ρ)) := by rw [hstep2]
      _ = 2 ^ (m + 1) * Module.finrank k (Representation.invariants ρ) := by
          rw [pow_succ]; ring

theorem finrank_le_two_pow_mul_finrank_invariants
    (m : ℕ) {E : Type} [Group E] [Finite E] {k : Type} [Field k] [CharP k 2]
    {C : Type} [AddCommGroup C] [Module k C] [Module.Finite k C]
    (ρ : Representation k E C) (hsq : ∀ e : E, e * e = 1) (hcard : Nat.card E = 2 ^ m) :
    Module.finrank k C ≤ 2 ^ m * Module.finrank k (Representation.invariants ρ) :=
  finrank_le_two_pow_mul_finrank_invariants_aux m E k C ρ hsq hcard

end CFSG.RankThree.GF2n.Tim81.Sec2
