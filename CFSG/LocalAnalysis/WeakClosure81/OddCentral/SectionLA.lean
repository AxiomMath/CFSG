module
public import CFSG.LocalAnalysis.WeakClosure81.OddCentral.OddTranspositions
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Timmesfeld.Bridge.Asc72

theorem exists_fixed_mem_coset {Y : Type} [Group Y] [Finite Y] {Z : Subgroup Y} [hZn : Z.Normal]
    (hZodd : Odd (Nat.card Z)) {u : Y} (hu : u * u = 1) {a : Y}
    (ha : u * a * u⁻¹ * a⁻¹ ∈ Z) : ∃ z ∈ Z, u * (a * z) * u⁻¹ = a * z := by
  classical
  haveI : Fintype Z := Fintype.ofFinite Z
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hmem : ∀ z ∈ Z, a⁻¹ * (u * (a * z) * u⁻¹) ∈ Z := by
    intro z hz
    have h1 : a⁻¹ * (u * a * u⁻¹ * a⁻¹) * a ∈ Z := by
      simpa using hZn.conj_mem _ ha a⁻¹
    have h2 : u * z * u⁻¹ ∈ Z := hZn.conj_mem z hz u
    rw [show a⁻¹ * (u * (a * z) * u⁻¹) = (a⁻¹ * (u * a * u⁻¹ * a⁻¹) * a) * (u * z * u⁻¹) by
      group]
    exact Z.mul_mem h1 h2
  let f : Function.End Z := fun z => ⟨a⁻¹ * (u * (a * z) * u⁻¹), hmem z z.2⟩
  have hf2 : f ^ 2 ^ 1 = 1 := by
    funext z
    apply Subtype.ext
    show a⁻¹ * (u * (a * (a⁻¹ * (u * (a * z) * u⁻¹))) * u⁻¹) = z
    rw [show a⁻¹ * (u * (a * (a⁻¹ * (u * (a * ↑z) * u⁻¹))) * u⁻¹) =
      a⁻¹ * ((u * u) * (a * z) * (u⁻¹ * u⁻¹)) by group, hu, ← mul_inv_rev, hu]
    group
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf2
  rw [← Nat.card_eq_fintype_card] at hmod
  have hpos : 0 < Fintype.card (Function.fixedPoints f) := by
    obtain ⟨k, hk⟩ := hZodd
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨⟨z, hz⟩⟩ := Fintype.card_pos_iff.mp hpos
  refine ⟨z, z.2, ?_⟩
  have h := congrArg Subtype.val hz
  have : u * (a * z) * u⁻¹ = a * (a⁻¹ * (u * (a * z) * u⁻¹)) := by group
  rw [this]
  exact congrArg (a * ·) h

theorem la_section {Y : Type} [Group Y] [Finite Y] {D : Set Y} (hD : IsOddTransp D)
    (hDc : ∀ x ∈ D, ∀ g : Y, g * x * g⁻¹ ∈ D) {d e : Y} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e)
    (hc : Commute d e) {X Z : Subgroup Y} [hZn : Z.Normal] (hXodd : Odd (Nat.card X))
    (hXd : ∀ x ∈ X, d * x * d⁻¹ ∈ X) (hZX : Z ≤ X) {a : Y} (ha : a ∈ X)
    (h : (d * e) * a * (d * e)⁻¹ * a⁻¹ ∈ Z) : d * a * d⁻¹ * a⁻¹ ∈ Z := by
  have hdd : d * d = 1 := by
    have := pow_orderOf_eq_one d; rw [hD.1 d hd, pow_two] at this; exact this
  have hee : e * e = 1 := by
    have := pow_orderOf_eq_one e; rw [hD.1 e he, pow_two] at this; exact this
  have huu : (d * e) * (d * e) = 1 := by
    rw [show d * e * (d * e) = d * (e * d) * e by group, ← hc.eq,
      show d * (d * e) * e = (d * d) * (e * e) by group, hdd, hee, one_mul]
  have hZodd : Odd (Nat.card Z) := Odd.of_dvd_nat hXodd (Subgroup.card_dvd_of_le hZX)
  obtain ⟨z, hz, hfix⟩ := exists_fixed_mem_coset hZodd huu h
  have hx : a * z ∈ X := X.mul_mem ha (hZX hz)
  have hcomm := commute_of_commute_mul hD hDc hd he hde hc hXodd hXd hx
    (by show a * z * (d * e) = d * e * (a * z)
        calc a * z * (d * e) = (d * e) * (a * z) * (d * e)⁻¹ * (d * e) := by rw [hfix]
          _ = d * e * (a * z) := by group)
  have hdx : d * (a * z) * d⁻¹ = a * z := by rw [← hcomm.eq]; group
  have : d * a * d⁻¹ * a⁻¹ = (a * z) * (d * z⁻¹ * d⁻¹) * a⁻¹ := by
    calc d * a * d⁻¹ * a⁻¹ = (d * (a * z) * d⁻¹) * (d * z⁻¹ * d⁻¹) * a⁻¹ := by group
      _ = (a * z) * (d * z⁻¹ * d⁻¹) * a⁻¹ := by rw [hdx]
  rw [this, show a * z * (d * z⁻¹ * d⁻¹) * a⁻¹ = a * (z * (d * z⁻¹ * d⁻¹)) * a⁻¹ by group]
  exact hZn.conj_mem _ (Z.mul_mem hz (hZn.conj_mem _ (Z.inv_mem hz) d)) a

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

