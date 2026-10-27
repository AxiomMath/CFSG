module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16c13bcA_exists_fixed_of_odd {Γ : Type*} [Group Γ] {X : Type*} [MulAction Γ X] {p : ℕ}
    [Fact p.Prime] (hΓ : IsPGroup p Γ) (S : Set X) [Finite S]
    (hS : ∀ g : Γ, ∀ x ∈ S, g • x ∈ S) (hodd : ¬ p ∣ Nat.card S) :
    ∃ x ∈ S, ∀ g : Γ, g • x = x := by
  let T : SubMulAction Γ X := ⟨S, hS⟩
  have h := hΓ.card_modEq_card_fixedPoints ↥T
  by_contra hne
  have hempty : IsEmpty (MulAction.fixedPoints Γ ↥T) := by
    refine ⟨fun ⟨x, hx⟩ => hne ⟨x.1, x.2, fun g => ?_⟩⟩
    exact congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx g)
  have h0 : Nat.card (MulAction.fixedPoints Γ ↥T) = 0 := Nat.card_of_isEmpty
  rw [h0] at h
  exact hodd ((Nat.modEq_zero_iff_dvd).1 h)

private lemma s16c13bcA_mulAut_smul_eq_one {W : Type*} [Group W] (q : MulAut W) {w : W}
    (hq : q • w = 1) : w = 1 := by
  have h1 : q⁻¹ • (q • w) = q⁻¹ • (1 : W) := by rw [hq]
  rw [inv_smul_smul] at h1
  simpa [MulAut.smul_def, map_one] using h1

private lemma s16c13bcA_orbit_mulAut_image {W : Type*} [Group W] {H P : Subgroup (MulAut W)}
    (hPH : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H)
    {q : MulAut W} (hq : q ∈ P) (w : W) :
    MulAction.orbit ↥H (q • w) = q '' MulAction.orbit ↥H w := by
  ext y
  constructor
  · intro hy
    rw [MulAction.mem_orbit_iff] at hy
    obtain ⟨h, hh⟩ := hy
    refine (Set.mem_image q (MulAction.orbit ↥H w) y).mpr
      ⟨(q⁻¹ * (h : MulAut W) * q) • w, ?_, ?_⟩
    · rw [MulAction.mem_orbit_iff]
      exact ⟨⟨q⁻¹ * (h : MulAut W) * q,
        by simpa using hPH q⁻¹ (P.inv_mem hq) (h : MulAut W) h.2⟩, rfl⟩
    · have hscalar : q * (q⁻¹ * (h : MulAut W) * q) = (h : MulAut W) * q := by
        group
      rw [← hh]
      change (q * (q⁻¹ * (h : MulAut W) * q)) w = ((h : MulAut W) * q) w
      rw [hscalar]
  · intro hy
    obtain ⟨x, hx, hxy⟩ := (Set.mem_image q (MulAction.orbit ↥H w) y).mp hy
    rw [MulAction.mem_orbit_iff] at hx
    obtain ⟨h, hh⟩ := hx
    rw [MulAction.mem_orbit_iff]
    refine ⟨⟨q * (h : MulAut W) * q⁻¹, hPH q hq (h : MulAut W) h.2⟩, ?_⟩
    have hscalar : q * (h : MulAut W) * q⁻¹ * q = q * (h : MulAut W) := by
      group
    rw [Subgroup.smul_def, ← hxy, ← hh, Subgroup.smul_def]
    change ((q * (h : MulAut W) * q⁻¹) * q) w = (q * (h : MulAut W)) w
    rw [hscalar]

theorem s16c13bcA_exists_fixed_odd_orbit {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (hW1 : ∃ w : W, w ≠ 1) {H P : Subgroup (MulAut W)}
    (hP : IsPGroup 2 ↥P) (hPH : ∀ p ∈ P, ∀ h ∈ H, p * h * p⁻¹ ∈ H)
    (hT : ∀ w₁ w₂ : W, w₁ ≠ 1 → w₂ ≠ 1 → Odd (Nat.card (MulAction.orbit ↥H w₁)) →
      Odd (Nat.card (MulAction.orbit ↥H w₂)) → w₂ ∈ MulAction.orbit ↥H w₁) :
    ∃ n : W, n ≠ 1 ∧ (∀ p ∈ P, p n = n) ∧ Odd (Nat.card (MulAction.orbit ↥H n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥H :=
    Finite.of_injective (fun x : ↥H => (x : MulAut W)) (fun _ _ h => Subtype.ext h)
  obtain ⟨w₀, hw₀⟩ := hW1
  have hord : orderOf w₀ = 2 := orderOf_eq_prime (hW w₀) hw₀
  have h2dvd : 2 ∣ Nat.card W := by
    rw [← hord]
    exact orderOf_dvd_natCard w₀
  let S : Sylow 2 ↥H := default
  have hfix1 : (1 : W) ∈ MulAction.fixedPoints ↥S W := by
    rw [MulAction.mem_fixedPoints]
    intro g
    simpa [Subgroup.smul_def, MulAut.smul_def] using map_one (g : MulAut W)
  obtain ⟨n, hnfix, h1n⟩ :=
    S.isPGroup'.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := W) h2dvd hfix1
  have hn_ne : n ≠ 1 := Ne.symm h1n
  have hSle : (S : Subgroup ↥H) ≤ MulAction.stabilizer ↥H n := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff]
    have h := (MulAction.mem_fixedPoints.1 hnfix) ⟨s, hs⟩
    simpa [Subgroup.smul_def, MulAut.smul_def] using h
  have hidxdvd : (MulAction.stabilizer ↥H n).index ∣ (S : Subgroup ↥H).index :=
    Subgroup.index_dvd_of_le hSle
  have hSodd : Odd (S : Subgroup ↥H).index :=
    Nat.not_even_iff_odd.1 (by simpa [even_iff_two_dvd] using S.not_dvd_index)
  have hstabodd : Odd (MulAction.stabilizer ↥H n).index := hSodd.of_dvd_nat hidxdvd
  have hnodd : Odd (Nat.card (MulAction.orbit ↥H n)) := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer ↥H n]
    exact hstabodd
  let R : Set W := {w | w ≠ 1 ∧ Odd (Nat.card (MulAction.orbit ↥H w))}
  have hnR : n ∈ R := ⟨hn_ne, hnodd⟩
  have hRorb : R = MulAction.orbit ↥H n := by
    ext x
    constructor
    · intro hx
      exact hT n x hn_ne hx.1 hnodd hx.2
    · intro hx
      rw [MulAction.mem_orbit_iff] at hx
      obtain ⟨h, hh⟩ := hx
      have hx_ne : x ≠ 1 := by
        rw [← hh]
        intro hcon
        exact hn_ne (s16c13bcA_mulAut_smul_eq_one (h : MulAut W)
          (by simpa [Subgroup.smul_def] using hcon))
      have hxodd : Odd (Nat.card (MulAction.orbit ↥H x)) := by
        rw [← hh, MulAction.orbit_smul]
        exact hnodd
      exact ⟨hx_ne, hxodd⟩
  have hRodd : Odd (Nat.card R) := by
    rw [congrArg (fun s : Set W => Nat.card s) hRorb]
    exact hnodd
  have hRnot : ¬ 2 ∣ Nat.card R := hRodd.not_two_dvd_nat
  haveI : Finite R :=
    Finite.of_injective (fun x : R => (x : W)) (fun _ _ h => Subtype.ext h)
  have hSinv : ∀ g : ↥P, ∀ x ∈ R, g • x ∈ R := by
    intro g x hx
    have hq : (g : MulAut W) ∈ P := g.2
    have hne : (g : MulAut W) • x ≠ 1 := by
      intro hcon
      exact hx.1 (s16c13bcA_mulAut_smul_eq_one (g : MulAut W) hcon)
    have hcard : Nat.card (MulAction.orbit ↥H ((g : MulAut W) • x)) =
        Nat.card (MulAction.orbit ↥H x) := by
      rw [s16c13bcA_orbit_mulAut_image hPH hq x]
      exact Nat.card_image_of_injective (g : MulAut W).injective
        (MulAction.orbit ↥H x)
    refine ⟨?_, ?_⟩
    · exact hne
    · change Odd (Nat.card (MulAction.orbit ↥H ((g : MulAut W) • x)))
      rw [hcard]
      exact hx.2
  obtain ⟨m, hmR, hmfix⟩ :=
    s16c13bcA_exists_fixed_of_odd (Γ := ↥P) (p := 2) hP R hSinv hRnot
  exact ⟨m, hmR.1, fun p hp => by
    have h := hmfix ⟨p, hp⟩
    simpa [Subgroup.smul_def, MulAut.smul_def] using h, hmR.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
