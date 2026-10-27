module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CyclicN0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Stellmacher.L3YC

section Coset

variable {G : Type} [Group G]

theorem exists_fixed_mem_coset {p : ℕ} [Fact p.Prime] {D N : Subgroup G} (hD : IsPGroup p ↥D)
    (hN : ¬ p ∣ Nat.card ↥N) (l : G)
    (hcl : ∀ d ∈ D, ∀ g : G, l⁻¹ * g ∈ N → l⁻¹ * (d * g * d⁻¹) ∈ N) :
    ∃ n ∈ N, ∀ d ∈ D, d * (l * n) * d⁻¹ = l * n := by
  classical
  let X : Type _ := {g : G // l⁻¹ * g ∈ N}
  let _ : MulAction ↥D X :=
    { smul := fun d g => ⟨(d : G) * g * (d : G)⁻¹, hcl d d.2 g g.2⟩
      one_smul := fun g => Subtype.ext (by
        change ((1 : ↥D) : G) * (g : G) * ((1 : ↥D) : G)⁻¹ = g
        simp)
      mul_smul := fun a b g => Subtype.ext (by
        change ((a * b : ↥D) : G) * (g : G) * ((a * b : ↥D) : G)⁻¹ =
          (a : G) * ((b : G) * (g : G) * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  have hcard : Nat.card X = Nat.card ↥N := by
    refine Nat.card_congr ⟨fun g => ⟨l⁻¹ * g.1, g.2⟩, fun n => ⟨l * n.1, by simp⟩, ?_, ?_⟩
    · intro g
      apply Subtype.ext
      simp
    · intro n
      apply Subtype.ext
      simp
  obtain ⟨g, hg⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card X (by rw [hcard]; exact hN)
  refine ⟨l⁻¹ * g.1, g.2, fun d hd => ?_⟩
  have h := MulAction.mem_fixedPoints.mp hg ⟨d, hd⟩
  have h' := congrArg Subtype.val h
  have : (d : G) * g.1 * (d : G)⁻¹ = g.1 := h'
  simpa using this

end Coset

section Lift

variable {G : Type} [Group G] [Finite G]

theorem coset_closed_of_mem_N0 {L : Subgroup G} {d : G} (hd : d ∈ N0 L) {l g : G} (hl : l ∈ L)
    (hg : l⁻¹ * g ∈ pCoreOf 2 L) : l⁻¹ * (d * g * d⁻¹) ∈ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hdN, hdc⟩ := hd
  have hdO : d ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L hdN
  have hlO : ∀ q ∈ pCoreOf 2 L, ∀ x ∈ L, x⁻¹ * q * x ∈ pCoreOf 2 L := by
    intro q hq x hx
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (L.inv_mem hx)) q).mp hq
    simpa using this
  set q : G := l⁻¹ * g with hq
  have hgq : g = l * q := by rw [hq]; group
  have h1 : d * q * d⁻¹ ∈ pCoreOf 2 L := (Subgroup.mem_normalizer_iff.mp hdO q).mp hg
  have h2 : d * l * d⁻¹ * l⁻¹ ∈ pCoreOf 2 L := hdc l hl
  have h3 : l⁻¹ * (d * l * d⁻¹ * l⁻¹) * l ∈ pCoreOf 2 L := hlO _ h2 l hl
  have e : l⁻¹ * (d * g * d⁻¹) =
      (l⁻¹ * (d * l * d⁻¹ * l⁻¹) * l) * (d * q * d⁻¹) := by
    rw [hgq]; group
  rw [e]
  exact (pCoreOf 2 L).mul_mem h3 h1

theorem exists_mem_centralizer_coset {L : Subgroup G} {y : G} (hy : y ∈ N0 L) (hy3 : y ^ 3 = 1)
    {l : G} (hl : l ∈ L) : ∃ p ∈ pCoreOf 2 L, y * (l * p) = (l * p) * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hD : IsPGroup 3 ↥(Subgroup.zpowers y) := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [hy3]
  have hN : ¬ 3 ∣ Nat.card ↥(pCoreOf 2 L) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCoreOf_isPGroup 2 L)
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (hk ▸ h)
    omega
  have hDN : Subgroup.zpowers y ≤ N0 L := Subgroup.zpowers_le.mpr hy
  obtain ⟨n, hn, hfix⟩ := exists_fixed_mem_coset hD hN l
    (fun d hd g hg => coset_closed_of_mem_N0 (hDN hd) hl hg)
  exact ⟨n, hn, mul_inv_eq_iff_eq_mul.mp (hfix y (Subgroup.mem_zpowers y))⟩

end Lift

end Stellmacher.L3YC

end CFSG.Quasithin
