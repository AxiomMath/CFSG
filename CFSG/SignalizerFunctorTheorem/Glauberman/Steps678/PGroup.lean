module

public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PrimeCore

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G]

theorem lt_inf_normalizer_of_lt {q : ℕ} (hq : q.Prime) {P H : Subgroup G} (hP : IsPGroup q P)
    (hHP : H ≤ P) (hne : H ≠ P) : H < P ⊓ Subgroup.normalizer (H : Set G) := by
  have : Fact q.Prime := ⟨hq⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  refine lt_of_le_of_ne (le_inf hHP Subgroup.le_normalizer) fun heq => hne ?_
  have hsub : (Subgroup.normalizer (H : Set G)).subgroupOf P = H.subgroupOf P := by
    ext x
    constructor
    · intro hx
      have hmem : (x : G) ∈ P ⊓ Subgroup.normalizer (H : Set G) := ⟨x.2, hx⟩
      rw [← heq] at hmem
      exact hmem
    · intro hx
      have hx' : (x : G) ∈ H := hx
      exact Subgroup.le_normalizer hx'
  have hnorm : Subgroup.normalizer (H.subgroupOf P : Set P) = H.subgroupOf P := by
    rw [← Subgroup.subgroupOf_normalizer_eq hHP]
    exact hsub
  have htop : H.subgroupOf P = ⊤ :=
    normalizerCondition_iff_only_full_group_self_normalizing.mp
      Group.normalizerCondition_of_isNilpotent _ hnorm
  exact le_antisymm hHP (Subgroup.subgroupOf_eq_top.mp htop)

theorem eq_bot_of_isPGroup_of_isPGroup {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    {Z S Y : Subgroup G} (hS : IsPGroup q S) (hY : IsPGroup r Y) (hZS : Z ≤ S) (hZY : Z ≤ Y) :
    Z = ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  have hdisj : Disjoint S Y := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨a, ha⟩ := hS.exists_card_eq
    obtain ⟨b, hb⟩ := hY.exists_card_eq
    rw [ha, hb]
    exact ((Nat.coprime_primes hq hr).mpr hqr).pow a b
  have hle := le_inf hZS hZY
  rw [hdisj.eq_bot] at hle
  exact le_bot_iff.mp hle

theorem eq_one_of_mem_of_isPGroup {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    {Y : Subgroup G} (hY : IsPGroup r Y) {c : G} (hc : c ∈ Y)
    (hcq : IsPGroup q (Subgroup.zpowers c)) : c = 1 := by
  have hbot := eq_bot_of_isPGroup_of_isPGroup hq hr hqr hcq hY le_rfl
    ((Subgroup.zpowers_le).mpr hc)
  have hmem : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
  rw [hbot] at hmem
  simpa using hmem

theorem commute_of_primeCoreIn {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (M : Subgroup G) {x y : G} (hx : x ∈ primeCoreIn {q} M) (hy : y ∈ primeCoreIn {r} M) :
    x * y = y * x := by
  have : Fact q.Prime := ⟨hq⟩
  have : Fact r.Prime := ⟨hr⟩
  have hxM : x ∈ M := primeCoreIn_le _ M hx
  have hyM : y ∈ M := primeCoreIn_le _ M hy
  have hX : M ≤ Subgroup.normalizer (primeCoreIn {q} M : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have hY : M ≤ Subgroup.normalizer (primeCoreIn {r} M : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ primeCoreIn {r} M := by
    have h3 : x * y * x⁻¹ ∈ primeCoreIn {r} M := (Subgroup.mem_normalizer_iff.mp (hY hxM) y).mp hy
    exact Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hy)
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ primeCoreIn {q} M := by
    have h3 : y * x⁻¹ * y⁻¹ ∈ primeCoreIn {q} M :=
      (Subgroup.mem_normalizer_iff.mp (hX hyM) x⁻¹).mp (Subgroup.inv_mem _ hx)
    have h4 := Subgroup.mul_mem _ hx h3
    simpa [mul_assoc] using h4
  have hdisj : Disjoint (primeCoreIn {q} M) (primeCoreIn {r} M) := by
    apply Subgroup.disjoint_of_coprime_natCard
    obtain ⟨a, ha⟩ := (isPGroup_primeCoreIn hq M).exists_card_eq
    obtain ⟨b, hb⟩ := (isPGroup_primeCoreIn hr M).exists_card_eq
    rw [ha, hb]
    exact ((Nat.coprime_primes hq hr).mpr hqr).pow a b
  have h5 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ primeCoreIn {q} M ⊓ primeCoreIn {r} M := ⟨h2, h1⟩
    rw [hdisj.eq_bot] at hmem
    simpa using hmem
  calc x * y = x * y * x⁻¹ * y⁻¹ * y * x := by group
    _ = y * x := by rw [h5, one_mul]

theorem inf_centralizer_ne_bot {q : ℕ} (hq : q.Prime) {E Y : Subgroup G} (hE : IsPGroup q E)
    (hY : IsPGroup q Y) (hY0 : Y ≠ ⊥) (hEY : E ≤ Subgroup.normalizer (Y : Set G)) :
    Y ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have hmod := centralizer_card_modEq q hq E Y hE hEY
  have hdvd : q ∣ Nat.card Y := by
    rcases hY.card_eq_or_dvd with h1 | h1
    · exact absurd ((Subgroup.eq_bot_iff_card Y).mpr h1) hY0
    · exact h1
  have hdvd' : q ∣ Nat.card (Y ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) :=
    (hmod.dvd_iff dvd_rfl).mp hdvd
  intro hbot
  rw [hbot, Subgroup.card_bot] at hdvd'
  exact hq.not_dvd_one hdvd'

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
