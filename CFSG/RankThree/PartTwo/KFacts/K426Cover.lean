module

public import CFSG.RankThree.PartTwo.KFacts.K426Kit

public section

namespace CFSG.RankThree.PartTwo.KFacts.K426

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement

theorem commutator_eq_one_of_det {X : Type*} [Group X] {u v g c₁ c₂ : X}
    (hc : ⁅u, v⁆ ∈ center X) (hc3 : ⁅u, v⁆ ^ 3 = 1) (h₁ : c₁ ∈ center X) (h₂ : c₂ ∈ center X)
    (hgu : g * u * g⁻¹ = v * c₁) (hgv : g * v * g⁻¹ = u * v * c₂) : ⁅u, v⁆ = 1 := by
  set c := ⁅u, v⁆ with hcdef
  have hconj : g * c * g⁻¹ = c := by
    rw [mem_center_iff.mp hc g, mul_inv_cancel_right]
  have hcomm : g * c * g⁻¹ = ⁅v, u⁆ := by
    have e : g * c * g⁻¹ = ⁅g * u * g⁻¹, g * v * g⁻¹⁆ := by
      rw [hcdef, ← MulAut.conj_apply, ← MulAut.conj_apply, ← MulAut.conj_apply,
        map_commutatorElement]
    rw [e, hgu, hgv, commutatorElement_mul_center_left h₁, commutatorElement_mul_center_right h₂,
      commutatorElement_def, commutatorElement_def]
    group
  have hinv : c = c⁻¹ := by
    have h1 : c = ⁅v, u⁆ := hconj.symm.trans hcomm
    have h2 : c⁻¹ = ⁅v, u⁆ := by rw [hcdef, commutatorElement_inv]
    rw [h2]
    exact h1
  have h2 : c ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [hinv]
    exact mul_inv_cancel c
  calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
    _ = 1 := by rw [hc3, h2]; group

theorem inf_ker_eq_bot_of_card_le {X G : Type*} [Group X] [Group G] [Finite X]
    (ρ : X →* G) {D₀ : Subgroup X} (h : Nat.card D₀ ≤ Nat.card (D₀.map ρ)) :
    D₀ ⊓ ρ.ker = ⊥ := by
  have hsurj : Function.Surjective (ρ.subgroupMap D₀) := ρ.subgroupMap_surjective D₀
  have hk : (ρ.subgroupMap D₀).ker = ρ.ker.subgroupOf D₀ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      exact Subtype.ext hx
  have hcard : Nat.card D₀ = Nat.card (D₀.map ρ) * Nat.card (ρ.ker.subgroupOf D₀) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (ρ.subgroupMap D₀).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv, hk]
  have : Finite (D₀.map ρ) := Finite.of_surjective _ hsurj
  have hpos : 0 < Nat.card (D₀.map ρ) := Nat.card_pos
  have h1 : Nat.card (ρ.ker.subgroupOf D₀) ≤ 1 := by
    by_contra hlt
    have hlt' : 2 ≤ Nat.card (ρ.ker.subgroupOf D₀) := by omega
    have : Nat.card (D₀.map ρ) * 2 ≤ Nat.card D₀ := by
      rw [hcard]; exact Nat.mul_le_mul_left _ hlt'
    omega
  have hbot : ρ.ker.subgroupOf D₀ = ⊥ :=
    (Subgroup.eq_bot_of_card_le _ h1)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxD, hxk⟩ := mem_inf.1 hx
  have : (⟨x, hxD⟩ : D₀) ∈ ρ.ker.subgroupOf D₀ := Subgroup.mem_subgroupOf.2 hxk
  rw [hbot, Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem perfect_inf_center_eq_bot {X : Type*} [Group X] [Finite X] {n : ℕ}
    {R : Subgroup (Equiv.Perm (Fin n))} (ρ : X →* Equiv.Perm (Fin n))
    (hρker : ρ.ker = center X) (hZ : Nat.card (center X) = 3) (hρR : ρ.range = R)
    {xA xB : Equiv.Perm (Fin n)} (hxA : xA ^ 3 = 1) (hxB : xB ^ 3 = 1)
    (hfus : ∀ x ∈ R, orderOf x = 3 → ∃ k ∈ R, ∃ c, (c = xA ∨ c = xB) ∧ ∃ e,
      (e = 1 ∨ e = 2) ∧ x = k * c ^ e * k⁻¹)
    (hB : IsPGroup 3 (centralizer {xB} ⊓ R : Subgroup (Equiv.Perm (Fin n))))
    {D : Subgroup (Equiv.Perm (Fin n))}
    (hA : ⁅(centralizer {xA} ⊓ R : Subgroup (Equiv.Perm (Fin n))), centralizer {xA} ⊓ R⁆ ≤ D)
    {D₀ : Subgroup X} (hD₀ : D₀.map ρ = D) (hD₀Z : D₀ ⊓ center X = ⊥)
    {y : X} (hy : y ∉ center X) (hy3 : y ^ 3 ∈ center X) {P : Subgroup X}
    (hP : P ≤ centralizer {y}) [hperf : Group.IsPerfect P] : P ⊓ center X = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : ρ y ≠ 1 := fun h => hy (hρker ▸ MonoidHom.mem_ker.2 h)
  have hρy3 : ρ y ^ 3 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (hρker.symm ▸ hy3)
  have hyo : orderOf (ρ y) = 3 := orderOf_eq_prime hρy3 hy1
  have hyR : ρ y ∈ R := hρR ▸ ⟨y, rfl⟩
  obtain ⟨k, hkR, c, hc, e, he, hyk⟩ := hfus _ hyR hyo
  obtain ⟨kk, hkk⟩ : ∃ kk, ρ kk = k := by
    rw [← hρR] at hkR
    exact hkR
  set P₁ := P.map (MulAut.conj kk⁻¹).toMonoidHom with hP₁def
  have hperf₁ : Group.IsPerfect P₁ := Group.IsPerfect.map _
  have hc3 : c ^ 3 = 1 := by rcases hc with rfl | rfl <;> assumption
  have hρP₁ : P₁.map ρ ≤ centralizer {c} ⊓ R := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨?_, hρR ▸ ⟨_, rfl⟩⟩
    have hqy : q * y = y * q := mem_centralizer_singleton_iff.1 (hP hq)
    have hce : ρ (kk⁻¹ * q * kk) * c ^ e = c ^ e * ρ (kk⁻¹ * q * kk) := by
      have hce' : c ^ e = ρ (kk⁻¹ * y * kk) := by
        rw [map_mul, map_mul, map_inv, hkk, hyk]
        group
      rw [hce', ← map_mul, ← map_mul]
      congr 1
      calc kk⁻¹ * q * kk * (kk⁻¹ * y * kk) = kk⁻¹ * (q * y) * kk := by group
        _ = kk⁻¹ * (y * q) * kk := by rw [hqy]
        _ = kk⁻¹ * y * kk * (kk⁻¹ * q * kk) := by group
    have hmem : ρ (kk⁻¹ * q * kk) ∈ centralizer {c ^ e} := mem_centralizer_singleton_iff.2 hce
    show ρ ((MulAut.conj kk⁻¹) q) ∈ centralizer {c}
    rw [MulAut.conj_apply, inv_inv]
    rcases he with rfl | rfl
    · simpa using hmem
    · exact centralizer_pow_two_le hc3 hmem
  suffices hP₁Z : P₁ ⊓ center X = ⊥ by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwP, hwZ⟩ := mem_inf.1 hw
    have hw' : w ∈ P₁ ⊓ center X := by
      refine mem_inf.2 ⟨⟨w, hwP, ?_⟩, hwZ⟩
      show kk⁻¹ * w * kk⁻¹⁻¹ = w
      rw [inv_inv, mem_center_iff.mp hwZ kk⁻¹, inv_mul_cancel_right]
    rw [hP₁Z] at hw'
    exact hw'
  have hZ3 : IsPGroup 3 (center X) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  rcases hc with rfl | rfl
  ·
    have hPD : P₁.map ρ ≤ D := by
      have : Group.IsPerfect (P₁.map ρ) := Group.IsPerfect.map _
      exact (le_commutator_of_isPerfect hρP₁).trans hA
    have hP₁D₀ : P₁ ≤ D₀ := by
      have hM : ⁅D.comap ρ, D.comap ρ⁆ ≤ D₀ := by
        rw [commutator_le]
        intro a ha b hb
        have hdecomp : ∀ w ∈ D.comap ρ, ∃ w₀ ∈ D₀, ∃ z ∈ center X, w = w₀ * z := by
          intro w hw
          have hw' : ρ w ∈ D₀.map ρ := hD₀ ▸ hw
          obtain ⟨w₀, hw₀, hw₀w⟩ := mem_map.1 hw'
          refine ⟨w₀, hw₀, w₀⁻¹ * w, ?_, by group⟩
          rw [← hρker, MonoidHom.mem_ker, map_mul, map_inv, hw₀w, inv_mul_cancel]
        obtain ⟨a₀, ha₀, za, hza, rfl⟩ := hdecomp a ha
        obtain ⟨b₀, hb₀, zb, hzb, rfl⟩ := hdecomp b hb
        rw [commutatorElement_mul_center_left hza, commutatorElement_mul_center_right hzb,
          commutatorElement_def]
        exact D₀.mul_mem (D₀.mul_mem (D₀.mul_mem ha₀ hb₀) (D₀.inv_mem ha₀)) (D₀.inv_mem hb₀)
      have hle : P₁ ≤ D.comap ρ := map_le_iff_le_comap.1 hPD
      rw [← Subgroup.commutator_eq_self (H := P₁)]
      exact (Subgroup.commutator_mono hle hle).trans hM
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwP, hwZ⟩ := mem_inf.1 hw
    rw [← hD₀Z]
    exact mem_inf.2 ⟨hP₁D₀ hwP, hwZ⟩
  ·
    have hbot : P₁.map ρ = ⊥ := by
      have : Group.IsPerfect (P₁.map ρ) := Group.IsPerfect.map _
      exact eq_bot_of_isPerfect_of_isPGroup (hB.to_le hρP₁)
    have hP₁Z : P₁ ≤ center X := hρker ▸ (Subgroup.map_eq_bot_iff _).1 hbot
    have hP₁bot : P₁ = ⊥ := eq_bot_of_isPerfect_of_isPGroup (hZ3.to_le hP₁Z)
    rw [hP₁bot, bot_inf_eq]

end CFSG.RankThree.PartTwo.KFacts.K426
