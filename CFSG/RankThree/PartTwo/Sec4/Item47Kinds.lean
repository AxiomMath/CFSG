module

public import CFSG.GH74.GLS.IVK.L2.Fixed
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Generic

variable {X Y : Type*} [Group X] [Group Y]

@[expose] def CubeInner (X : Type*) [Group X] : Prop :=
  ∀ τ : MulAut X, τ ^ 3 = 1 → IsInnerAut τ

theorem isInnerAut_of_pow_three_eq_one {τ : MulAut X} (h3 : τ ^ 3 = 1) {m : ℕ} (hm : ¬ 3 ∣ m)
    (hτm : IsInnerAut (τ ^ m)) : IsInnerAut τ := by
  have hmm : m * m % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  have hτ : τ = (τ ^ m) ^ m := by
    rw [← pow_mul, ← Nat.mod_add_div (m * m) 3, pow_add, pow_mul, h3, one_pow, mul_one, hmm,
      pow_one]
  rw [hτ]
  exact Subgroup.pow_mem _ hτm m

theorem cubeInner_of_not_three_dvd_card_outer (hX : ¬ 3 ∣ Nat.card (Outer X)) : CubeInner X := by
  intro τ h3
  have hb3 : (QuotientGroup.mk τ : Outer X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
  have hd : orderOf (QuotientGroup.mk τ : Outer X) ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3'
  · have h1' : (QuotientGroup.mk τ : Outer X) = 1 := orderOf_eq_one_iff.1 h1
    exact (QuotientGroup.eq_one_iff (N := inner X) τ).1 h1'
  · exact absurd (h3' ▸ orderOf_dvd_natCard _) hX

theorem CubeInner.of_mulEquiv (hY : CubeInner Y) (e : X ≃* Y) : CubeInner X := by
  intro τ h3
  have h3' : MulAut.congr e τ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  exact (isInnerAut_congr e τ).mp (hY _ h3')

theorem cubeInner_of_center_quotient [Group.IsPerfect X]
    (hY : CubeInner (X ⧸ Subgroup.center X)) : CubeInner X := by
  intro τ h3
  apply isInnerAut_of_isInnerAut_centerDescend
  apply hY
  rw [← map_pow, h3, map_one]

theorem not_three_dvd_card_outer_of_le_two [Finite X] (h : Nat.card (Outer X) ≤ 2) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have : Finite (Outer X) := inferInstance
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  intro h3
  have := Nat.le_of_dvd hpos h3
  omega

theorem card_outer_le_two_of_card_mulAut_le [Finite X] (hZ : Subgroup.center X = ⊥)
    (h : Nat.card (MulAut X) ≤ 2 * Nat.card X) : Nat.card (Outer X) ≤ 2 := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    intro x y hxy
    have h1 : x⁻¹ * y ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h2 := congrArg (fun φ : MulAut X => φ z) hxy
      simp only [MulAut.conj_apply] at h2
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h2]
        _ = x⁻¹ * y * z := by group
    rw [hZ, Subgroup.mem_bot] at h1
    exact (inv_mul_eq_one.mp h1)
  have hInn : Nat.card (inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hcard := (inner X).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hle : Nat.card (Outer X) * Nat.card X ≤ 2 * Nat.card X := by
    rw [← hcard]
    exact h
  exact Nat.le_of_mul_le_mul_right hle hpos

end Generic

section Induced

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_cubeInner {M : Type*} [Group M] (e : L ⧸ aschbacherSolvableCore 3 L ≃* M)
    (hM : CubeInner M) {a : G} (ha3 : a ^ 3 = 1) (hout : InducesOuterTheta a L) : False := by
  obtain ⟨ha, -⟩ := id hout
  exact (not_isInnerAut_inducedAutHom_iff L e ha).mpr hout
    (hM _ (inducedAutHom_pow_eq_one L e ha ha3))

theorem false_of_inducesKind_diagonal {M : Type*} [Group M] {P : PinnedAut M}
    (hP : ∀ τ ∈ P.inndiag, τ ^ 3 = 1 → IsInnerAut τ) {e : L ⧸ aschbacherSolvableCore 3 L ≃* M}
    {a : G} (h : InducesKind L P e a .diagonal) (ha3 : a ^ 3 = 1) : False := by
  obtain ⟨ha, hd, hnot⟩ := h
  exact hnot (hP _ hd (inducedAutHom_pow_eq_one L e ha ha3))

theorem three_dvd_card_of_isField {M : Type*} [Group M] {P : PinnedAut M} {Γ : Type*} [Group Γ]
    [Finite Γ] {ψ : Γ →* MulAut M} (hP : P.field = ψ.range) {τ : MulAut M} (hτ : P.IsField τ)
    (h3 : τ ^ 3 = 1) : 3 ∣ Nat.card Γ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ, hφ1, d, -, rfl⟩ := hτ
  have hφ3 : φ ^ 3 = 1 := by
    have h1 : (d * φ * d⁻¹) ^ 3 = d * φ ^ 3 * d⁻¹ := conj_pow
    rw [h1] at h3
    calc φ ^ 3 = d⁻¹ * (d * φ ^ 3 * d⁻¹) * d := by group
      _ = 1 := by rw [h3]; group
  have hord : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
  rw [hP] at hφ
  obtain ⟨σ, rfl⟩ := hφ
  have h1 : orderOf (ψ σ) ∣ orderOf σ := orderOf_map_dvd ψ σ
  rw [hord] at h1
  exact h1.trans (orderOf_dvd_natCard σ)

theorem three_dvd_card_of_inducesKind_field {M : Type*} [Group M] {P : PinnedAut M}
    {Γ : Type*} [Group Γ] [Finite Γ] {ψ : Γ →* MulAut M} (hP : P.field = ψ.range)
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* M} {a : G} (h : InducesKind L P e a .field)
    (ha3 : a ^ 3 = 1) : 3 ∣ Nat.card Γ := by
  obtain ⟨ha, hf⟩ := h
  exact three_dvd_card_of_isField hP hf (inducedAutHom_pow_eq_one L e ha ha3)

end Induced

theorem card_ringAut_eq {K : Type*} [Field K] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) : Nat.card (K ≃+* K) = f :=
  (CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hf
    hK).choose_spec.2.2.2.1

theorem finite_ringAut {K : Type*} [Field K] {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) : Finite (K ≃+* K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ hp.ne_zero)
  infer_instance

end CFSG.RankThree.PartTwo.Sec4
