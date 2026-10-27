module

public import CFSG.Blueprint.Catalog
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2Field
import CFSG.LieType.Chevalley.ExactG2FiniteOrder
import CFSG.RankThree.PartTwo.KFacts.AutG2OrderThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley
open CFSG.Blueprint (LieModel)

private theorem padicValNat_g2_orders {a : ℕ} (ha2 : 2 ≤ a) (ha3 : ¬ 3 ∣ a) :
    padicValNat 3 ((a ^ 3) ^ 6 * ((a ^ 3) ^ 6 - 1) * ((a ^ 3) ^ 2 - 1)) =
        2 * padicValNat 3 (a ^ 2 - 1) + 3 ∧
      padicValNat 3 (a ^ 6 * (a ^ 6 - 1) * (a ^ 2 - 1)) = 2 * padicValNat 3 (a ^ 2 - 1) + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd 3 := by decide
  have hu1 : 1 < a ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have hu3 : ¬ 3 ∣ a ^ 2 := fun h => ha3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hdvd : 3 ∣ a ^ 2 - 1 := by
    have h1 : a ^ 2 % 3 = 1 := by
      have hmod : a % 3 = 1 ∨ a % 3 = 2 := by omega
      rcases hmod with h | h <;> simp [Nat.pow_mod, h]
    have h2 : 1 ≤ a ^ 2 := hu1.le
    generalize a ^ 2 = u at h1 h2 ⊢
    omega
  have e3 : padicValNat 3 ((a ^ 2) ^ 3 - 1) = padicValNat 3 (a ^ 2 - 1) + 1 := by
    have h := padicValNat.pow_sub_pow (p := 3) hodd hu1 hdvd hu3 (n := 3) (by norm_num)
    rw [one_pow, padicValNat_self] at h
    exact h
  have e9 : padicValNat 3 ((a ^ 2) ^ 9 - 1) = padicValNat 3 (a ^ 2 - 1) + 2 := by
    have h := padicValNat.pow_sub_pow (p := 3) hodd hu1 hdvd hu3 (n := 9) (by norm_num)
    rw [one_pow] at h
    have h9 : padicValNat 3 9 = 2 := by
      have h' := padicValNat.prime_pow (p := 3) 2
      norm_num at h'
      exact h'
    rw [h9] at h
    exact h
  have hp6 : (a ^ 3) ^ 6 = (a ^ 2) ^ 9 := by ring
  have hp2 : (a ^ 3) ^ 2 = (a ^ 2) ^ 3 := by ring
  have hp6' : a ^ 6 = (a ^ 2) ^ 3 := by ring
  have ha0 : a ^ 2 ≠ 0 := by positivity
  have hA9 : (a ^ 2) ^ 9 ≠ 0 := pow_ne_zero _ ha0
  have hA3 : (a ^ 2) ^ 3 ≠ 0 := pow_ne_zero _ ha0
  have hB9 : (a ^ 2) ^ 9 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by norm_num) hu1)
  have hB3 : (a ^ 2) ^ 3 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by norm_num) hu1)
  have hC : a ^ 2 - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hu1
  have hz9 : padicValNat 3 ((a ^ 2) ^ 9) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hu3 (Nat.prime_three.dvd_of_dvd_pow h))
  have hz3 : padicValNat 3 ((a ^ 2) ^ 3) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun h => hu3 (Nat.prime_three.dvd_of_dvd_pow h))
  constructor
  · rw [hp6, hp2, padicValNat.mul (mul_ne_zero hA9 hB9) hB3, padicValNat.mul hA9 hB9, hz9, e9, e3]
    omega
  · rw [hp6', padicValNat.mul (mul_ne_zero hA3 hB3) hC, padicValNat.mul hA3 hB3, hz3, e3]
    omega

theorem g2AutCentralizingSylowIsInner_holds :
    ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 3 → (p = 2 → 2 ≤ f) → 3 ∣ f →
      LieModel Y .G2 0 p f → ∀ Q : Subgroup Y, (∃ S : Sylow 3 Y, (S : Subgroup Y) = Q) →
        ∀ φ : MulAut Y, φ ^ 3 = 1 → (∀ q ∈ Q, φ q = q) → ∃ g : Y, φ = MulAut.conj g := by
  classical
  intro Y _ _ p f hp hp3 hp2f hf3 hY Q hQ φ hφ3 hφQ
  by_contra hnot
  obtain ⟨S, rfl⟩ := hQ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hY (by decide)
  have hrf3 : 3 ≤ p ^ f := hc.1.2.2.2
  obtain ⟨K, _, _, hKcard, ⟨eY⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hc.2
  have : Finite (adjointGroup .G2 K) := CFSG.LieType.Chevalley.generated_group_finite .G2 K
  obtain ⟨m, hm⟩ := hf3
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [hm] at hrf3
      simp at hrf3
    · exact h
  have hK3 : ringChar K ≠ 3 := by
    have hchar : CharP K p :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (by omega : 0 < f) hKcard
    rw [ringChar.eq K p]
    exact hp3
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ p ^ f := Nat.pow_le_pow_left hp.two_le f
  set α : MulAut (adjointGroup .G2 K) := MulAut.congr eY φ with hαdef
  have hαy : ∀ y : Y, α (eY y) = eY (φ y) := by
    intro y
    simp [hαdef, MulAut.congr_apply]
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, hφ3, map_one]
  have hαout : ¬ CFSG.RankThree.PartTwo.KFacts.IsInnerAut α := by
    rintro ⟨g', hg'⟩
    apply hnot
    refine ⟨eY.symm g', ?_⟩
    ext y
    have h1 : g' * eY y * g'⁻¹ = eY (φ y) := by
      rw [← hαy y, ← hg']
      simp [MulAut.conj_apply]
    have h2 : φ y = eY.symm (g' * eY y * g'⁻¹) := by
      rw [h1]
      simp
    rw [h2]
    simp [MulAut.conj_apply]
  obtain ⟨σ, hσo, k, hk⟩ :=
    CFSG.RankThree.PartTwo.KFacts.g2_order_three_field_descent hK3 hK4 hα3 hαout
  have hF : CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ =
      (MulAut.conj k)⁻¹ * α * MulAut.conj k := by
    rw [hk]
    group
  let ψ : Y →* adjointGroup .G2 K :=
    ((MulAut.conj k)⁻¹ : MulAut (adjointGroup .G2 K)).toMonoidHom.comp eY.toMonoidHom
  have hψinj : Function.Injective ψ :=
    ((MulAut.conj k)⁻¹ : MulAut (adjointGroup .G2 K)).injective.comp eY.injective
  have hfixψ : ∀ y ∈ (S : Subgroup Y),
      CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ (ψ y) = ψ y := by
    intro y hy
    have h1 : α (eY y) = eY y := by rw [hαy y, hφQ y hy]
    have e1 : (MulAut.conj k) ((MulAut.conj k)⁻¹ (eY y)) = eY y :=
      MulAut.apply_inv_self _ _ _
    rw [hF]
    show ((MulAut.conj k)⁻¹ * α * MulAut.conj k) ((MulAut.conj k)⁻¹ (eY y)) =
      (MulAut.conj k)⁻¹ (eY y)
    rw [MulAut.mul_apply, MulAut.mul_apply, e1, h1]
  have hle : (S : Subgroup Y).map ψ ≤
      CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
        (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ) := by
    rintro _ ⟨y, hy, rfl⟩
    exact hfixψ y hy
  have hdvd : Nat.card (S : Subgroup Y) ∣ Nat.card (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ)) := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective hψinj] at this
  obtain ⟨e⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.g2_fixSub_equiv σ
  have hq0 : Nat.card (CFSG.LieType.Chevalley.fixSubfield σ) = p ^ m := by
    rw [CFSG.GH74.GLS.Stage2.Bender.Thm1.card_fixSubfield hp (by omega : 1 ≤ f) hKcard hσo, hm]
    congr 1
    omega
  have hJ : Nat.card (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.fixSub
      (CFSG.RankThree.PartTwo.KFacts.g2FieldHom K σ)) =
      (p ^ m) ^ 6 * ((p ^ m) ^ 6 - 1) * ((p ^ m) ^ 2 - 1) := by
    rw [← Nat.card_congr e.toEquiv]
    exact (CFSG.LieType.Chevalley.exact_G2_finite_order
      (CFSG.LieType.Chevalley.fixSubfield σ) hq0).2.1
  have hYcard : Nat.card Y = ((p ^ m) ^ 3) ^ 6 * (((p ^ m) ^ 3) ^ 6 - 1) *
      (((p ^ m) ^ 3) ^ 2 - 1) := by
    rw [Nat.card_congr eY.toEquiv]
    have h := (CFSG.LieType.Chevalley.exact_G2_finite_order K hKcard).2.1
    have h3 : p ^ f = (p ^ m) ^ 3 := by rw [hm, mul_comm, pow_mul]
    rw [h, h3]
  have hSyl : Nat.card (S : Subgroup Y) = 3 ^ padicValNat 3 (Nat.card Y) := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_def _ Nat.prime_three]
  have ha3 : ¬ 3 ∣ p ^ m := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
    (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have ha2 : 2 ≤ p ^ m := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm1
  obtain ⟨hv1, hv0⟩ := padicValNat_g2_orders ha2 ha3
  rw [hSyl, hJ] at hdvd
  have hne0 : (p ^ m) ^ 6 * ((p ^ m) ^ 6 - 1) * ((p ^ m) ^ 2 - 1) ≠ 0 := by
    have h6 : 1 < (p ^ m) ^ 6 := Nat.one_lt_pow (by norm_num) (by omega)
    have h2 : 1 < (p ^ m) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    exact mul_ne_zero (mul_ne_zero (by positivity) (Nat.sub_ne_zero_of_lt h6))
      (Nat.sub_ne_zero_of_lt h2)
  rw [padicValNat_dvd_iff_le hne0, hYcard, hv1, hv0] at hdvd
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
