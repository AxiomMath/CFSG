module

public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.Generic
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem not_three_dvd_of_prime_pow {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    ¬ 3 ∣ p ^ n := by
  intro h
  have h1 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow h
  exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h1).symm

theorem nine_dvd_pow_six_sub_one {s : ℕ} (hs : ¬ 3 ∣ s) : 9 ∣ s ^ 6 - 1 := by
  have h3 : s % 3 ≠ 0 := fun h => hs (Nat.dvd_of_mod_eq_zero h)
  have hcases : s % 9 = 1 ∨ s % 9 = 2 ∨ s % 9 = 4 ∨ s % 9 = 5 ∨ s % 9 = 7 ∨ s % 9 = 8 := by
    omega
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [Nat.pow_mod]
  rcases hcases with h | h | h | h | h | h <;> norm_num [h]

theorem not_three_dvd_of_pow_card {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (h9 : ¬ 9 ∣ (p ^ n) ^ 2 - 1) : ¬ 3 ∣ n := by
  rintro ⟨g, rfl⟩
  apply h9
  have e : (p ^ (3 * g)) ^ 2 = (p ^ g) ^ 6 := by ring
  rw [e]
  exact nine_dvd_pow_six_sub_one (not_three_dvd_of_prime_pow hp hp3)

theorem not_eighty_one_dvd (Q f : ℕ) (hQ : ¬ 3 ∣ Q) (hf : ¬ 3 ∣ f)
    (h3 : 3 ∣ Q ^ 2 - 1) (h9 : ¬ 9 ∣ Q ^ 2 - 1) :
    ¬ 81 ∣ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) * f := by
  have hQ1 : 1 ≤ Q := Nat.pos_of_ne_zero (fun h => hQ (h ▸ dvd_zero 3))
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  obtain ⟨m, hm⟩ := h3
  have hQsq : Q ^ 2 = 3 * m + 1 := by omega
  have hm3 : ¬ 3 ∣ m := fun h => h9 (by rw [hm]; exact Nat.mul_dvd_mul_left 3 h)
  have hQ6 : Q ^ 6 - 1 = 9 * m * (3 * m ^ 2 + 3 * m + 1) := by
    have h6 : Q ^ 6 = 9 * m * (3 * m ^ 2 + 3 * m + 1) + 1 := by
      rw [show Q ^ 6 = (Q ^ 2) ^ 3 by ring, hQsq]
      ring
    omega
  have hprod : Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) * f
      = 27 * (Q ^ 6 * m * m * (3 * m ^ 2 + 3 * m + 1) * f) := by
    rw [hQ6, hm]
    ring
  rw [hprod]
  intro h
  have h81 : (27 : ℕ) * 3 ∣ 27 * (Q ^ 6 * m * m * (3 * m ^ 2 + 3 * m + 1) * f) := h
  have hdiv : 3 ∣ Q ^ 6 * m * m * (3 * m ^ 2 + 3 * m + 1) * f :=
    (mul_dvd_mul_iff_left (by norm_num : (27 : ℕ) ≠ 0)).mp h81
  simp only [Nat.Prime.dvd_mul Nat.prime_three] at hdiv
  rcases hdiv with ((((h1 | h1) | h1) | h1) | h1)
  · exact hQ (Nat.prime_three.dvd_of_dvd_pow h1)
  · exact hm3 h1
  · exact hm3 h1
  · omega
  · exact hf h1

theorem exists_prime_pow_card_field (K : Type) [Field K] [Finite K] :
    ∃ p n : ℕ, p.Prime ∧ ringChar K = p ∧ Nat.card K = p ^ n := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' K
  haveI := hchar
  refine ⟨p, (n : ℕ), hp, ringChar.eq K p, ?_⟩
  rw [Nat.card_eq_fintype_card, hcard]

theorem not_three_dvd_card_field (K : Type) [Field K] [Finite K] (hK3 : ringChar K ≠ 3) :
    ¬ 3 ∣ Nat.card K := by
  obtain ⟨p, n, hp, hchar, hcard⟩ := exists_prime_pow_card_field K
  rw [hcard]
  exact not_three_dvd_of_prime_pow hp (by rw [← hchar]; exact hK3)

theorem three_dvd_and_not_nine_dvd_of_factorization {Q : ℕ} (hQ : ¬ 3 ∣ Q) (hQ1 : 1 < Q)
    (h : (Q * (Q ^ 2 - 1)).factorization 3 = 1) : 3 ∣ Q ^ 2 - 1 ∧ ¬ 9 ∣ Q ^ 2 - 1 := by
  have hsq : 1 < Q ^ 2 := by nlinarith
  have hne : Q * (Q ^ 2 - 1) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  constructor
  · by_contra h3
    have hnd : ¬ 3 ∣ Q * (Q ^ 2 - 1) := by
      intro hd
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hd with h' | h'
      · exact hQ h'
      · exact h3 h'
    rw [Nat.factorization_eq_zero_of_not_dvd hnd] at h
    omega
  · intro h9
    have h9' : 3 ^ 2 ∣ Q * (Q ^ 2 - 1) := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact Dvd.dvd.mul_left h9 Q
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h9'
    omega

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section CertG2


theorem natCard_mulAut_adjointGroup_g2 {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) :
    Nat.card (MulAut (adjointGroup Tag.G2 K)) =
      Nat.card (adjointGroup Tag.G2 K) * Nat.card (K ≃+* K) := by
  obtain ⟨hNF, hInner⟩ := KFacts.g2_automorphism_normal_form hK3 hK4
  let Φ : adjointGroup Tag.G2 K × (K ≃+* K) → MulAut (adjointGroup Tag.G2 K) :=
    fun p => MulAut.conj p.1 * KFacts.g2FieldHom K p.2
  have hbij : Function.Bijective Φ := by
    refine ⟨?_, ?_⟩
    · rintro ⟨g, σ⟩ ⟨g', σ'⟩ h
      change MulAut.conj g * KFacts.g2FieldHom K σ =
        MulAut.conj g' * KFacts.g2FieldHom K σ' at h
      have e1 : MulAut.conj g =
          MulAut.conj g' * KFacts.g2FieldHom K σ' * (KFacts.g2FieldHom K σ)⁻¹ :=
        eq_mul_inv_of_mul_eq h
      have h1 : MulAut.conj (g'⁻¹ * g) = KFacts.g2FieldHom K (σ' * σ⁻¹) := by
        calc MulAut.conj (g'⁻¹ * g) = (MulAut.conj g')⁻¹ * MulAut.conj g := by
              rw [map_mul, map_inv]
          _ = (MulAut.conj g')⁻¹ *
              (MulAut.conj g' * KFacts.g2FieldHom K σ' * (KFacts.g2FieldHom K σ)⁻¹) := by
              rw [e1]
          _ = KFacts.g2FieldHom K σ' * (KFacts.g2FieldHom K σ)⁻¹ := by group
          _ = KFacts.g2FieldHom K σ' * KFacts.g2FieldHom K σ⁻¹ := by rw [map_inv]
          _ = KFacts.g2FieldHom K (σ' * σ⁻¹) := by rw [map_mul]
      have hσ : σ' * σ⁻¹ = 1 := hInner _ (MonoidHom.mem_range.mpr ⟨g'⁻¹ * g, h1⟩)
      obtain rfl : σ' = σ := mul_inv_eq_one.mp hσ
      rw [mul_inv_cancel, map_one] at h1
      have hc : g'⁻¹ * g ∈ Subgroup.center (adjointGroup Tag.G2 K) := by
        rw [Subgroup.mem_center_iff]
        intro w
        have hw := congrArg (fun φ : MulAut (adjointGroup Tag.G2 K) => φ w) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at hw
        rw [mul_inv_eq_iff_eq_mul] at hw
        exact hw.symm
      rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hc
      obtain rfl : g' = g := inv_mul_eq_one.mp hc
      rfl
    · intro α
      obtain ⟨g, σ, hα⟩ := hNF α
      exact ⟨(g, σ), hα.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective Φ hbij), Nat.card_prod]

theorem card_le_27_adjointGroup_g2 {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK4 : 4 ≤ Nat.card K) (h3 : 3 ∣ Nat.card K ^ 2 - 1) (h9 : ¬ 9 ∣ Nat.card K ^ 2 - 1)
    (P : Subgroup (MulAut (adjointGroup Tag.G2 K))) (hP : IsPGroup 3 P) : Nat.card P ≤ 27 := by
  obtain ⟨p, n, hp, hchar, hcard⟩ := exists_prime_pow_card_field K
  have hp3 : p ≠ 3 := by rw [← hchar]; exact hK3
  have hQ3 : ¬ 3 ∣ Nat.card K := not_three_dvd_card_field K hK3
  have hf : Nat.card (K ≃+* K) = n :=
    CFSG.Semidihedral.SemilinearOuterQuotient.fieldAut_card K hp hcard
  have hn3 : ¬ 3 ∣ n := not_three_dvd_of_pow_card hp hp3 (by rw [← hcard]; exact h9)
  have hQ4 : 0 < Nat.card K := by omega
  have hQ2 : 1 < Nat.card K ^ 2 := by nlinarith
  have hQ6 : 1 < Nat.card K ^ 6 :=
    lt_of_lt_of_le hQ2 (Nat.pow_le_pow_right hQ4 (by norm_num))
  have hord : CFSG.Open.ordG2 (Nat.card K) ≠ 0 := by
    unfold CFSG.Open.ordG2
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (pow_ne_zero 6 hQ4.ne') (by omega)) (by omega)
  have hMul : Nat.card (MulAut (adjointGroup Tag.G2 K)) = CFSG.Open.ordG2 (Nat.card K) * n := by
    rw [natCard_mulAut_adjointGroup_g2 hK3 hK4,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hf]
  have hn0 : n ≠ 0 := fun h => hn3 (h ▸ dvd_zero 3)
  have hfin : Finite (MulAut (adjointGroup Tag.G2 K)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hMul]
    exact Nat.mul_ne_zero hord hn0
  haveI := hfin
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hP
  by_contra hlt
  push Not at hlt
  have h4 : 4 ≤ m := by
    by_contra h4
    push Not at h4
    have h27 : 3 ^ m ≤ 27 :=
      (Nat.pow_le_pow_right (by norm_num) (by omega : m ≤ 3)).trans (by norm_num)
    omega
  have h81 : 81 ∣ Nat.card P := by
    rw [hm, show (81 : ℕ) = 3 ^ 4 by norm_num]
    exact pow_dvd_pow 3 h4
  have hnd : ¬ 81 ∣ Nat.card (MulAut (adjointGroup Tag.G2 K)) := by
    rw [hMul, CFSG.Open.ordG2]
    exact not_eighty_one_dvd (Nat.card K) n hQ3 hn3 h3 h9
  exact hnd (h81.trans (Subgroup.card_subgroup_dvd_card P))

theorem autThreeAut_g2 : AutThreeAut (fun (X : Type) [Group X] =>
    ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) := by
  intro Z _ _ hZ α J hα3 hJ hJT hJf P hP
  by_cases hin : α ∈ (MulAut.conj : Z →* MulAut Z).range
  swap
  · exact (noOuterType424G2_holds Z hZ α J hα3 hin hJ hJT).elim
  obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hin
  obtain ⟨X, hXg, hF, ⟨e⟩⟩ := hZ
  obtain ⟨q, hq, ⟨f⟩⟩ := hF
  by_cases hp3 : q.p = 3
  · exact (KS11Lie3Proof.false_of_isType424_g2_three hp3 f e hα3 hJ hJT).elim
  have hZ' : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨X, hXg, ⟨q, hq, hp3, ⟨f⟩⟩, ⟨e⟩⟩
  obtain ⟨K, hKF, hKfin, hK3, hK4, e', -, hS⟩ :=
    KS11Lie4Proof.exists_g2_threeB KS11Lie7Proof.g2ThreeConjSL2_holds
      KS11Lie7Proof.g2ThreeACent_holds KS11Lie4Proof.g2ThreeBCent_holds hZ' hα3 hJ hJT
  have hcard : Nat.card ((KS11Lie4Proof.g2ShortSL2 K).comap e'.toMonoidHom) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr ((Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e'.surjective _))).toEquiv]
    obtain ⟨e₂⟩ := KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := K)
    rw [← Nat.card_congr e₂.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hJeq : J = (KS11Lie4Proof.g2ShortSL2 K).comap e'.toMonoidHom :=
    KS11Lie4Proof.ThreeBAt.eq hS hJ
  rw [hJeq, hcard] at hJf
  obtain ⟨h3, h9⟩ := three_dvd_and_not_nine_dvd_of_factorization
    (not_three_dvd_card_field K hK3) (by omega) hJf
  exact card_le_27_of_equiv e' (fun Q hQ => card_le_27_adjointGroup_g2 hK3 hK4 h3 h9 Q hQ) P hP

end CertG2

end CFSG.RankThree.PartTwo.Sec11

end
