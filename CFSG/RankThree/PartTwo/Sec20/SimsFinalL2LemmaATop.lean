module

public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Statements
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KFactL34QEightClosure : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* projSL 3 (GaloisField 2 2)) →
    ∀ (Bb Q : Subgroup X), Nat.card Bb = 9 → Nat.card Q = 8 →
      Q ≤ Subgroup.normalizer (Bb : Set X) →
      ∀ x : X, (orderOf x = 5 ∨ orderOf x = 7) →
        3 ∣ Nat.card (Subgroup.closure {y : X | ∃ q ∈ Q, y = q * x * q⁻¹})

section Aut

variable {X : Type*} [Group X]

private theorem card_mulAut_of_mulEquiv (e : X ≃* projSL 3 (GaloisField 2 2)) :
    Nat.card (MulAut X) = 241920 := by
  rw [Nat.card_congr (MulAut.congr (e.trans
    (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)))).toEquiv]
  exact KFacts.L34.card_mulAut KFacts.L34.card_galoisField_two_two

private theorem injective_conj_of_mulEquiv (e : X ≃* projSL 3 (GaloisField 2 2)) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  have hZ : Subgroup.center X = ⊥ := by
    rw [← Subgroup.map_center_eq e.symm, Sec4.center_projSL_eq_bot, Subgroup.map_bot]
  rw [injective_iff_map_eq_one]
  intro z hz
  have hc : z ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro t
    have h := congrArg (fun φ : MulAut X => φ t) hz
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc t * z = z * t * z⁻¹ * z := by rw [h]
      _ = z * t := by group
  rw [hZ] at hc
  exact Subgroup.mem_bot.mp hc

private theorem exists_conj_eq_of_coprime (e : X ≃* projSL 3 (GaloisField 2 2)) (σ : MulAut X)
    (hσ : Nat.Coprime 12 (orderOf σ)) : ∃ x : X, MulAut.conj x = σ := by
  have hinj := injective_conj_of_mulEquiv e
  have hN : (MulAut.conj : X →* MulAut X).range.Normal := ⟨by
    rintro _ ⟨x, rfl⟩ τ
    refine ⟨τ x, ?_⟩
    ext t
    simp⟩
  have hcard : Nat.card (MulAut.conj : X →* MulAut X).range = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr e.toEquiv,
      KFacts.L34.card_projSL]
  have hidx : (MulAut.conj : X →* MulAut X).range.index = 12 := by
    have h := (MulAut.conj : X →* MulAut X).range.card_mul_index
    rw [hcard, card_mulAut_of_mulEquiv e] at h
    omega
  have hmem := Subgroup.pow_index_mem (MulAut.conj : X →* MulAut X).range σ
  rw [hidx] at hmem
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hσ
  rw [← hm]
  exact MonoidHom.mem_range.mp (Subgroup.pow_mem _ hmem m)

end Aut

section PowSubgroup

variable {Γ : Type*} [Group Γ] {J O : Subgroup Γ}

private theorem mem_zpowers_mk_of_le_sup_zpowers (hOJ : O ≤ J) (hn : (O.subgroupOf J).Normal)
    {g : Γ} (hgJ : g ∈ J) (hJ : J ≤ O ⊔ Subgroup.zpowers g) (u : ↥J ⧸ O.subgroupOf J) :
    u ∈ Subgroup.zpowers ((⟨g, hgJ⟩ : J) : ↥J ⧸ O.subgroupOf J) := by
  have hJN : J ≤ Subgroup.normalizer (O : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).mp hn
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (O : Set Γ) :=
    Subgroup.zpowers_le.mpr (hJN hgJ)
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective u
  have hj : (j : Γ) ∈ ((Subgroup.zpowers g ⊔ O : Subgroup Γ) : Set Γ) := by
    rw [sup_comm]
    exact hJ j.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN] at hj
  obtain ⟨v, hv, o, ho, hvo⟩ := hj
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
  have hoJ : o ∈ J := hOJ ho
  have hsplit : j = (⟨g, hgJ⟩ : J) ^ i * ⟨o, hoJ⟩ := Subtype.ext (by simpa using hvo.symm)
  rw [hsplit, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
    (QuotientGroup.eq_one_iff (⟨o, hoJ⟩ : J)).mpr (Subgroup.mem_subgroupOf.mpr ho), mul_one]

private theorem exists_subgroup_pow_mem (hOJ : O ≤ J) (hn : (O.subgroupOf J).Normal) {g : Γ}
    (hgJ : g ∈ J) (hJ : J ≤ O ⊔ Subgroup.zpowers g) (n : ℕ) :
    ∃ V : Subgroup Γ, ∀ j : Γ, j ∈ V ↔ j ∈ J ∧ j ^ n ∈ O := by
  have hpow : ∀ (j : Γ) (hj : j ∈ J),
      j ^ n ∈ O ↔ ((⟨j, hj⟩ : J) : ↥J ⧸ O.subgroupOf J) ^ n = 1 := by
    intro j hj
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Iff.rfl
  refine ⟨{ carrier := {j | j ∈ J ∧ j ^ n ∈ O}
            mul_mem' := ?_
            one_mem' := ⟨J.one_mem, by rw [one_pow]; exact O.one_mem⟩
            inv_mem' := ?_ }, fun j => Iff.rfl⟩
  · rintro a b ⟨ha, haO⟩ ⟨hb, hbO⟩
    refine ⟨J.mul_mem ha hb, ?_⟩
    rw [hpow _ (J.mul_mem ha hb)]
    rw [hpow _ ha] at haO
    rw [hpow _ hb] at hbO
    have hc : Commute ((⟨a, ha⟩ : J) : ↥J ⧸ O.subgroupOf J)
        ((⟨b, hb⟩ : J) : ↥J ⧸ O.subgroupOf J) := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_mk_of_le_sup_zpowers hOJ hn hgJ hJ ((⟨a, ha⟩ : J) : ↥J ⧸ O.subgroupOf J))
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_mk_of_le_sup_zpowers hOJ hn hgJ hJ ((⟨b, hb⟩ : J) : ↥J ⧸ O.subgroupOf J))
      rw [← hi, ← hk]
      exact Commute.zpow_zpow_self _ i k
    have hsplit : (⟨a * b, J.mul_mem ha hb⟩ : J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [hsplit, QuotientGroup.mk_mul, hc.mul_pow, haO, hbO, one_mul]
  · rintro a ⟨ha, haO⟩
    exact ⟨J.inv_mem ha, by rw [inv_pow]; exact O.inv_mem haO⟩

end PowSubgroup

theorem kFactL34QEightTop_of_closure (h : KFactL34QEightClosure) : KFactL34QEightTop := by
  rintro X _ _ ⟨e⟩ Bb Q hBb hQ hQB J O hOJ hn hQJ hQO hO3 ⟨g, hgJ, hJg⟩ hidx
  have hinj := injective_conj_of_mulEquiv e
  have hAut := card_mulAut_of_mulEquiv e
  have : Finite (MulAut X) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  by_contra hJO
  obtain ⟨p, hp, hp57, hpJ⟩ : ∃ p : ℕ, p.Prime ∧ (p = 5 ∨ p = 7) ∧ p ∣ Nat.card J := by
    have hd1 : O.relIndex J ≠ 1 := fun h1 =>
      hJO (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hOJ)
    have hdJ : O.relIndex J ∣ Nat.card J := Subgroup.relIndex_dvd_card O J
    have hd35 : O.relIndex J ∣ 5 * 7 := by
      have h1 : O.relIndex J ∣ 5 * 7 * 6912 := by
        rw [show (5 * 7 * 6912 : ℕ) = 241920 by norm_num, ← hAut]
        exact hdJ.trans (Subgroup.card_subgroup_dvd_card J)
      have h2 : Nat.Coprime (O.relIndex J) 6912 :=
        Nat.Coprime.coprime_dvd_right (by norm_num) (Nat.Coprime.pow_right 8 hidx)
      exact h2.dvd_of_dvd_mul_right h1
    have hpr := Nat.minFac_prime hd1
    refine ⟨(O.relIndex J).minFac, hpr, ?_, (Nat.minFac_dvd _).trans hdJ⟩
    rcases (Nat.Prime.dvd_mul hpr).mp ((Nat.minFac_dvd _).trans hd35) with h5 | h7
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_five).mp h5)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hpr (by norm_num)).mp h7)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpJ
  have hyord : orderOf (y : MulAut X) = p := by rw [Subgroup.orderOf_coe, hy]
  obtain ⟨x, hx⟩ := exists_conj_eq_of_coprime e (y : MulAut X) (by
    rw [hyord]
    rcases hp57 with rfl | rfl <;> norm_num)
  have hxord : orderOf x = p := by
    rw [← orderOf_injective (MulAut.conj : X →* MulAut X) hinj x, hx, hyord]
  obtain ⟨V, hV⟩ := exists_subgroup_pow_mem hOJ hn hgJ hJg p
  have hyV : (y : MulAut X) ∈ V :=
    (hV _).mpr ⟨y.2, by rw [← hyord, pow_orderOf_eq_one]; exact O.one_mem⟩
  have hVQ : ∀ q ∈ Q, ∀ v ∈ V, MulAut.conj q * v * (MulAut.conj q)⁻¹ ∈ V := by
    intro q hq v hv
    have hcJ := hQJ (Subgroup.mem_map_of_mem MulAut.conj hq)
    have hcO := hQO (Subgroup.mem_map_of_mem MulAut.conj hq)
    obtain ⟨hvJ, hvO⟩ := (hV v).mp hv
    refine (hV _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hcJ v).mp hvJ, ?_⟩
    rw [conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp hcO _).mp hvO
  have hcl : Subgroup.closure {y : X | ∃ q ∈ Q, y = q * x * q⁻¹} ≤ V.comap MulAut.conj := by
    rw [Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv, hx]
    exact hVQ q hq _ hyV
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3
    (h X ⟨e⟩ Bb Q hBb hQ hQB x (by rw [hxord]; exact hp57))
  obtain ⟨-, hzO⟩ := (hV _).mp (Subgroup.mem_comap.mp (hcl z.2))
  have hzc : orderOf (MulAut.conj (z : X)) = 3 := by
    rw [orderOf_injective (MulAut.conj : X →* MulAut X) hinj, Subgroup.orderOf_coe, hz]
  have hcop : (orderOf (MulAut.conj (z : X))).Coprime p := by
    rw [hzc]
    rcases hp57 with rfl | rfl <;> norm_num
  have h3O : 3 ∣ Nat.card O := by
    rw [← hzc, ← hcop.orderOf_pow]
    exact Subgroup.orderOf_dvd_natCard O hzO
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hO3.symm h3O

end CFSG.RankThree.PartTwo.Sec20
