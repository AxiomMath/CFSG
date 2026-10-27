module

public import CFSG.RankThree.PartTwo.KFacts.KS17J2
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.Sporadic.Bridge.M12
public import CFSG.Sporadic.Bridge.M22

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem card_projSL_three_mul_gcd (K : Type) [Field K] [Finite K] :
    Nat.card (projSL 3 K) * Nat.gcd 3 (Nat.card K - 1) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
    (by norm_num)
  rw [Nat.card_congr ((Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (Census.projImage_statedSL 3 K))).toEquiv] at h
  rw [h, show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num)]
  refine Nat.div_mul_cancel ?_
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 _).trans
    (Nat.sub_one_dvd_pow_sub_one _ 3)) _) _

theorem card_projSU_three_mul_gcd (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    Nat.card (projSU 3 p f) * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have hp : p.Prime := Fact.out
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have h := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (n := 3)
    (by norm_num)
  rw [Nat.card_congr ((Census.statedProjEquivProjImage _).trans
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 3 p f))).toEquiv] at h
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have hq2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq
  have h2 : ((((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2)).toNat = (p ^ f) ^ 2 - 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((p ^ f) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hq2]
      ring, Int.toNat_natCast]
  have h3 : ((((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3)).toNat = (p ^ f) ^ 3 + 1 := by
    rw [show ((p ^ f : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((p ^ f) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast
      ring, Int.toNat_natCast]
  rw [h, show 3 * (3 - 1) / 2 = 3 from rfl, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), h2, h3]
  refine Nat.div_mul_cancel ?_
  have hd : p ^ f + 1 ∣ (p ^ f) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (p ^ f) 1 (n := 3) (by decide)
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left ((Nat.gcd_dvd_right 3 _).trans hd) _) _

theorem forall_of_forall_lt {N B : ℕ} (hN : 0 < N) (hB : N < B ^ 3) {P : ℕ → Prop}
    (h : ∀ q < B, 2 ≤ q → q ^ 3 ∣ N → P q) : ∀ q, 2 ≤ q → q ^ 3 ∣ N → P q := by
  intro q hq hd
  refine h q ?_ hq hd
  by_contra hqB
  have h1 : B ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (not_lt.mp hqB) 3
  have h2 := Nat.le_of_dvd hN hd
  omega

theorem isEmpty_mulEquiv_projSL_three_of_card {X : Type*} [Group X] {N : ℕ}
    (hN : Nat.card X = N)
    (h : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (K : Type) [Field K] [Finite K] : IsEmpty (X ≃* projSL 3 K) := by
  refine ⟨fun e => ?_⟩
  have hc := card_projSL_three_mul_gcd K
  rw [← Nat.card_congr e.toEquiv, hN] at hc
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hcop : Nat.Coprime (Nat.card K ^ 3) (Nat.gcd 3 (Nat.card K - 1)) := by
    refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
    have h1 : Nat.Coprime (Nat.card K - 1) (Nat.card K - 1 + 1) :=
      Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rw [Nat.sub_add_cancel (by omega)] at h1
    exact h1.symm
  have hdvd : Nat.card K ^ 3 ∣ N :=
    hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)
  exact h _ hq2 hdvd hc

theorem isEmpty_mulEquiv_projSU_three_of_card {X : Type*} [Group X] {N : ℕ}
    (hN : Nat.card X = N)
    (h : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) : IsEmpty (X ≃* projSU 3 p f) := by
  refine ⟨fun e => ?_⟩
  have hp : p.Prime := Fact.out
  have hc := card_projSU_three_mul_gcd p f hf
  rw [← Nat.card_congr e.toEquiv, hN] at hc
  have hq2 : 2 ≤ p ^ f :=
    (hp.two_le).trans (Nat.le_self_pow (by omega) p)
  have hcop : Nat.Coprime ((p ^ f) ^ 3) (Nat.gcd 3 (p ^ f + 1)) := by
    refine Nat.Coprime.pow_left 3 (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _) ?_)
    exact Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  have hdvd : (p ^ f) ^ 3 ∣ N :=
    hcop.dvd_of_dvd_mul_right (hc ▸ Dvd.intro _ rfl)
  exact h _ hq2 hdvd hc

theorem not_isoLThreePi_of_card {X : Type} [Group X] {N : ℕ} (hN : Nat.card X = N)
    (hSL : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (hSU : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (p e : ℕ) [Fact p.Prime] : ¬ Sec4.IsoLThreePi X p e := by
  rintro (⟨-, ⟨φ⟩⟩ | ⟨he, ⟨φ⟩⟩)
  · exact (isEmpty_mulEquiv_projSL_three_of_card hN hSL (GaloisField p e)).false φ
  · have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · simp at he
      · exact h
    exact (isEmpty_mulEquiv_projSU_three_of_card hN hSU p e he1).false φ

theorem not_isLThreeEpsAt_of_card {X : Type} [Group X] {N : ℕ} (hN : Nat.card X = N)
    (hSL : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)))
    (hSU : ∀ q, 2 ≤ q → q ^ 3 ∣ N → N * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)))
    (p f : ℕ) [Fact p.Prime] : ¬ Sec14.IsLThreeEpsAt X p f := by
  rintro (⟨⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩)
  · exact (isEmpty_mulEquiv_projSL_three_of_card hN hSL (GaloisField p f)).false φ
  · have hf1 : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | h
      · simp at hq
      · exact h
    exact (isEmpty_mulEquiv_projSU_three_of_card hN hSU p f hf1).false φ

theorem checkSL_j2 : ∀ q < 85, 2 ≤ q → q ^ 3 ∣ 604800 →
    604800 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_j2 : ∀ q < 85, 2 ≤ q → q ^ 3 ∣ 604800 →
    604800 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem checkSL_m12 : ∀ q < 46, 2 ≤ q → q ^ 3 ∣ 95040 →
    95040 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_m12 : ∀ q < 46, 2 ≤ q → q ^ 3 ∣ 95040 →
    95040 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem checkSL_m22 : ∀ q < 77, 2 ≤ q → q ^ 3 ∣ 443520 →
    443520 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_m22 : ∀ q < 77, 2 ≤ q → q ^ 3 ∣ 443520 →
    443520 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel

theorem card_nativeM12 : Nat.card NativeSporadic.M12 = 95040 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M12.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M12.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M12.le_card_native

theorem card_nativeM22 : Nat.card NativeSporadic.M22 = 443520 := by
  obtain ⟨hfin, hle⟩ := CFSG.Sporadic.Bridge.M22.finite_card_le
  exact le_antisymm ((Nat.card_le_card_of_surjective _
    CFSG.Sporadic.Bridge.M22.toNative_surjective).trans hle)
    CFSG.Sporadic.Bridge.M22.le_card_native

theorem card_alternatingGroup_fin {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_alternatingGroup_five_seven_ten :
    Nat.card (alternatingGroup (Fin 5)) = 60 ∧ Nat.card (alternatingGroup (Fin 7)) = 2520 ∧
      Nat.card (alternatingGroup (Fin 10)) = 1814400 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [card_alternatingGroup_fin (by norm_num)]
    decide

theorem ks17J2NotList : KS17J2NotList := by
  refine ⟨fun p e _ => not_isoLThreePi_of_card card_nativeJ2
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSL_j2)
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSU_j2) p e, ?_, ?_⟩
  · refine ⟨fun e => ?_⟩
    have h := Nat.card_congr e.toEquiv
    rw [card_nativeJ2, card_alternatingGroup_five_seven_ten.2.1] at h
    norm_num at h
  · refine ⟨fun e => ?_⟩
    have h := Nat.card_congr e.toEquiv
    rw [card_nativeJ2, card_nativeM22] at h
    norm_num at h

theorem not_isLThreeEpsAt_j2 (p f : ℕ) [Fact p.Prime] :
    ¬ Sec14.IsLThreeEpsAt NativeSporadic.J2 p f :=
  not_isLThreeEpsAt_of_card card_nativeJ2
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSL_j2)
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSU_j2) p f

theorem not_isLThreeEpsAt_M12 (p f : ℕ) [Fact p.Prime] :
    ¬ Sec14.IsLThreeEpsAt NativeSporadic.M12 p f :=
  not_isLThreeEpsAt_of_card card_nativeM12
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSL_m12)
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSU_m12) p f

theorem not_isLThreeEpsAt_M22 (p f : ℕ) [Fact p.Prime] :
    ¬ Sec14.IsLThreeEpsAt NativeSporadic.M22 p f :=
  not_isLThreeEpsAt_of_card card_nativeM22
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSL_m22)
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSU_m22) p f

theorem not_isoLThreePi_M12 (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi NativeSporadic.M12 p e :=
  not_isoLThreePi_of_card card_nativeM12
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSL_m12)
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSU_m12) p e

theorem not_isoLThreePi_M22 (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi NativeSporadic.M22 p e :=
  not_isoLThreePi_of_card card_nativeM22
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSL_m22)
    (forall_of_forall_lt (by norm_num) (by norm_num) checkSU_m22) p e

theorem isEmpty_mulEquiv_M12_alternating :
    IsEmpty (NativeSporadic.M12 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (NativeSporadic.M12 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (NativeSporadic.M12 ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨h5, h7, h10⟩ := card_alternatingGroup_five_seven_ten
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩ <;>
  · have h := Nat.card_congr e.toEquiv
    rw [card_nativeM12] at h
    omega

theorem isEmpty_mulEquiv_M22_alternating :
    IsEmpty (NativeSporadic.M22 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (NativeSporadic.M22 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (NativeSporadic.M22 ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨h5, h7, h10⟩ := card_alternatingGroup_five_seven_ten
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩ <;>
  · have h := Nat.card_congr e.toEquiv
    rw [card_nativeM22] at h
    omega

theorem isEmpty_mulEquiv_j2_alternating :
    IsEmpty (NativeSporadic.J2 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (NativeSporadic.J2 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (NativeSporadic.J2 ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨h5, h7, h10⟩ := card_alternatingGroup_five_seven_ten
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩ <;>
  · have h := Nat.card_congr e.toEquiv
    rw [card_nativeJ2] at h
    omega

end CFSG.RankThree.PartTwo.KFacts.KS14
