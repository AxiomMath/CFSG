module

public import CFSG.RankThree.PartTwo.Sec11.AutThree1129.Generic
public import CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofOuter
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent

public section

namespace CFSG.RankThree.PartTwo.Sec11.AutThree1129

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem nine_dvd_pow_six_sub_one_of_not_three_dvd {s : ℕ} (hs : ¬ 3 ∣ s) : 9 ∣ s ^ 6 - 1 := by
  have h3 : s % 3 ≠ 0 := fun h => hs (Nat.dvd_of_mod_eq_zero h)
  have hcases : s % 9 = 1 ∨ s % 9 = 2 ∨ s % 9 = 4 ∨ s % 9 = 5 ∨ s % 9 = 7 ∨ s % 9 = 8 := by
    omega
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.sub_mod_eq_zero_of_mod_eq
  rw [Nat.pow_mod]
  rcases hcases with h | h | h | h | h | h <;> norm_num [h]

theorem factorization_three_ne_one_of_nine_dvd {Q : ℕ} (h9 : 9 ∣ Q ^ 2 - 1) :
    (Q * (Q ^ 2 - 1)).factorization 3 ≠ 1 := by
  intro h
  have hne : Q * (Q ^ 2 - 1) ≠ 0 := by
    intro h0
    rw [h0, Nat.factorization_zero] at h
    simp at h
  have h9' : 3 ^ 2 ∣ Q * (Q ^ 2 - 1) := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]
    exact Dvd.dvd.mul_left h9 Q
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h9'
  omega

section CertD4


theorem autThreeAut_d4 (hOdd : NoOuterType424D4Odd) : AutThreeAut (fun (X : Type) [Group X] =>
    ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
      Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) := by
  intro Z _ _ hZ α J hα3 hJ hJT hJf P hP
  by_cases hin : α ∈ (MulAut.conj : Z →* MulAut Z).range
  swap
  · exact (noOuterType424D4_of_odd hOdd Z hZ α J hα3 hin hJ hJT).elim
  obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hin
  obtain ⟨X, hXg, hF, ⟨e⟩⟩ := hZ
  obtain ⟨q, hq, ⟨f⟩⟩ := hF
  by_cases hp3 : q.p = 3
  · exact (KS11Lie3Proof.false_of_isType424_d4_three hp3 f e hα3 hJ hJT).elim
  have hZ' : ∃ (X : Type) (_ : Group X), (∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid), q.p ≠ 3 ∧
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨X, hXg, ⟨q, hq, hp3, ⟨f⟩⟩, ⟨e⟩⟩
  obtain ⟨K, hKF, hKfin, n, σ, hK, -, hn3, hσ3, -, -, e', -, hS⟩ :=
    KS11Lie4Proof.exists_d4_threeB KS11Lie6Proof.d4ThreeConj_holds
      KS11Lie6Proof.d4ThreeACent_holds KS11Lie6Proof.d4ThreeBCent_holds hZ' hα3 hJ hJT
  have hcard : Nat.card ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom).comap e'.toMonoidHom) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
    rw [Nat.card_congr ((Subgroup.equivMapOfInjective _ e'.toMonoidHom e'.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e'.surjective _))).toEquiv]
    exact KS11Lie4Proof.card_d4ShortSL2 hσ3
  have hJeq : J = (KS11Lie4Proof.d4ShortSL2 K σ.toRingHom).comap e'.toMonoidHom :=
    KS11Lie4Proof.ThreeBAt.eq hS hJ
  have h9 : 9 ∣ Nat.card K ^ 2 - 1 := by
    rw [hK, show (n ^ 3) ^ 2 = n ^ 6 by ring]
    exact nine_dvd_pow_six_sub_one_of_not_three_dvd hn3
  rw [hJeq, hcard] at hJf
  exact (factorization_three_ne_one_of_nine_dvd h9 hJf).elim

end CertD4

end CFSG.RankThree.PartTwo.Sec11.AutThree1129

end
