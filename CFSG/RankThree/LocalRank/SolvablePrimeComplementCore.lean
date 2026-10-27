module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaIntersection

public section

namespace CFSG.RankThree.LocalRank

open CFSG

@[expose] noncomputable def aschbacherSolvableCore (p : ℕ) (H : Type*) [Group H] : Subgroup H :=
  inSubgroup (pPrimeCore p) (solvableRadical H)

theorem aschbacherSolvableCore_eq_aschbacherTheta {p : ℕ} (hp : p.Prime) (H : Type*) [Group H] :
    aschbacherSolvableCore p H = CFSG.RankThreeEvenClassification.Helpers.aschbacherTheta H p := by
  have hcore : pPrimeCore p (solvableRadical H) =
      CFSG.RankThreeEvenClassification.Helpers.primeComplementCore (solvableRadical H) p :=
    congrArg sSup (Set.ext fun N => and_congr_right fun _ => hp.coprime_iff_not_dvd)
  simp only [aschbacherSolvableCore, inSubgroup, hcore]
  rfl

theorem solvable_prime_complement_core_characterization {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) :
    Group.IsSolvable (aschbacherSolvableCore p H) ∧
    (aschbacherSolvableCore p H).Characteristic ∧
    ¬p ∣ Nat.card (aschbacherSolvableCore p H) ∧
    (∀ N : Subgroup H, N.Normal → Group.IsSolvable N → ¬p ∣ Nat.card N →
      N ≤ aschbacherSolvableCore p H) ∧
    IsGreatest {N : Subgroup H | N.Normal ∧ Group.IsSolvable N ∧ ¬p ∣ Nat.card N}
      (aschbacherSolvableCore p H) ∧
    (∀ M : Subgroup H,
      IsGreatest {N : Subgroup H | N.Normal ∧ Group.IsSolvable N ∧ ¬p ∣ Nat.card N} M →
        M = aschbacherSolvableCore p H) ∧
    ∀ r : ℕ, r.Prime → r ≠ p → pCore r H ≤ aschbacherSolvableCore p H := by
  have hθ := aschbacherSolvableCore_eq_aschbacherTheta hp H
  obtain ⟨hnormal, hsolvable, hcomplement⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.aschbacherTheta_properties H p hp
  have hmax : ∀ N : Subgroup H, N.Normal → Group.IsSolvable N → ¬p ∣ Nat.card N →
      N ≤ aschbacherSolvableCore p H := by
    intro N hN hNs hNp
    rw [hθ, CFSG.RankThreeEvenClassification.Helpers.aschbacherTheta_eq_solvablePrimeComplementCore
      H p hp]
    exact CFSG.RankThreeEvenClassification.Helpers.le_solvablePrimeComplementCore p N hN hNs hNp
  have hgreatest : IsGreatest {N : Subgroup H | N.Normal ∧ Group.IsSolvable N ∧ ¬p ∣ Nat.card N}
      (aschbacherSolvableCore p H) :=
    ⟨hθ ▸ ⟨hnormal, hsolvable, hcomplement⟩, fun N ⟨hN, hNs, hNp⟩ => hmax N hN hNs hNp⟩
  have hchar := CFSG.RankThreeEvenClassification.Helpers.aschbacherTheta_characteristic H p hp
  refine ⟨hθ ▸ hsolvable, hθ ▸ hchar, hθ ▸ hcomplement, hmax, hgreatest,
    fun M hM => hM.unique hgreatest, ?_⟩
  intro r hr hrp
  have : Fact r.Prime := ⟨hr⟩
  have hpg : IsPGroup r (pCore r H) := pCore_isPGroup
  have : Group.IsNilpotent (pCore r H) := hpg.isNilpotent
  apply hmax _ pCore_normal inferInstance
  intro hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  rw [hk] at hdvd
  exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hdvd)).symm

instance aschbacherSolvableCore_normal (p : ℕ) (H : Type*) [Group H] :
    (aschbacherSolvableCore p H).Normal := by
  have : (solvableRadical H).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  exact ConjAct.normal_of_characteristic_of_normal

theorem aschbacherSolvableCore_eq_solvablePrimeComplementCore {p : ℕ} (hp : p.Prime)
    (H : Type*) [Group H] [Finite H] :
    aschbacherSolvableCore p H =
      CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore H p := by
  rw [aschbacherSolvableCore_eq_aschbacherTheta hp,
    CFSG.RankThreeEvenClassification.Helpers.aschbacherTheta_eq_solvablePrimeComplementCore H p hp]

theorem inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf {p : ℕ} (hp : p.Prime) {X : Type*}
    [Group X] [Finite X] (K : Subgroup X) :
    inSubgroup (aschbacherSolvableCore p) K =
      CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf p K := by
  simp only [inSubgroup, CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf,
    aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]

end CFSG.RankThree.LocalRank
