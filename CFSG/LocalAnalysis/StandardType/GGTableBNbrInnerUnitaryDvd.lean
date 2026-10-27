module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUDvd

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.StandardType.LineU

theorem ggTorusNbrSCr_PSU (hU : UnitaryUniversalCover) {n d p : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hd : 5 ≤ d) (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGTorusNbrSCr p (ggUnitaryTorusRank p d)
      (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hrank : ggUnitaryTorusRank p d = d - 3 := by
    simp [ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    exists_diagModel hK hn hd hp hpq hpd (hU n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  have hKd := TableBU.unitaryFieldData_of_card hK hn
  have hA1 : Nat.card A ≠ 1 := by
    intro h1
    rw [h1] at h3
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  exact nbr_of_model_U hKd hp hp2 hpq hd hφs hφker hA hA1 hsc hdiag

theorem largeEvenLabelAll_unitDvd_nbr (hU : UnitaryUniversalCover)
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGUnitDvdLabelNo63 p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusNbrSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, hl, hpn, hpd⟩, hno⟩ := h
  dsimp only at ht hl hpn hpd hno
  subst ht
  have hn : 1 ≤ n := hlab.1
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (l + 1, 2 ^ n) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hlift : GGTorusLift p (ggUnitaryTorusRank p (l + 1))
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) :=
    ggTorusLift_unitary hK hn (by omega) hdq hp hpn
  have h63' : ¬ (l + 1 = 6 ∧ p = 3) := fun ⟨h6, h3⟩ => hno ⟨by omega, h3⟩
  have hd5 : 5 ≤ l + 1 := by
    by_contra hlt
    have hl3 : l = 3 := by omega
    subst hl3
    have h4 : p ∣ 2 ^ 2 := by simpa using hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4))
  exact ⟨K, i1, i2, hK, ⟨hQ', ggUnitaryTorusRank p (l + 1), hlift,
    ggTorusNbrSCr_PSU hU hK hn hd5 hp hpn hpd h63'⟩⟩

theorem ggTableBNbrInnerInputOn_unitaryDvd (hU : UnitaryUniversalCover) :
    GGTableBNbrInnerInputOn GGUnitDvdLabelNo63 :=
  ggTableBNbrInnerInputOn_of_labelsSCr fun _ _ hp hlab h =>
    largeEvenLabelAll_unitDvd_nbr hU hp hlab h

end CFSG.StandardType

end
