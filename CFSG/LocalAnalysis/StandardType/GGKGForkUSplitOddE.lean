module

public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitE
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddC
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitOddL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Multiplicative

private theorem ggKGUe1_center_card_dvd {d n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 3 ≤ d) (hdq : (d, 2 ^ n) ≠ (3, 2)) :
    Nat.card (Subgroup.center (LargeEvenSUGroup (Fin d) K (2 ^ n))) ∣ 2 ^ n + 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : Subgroup.center (LargeEvenSUGroup (Fin d) K (2 ^ n)) =
      (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSUGroup (Fin d) K (2 ^ n)) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := K) hK hd hdq).2
  rw [hcen]
  exact card_scalars_statedSU_dvd hK (by omega)

theorem ggTorusSignedElt_unitary_split_odd {K : Type} [Field K] [Finite K] {n r p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 1 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusSignedElt p r (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n))) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  obtain ⟨Rmat, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := r) (ε := 1) h
  have hhyp : GGTorusSignedElt p r (CFSG.ClassicalGroups.UnitaryFlag.hypSU h r 1) :=
    fun E hE hcard _ => ggKGUs_signed_frame_hypSU_odd h hp hp2 hpq (by omega) E hE hcard
  have hSU : GGTorusSignedElt p r (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n)) :=
    ggTorusSignedElt_of_mulEquiv (CFSG.ClassicalGroups.UnitaryFlag.hypTransport h hR).symm hhyp
  haveI : Finite (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n) =>
      ((x : GL (Fin (2 * r + 1)) K) : Matrix (Fin (2 * r + 1)) (Fin (2 * r + 1)) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  have hker : (QuotientGroup.mk' ((LargeEvenScalars (Fin (2 * r + 1)) K).subgroupOf
      (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n)))).ker ≤
      Subgroup.center (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n)) := by
    rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  have hdq : (2 * r + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := by simpa using congrArg Prod.snd h
    have hn1 : n = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa using h2)
    have hp1 : p ∣ 1 := by simpa [hn1] using hpq
    exact hp.not_dvd_one hp1
  have hcp : ¬ p ∣ Nat.card (Subgroup.center (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n))) :=
    fun hdvd => not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
      (hdvd.trans (ggKGUe1_center_card_dvd hK (by omega : 3 ≤ 2 * r + 1) hdq))
  exact ggKGUs_signedElt_of_centralQuotient hp
    (QuotientGroup.mk' ((LargeEvenScalars (Fin (2 * r + 1)) K).subgroupOf
      (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n))))
    (QuotientGroup.mk'_surjective _) hker hcp hSU

private theorem ggKGUe1_recipeUnitarySplitOdd_lattice
    {d r n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) (hn : 1 ≤ n) (hdr : d = 2 * r + 1) (hr : 1 ≤ r) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      ∃ r', GGTorusLift p r' R ∧ GGTorusLattice p r' R I := by
  subst hdr
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpq
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hK
  have hd : 3 ≤ 2 * r + 1 := by omega
  have hdq : (2 * r + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := by simpa using congrArg Prod.snd h
    have hn1 : n = 1 := Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa using h2)
    have hp1 : p ∣ 1 := by simpa [hn1] using hpq
    exact hp.not_dvd_one hp1
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hIp : GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (2 * r + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (2 * r + 1)) K (2 ^ n))) :=
    fun φ hφ hφp =>
      NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn hd
        (fun h => hdq (Prod.ext h.1 h.2)) hp hpq' φ hφ hφp
  exact ⟨r, ggTorusLift_unitarySplit_odd hK hn hr hp hp2 hpq,
    ggTorusLattice_of_signedElt_pow hp hp2 hIp hZ
      (ggTorusSignedElt_unitary_split_odd hK hn hr hp hp2 hpq)⟩

theorem ggKGTwoOn_unitarySplitOdd :
    GGKGTwoOn fun p lab => lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ 2 ∣ lab.rank + 1 := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨ht, hpn, hnot2⟩
  dsimp only at ht hpn hnot2
  subst ht
  have hl2 : 2 ≤ l := hlab.2.1
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' l
  · exact ggKGUe1_recipeUnitarySplitOdd_lattice (d := l + 1) (r := r) hp hpn hn (by omega)
      (by omega) hQ
  · exfalso
    apply hnot2
    refine ⟨r + 1, ?_⟩
    omega

end CFSG.StandardType

end
