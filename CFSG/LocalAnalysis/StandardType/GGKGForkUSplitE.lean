module

public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkSignedPow
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitC
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitQ
public import CFSG.LocalAnalysis.StandardType.GGKGForkUSplitL
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneUnitaryLabel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Multiplicative

theorem ggTorusSignedElt_unitary_split_even {K : Type} [Field K] [Finite K] {n r p : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hr : 2 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ n - 1) :
    GGTorusSignedElt p r (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n))) := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n K :=
    TableBU.unitaryFieldData_of_card hK hn
  obtain ⟨Rmat, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := r) (ε := 0) h
  have hhyp : GGTorusSignedElt p r (CFSG.ClassicalGroups.UnitaryFlag.hypSU h r 0) :=
    fun E hE hcard _ => ggKGUs_signed_frame_hypSU h hp hp2 hpq (by omega) E hE hcard
  have hSU : GGTorusSignedElt p r (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)) :=
    ggTorusSignedElt_of_mulEquiv (CFSG.ClassicalGroups.UnitaryFlag.hypTransport h hR).symm hhyp
  haveI : Finite (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)) := Finite.of_injective
    (fun x : LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n) =>
      ((x : GL (Fin (2 * r)) K) : Matrix (Fin (2 * r)) (Fin (2 * r)) K))
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  have hker : (QuotientGroup.mk' ((LargeEvenScalars (Fin (2 * r)) K).subgroupOf
      (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)))).ker ≤
      Subgroup.center (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)) := by
    rw [QuotientGroup.ker_mk']
    exact scalars_le_center_statedSU
  have hcp : ¬ p ∣ Nat.card (Subgroup.center (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n))) :=
    fun hdvd => not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
      (hdvd.trans (card_center_statedSU_dvd hK (by omega : 4 ≤ 2 * r)))
  exact ggKGUs_signedElt_of_centralQuotient hp
    (QuotientGroup.mk' ((LargeEvenScalars (Fin (2 * r)) K).subgroupOf
      (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n))))
    (QuotientGroup.mk'_surjective _) hker hcp hSU

private theorem ggKGUs_recipeUnitarySplitEven_lattice
    {d r n p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n - 1) (hn : 1 ≤ n) (hdr : d = 2 * r) (hr : 2 ≤ r) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧
      ∃ r', GGTorusLift p r' R ∧ GGTorusLattice p r' R I := by
  subst hdr
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one hn hpq
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := n) hK
  have hd : 3 ≤ 2 * r := by omega
  have hdq : (2 * r, 2 ^ n) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hZ := TableBUE.center_proj_eq_bot hK hd hdq
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  have hIp : GGOutdiagPrime p (LargeEvenProj (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin (2 * r)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (2 * r)) K (2 ^ n))) :=
    fun φ hφ hφp =>
      NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn hd
        (fun h => hdq (Prod.ext h.1 h.2)) hp hpq' φ hφ hφp
  exact ⟨r, ggTorusLift_unitarySplit_even hK hn hr hp hp2 hpq,
    ggTorusLattice_of_signedElt_pow hp hp2 hIp hZ
      (ggTorusSignedElt_unitary_split_even hK hn hr hp hp2 hpq)⟩

theorem ggKGTwoOn_unitarySplitEven :
    GGKGTwoOn fun p lab => (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1 ∧ 2 ∣ lab.rank + 1) ∨
      (lab.tag = .twD ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1) := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  rcases hs with ⟨ht, hpn, r, hr⟩ | ⟨ht, hl3, hpn⟩
  · dsimp only at ht hpn hr
    subst ht
    have hl2 : 2 ≤ l := hlab.2.1
    exact ggKGUs_recipeUnitarySplitEven_lattice (d := l + 1) (r := r) hp hpn hn (by omega)
      (by omega) hQ
  · dsimp only at ht hl3 hpn
    subst ht hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_right (show ¬ (3 = 2) by decide), ite_eq_left (show (3 = 3) from rfl)] at hQ ⊢
    exact ggKGUs_recipeUnitarySplitEven_lattice (d := 4) (r := 2) hp hpn hn rfl le_rfl hQ

end CFSG.StandardType
