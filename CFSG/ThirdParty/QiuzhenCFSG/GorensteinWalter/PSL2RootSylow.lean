module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27

namespace CFSG
end CFSG
open CFSG

/-!
# The defining-characteristic root group of `PSL₂`

This file identifies the standard upper-unipotent root group as a Sylow
subgroup in the defining characteristic and computes its normalizer.  These
are the group-theoretic inputs needed to let an arbitrary automorphism of
`PSL₂` permute the projective-line points in Dieudonne's automorphism proof.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

/-- The standard upper-unipotent root group is a defining-characteristic
`p`-group. -/
public theorem psl2UpperUnipotent_isPGroup
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    IsPGroup p (psl2UpperUnipotentSubgroup K) := by
  apply IsPGroup.of_card
  rw [psl2UpperUnipotentSubgroup_card, hKcard]

/-- The standard upper-unipotent root group is a Sylow subgroup in the
defining characteristic. -/
public theorem psl2UpperUnipotent_isSylow
    (K : Type u) [Field K] [Finite K]
    {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) :
    ∃ Q : Sylow p (PSL2 K),
      (Q : Subgroup (PSL2 K)) = psl2UpperUnipotentSubgroup K := by
  let U := psl2UpperUnipotentSubgroup K
  have hUp : IsPGroup p U := psl2UpperUnipotent_isPGroup K hKcard
  obtain ⟨Q, hUQ⟩ := hUp.exists_le_sylow
  let e : Multiplicative K ≃* Q :=
    (BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
      hKcard Q).some
  have hQcard : Nat.card Q = Nat.card K := by
    calc
      Nat.card Q = Nat.card (Multiplicative K) :=
        Nat.card_congr e.symm.toEquiv
      _ = Nat.card K := Nat.card_congr Multiplicative.toAdd
  have hUeq : U = (Q : Subgroup (PSL2 K)) := by
    apply Subgroup.eq_of_le_of_card_ge hUQ
    rw [hQcard, show Nat.card U = Nat.card K by
      exact psl2UpperUnipotentSubgroup_card K]
  exact ⟨Q, hUeq.symm⟩

/-- The unit upper transvection fixes exactly the point at infinity. -/
public theorem psl2UpperUnipotent_one_fixed_iff
    (K : Type u) [Field K] (p : PSL2ProjectiveLine K) :
    psl2QuotientMap K (sl2UpperUnipotent (1 : K)) • p = p ↔
      p = psl2ProjectiveInfinity K := by
  constructor
  · induction p using Projectivization.ind with
    | h v hv =>
        intro hfix
        rw [psl2QuotientMap_smul, Projectivization.smul_mk,
          Projectivization.mk_eq_mk_iff] at hfix
        obtain ⟨a, ha⟩ := hfix
        have hUv :
            sl2UpperUnipotent (1 : K) • v = ![v 0 + v 1, v 1] := by
          change (sl2UpperUnipotent (1 : K)).val *ᵥ v = _
          ext i
          fin_cases i <;>
            simp [sl2UpperUnipotent, Matrix.mulVec, Matrix.vecHead,
              Matrix.vecTail]
        rw [hUv] at ha
        by_cases hv1 : v 1 = 0
        · rw [psl2ProjectiveInfinity,
            Projectivization.mk_eq_mk_iff']
          refine ⟨v 0, ?_⟩
          ext i
          fin_cases i <;> simp [hv1]
        · have ha1 : (a : K) = 1 := by
            apply mul_right_cancel₀ hv1
            simpa [Units.smul_def] using congrFun ha 1
          have h0 : v 0 = v 0 + v 1 := by
            simpa [Units.smul_def, ha1] using congrFun ha 0
          have : v 1 = 0 := by
            apply add_left_cancel (a := v 0)
            simpa using h0.symm
          exact (hv1 this).elim
  · rintro rfl
    have hu :
        psl2QuotientMap K (sl2UpperUnipotent (1 : K)) ∈
          psl2UpperUnipotentSubgroup K :=
      (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨1, rfl⟩
    have hB := psl2UpperUnipotent_le_borel hu
    exact (MulAction.mem_stabilizer_iff.mp hB)

/-- The normalizer of the standard upper-unipotent root group is exactly the
standard Borel subgroup. -/
public theorem psl2UpperUnipotent_normalizer_eq_borel
    (K : Type u) [Field K] :
    Subgroup.normalizer
        (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) =
      psl2Borel K := by
  apply le_antisymm
  · intro g hg
    let u : PSL2 K :=
      psl2QuotientMap K (sl2UpperUnipotent (1 : K))
    have hu : u ∈ psl2UpperUnipotentSubgroup K :=
      (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨1, rfl⟩
    have hginv :
        g⁻¹ ∈ Subgroup.normalizer
          (psl2UpperUnipotentSubgroup K : Set (PSL2 K)) :=
      Subgroup.inv_mem _ hg
    have hconj : g⁻¹ * u * g ∈ psl2UpperUnipotentSubgroup K := by
      simpa only [inv_inv] using
        ((Subgroup.mem_normalizer_iff.mp hginv u).1 hu)
    have hconjFix :
        (g⁻¹ * u * g) • psl2ProjectiveInfinity K =
          psl2ProjectiveInfinity K := by
      have hB := psl2UpperUnipotent_le_borel hconj
      exact MulAction.mem_stabilizer_iff.mp hB
    have huFix :
        u • (g • psl2ProjectiveInfinity K) =
          g • psl2ProjectiveInfinity K := by
      rw [← mul_smul]
      calc
        (u * g) • psl2ProjectiveInfinity K =
            (g * (g⁻¹ * u * g)) • psl2ProjectiveInfinity K := by
          congr 1
          group
        _ = g • ((g⁻¹ * u * g) • psl2ProjectiveInfinity K) :=
          mul_smul _ _ _
        _ = g • psl2ProjectiveInfinity K := by rw [hconjFix]
    have hgFix :
        g • psl2ProjectiveInfinity K = psl2ProjectiveInfinity K :=
      (psl2UpperUnipotent_one_fixed_iff K
        (g • psl2ProjectiveInfinity K)).mp huFix
    exact MulAction.mem_stabilizer_iff.mpr hgFix
  · exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (psl2UpperUnipotent_le_borel (K := K))).mp
        (psl2UpperUnipotent_normal_in_borel (K := K))

public theorem psl2UpperUnipotentSubgroup_card_odd
    (K : Type u) [Field K] [Finite K] (hodd : Odd (Nat.card K)) :
    Odd (Nat.card (psl2UpperUnipotentSubgroup K)) := by
  rw [psl2UpperUnipotentSubgroup_card]
  exact hodd

public theorem no_involution_of_psl2UpperUnipotentSubgroup
    (K : Type u) [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (v : PSL2 K) (hv : IsInvolution v) :
    v ∉ psl2UpperUnipotentSubgroup K := by
  intro hvmem
  have hord_dvd : orderOf v ∣ Nat.card (psl2UpperUnipotentSubgroup K) :=
    by
      have hzle : Subgroup.zpowers v ≤ psl2UpperUnipotentSubgroup K :=
        Subgroup.zpowers_le.mpr hvmem
      have hcard : Nat.card (Subgroup.zpowers v) ∣
          Nat.card (psl2UpperUnipotentSubgroup K) :=
        Subgroup.card_dvd_of_le hzle
      rw [show orderOf v = Nat.card (Subgroup.zpowers v) by
        exact (Nat.card_zpowers v).symm]
      exact hcard
  have hodd_card : Odd (Nat.card (psl2UpperUnipotentSubgroup K)) :=
    psl2UpperUnipotentSubgroup_card_odd K hodd
  have hord_odd : Odd (orderOf v) := Odd.of_dvd_nat hodd_card hord_dvd
  have hord2 : orderOf v ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hv.2)
  have hord1 : orderOf v = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hord_odd.not_two_dvd_nat (by rw [h])
  exact hv.1 (orderOf_eq_one_iff.mp hord1)

end CFSG.GorensteinWalter
