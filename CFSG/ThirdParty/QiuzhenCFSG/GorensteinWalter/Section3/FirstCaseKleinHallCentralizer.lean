module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FittingDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma28Helpers
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem piCore_nat_eq_root_piCore_local
    {F : Type u} [Group F] [Finite F] (π : Set ℕ) :
    GorensteinWalter.piCore π F =
      _root_.CFSG.piCore {p : Nat.Primes | (p : ℕ) ∈ π} F := by
  unfold GorensteinWalter.piCore _root_.CFSG.piCore
  congr 1
  ext K
  constructor
  · intro hK
    refine ⟨hK.1, ?_⟩
    intro p hp
    apply hK.2 p.1
    exact Nat.mem_primeFactors.mpr ⟨p.2, hp, Nat.card_pos.ne'⟩
  · intro hK
    refine ⟨hK.1, ?_⟩
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    let p : Nat.Primes := ⟨q, hqprime⟩
    exact hK.2 p (by simpa using (Nat.dvd_of_mem_primeFactors hq))

private theorem hallSubgroup_of_isHallIn_local
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} (hHall : IsHallIn K H) :
    IsHallSubgroup (subgroupPrimeSet K) (K.subgroupOf H) := by
  classical
  rcases hHall with ⟨hKH, hcop⟩
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  refine isHallSubgroup_of (G := H) (subgroupPrimeSet K) (K.subgroupOf H) ?_ ?_
  · intro q hq
    simpa [subgroupPrimeSet, hcard] using hq
  · intro q hqK hqIndex
    have hqCard : q.1 ∣ Nat.card K := by
      simpa [subgroupPrimeSet] using hqK
    exact ((q.2.coprime_iff_not_dvd).1
      (hcop.coprime_dvd_left hqCard)) hqIndex

/-- In the Klein-four branch, the Hall subgroup inverted by a reflection is
centralized by the whole Fitting subgroup. -/
public theorem firstCase_klein_FU_centralizes_hall
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) {s : G} (hs : c.IsReflection s)
    {K : Subgroup G} (hKinv : IsInvertedSubgroup K c.U s)
    (hKHall : IsHallIn K c.FU) :
    c.FU ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have hKcomm : IsMulCommutative K :=
    (centralizerSetup_reflection_invertedSubgroup_abelian_normal c hs hKinv).1
  let πK : Set Nat.Primes := subgroupPrimeSet K
  let π : Set ℕ := {q : ℕ | ¬ ∃ p : Nat.Primes, p ∈ πK ∧ (p : ℕ) = q}
  let F : Subgroup G := c.FU
  let A : Subgroup G := piCoreOf F π
  let B : Subgroup G := piCoreOf F πᶜ
  have hFNil : Group.IsNilpotent (↥F) := fittingSubgroupOf_isNilpotent c.U
  have hKFUHall : IsHallSubgroup πK (K.subgroupOf F) :=
    hallSubgroup_of_isHallIn_local hKHall
  have hKNormal : (K.subgroupOf F).Normal :=
    section15_hall_subgroup_normal_of_nilpotent hFNil hKFUHall
  have hKPi : (K.subgroupOf F) = _root_.CFSG.piCore πK (↥F) := by
    have hPiHall : IsHallSubgroup πK (_root_.CFSG.piCore πK (↥F)) :=
      section12_piCore_isHallSubgroup_of_nilpotent hFNil
    exact hPiHall.eq_of_normal hKFUHall
  have hpi : GorensteinWalter.piCore πᶜ (↥F) =
      _root_.CFSG.piCore πK (↥F) := by
    rw [piCore_nat_eq_root_piCore_local]
    congr 1
    ext p
    constructor
    · intro hp
      change ¬ (¬ ∃ q : Nat.Primes, q ∈ πK ∧ (q : ℕ) = (p : ℕ)) at hp
      rcases not_not.mp hp with ⟨q, hq, hqp⟩
      have hEq : q = p := Subtype.ext hqp
      simpa [hEq] using hq
    · intro hp hpin
      exact hpin ⟨p, hp, rfl⟩
  have hB_eq_K : B = K := by
    change (GorensteinWalter.piCore πᶜ (↥F)).map F.subtype = K
    rw [hpi, ← hKPi]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hKHall.1]
  let A0 : Subgroup (↥F) := GorensteinWalter.piCore π (↥F)
  let B0 : Subgroup (↥F) := GorensteinWalter.piCore πᶜ (↥F)
  have : A0.Normal := by dsimp [A0]; exact piCore_normal_local π
  have : B0.Normal := by dsimp [B0]; exact piCore_normal_local πᶜ
  have hFtop : A0 ⊔ B0 = ⊤ := by
    simpa [A0, B0] using
      (piCore_sup_piCore_compl_eq_top_of_isNilpotent hFNil π)
  intro f hf
  let fF : ↥F := ⟨f, hf⟩
  have hfprod : fF ∈ (A0 : Set (↥F)) * (B0 : Set (↥F)) := by
    rw [← Subgroup.mul_normal A0 B0]
    rw [hFtop]
    exact Subgroup.mem_top fF
  rcases Set.mem_mul.mp hfprod with ⟨a0, ha0, b0, hb0, hab0⟩
  let a : G := (a0 : ↥F)
  let b : G := (b0 : ↥F)
  have hab : a * b = f := by
    simpa [a, b, fF] using congrArg (fun z : ↥F => (z : G)) hab0
  have hbK : b ∈ K := by
    have hbB : b ∈ B := by
      exact Subgroup.mem_map.mpr ⟨b0, hb0, rfl⟩
    rw [hB_eq_K] at hbB
    exact hbB
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have haA : a ∈ A := by
    exact Subgroup.mem_map.mpr ⟨a0, ha0, rfl⟩
  have hcentA : a ∈ Subgroup.centralizer (K : Set G) := by
    have hcentA' : a ∈ Subgroup.centralizer (B : Set G) := by
      have hcent := piCoreOf_centralizer_piCoreOf_compl c.U π
      change a ∈ Subgroup.centralizer
        (piCoreOf (fittingSubgroupOf c.U) πᶜ : Set G)
      simpa [A, B, F, CentralizerSetup.FU] using hcent haA
    rw [hB_eq_K] at hcentA'
    exact hcentA'
  have hbk : b * k = k * b := by
    exact congrArg Subtype.val (hKcomm.is_comm.comm ⟨b, hbK⟩ ⟨k, hk⟩)
  have habK : (a * b) * k = k * (a * b) := by
    calc
      (a * b) * k = a * (b * k) := by simp [mul_assoc]
      _ = a * (k * b) := by rw [hbk]
      _ = (a * k) * b := by simp [mul_assoc]
      _ = (k * a) * b := by
        exact congrArg (fun z : G => z * b)
          ((Subgroup.mem_centralizer_iff.mp hcentA) k hk).symm
      _ = k * (a * b) := by simp [mul_assoc]
  rw [← hab]
  exact habK.symm

end CFSG.GorensteinWalter
