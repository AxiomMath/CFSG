module

public import CFSG.Timmesfeld.Bridge.Asc72Local
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] {D : Set G}

theorem mul_mul_mem_centSet {z u v : G} (hu : u ∈ centSet D z) (hv : v ∈ centSet D z)
    (huvz : u * v * z ∈ D) : u * v * z ∈ centSet D z :=
  ⟨huvz, (hu.2.mul_left hv.2).mul_left (Commute.refl z)⟩

theorem mul_self_eq_one_of_mul_mul_mem {z u v : G} (hD : IsOddTransp D)
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (hc : Commute u v)
    (huvz : u * v * z ∈ D) : z * z = 1 := by
  have h := hD.mul_self_eq_one huvz
  rw [← pow_two, (hu.2.mul_left hv.2).mul_pow, hc.mul_pow, pow_two, pow_two, pow_two,
    hD.mul_self_eq_one hu.1, hD.mul_self_eq_one hv.1] at h
  simpa using h

theorem eq_mul_mul_of_mul_mul_mem {z u v : G} (hD : IsOddTransp D)
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (hc : Commute u v) :
    z = u * v * (u * v * z) := by
  have hu2 : u * u = 1 := hD.mul_self_eq_one hu.1
  have hv2 : v * v = 1 := hD.mul_self_eq_one hv.1
  have huv2 : (u * v) * (u * v) = 1 := by
    rw [← pow_two]
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one hu2 hv2).mp hc
  calc z = (u * v) * (u * v) * z := by rw [huv2, one_mul]
    _ = u * v * (u * v * z) := by group

theorem commute_self_mul_mul_of_mem_centSet {z u v : G} (hu : u ∈ centSet D z)
    (hv : v ∈ centSet D z) (hc : Commute u v) :
    Commute u (u * v * z) ∧ Commute v (u * v * z) :=
  ⟨((Commute.refl u).mul_right hc).mul_right hu.2,
    (hc.symm.mul_right (Commute.refl v)).mul_right hv.2⟩

theorem mul_eq_mul_mul_mul_of_mem_centSet {z u v : G} (hD : IsOddTransp D)
    (hv : v ∈ centSet D z) (hc : Commute u v) : u * z = v * (u * v * z) := by
  have hv2 : v * v = 1 := hD.mul_self_eq_one hv.1
  calc u * z = u * (v * v) * z := by rw [hv2, mul_one]
    _ = (u * v) * v * z := by group
    _ = (v * u) * v * z := by rw [hc.eq]
    _ = v * (u * v * z) := by group

theorem mul_mul_ne_self_of_mem_centSet_of_not_mem {z u v : G} (hD : IsOddTransp D)
    (hzD : z ∉ D) (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) :
    u * v * z ≠ u ∧ u * v * z ≠ v := by
  constructor
  · intro h
    apply hzD
    have h1 : v * z = 1 := by
      calc v * z = u⁻¹ * (u * v * z) := by group
        _ = 1 := by rw [h, inv_mul_cancel]
    rw [show z = v⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq hv.1]
    exact hv.1
  · intro h
    apply hzD
    have h1 : u * z = 1 := by
      have e : u * v * z = u * z * v := by
        rw [mul_assoc u v z, hv.2.eq, ← mul_assoc]
      rw [e] at h
      calc u * z = u * z * v * v⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
    rw [show z = u⁻¹ from eq_inv_of_mul_eq_one_right h1, hD.inv_eq hu.1]
    exact hu.1

theorem pairwise_commute_of_mem_centSet {z u v : G} (hu : u ∈ centSet D z)
    (hv : v ∈ centSet D z) (hc : Commute u v) :
    ({u, v, u * v * z} : Set G).Pairwise Commute := by
  obtain ⟨huw, hvw⟩ := commute_self_mul_mul_of_mem_centSet hu hv hc
  intro a ha b hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hab
      | exact hc
      | exact huw
      | exact hvw
      | exact hc.symm
      | exact huw.symm
      | exact hvw.symm

theorem self_mem_localGroup_of_mul_mul_mem {z u v : G} (hD : IsOddTransp D)
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (hc : Commute u v)
    (huvz : u * v * z ∈ D) : z ∈ localGroup D z := by
  have hz_eq : u * v * (u * v * z) = z :=
    (eq_mul_mul_of_mul_mul_mem hD hu hv hc).symm
  have h := (localGroup D z).mul_mem
    ((localGroup D z).mul_mem (mem_localGroup_of_mem hu) (mem_localGroup_of_mem hv))
    (mem_localGroup_of_mem (mul_mul_mem_centSet hu hv huvz))
  rwa [hz_eq] at h

theorem self_mem_center_localGroup_of_mul_mul_mem {z u v : G} (hD : IsOddTransp D)
    (hu : u ∈ centSet D z) (hv : v ∈ centSet D z) (hc : Commute u v)
    (huvz : u * v * z ∈ D) :
    (⟨z, self_mem_localGroup_of_mul_mul_mem hD hu hv hc huvz⟩ : localGroup D z) ∈
      Subgroup.center (localGroup D z) :=
  Subgroup.mem_center_iff.mpr fun g => Subtype.ext (commute_of_mem_localGroup g.2).eq

end CFSG.OddTranspositions.PartThree
