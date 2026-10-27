module

public import CFSG.LocalAnalysis.StandardType.GGResXDatumOfWeylType
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Certs


theorem ggWeylTypeFamilyOn_twE6Dvd :
    GGWeylTypeFamilyOn (fun p lab => lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) := by
  intro p hp hp2 lab hlab hT
  obtain ⟨htag, rfl, hdvd⟩ := hT
  refine ggNbrTableBWeylTypeNonSplitOn_twE6 3 hp hp2 lab hlab ⟨htag, Or.inr hdvd⟩ ?_
  refine ⟨Or.inr (Or.inr (Or.inl ⟨Or.inr htag, hdvd⟩)), ?_, ?_, ?_⟩
  · first
      | exact Nat.dvd_trans hdvd (Nat.sub_one_dvd_pow_sub_one (2 ^ lab.n) 2)
      | (have e : (2 ^ lab.n) ^ 2 - 1 = (2 ^ lab.n + 1) * (2 ^ lab.n - 1) := by
           simpa using Nat.pow_two_sub_pow_two (2 ^ lab.n) 1
         rw [e]
         exact dvd_mul_of_dvd_right hdvd _)
  · rintro ⟨h1, -⟩
    rw [htag] at h1
    first
      | exact h1
      | simp [LargeEvenUntwisted] at h1
  · rintro ⟨-, -, h3⟩
    have hpos : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    first
      | omega
      | (have h1 := Nat.dvd_sub h3 hdvd
         have h2 : 2 ^ lab.n + 1 - (2 ^ lab.n - 1) = 2 := by omega
         rw [h2] at h1
         have := Nat.le_of_dvd (by norm_num : 0 < 2) h1
         omega)

theorem ggTBXDatumResOn_of_twE6Dvd (hRig : GGLabelRigidInput) (hcyc : GGLabelCenterPCyclicInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTBXDatumResOn
      (fun p lab => S p lab ∧ ¬ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1))) :
    GGTBXDatumResOn S :=
  ggTBXDatumResOn_of_weylType ggWeylTypeFamilyOn_twE6Dvd hRig hcyc h

theorem ggPZNbrResDatumOn_of_twE6Dvd (hRig : GGLabelRigidInput)
    (hcyc : GGLabelCenterPCyclicInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGPZNbrResDatumOn
      (fun p lab => S p lab ∧ ¬ (lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1))) :
    GGPZNbrResDatumOn S :=
  ggPZNbrResDatumOn_of_weylType ggWeylTypeFamilyOn_twE6Dvd hRig hcyc h

end Certs

end CFSG.StandardType

end
