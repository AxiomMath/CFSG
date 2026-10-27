module

public import CFSG.RankThree.PartOne.SEITZ7.SzPair
public import CFSG.RankThree.PartOne.Q1327T.Item7D4W
public import CFSG.LieType.Ree.LargeReeInvolutionFusionWord

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.LieType.Ree.LargeReeCover
  CFSG.RankThree.PartOne.SEITZ7

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem szW_mul_self : szW * szW = 1 := by
  refine ext_single fun i => ?_
  rw [mul_smul, one_smul, szW, fixedRelElt_smul, fixedRelElt_smul]
  revert i
  decide +kernel

theorem szW_eq : szW = F4.fixedOrbitElement ⟨0, by decide⟩ * F4.fixedOrbitElement ⟨1, by decide⟩ *
    F4.fixedOrbitElement ⟨0, by decide⟩ := by
  have e : F4.fixedRelWord ⟨5, by decide⟩ = [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩] := by
    decide
  rw [szW, fixedRelElt, e]
  simp [mul_assoc]

theorem szNw_eq_weyl : szNw K = weylOne K * weylTwo K * weylOne K := by
  have : CharP K 2 := ‹CharP K F4.prime›
  rw [szNw, szW_eq, Q1327T.canonicalRep_mul_charTwo (τ := F4.tag) (R := K),
    Q1327T.canonicalRep_mul_charTwo (τ := F4.tag) (R := K)]

theorem szNw_mul_self : szNw K * szNw K = 1 := by
  have : CharP K 2 := ‹CharP K F4.prime›
  have h := Q1327T.canonicalRep_mul_charTwo (τ := F4.tag) (R := K) szW szW
  rw [szW_mul_self, canonicalRep_one] at h
  exact h.symm

theorem szNw_eq_nFour : szNw K = nFour K 3 := rfl

theorem nFour_zero : nFour K 0 = 1 := by
  have h : F4.fixedRelElt (kFour 0) = 1 := by
    have e : F4.fixedRelWord (kFour 0) = [] := by decide
    rw [fixedRelElt, e]
    rfl
  rw [nFour, h, canonicalRep_one]

theorem sylowB_eq_stdFourG (b c : K) : sylowB m K b c = stdFourG m b c := by
  rw [sylowB_eq, fourCoordG, nFour_zero]
  simp

theorem szNw_conj_sylowB (b c : K) :
    szNw K * sylowB m K b c * (szNw K)⁻¹ = sylowH m K b c := by
  rw [sylowB_eq_stdFourG, sylowH_eq, szNw_eq_nFour]
  rfl

theorem szNw_conj_sylowH (b c : K) :
    szNw K * sylowH m K b c * (szNw K)⁻¹ = sylowB m K b c := by
  have h := szNw_mul_self (K := K)
  have ht : (szNw K)⁻¹ = szNw K := inv_eq_of_mul_eq_one_right h
  rw [← szNw_conj_sylowB b c, ht]
  calc szNw K * (szNw K * sylowB m K b c * szNw K) * szNw K
      = (szNw K * szNw K) * sylowB m K b c * (szNw K * szNw K) := by group
    _ = sylowB m K b c := by rw [h]; group

theorem szNw_conj_sylowB_zero (c : K) :
    szNw K * sylowB m K 0 c * (szNw K)⁻¹ = centralZ K m c := by
  rw [szNw_conj_sylowB, sylowH_zero_eq_centralZ]

end CFSG.RankThree.PartOne.SEITZ12
