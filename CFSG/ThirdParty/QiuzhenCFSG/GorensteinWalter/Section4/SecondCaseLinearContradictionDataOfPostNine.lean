module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP1Data
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0Odd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPDvdKinv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearParameterPack
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Numerical completion after equations (9) and (10)
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Once the equation-(11) region count and the three elementary parameter
bounds have been supplied, the completed equation-(9)/(10) package feeds
straight into the rational contradiction constructor.  This theorem keeps
the final integration site independent of the group-theoretic producer for
those inputs. -/
public theorem secondCase_linearContradictionData_of_postNine
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    {p1 L : ℕ}
    (hp0 : 3 ≤ post.indices.p0)
    (hp01 : post.indices.p0 ≤ p1)
    (hp0p : post.indices.p0 ≤ post.od.p)
    (hL : (L : ℚ) = ((p1 : ℚ) - 1) *
      ((Nat.card K : ℚ) * (post.equation9.k' : ℚ) - 1) -
      ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) * (Nat.card K : ℚ))
    (h11 : ((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
      (post.equation9.k' : ℚ) * (L : ℚ) ≤ (w.M.index : ℚ))
    (hpdvd : post.od.p ∣ Nat.card post.equation9.Kinv) :
    LinearCaseContradictionData := by
  classical
  letI : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
  have hpodd : Odd post.od.p :=
    secondCase_linear_omega_p_odd c w d post.od
  have hu_nonneg : 0 ≤ post.indices.u := Nat.zero_le _
  exact secondCase_linearParameters_arithmetic
    (secondCase_linearParameters_of_equationData
      d K post.equation9 post.od.hp_prime hpodd hpdvd hp0 hp01 hp0p
      post.indices.u_le_p hu_nonneg hL
      (by
        simpa [post.equation10.bg_H_eq] using post.equation10.equation10)
      h11)

/-- The integration wrapper for the completed equation-(11) parameter
package.  It derives `p₁`, the line cardinality, `p₀ ≤ p₁`, `p₁ ≤ p + 1`,
`p₀ ≤ p`, and the divisibility of the selected prime from the post-nine
structure, leaving only the source-specific lower bound on `p₀` and the two
region inequalities. -/
public theorem secondCase_linearContradictionData_of_postNine_and_p1Data
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    {K : Type u} [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    (hp0 : 3 ≤ post.indices.p0)
    (hL : ∃ L : ℕ, (L : ℚ) = ((conjugateCount post.od.P post.od.A : ℚ) - 1) *
      ((Nat.card K : ℚ) * (post.equation9.k' : ℚ) - 1) -
      ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) * Nat.card K ∧
      ((conjugateCount post.od.P post.od.A : ℚ) - 1) * Nat.card K *
        (post.equation9.k' : ℚ) * (L : ℚ) ≤ (w.M.index : ℚ)) :
    LinearCaseContradictionData := by
  classical
  obtain ⟨L, hLdef, h11⟩ := hL
  obtain ⟨p1, hp1eq, hp01, hp1p, _hlines⟩ :=
    secondCase_linear_p1_data c w d post.od post.indices.p0
      post.indices.p0_def
  have hp0p : post.indices.p0 ≤ post.od.p :=
    secondCase_linear_p0_le_p_of_le_add_one c w d post.od
      post.indices.p0 post.indices.p0_def (hp01.trans hp1p)
  exact secondCase_linearContradictionData_of_postNine c w d K post
    hp0 hp01 hp0p (by simpa [hp1eq] using hLdef)
      (by simpa [hp1eq] using h11)
      (secondCase_linear_p_dvd_Kinv c w d post)

end CFSG.GorensteinWalter
