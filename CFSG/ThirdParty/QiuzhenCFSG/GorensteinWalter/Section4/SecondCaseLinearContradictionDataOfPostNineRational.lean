module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0Odd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearParameterPack
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Numerical completion from a rational equation-(11) bound

The bad-fibre estimate naturally contains natural floor division, while the
source's final arithmetic uses the weaker rational term `(q - 1) / p`.
This owner therefore avoids choosing a natural number equal to the rational
line bound: it installs the rational expression directly as the `L` field of
`SecondCaseLinearParameters`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The post-equation-(nine) package produces the final contradiction data
from equation (11) stated directly with its rational line expression. -/
public theorem secondCase_linearContradictionData_of_postNine_rational
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    {p1 : ℕ}
    (hp0 : 3 ≤ post.indices.p0)
    (hp01 : post.indices.p0 ≤ p1)
    (hp0p : post.indices.p0 ≤ post.od.p)
    (h11 : ((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
      (post.equation9.k' : ℚ) *
        (((p1 : ℚ) - 1) *
          ((Nat.card K : ℚ) * (post.equation9.k' : ℚ) - 1) -
          ((Nat.card K : ℚ) - 1) / (post.od.p : ℚ) *
            (Nat.card K : ℚ)) ≤
      (w.M.index : ℚ))
    (hpdvd : post.od.p ∣ Nat.card post.equation9.Kinv) :
    LinearCaseContradictionData := by
  classical
  let q : ℚ := Nat.card K
  let k : ℚ := post.equation9.k
  let k' : ℚ := post.equation9.k'
  let p : ℚ := post.od.p
  let p0 : ℚ := post.indices.p0
  let p1q : ℚ := p1
  let uq : ℚ := post.indices.u
  let m : ℚ := w.M.index
  let L : ℚ := (p1q - 1) * (q * k' - 1) - (q - 1) / p * q
  have hpodd : Odd post.od.p :=
    secondCase_linear_omega_p_odd c w d post.od
  have hqNat : 7 ≤ Nat.card K :=
    secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv
      d K post.equation9 post.od.hp_prime hpodd hpdvd
  have hpkNat : 2 * post.od.p ≤ post.equation9.k :=
    secondCase_equationNine_two_p_le_k
      d K post.equation9 post.od.hp_prime hpodd hpdvd
  have P : SecondCaseLinearParameters :=
    { q := q
      k := k
      k' := k'
      p := p
      p0 := p0
      p1 := p1q
      u := uq
      m := m
      L := L
      hq := by
        dsimp [q]
        exact_mod_cast hqNat
      hk := by
        simpa [q, k] using post.equation9.hk_rat
      hk' := by
        simpa [q, k'] using post.equation9.hk'_rat
      hp0 := by
        dsimp [p0]
        exact_mod_cast hp0
      hp01 := by
        dsimp [p0, p1q]
        exact_mod_cast hp01
      hp0p := by
        dsimp [p0, p]
        exact_mod_cast hp0p
      hpk := by
        dsimp [p, k]
        exact_mod_cast hpkNat
      hu := by
        dsimp [uq, p]
        exact_mod_cast post.indices.u_le_p
      hu_nonneg := by positivity
      hL := rfl
      h10 := by
        dsimp [q, k, k', uq, p0, m]
        simpa [post.equation10.bg_H_eq] using post.equation10.equation10
      h11 := by
        simpa [q, k', p, p1q, m, L] using h11 }
  exact secondCase_linearParameters_arithmetic P

end CFSG.GorensteinWalter
