module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Base

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step77OneNotNormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    conjSubgroup g (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z

theorem step77One_of_notNorm (hN : Step77OneNotNormStatement)
    (hB : Stroth73aOm4BaseStatement) : Step77OneStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3
  by_cases hV : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t
  · exfalso
    have hmV : g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
      conjSubgroup_eq_self_iff.mp hV
    have hgt : g * t * g⁻¹ ∈ Z0 := hB G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM hmV
    apply hs3
    have hQZ0 : Q ≤ Z0 := hc.Q_le_centre (hs.toSec5.mem) hZ0
    have e : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [e]
    exact Z0.mul_mem (hQZ0 hs1) hgt
  · exact hN G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV

end CFSG.RankThree.GF2n.Stroth80
