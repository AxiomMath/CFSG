module

public import CFSG.RankThree.PartOne.K128.F4Syl
import CFSG.RankThree.PartOne.K128.SylowShapeRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.R3c18F

public section

namespace CFSG.Quasithin

namespace R3c18

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.RankThree.PartOne.K128 (phiF4 phiF4_ne_zero sylowShape_ree ree_class zmodIncl
  zmodIncl_injective)

open CFSG.RankThree.PartOne.K1214 (SylowShape)

theorem two_le_pRank_of_sylowShape_w {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {X : Type*} [Group X]
    [Finite X] (h : SylowShape p 2 e X) : 2 ≤ CFSG.pRank p X :=
  CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he h

section Certificates

theorem f4ReeClass_holds : F4ReeClass := by
  intro a K _ _ _ hK p hp hp5 hrk
  obtain ⟨d, hd, hpd⟩ := ree_class hK hp hp5 hrk
  rcases hd with rfl | rfl | rfl
  · exact Or.inl hpd
  · exact Or.inr (Or.inl hpd)
  · exact Or.inr (Or.inr hpd)

theorem f4ReeRank_holds : F4ReeRank := by
  intro a K _ _ _ hK p hp hp5 hdiv
  have hQ : 2 ≤ 2 ^ (2 * a + 1) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  obtain ⟨d, hd, hpd⟩ : ∃ d, (d = 1 ∨ d = 2 ∨ d = 4) ∧ p ∣ phiF4 d (2 ^ (2 * a + 1)) := by
    rcases hdiv with h | h | h
    · exact ⟨1, Or.inl rfl, h⟩
    · exact ⟨2, Or.inr (Or.inl rfl), h⟩
    · exact ⟨4, Or.inr (Or.inr rfl), h⟩
  have hsh := sylowShape_ree hK hd hp hp5 hpd
  have hone : 1 ≤ (phiF4 d (2 ^ (2 * a + 1))).factorization p :=
    (hp.dvd_iff_one_le_factorization (phiF4_ne_zero hd hQ)).1 hpd
  exact two_le_pRank_of_sylowShape_w hp hone hsh

end Certificates

end R3c18

end CFSG.Quasithin
