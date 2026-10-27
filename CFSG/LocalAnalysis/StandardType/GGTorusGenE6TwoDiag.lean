module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation
import CFSG.LocalAnalysis.StandardType.GGLangTwoPairAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.CentralCover
open TableBExc.E6Three

namespace E6TwoGen


theorem exists_map_eq_rootDiagUnit_of_mem_range_torusE6Two {K L : Type} [Field K] [Field L]
    (h2 : (2 : K) = 0) (ι : adjointGroup .E6 K →* ModGL .E6 L) {ω : Lˣ} (hω : ω ^ 3 = 1)
    (hιu : ∀ i : Fin 4, ι (uE6Two i) = rootSL2 .E6 L (bE6 i) (HSL ω))
    {z : adjointGroup .E6 K} (hz : z ∈ (torusE6Two h2).range) :
    ∃ c : Fin Tag.E6.rank → Lˣ, ι z = rootDiagUnit .E6 c ∧ ∀ k, c k ^ 3 = 1 := by
  let D : Subgroup (ModGL .E6 L) :=
    { carrier := {g | ∃ c : Fin Tag.E6.rank → Lˣ,
        g = rootDiagUnit .E6 c ∧ ∀ k, c k ^ 3 = 1}
      one_mem' := ⟨1, (rootDiagUnit_one).symm, fun _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨a, rfl, ha⟩ ⟨b, rfl, hb⟩
        exact ⟨a * b, (rootDiagUnit_mul a b).symm, fun k => by
          change (a k * b k) ^ 3 = 1
          rw [mul_pow, ha k, hb k, mul_one]⟩
      inv_mem' := by
        rintro g ⟨a, rfl, ha⟩
        exact ⟨a⁻¹, rootDiagUnit_inv a, fun k => by
          change ((a k)⁻¹) ^ 3 = 1
          rw [inv_pow, ha k, inv_one]⟩ }
  have hιu_mem : ∀ i : Fin 4, ι (uE6Two (K := K) i) ∈ D := by
    intro i
    have hcube : ∀ n : ℤ, (ω ^ n) ^ 3 = 1 := by
      intro n
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω, one_zpow]
    change ∃ c : Fin Tag.E6.rank → Lˣ,
      ι (uE6Two (K := K) i) = rootDiagUnit .E6 c ∧ ∀ k, c k ^ 3 = 1
    refine ⟨fun j => ω ^ corootPair (bE6 i) (Pi.single j 1), ?_, fun k => hcube _⟩
    rw [hιu i]
    exact LangRat.j4e_rootSL2_HSL_eq_rootDiagUnit (isRoot_bE6 i) ω
  have hD_range : (torusE6Two (K := K) h2).range ≤ D.comap ι := by
    have htor : (torusE6Two (K := K) h2).range ≤
        (MonoidHom.noncommPiCoprod
          (fun i : Fin 4 => zmodPowHom (uE6Two (K := K) i) (uE6Two_pow_three h2 i))
          (uE6Two_pairwise h2)).range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨(MulEquiv.funMultiplicative (Fin 4) (ZMod 3)).toMonoidHom x, rfl⟩
    have hnc : (MonoidHom.noncommPiCoprod
          (fun i : Fin 4 => zmodPowHom (uE6Two (K := K) i) (uE6Two_pow_three h2 i))
          (uE6Two_pairwise h2)).range ≤ D.comap ι := by
      rw [MonoidHom.noncommPiCoprod_range]
      refine iSup_le fun i => ?_
      rintro y ⟨x, rfl⟩
      change ι ((uE6Two (K := K) i) ^ (Multiplicative.toAdd x).val) ∈ D
      rw [map_pow]
      exact D.pow_mem (hιu_mem i) _
    exact htor.trans hnc
  have hιz : ι z ∈ D := hD_range hz
  change ∃ c : Fin Tag.E6.rank → Lˣ,
    ι z = rootDiagUnit .E6 c ∧ ∀ k, c k ^ 3 = 1 at hιz
  exact hιz

end E6TwoGen

end CFSG.StandardType
