module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Uniqueness of inverted elements in order-three cosets -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If an order-three subgroup has normalizer `M`, then two elements of `M`
inverted by an involution outside `M` cannot lie in the same left coset of
that subgroup. -/
public theorem inverted_elements_eq_of_mul_inv_mem_card_three_normalizer
    {G : Type u} [Group G] [Finite G]
    (M F : Subgroup G)
    (hFcard : Nat.card F = 3)
    (hFnormalizer : Subgroup.normalizer (F : Set G) = M)
    {y x z : G}
    (hy : IsInvolution y) (hyM : y ∉ M)
    (hx : x ∈ invertedElements M y)
    (hz : z ∈ invertedElements M y)
    (hprodF : x * z⁻¹ ∈ F) :
    x = z := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : G := x * z⁻¹
  have hfF : f ∈ F := hprodF
  by_contra hxz
  have hfne : f ≠ 1 := by
    intro hf
    apply hxz
    change x * z⁻¹ = 1 at hf
    calc
      x = (x * z⁻¹) * z := by group
      _ = z := by rw [hf]; simp
  have hF_eq_zpowers : F = Subgroup.zpowers f := by
    apply le_antisymm
    · intro a ha
      let fF : F := ⟨f, hfF⟩
      let aF : F := ⟨a, ha⟩
      have hfFne : fF ≠ 1 := by
        intro h
        apply hfne
        exact congrArg Subtype.val h
      have haz := mem_zpowers_of_prime_card
        (G := F) (p := 3) hFcard (g := fF) (g' := aF) hfFne
      rcases Subgroup.mem_zpowers_iff.mp haz with ⟨n, hn⟩
      apply Subgroup.mem_zpowers_iff.mpr
      exact ⟨n, congrArg Subtype.val hn⟩
    · exact Subgroup.zpowers_le.mpr hfF
  have hxTop : x ∈ invertedElements (⊤ : Subgroup G) y :=
    ⟨by simp, hx.2⟩
  have hzTop : z ∈ invertedElements (⊤ : Subgroup G) y :=
    ⟨by simp, hz.2⟩
  let v : G := z * y
  have hvI : IsInvolution v := by
    dsimp [v]
    rw [fact_1_4_involution_mul hy]
    refine ⟨?_, ?_⟩
    · intro hzy
      apply hyM
      simpa [hzy] using hz.1
    · have hyInv : y⁻¹ = y := inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using hy.2)
      simpa [hyInv] using hz.2
  have hfInv : f ∈ invertedElements (⊤ : Subgroup G) v := by
    simpa [f, v] using fact_1_4_inverted_mul_inv hy hxTop hzTop
  have hvNormF : v ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hF_eq_zpowers,
      MonoidHom.map_zpowers]
    change Subgroup.zpowers (v * f * v⁻¹) = Subgroup.zpowers f
    rw [hfInv.2]
    simp
  have hvM : v ∈ M := by
    rw [← hFnormalizer]
    exact hvNormF
  apply hyM
  have hyEq : y = z⁻¹ * v := by
    dsimp [v]
    group
  rw [hyEq]
  exact M.mul_mem (M.inv_mem hz.1) hvM

end CFSG.GorensteinWalter
