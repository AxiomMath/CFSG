module

public import CFSG.RankThree.GF2n.Smith81.TiD3Irreducible
public import CFSG.RankThree.GF2n.Stroth80.SL2CubeFixed

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Stroth80.SL2Descent
open scoped MatrixGroups

theorem d3ModuleStatement_holds : D3ModuleStatement := by
  intro K F _ _ _ _ _ _ hcard hK4 E _ _ _ B Qf halt hnd hQadd hQsmul _ hdim ρ hρQ hρinj hC
  classical
  letI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_injective_algebraMap (algebraMap K F).injective 2
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  have hkK : Fintype.card K = 2 ^ (k : ℕ) := hk
  have hK4' : 4 ≤ Fintype.card K := by rwa [Nat.card_eq_fintype_card] at hK4
  have hk2 : 2 ≤ (k : ℕ) := by
    by_contra h
    have h1 : (k : ℕ) ≤ 1 := by omega
    have h2 := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h1
    omega
  have hF : Fintype.card F = 2 ^ ((k : ℕ) * 3) := by
    rw [← Nat.card_eq_fintype_card, hcard, Nat.card_eq_fintype_card, hkK, ← pow_mul]
  have hG : commutator SL(2, F) = ⊤ := by
    refine D2.sl2_commutator_eq_top ?_
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ ((k : ℕ) * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  let ρ' : Representation K SL(2, F) E := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
  have hinj' : ∀ g, (∀ e, ρ' g e = e) → g = 1 := fun g hg => by
    apply hρinj
    rw [map_one]
    exact LinearEquiv.ext hg
  have hg1 : ∃ g : SL(2, F), g ≠ 1 := by
    refine ⟨D2.uSL 1, fun h => ?_⟩
    have h1 := congrArg (fun g : SL(2, F) => (g : Mat2 F) 0 1) h
    simp [D2.uSL] at h1
  have hnt : ∃ g, ρ g ≠ 1 := by
    obtain ⟨g, hg⟩ := hg1
    exact ⟨g, fun h => hg (hρinj (by rw [h, map_one]))⟩
  have hirr : ∀ W : Submodule K E, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    by_cases hC0 : ∀ e, (∀ g, ρ g e = e) → e = 0
    · exact irreducible_of_fixed_zero hkK (by omega) hF hdim B Qf halt hnd hQadd ρ' hρQ hC0
    · exfalso
      push Not at hC0
      obtain ⟨e, he, he0⟩ := hC0
      exact false_of_fixed_ne_zero hkK (by omega) hK4 hF hG hdim B Qf halt hnd hQadd hQsmul ρ'
        hρQ hinj' hC ⟨e, he, he0⟩ hg1
  exact d3_of_irreducible hcard hK4 B Qf halt hnd hQadd hQsmul hdim ρ hρQ hirr hnt

end CFSG.RankThree.GF2n.Smith81
