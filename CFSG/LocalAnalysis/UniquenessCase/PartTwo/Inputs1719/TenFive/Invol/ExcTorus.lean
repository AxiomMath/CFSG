module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRootE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcRootG2
public import CFSG.ClassicalInvolution.Balance.LayerGenerationShortAdjoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  (rootDiagUnit rootChar rootChar_add rootChar_nsmul_single)
open CFSG.ClassicalInvolution.Balance (rootDiagAut_xPar rootChar_single_eq)


theorem exists_rootDiag_inv_good {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (hK : Nat.card K = p ^ e)
    (h3 : 3 < p ^ e) (b : Fin τ.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1) (hb1 : b ≠ 1) :
    ∃ x : adjointGroup τ K, orderOf x = p ∧ rootDiagAut τ K b x = x⁻¹ ∧ IsSpecialGood p x := by
  rcases hτ with rfl | hτ
  ·
    let i0 : Fin (Tag.rank .G2) := ⟨0, by decide⟩
    let i1 : Fin (Tag.rank .G2) := ⟨1, by decide⟩
    have hsingle1 : (Pi.single i0 1 : Fin (Tag.rank .G2) → ℤ) = ![1, 0] := by
      funext j; fin_cases j <;> decide
    have hsingle23 : (2 • Pi.single i0 1 + 3 • Pi.single i1 1 :
        Fin (Tag.rank .G2) → ℤ) = ![2, 3] := by
      funext j; fin_cases j <;> decide
    by_cases hb0 : b i0 = -1
    · have hγ1 : IsRoot .G2 ![1, 0] := by
        rw [← hsingle1]
        exact isRoot_single .G2 i0
      refine ⟨xPar (rootOperatorFamily .G2) ![1, 0] 1, ?_, ?_, ?_⟩
      · exact orderOf_xPar hp hγ1 one_ne_zero
      · have hrc : ((rootChar b ![1, 0] : Kˣ) : K) = -1 := by
          rw [← hsingle1, rootChar_single_eq, hb0, Units.val_neg, Units.val_one]
        rw [rootDiagAut_xPar b hγ1 1, hrc, mul_one]
        exact (xPar_neg (F := rootOperatorFamily .G2) ![1, 0] 1).symm
      · exact (isSpecialGood_xPar_G2 hp hp2 hK h3 1).1
    · have hb0' : b i0 = 1 := by
        rcases hb i0 with h | h
        · exact h
        · exact absurd h hb0
      obtain ⟨i, hbi⟩ := Function.ne_iff.mp hb1
      have hb1' : b i1 = -1 := by
        have hi : i = i1 := by
          have h2 : i = (1 : Fin 2) := by
            refine Fin.eq_one_of_ne_zero i ?_
            intro h0
            apply hbi
            rw [h0]
            exact hb0'
          rwa [show (1 : Fin 2) = i1 from rfl] at h2
        rw [hi] at hbi
        rcases hb i1 with h | h
        · exact absurd h hbi
        · exact h
      have hγ2 : IsRoot .G2 ![2, 3] := by
        have h := CFSG.LieType.Steinberg.RankTwo.G2Extras.isRoot_g2Root (n := 7) (by norm_num)
        rwa [CFSG.LieType.Steinberg.RankTwo.G2Extras.g2Root_seven] at h
      refine ⟨xPar (rootOperatorFamily .G2) ![2, 3] 1, ?_, ?_, ?_⟩
      · exact orderOf_xPar hp hγ2 one_ne_zero
      · have hrc : ((rootChar b ![2, 3] : Kˣ) : K) = -1 := by
          rw [← hsingle23, rootChar_add, rootChar_nsmul_single, rootChar_nsmul_single,
            hb0', hb1']
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one, Units.val_neg,
            one_pow]
          norm_num
        rw [rootDiagAut_xPar b hγ2 1, hrc, mul_one]
        exact (xPar_neg (F := rootOperatorFamily .G2) ![2, 3] 1).symm
      · exact (isSpecialGood_xPar_G2 hp hp2 hK h3 1).2
  ·
    obtain ⟨i, hbi⟩ := Function.ne_iff.mp hb1
    have hbi' : b i = -1 := by
      rcases hb i with h | h
      · exact absurd h hbi
      · exact h
    refine ⟨xPar (rootOperatorFamily τ) (Pi.single i 1) 1, ?_, ?_, ?_⟩
    · exact orderOf_xPar hp (isRoot_single τ i) one_ne_zero
    · have hc : ((b i : Kˣ) : K) * 1 = -1 := by rw [hbi']; simp
      rw [rootDiagAut_xPar b (isRoot_single τ i) 1, rootChar_single_eq, hc]
      exact (xPar_neg (F := rootOperatorFamily τ) (Pi.single i 1) 1).symm
    · exact isSpecialGood_xPar_single hτ hp hp2 hK h3 i 1

theorem exists_inv_good_of_involution {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (z : adjointGroup τ K) (hz : z * z = 1)
    (hz1 : z ≠ 1) :
    ∃ x : adjointGroup τ K, orderOf x = p ∧ z * x * z⁻¹ = x⁻¹ ∧ IsSpecialGood p x := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hKodd : Odd (Nat.card K) := by
    rw [hK]
    exact hpodd.pow
  obtain ⟨g, b, hb, hgz⟩ :=
    CFSG.ClassicalInvolution.ModelFacts.exists_conj_eq_rootDiagUnit_of_involution
      hτ hKodd z hz
  set w : adjointGroup τ K := g * z * g⁻¹ with hw_def
  have hw : (w : ModGL τ K) = rootDiagUnit τ b := hgz
  have hz_eq : z = g⁻¹ * w * g := by
    rw [hw_def]
    group
  have hb1 : b ≠ 1 := by
    intro hb1'
    apply hz1
    have hw1 : w = 1 := by
      apply Subtype.ext
      rw [hw, hb1', rootDiagUnit_one]
      simp
    rw [hz_eq, hw1]
    group
  have hτ5 : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by tauto
  obtain ⟨x, hxo, hxi, hxg⟩ := exists_rootDiag_inv_good hτ5 hp hp2 hK h3 b hb hb1
  have hconj_x : w * x * w⁻¹ = x⁻¹ := by
    rw [← hxi]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
    rw [hw]
  refine ⟨g⁻¹ * x * g, ?_, ?_, ?_⟩
  · have hconj : g⁻¹ * x * g = (MulAut.conj g⁻¹) x := by
      simp
    rw [hconj, MulEquiv.orderOf_eq, hxo]
  · calc z * (g⁻¹ * x * g) * z⁻¹
        = g⁻¹ * (w * x * w⁻¹) * g := by
          rw [hz_eq]; group
      _ = g⁻¹ * x⁻¹ * g := by rw [hconj_x]
      _ = (g⁻¹ * x * g)⁻¹ := by group
  · have hmap := IsSpecialGood.map (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective hxg
    have hy : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
      simp
    rwa [hy] at hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
