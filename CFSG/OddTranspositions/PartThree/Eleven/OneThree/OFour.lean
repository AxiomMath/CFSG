module

public import CFSG.OddTranspositions.PartThree.EightNine.O4
public import CFSG.OddTranspositions.PartThree.EightEight.OFourMinus
public import CFSG.OddTranspositions.O4Minus5Pair

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartThree.EightEight

theorem isPGroup_solvableRadical_Halpha_of_o4PairData {G : Type} [Group G] [Finite G]
    {D : Set G} (hC : HypothesisC D) (hO4 : O4PairData G D) :
    IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  obtain ⟨ψ⟩ := CFSG.OddTranspositions.PartThree.nonempty_Halpha_equiv_Yten hC hO4
  obtain ⟨e, -⟩ := CFSG.OddTranspositions.QZ.fixK_equiv_s5
  let φ : H →* Equiv.Perm (Fin 5) :=
    (e : FixK →* Equiv.Perm (Fin 5)).comp (leftHomYten.comp (ψ : H →* Yten))
  have hRle : R ≤ φ.ker :=
    solvableRadical_le_ker_comp_leftHomYten_comp ψ e
  have hker_two : IsPGroup 2 φ.ker := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hφx : φ (x : H) = 1 := x.2
    have hψx : leftHomYten (ψ (x : H)) = 1 := by
      have h := congrArg (fun y => e.symm y) hφx
      simpa [φ, MonoidHom.comp_apply, map_one, MulEquiv.symm_apply_apply] using h
    have hx_sq : (x : H) ^ 2 = 1 := by
      rcases eq_one_or_eq_inr_frob25_of_leftHomYten_eq_one hψx with h1 | h2
      · have hx1 : (x : H) = 1 := by
          apply ψ.injective
          rw [map_one]
          exact Subtype.ext h1
        rw [hx1, one_pow]
      · have hsq : (SemidirectProduct.inr frob25 : PSigmaL225) *
            SemidirectProduct.inr frob25 = 1 := by
          rw [← map_mul, frob25_mul_self, map_one]
        have hψx_sq : (ψ (x : H)) * (ψ (x : H)) = 1 := by
          apply Subtype.ext
          simpa [Subgroup.coe_mul, Subgroup.coe_one, h2] using hsq
        have hx_sq' : (x : H) * (x : H) = 1 := by
          apply ψ.injective
          rw [map_mul, map_one]
          exact hψx_sq
        simpa [pow_two] using hx_sq'
    have hx_sq_ker : (x : ↥φ.ker) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, Subgroup.coe_one] using hx_sq
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx_sq_ker
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h2, pow_one]⟩
  change IsPGroup 2 R
  exact hker_two.to_le hRle

end CFSG.OddTranspositions.PartThree.ElevenThree
