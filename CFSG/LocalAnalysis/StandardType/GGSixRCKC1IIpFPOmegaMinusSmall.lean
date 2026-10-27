module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpAltEightTwo
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoOmTwoAux
import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.LieType.Universal CFSG.StandardType

theorem rckIIp_false_of_POmegaMinus_le_two
    {X : Type} [Group X] {m g : ℕ} (hm : m ≤ 2) (hg : 1 ≤ g)
    (φ : (ggU .POmegaMinus m g).K →* X) {J : Subgroup X} (hJ : J ≤ φ.range)
    (hA8 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 8))) : False := by
  let G : Subgroup (ggU .POmegaMinus m g).K := J.comap φ
  let π : ↥G →* X := φ.comp G.subtype
  have hπrange : π.range = J := by
    change (φ.comp G.subtype).range = J
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact Subgroup.map_comap_eq_self hJ
  have hA8' : Nonempty
      ((↥π.range ⧸ Subgroup.center ↥π.range) ≃* alternatingGroup (Fin 8)) := by
    rw [hπrange]
    exact hA8
  rcases lt_or_eq_of_le hm with hm2 | rfl
  ·
    have hm1 : m - 1 = 0 := by omega
    let K := GaloisField 2 g
    let b := (CFSG.LieType.Universal.minusCoeffs 2 g).1
    let c := (CFSG.LieType.Universal.minusCoeffs 2 g).2
    have hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0 :=
      CFSG.LieType.Universal.minusCoeffs_irr 2 g
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hker : (Spin.spinMatrix (Spin.quadMinus m K b c)).ker = ⊥ :=
      Spin.ker_spinMatrix_quadMinus_eq_bot (K := K) (n := m) (b := b) (c := c) hirr h2
    have hι : Fintype.card (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) = 2 := by
      rw [hm1]
      simp
    let j : ↥G →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K :=
      (Spin.spinMatrix (Spin.quadMinus m K b c)).comp G.subtype
    have hspin_inj : Function.Injective (Spin.spinMatrix (Spin.quadMinus m K b c)) :=
      (MonoidHom.ker_eq_bot_iff _).mp hker
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subgroup.subtype_injective G (hspin_inj hxy)
    let : Finite ↥G := Finite.of_injective j hj
    exact rckIIp_false_of_alt_eight_of_GL_two (F := K) hι j hj π hA8'
  ·
    let K := GaloisField 2 g
    let b := (CFSG.LieType.Universal.minusCoeffs 2 g).1
    let c := (CFSG.LieType.Universal.minusCoeffs 2 g).2
    have hK : Nat.card K = 2 ^ g := GaloisField.card 2 g (by omega)
    have hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0 :=
      CFSG.LieType.Universal.minusCoeffs_irr 2 g
    have : Fact (∀ r : K, r ^ 2 ≠ -c + b * r) :=
      Spin.Twisted.fact_shortField hirr
    obtain ⟨eSpin⟩ := CFSG.StandardType.RCKRP.irgOm2_exists_spinEquivSL2
      (K := K) (b := b) (c := c) hirr
    have hEcard : Nat.card (Spin.Twisted.ShortField b c) =
        Nat.card (GaloisField 2 (2 * g)) := by
      rw [CFSG.StandardType.RCKRP.irgOm2_card_shortField,
        GaloisField.card 2 (2 * g) (by omega)]
      change Nat.card K ^ 2 = 2 ^ (2 * g)
      rw [hK, ← pow_mul]
      congr 1
      omega
    have : Finite (Spin.Twisted.ShortField b c) :=
      Spin.Twisted.finite_shortField (K := K) (b := b) (c := c)
    let : Fintype (Spin.Twisted.ShortField b c) := Fintype.ofFinite _
    let : Fintype (GaloisField 2 (2 * g)) := Fintype.ofFinite _
    let φfield : Spin.Twisted.ShortField b c ≃+* GaloisField 2 (2 * g) :=
      FiniteField.ringEquivOfCardEq (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact hEcard)
    let eField : Matrix.SpecialLinearGroup (Fin 2) (Spin.Twisted.ShortField b c) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * g)) :=
      CFSG.GorensteinWalter.FieldTransport.specialLinearGroupMulEquiv φfield
    let eAux : spinGroup (Spin.quadMinus 2 K b c) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * g)) :=
      eSpin.trans eField
    let j : ↥G →* GL (Fin 2) (GaloisField 2 (2 * g)) :=
      Matrix.SpecialLinearGroup.toGL.comp (eAux.toMonoidHom.comp G.subtype)
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subgroup.subtype_injective G
        (eAux.injective (Matrix.SpecialLinearGroup.toGL_injective hxy))
    let : Finite ↥G := Finite.of_injective j hj
    exact rckIIp_false_of_alt_eight_of_GL_two (F := GaloisField 2 (2 * g))
      (ι := Fin 2) (by simp) j hj π hA8'

end CFSG.StandardType.RCKC1
