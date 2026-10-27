module

public import CFSG.LieType.Steinberg.CentralExt.PSLSmall

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

theorem card_ker_le_two_of_perfect_central
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] {X : Type} [Group X]
    (e : X ≃* GL (Fin 3) (ZMod 2)) (q : E →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center E) : Nat.card q.ker ≤ 2 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let e₂ : PSL(3, ZMod 2) ≃* SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq
      CFSG.LocalAnalysis.ComponentInitial.center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hcard : Fintype.card (ZMod 2) = Fintype.card (GaloisField 2 1) := by
    rw [ZMod.card, Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
  let φ : ZMod 2 ≃+* GaloisField 2 1 := FiniteField.ringEquivOfCardEq hcard
  let e' : X ≃* PSL(3, GaloisField 2 1) :=
    e.trans (e₃.symm.trans (e₂.symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3))))
  obtain ⟨hperf, ⟨m⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_two_hopfMultiplier
  let q' : E →* PSL(3, GaloisField 2 1) := e'.toMonoidHom.comp q
  have hq' : Function.Surjective q' := e'.surjective.comp hq
  have hker' : q'.ker = q.ker := by
    ext x
    simp only [MonoidHom.mem_ker, q', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => e'.injective (by simpa using h), fun h => by simp [h]⟩
  have hkc : q'.ker ≤ Subgroup.center E := hker'.le.trans hker
  have hsurj := CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective q' hq' hkc
  have hG : Nat.card (CFSG.Open.griessHopfMultiplier PSL(3, GaloisField 2 1)) = 2 := by
    rw [Nat.card_congr m.toEquiv]
    simp
  have hfin : Finite (CFSG.Open.griessHopfMultiplier PSL(3, GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by omega)
  let ψ := (CFSG.RankThree.PerfectCover.hopfMultiplierToKer q' hq' hkc).comp
    (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      PSL(3, GaloisField 2 1)).toMonoidHom
  have hψ : Function.Surjective ψ :=
    hsurj.comp (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      PSL(3, GaloisField 2 1)).surjective
  have := Nat.card_le_card_of_surjective ψ hψ
  rw [hker'] at this
  omega

end Stellmacher.PU.L3YC

end CFSG.Quasithin
