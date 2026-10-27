module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCenter
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofG2
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofConj
import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofCent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie3ProofEight
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier
public import CFSG.RankThree.PartTwo.Sec11.Item1119NUFam
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarG2

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.HighestRoot
open CFSG.Open (ordG2)
open CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar

namespace Item1119NU

section Main


theorem numFamG2 : NumFamG2 := by
  intro Z _ _ hZq α σ J ξ γ hα3 hJα hJT _hξJ hξsyl _hξ9 _hσ3 _hσα _hσJ _hσξ _hγ3 _hP3 hLB
  obtain ⟨q, hq, ⟨e0⟩⟩ := hZq
  have hperf : Group.IsPerfect Z := by
    have := SetUp1118Proof.isPerfect_lie_G2 q hq
    exact Group.IsPerfect.ofSurjective (f := e0.symm.toMonoidHom) e0.symm.surjective
  have hZ : ∃ (X : Type) (_ : Group X), (∃ (q' : TauCeti.PrimePower)
      (hq' : (TauCeti.LieTypeIndex.G2 q').Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q', hq'⟩).Group)) ∧
      Nonempty (Z ≃* _root_.commutator X) :=
    ⟨Z, inferInstance, ⟨q, hq, ⟨e0⟩⟩, nonempty_mulEquiv_commutator_of_isPerfect hperf⟩
  have hinner : α ∈ (MulAut.conj : Z →* MulAut Z).range := by
    by_contra hno
    exact noOuterType424G2_holds Z hZ α J hα3 hno hJα hJT
  obtain ⟨z, rfl⟩ := hinner
  have hz3 : MulAut.conj z ^ 3 = 1 := hα3
  rcases KS11Lie3Proof.splitFamily_g2 Z hZ with hZ' | hno
  swap
  · exact (hno z J hz3 hJα hJT).elim
  have hcen : Subgroup.center Z = ⊥ := KS11Lie3Proof.center_eq_bot_g2 Z hZ
  have hcent : Function.Injective (MulAut.conj : Z →* MulAut Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have h1 := KS11Lie3Proof.mem_center_of_conj_eq_one (MonoidHom.mem_ker.mp hx)
    rw [hcen, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr h1
  obtain ⟨K, _, _, _hK3, _hK4, e, hezM, hB⟩ := KS11Lie4Proof.exists_g2_threeB
    (KS11Lie4Proof.g2ThreeConjSL2_of_minus KS11Lie7Proof.g2ThreeConjSL2Minus_holds)
    (KS11Lie4Proof.g2ThreeACent_of_minus KS11Lie7Proof.g2ThreeACentMinus_holds)
    KS11Lie4Proof.g2ThreeBCent_holds hZ' hz3 hJα hJT
  have hJS : J = (KS11Lie4Proof.g2ShortSL2 K).comap e.toMonoidHom := hB.eq hJα
  obtain ⟨e'⟩ := nonempty_mulEquiv_long_short e
  have hz3' : z ^ 3 = 1 := (KS11Lie4Proof.g2_order_three hZ' hz3 hJα hJT).1
  obtain ⟨ζ, hζM, hzζ, hζ3, hζord⟩ := exists_big_elt_of_sylow
    (e'.trans (MulEquiv.subgroupCongr hJS.symm)) hξsyl hezM hz3'
  have hζJ : ∀ j ∈ J, ζ * j = j * ζ := by
    intro j hj
    rw [hJS] at hj
    apply e.injective
    rw [map_mul, map_mul]
    exact (KS11Lie4Proof.g2Short_commute_g2Long hj hζM).symm
  have hle := hLB ζ hζ3
    (by
      rw [MulAut.conj_apply]
      calc z * ζ * z⁻¹ = ζ * z * z⁻¹ := by rw [hzζ]
        _ = ζ := by group)
    (fun j hj => by
      calc ζ * j * ζ⁻¹ = j * ζ * ζ⁻¹ := by rw [hζJ j hj]
        _ = j := by group)
  rw [orderOf_injective (MulAut.conj : Z →* MulAut Z) hcent ζ] at hle
  rw [hζord] at hle
  omega

end Main

end Item1119NU

end CFSG.RankThree.PartTwo.Sec11

end
