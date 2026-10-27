module

public import CFSG.Quasithin.Background.JonesParshallG2Field
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix

namespace Insp9

noncomputable def slMapEquiv {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (n : ℕ) :
    SpecialLinearGroup (Fin n) K ≃* SpecialLinearGroup (Fin n) K' :=
  MonoidHom.toMulEquiv (SpecialLinearGroup.map e.toRingHom) (SpecialLinearGroup.map e.symm.toRingHom)
    (by ext x i j; simp) (by ext x i j; simp)

noncomputable def ringEquivZMod2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    K ≃+* ZMod 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  exact (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm

noncomputable def statedSLEquivZMod2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) :
    ↥(CFSG.Assembly.LowTwoRank.StatedSL n K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL n (ZMod 2)) :=
  (specialLinearGroupEquivStatedSL n K).symm.trans
    ((slMapEquiv (ringEquivZMod2 K hK) n).trans (specialLinearGroupEquivStatedSL n (ZMod 2)))

noncomputable def g2EquivZMod2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ↥(quasithinG2 K) ≃* ↥(quasithinG2 (ZMod 2)) := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  have h2 : CharP (ZMod 2) 2 := inferInstance
  refine ((JonesParshall.zornConj (ringEquivZMod2 K hK)).subgroupMap (quasithinG2 K)).trans
    (MulEquiv.subgroupCongr ?_)
  rw [Bridge.Alt57Model.quasithinG2_eq_cayleyGroup, JonesParshall.map_cayleyGroup,
    Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]

noncomputable def g2DerivedEquivZMod2 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  have h2 : CharP (ZMod 2) 2 := inferInstance
  refine ((JonesParshall.zornConj (ringEquivZMod2 K hK)).subgroupMap
    ⁅quasithinG2 K, quasithinG2 K⁆).trans (MulEquiv.subgroupCongr ?_)
  rw [Bridge.Alt57Model.quasithinG2_eq_cayleyGroup, Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    JonesParshall.map_cayley_commutator]

end Insp9

end CFSG.Quasithin
