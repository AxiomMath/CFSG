module

public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.JonesParshallG2Field
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import Certificates.Certificate8080
public import Certificates.Certificate8081
public import Certificates.Certificate17002
public import Certificates.Certificate17028
public import Certificates.Certificate17951
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import Certificates.Certificate19953
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57ModelBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.B1MoreElevenF
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Bridge.Alt57Model
  CFSG.Open
open scoped commutatorElement

theorem outAbelian_commutator_of_g2_of_bound
    (hsub : OutAbelian ↥subG2) {Ω : Type} [Group Ω]
    {M : Subgroup Ω} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (e : ↥M ≃* ↥(quasithinG2 K)) : OutAbelian ↥⁅M, M⁆ := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨f1⟩ := nonempty_commutator_equiv e
  have hc : ⁅quasithinG2 K, quasithinG2 K⁆ = ⁅cayleyGroup K, cayleyGroup K⁆ := by
    rw [quasithinG2_eq_cayleyGroup]
  let f2 : ↥⁅quasithinG2 K, quasithinG2 K⁆ ≃* ↥⁅cayleyGroup K, cayleyGroup K⁆ :=
    MulEquiv.subgroupCongr hc
  let f3 : ↥⁅cayleyGroup K, cayleyGroup K⁆ ≃* ↥subG2 :=
    ((zornConj ε).subgroupMap _).trans
      (MulEquiv.subgroupCongr ((map_cayley_commutator ε).trans g2Two_commutator_eq))
  exact outAbelian_of_mulEquiv ((f1.trans f2).trans f3).symm hsub

theorem asOutAbelian_of_g2Bound
    (hsub : OutAbelian ↥subG2) : AsOutAbelian := by
  intro V _ M h
  rcases h with ⟨n, h5, h8, ⟨e⟩⟩ | ⟨K, _, _, hK, ⟨e⟩⟩
  · exact outAbelian_commutator_of_perm h5 h8 e
  · exact outAbelian_commutator_of_g2_of_bound hsub hK e

theorem asOutAbelian
    : AsOutAbelian := asOutAbelian_of_g2Bound outAbelian_subG2

end CFSG.Quasithin
