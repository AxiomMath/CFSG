module

public import CFSG.Quasithin.Recognition.St84.AppTreeSAE
public import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

import CFSG.Quasithin.Recognition.St84.TransferVertex
import CFSG.Quasithin.Recognition.St84.Gen.OTwoResL2
import CFSG.Quasithin.Recognition.St84.Gen.CoprimeLift
import CFSG.Quasithin.Recognition.St84.Gen.TransferL2Torus
import CFSG.GroupTheory.FixedCosetCommutator
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.CharacterTheory.Wreathed.OddKernelSylowQuotient
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.GroupTheory.QuasiDihedralFusion.InvolutionCentralizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.Timmesfeld.RankOne.Defs
import CFSG.Dihedral.Glauberman.DicksonMaxB
import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFA5
import CFSG.Quasithin.Recognition.St84.AppTreeL2
import CFSG.Quasithin.Recognition.St84.AppTreeSAP2
import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
import CFSG.Quasithin.Vol2.KGFact3312A5
import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_mem_trivOTwoQuot_of_commutator_mem {L T D : Subgroup G} {n : ℕ}
    (hn : 2 ≤ n) (hq : IsL2Quot n (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L)
    (hD : D ≤ L ⊓ Subgroup.normalizer (T : Set G)) (hDcard : Nat.card D = 2 ^ n - 1)
    {c : G} (hc2 : ∃ k, c ^ (2 ^ k) = 1) (hcL : c ∈ Subgroup.normalizer (L : Set G))
    (hcT : c ∈ Subgroup.normalizer (T : Set G)) (hcD : ∀ d ∈ D, d * c * d⁻¹ * c⁻¹ ∈ T) :
    ∃ t ∈ T, t * c ∈ trivOTwoQuot L := by
  classical
  have hDT : D ≤ Subgroup.normalizer (T : Set G) := hD.trans inf_le_right
  have hoddD : Odd (Nat.card D) := by
    rw [hDcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)) odd_one
  obtain ⟨t, htT, htc⟩ := exists_mul_mem_centralizer_of_odd (Q := T) (J := D)
    hT.2.1 hoddD hDT hcT hcD
  have hcyc2 : IsPGroup 2 (Subgroup.zpowers c) := by
    obtain ⟨k, hk⟩ := hc2
    exact IsPGroup.of_card_dvd_pow (p := 2)
      (by rw [Nat.card_zpowers, orderOf_dvd_iff_pow_eq_one]; exact hk)
  have hsup2 : IsPGroup 2 ↥(Subgroup.zpowers c ⊔ T) :=
    IsPGroup.to_sup_of_normal_right' hcyc2 hT.2.1 (Subgroup.zpowers_le.mpr hcT)
  have ht_mem : t ∈ Subgroup.zpowers c ⊔ T :=
    (le_sup_right : T ≤ Subgroup.zpowers c ⊔ T) htT
  have hc_mem : c ∈ Subgroup.zpowers c ⊔ T :=
    (le_sup_left : Subgroup.zpowers c ≤ Subgroup.zpowers c ⊔ T) (Subgroup.mem_zpowers c)
  have htc_mem : t * c ∈ Subgroup.zpowers c ⊔ T :=
    (Subgroup.zpowers c ⊔ T).mul_mem ht_mem hc_mem
  obtain ⟨k, hk⟩ := hsup2 ⟨t * c, htc_mem⟩
  have htc2 : ∃ k, (t * c) ^ (2 ^ k) = 1 :=
    ⟨k, by simpa using congrArg (fun x : ↥(Subgroup.zpowers c ⊔ T) => (x : G)) hk⟩
  have htcL : t * c ∈ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normalizer (L : Set G)).mul_mem (Subgroup.le_normalizer (hT.1 htT)) hcL
  have htcT : t * c ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem (Subgroup.le_normalizer htT) hcT
  have htcD : ∀ d ∈ D, (t * c) * d = d * (t * c) := by
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp htc d hd).symm
  have hcomm := commutator_mem_pCoreOf_of_centralizes_torus hn hq hT hD hDcard
    htc2 htcL htcT htcD
  refine ⟨t, htT, mem_trivOTwoQuot.mpr ⟨htcL, fun x hx => ?_⟩⟩
  simpa [commutatorElement_def] using hcomm x hx

end Lift

section Vertex

variable {H : Type} [Group H] [Finite H]

theorem f112sa_oTwoPrime_P1'_le_L1_of_isL2Quot {L1 L2 S : Subgroup H} {m k : ℕ}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (hk : 2 ≤ k) (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP1' L1 L2 S)) :
    oTwoPrime (f112saP1' L1 L2 S) ≤ L1 := by
  have hP1N : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).1
  have hQN : pCoreOf 2 (f112saP1' L1 L2 S) ≤ Subgroup.normalizer (L1 : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saP1' L1 L2 S)).trans
      (f112sa_P1'_le_P1 hF)).trans hP1N
  have hL : oTwoPrime (f112saP1' L1 L2 S) =
      oTwoRes L1 ⊔ pCoreOf 2 (f112saP1' L1 L2 S) :=
    f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P1'_of_isL2Quot hF hm h1 hk hq
  have hAQ : oTwoRes L1 ≤ Subgroup.normalizer (pCoreOf 2 (f112saP1' L1 L2 S) : Set H) :=
    (le_sup_left : oTwoRes L1 ≤ f112saP1' L1 L2 S).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP1' L1 L2 S))
  have hQle : pCoreOf 2 (f112saP1' L1 L2 S) ≤ L1 :=
    CFSG.GroupTheory.le_of_commutator_eq_of_sup_eq
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP1' L1 L2 S)).isNilpotent
      hL (oTwoRes_le L1) hQN hAQ hindec
  rw [hL]
  exact sup_le (oTwoRes_le L1) hQle

theorem f112sa_oTwoPrime_P2'_le_L2_of_isL2Quot {L1 L2 S : Subgroup H} {n k : ℕ}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hk : 2 ≤ k) (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP2' L1 L2 S)) :
    oTwoPrime (f112saP2' L1 L2 S) ≤ L2 := by
  have hP2N : f112P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).2
  have hQN : pCoreOf 2 (f112saP2' L1 L2 S) ≤ Subgroup.normalizer (L2 : Set H) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (f112saP2' L1 L2 S)).trans
      (f112sa_P2'_le_P2 hF)).trans hP2N
  have hL : oTwoPrime (f112saP2' L1 L2 S) =
      oTwoRes L2 ⊔ pCoreOf 2 (f112saP2' L1 L2 S) :=
    f112sa_oTwoPrime_eq_oTwoRes_sup_pCoreOf_P2'_of_isL2Quot hF hn h2 hk hq
  have hAQ : oTwoRes L2 ≤ Subgroup.normalizer (pCoreOf 2 (f112saP2' L1 L2 S) : Set H) :=
    (le_sup_left : oTwoRes L2 ≤ f112saP2' L1 L2 S).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112saP2' L1 L2 S))
  have hQle : pCoreOf 2 (f112saP2' L1 L2 S) ≤ L2 :=
    CFSG.GroupTheory.le_of_commutator_eq_of_sup_eq
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (f112saP2' L1 L2 S)).isNilpotent
      hL (oTwoRes_le L2) hQN hAQ hindec
  rw [hL]
  exact sup_le (oTwoRes_le L2) hQle

theorem f112sa_L1_eq_oTwoPrime_of_pCoreOf_le {L1 L2 S : Subgroup H} {m k : ℕ}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) (hm : 2 ≤ m) (h1 : IsL2Quot m (oTwoQuot ↥L1))
    (hk : 2 ≤ k) (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP1' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP1' L1 L2 S), oTwoPrime (f112saP1' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP1' L1 L2 S))
    (hO : pCoreOf 2 L1 ≤ S ⊓ f112saK L1 L2 S) :
    L1 = oTwoPrime (f112saP1' L1 L2 S) := by
  refine le_antisymm ?_ (f112sa_oTwoPrime_P1'_le_L1_of_isL2Quot hF hR hm h1 hk hq hindec)
  have hsup : oTwoRes L1 ⊔ pCoreOf 2 L1 ≤ oTwoPrime (f112saP1' L1 L2 S) :=
    sup_le (f112sa_oTwoRes_le_oTwoPrime_P1'_of_isL2Quot hm h1)
      (hO.trans (f112sa_T_le_oTwoPrime_P1'_of_hyp111R hF hR))
  exact (f112sl_oTwoRes_sup_pCoreOf hm h1).ge.trans hsup

theorem f112sa_L2_eq_oTwoPrime_of_pCoreOf_le {L1 L2 S : Subgroup H} {n k : ℕ}
    (hF : F112HypW L1 L2 S) (hR : Hyp111R L1 L2 S) (hn : 2 ≤ n) (h2 : IsL2Quot n (oTwoQuot ↥L2))
    (hk : 2 ≤ k) (hq : IsL2Quot k (oTwoQuot ↥(oTwoPrime (f112saP2' L1 L2 S))))
    (hindec : ⁅pCoreOf 2 (f112saP2' L1 L2 S), oTwoPrime (f112saP2' L1 L2 S)⁆ =
      pCoreOf 2 (f112saP2' L1 L2 S))
    (hO : pCoreOf 2 L2 ≤ S ⊓ f112saK L1 L2 S) :
    L2 = oTwoPrime (f112saP2' L1 L2 S) := by
  refine le_antisymm ?_ (f112sa_oTwoPrime_P2'_le_L2_of_isL2Quot hF hR hn h2 hk hq hindec)
  have hsup : oTwoRes L2 ⊔ pCoreOf 2 L2 ≤ oTwoPrime (f112saP2' L1 L2 S) :=
    sup_le (f112sa_oTwoRes_le_oTwoPrime_P2'_of_isL2Quot hn h2)
      (hO.trans (f112sa_T_le_oTwoPrime_P2'_of_hyp111R hF hR))
  exact (f112sl_oTwoRes_sup_pCoreOf hn h2).ge.trans hsup

end Vertex

end CFSG.Quasithin.F112R.St84

end
