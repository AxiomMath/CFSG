module

public import CFSG.Quasithin.H13.J4TypeFinal
public import CFSG.Sporadic.J4.QT2LocX0CentMain
public import CFSG.Sporadic.J4.QT2LocOrder
public import CFSG.Sporadic.J4.QTRankProof
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Three
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Cent
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Count
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Amalgams
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146G4
public import CFSG.Quasithin.EmptyFaithful.S146R2
public import CFSG.Quasithin.EmptyFaithful.S146R3
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Sporadic.J4.QT2LocCntProof
public import CFSG.Sporadic.J4.QT2LocFiveProof
public import CFSG.Sporadic.J4.QT2LocFixMain
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.J4L4

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Blueprint

local notation "A₈" => alternatingGroup (Fin 8)

theorem card_centralizer_of_order_five
    {g : J} (hg : orderOf g = 5) :
    Nat.card ↥(Subgroup.centralizer ({g} : Set J)) = 6720 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hF : J4Facts := j4Facts
  have : Finite J := CFSG.Quasithin.H13.J4.finite_J'
  rw [card_centralizer_eq_of_order_prime CFSG.Sporadic.J4.QT2.card_J_factorization_five
    (CFSG.Sporadic.J4.QT2.orderOf_fiveElt hF.mat) hg]
  exact CFSG.Sporadic.J4.QT2.card_centralizer_fiveElt hF

theorem card_le_of_centralizes_five
    {g : J} (hg : orderOf g = 5)
    {K : Subgroup J} (hK : IsPGroup 2 K) (hKc : K ≤ Subgroup.centralizer ({g} : Set J)) :
    Nat.card K ≤ 64 := by
  have : Finite J := CFSG.Quasithin.H13.J4.finite_J'
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hdvd : Nat.card K ∣ 6720 := card_centralizer_of_order_five hg ▸ Subgroup.card_dvd_of_le hKc
  rw [hn] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have h7 : 7 ≤ n := by
    by_contra h
    push Not at h
    have : 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : 2 ^ 7 ∣ 2 ^ n := pow_dvd_pow 2 h7
  have h := this.trans hdvd
  norm_num at h

section H13

open CFSG.Quasithin.H13.J4

theorem isTypeJ4Centralizer_of_fixed
    {z : J} (hzE : z ∈ Eg uJ 11) (hz1 : z ≠ 1) (hfix : ∀ t ∈ P0, t * z = z * t) :
    IsTypeJ4Centralizer J z := by
  have hF : J4Facts := j4Facts
  have hM := hF.mat
  have : Finite J := finite_J'
  have : Finite NativeSporadic.J4 := (fam_j4_simplicity).1
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact Eg_sq (elem_uJ hM) hzE) hz1
  let S : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM hF, card_J_factorization hF])
  have hzS : z ∈ (Subgroup.center (S : Subgroup J)).map (S : Subgroup J).subtype := by
    rw [mem_center_map_iff, Sylow.coe_ofCard]
    exact ⟨Eg_le_P0 hzE, fun y hy => hfix y hy⟩
  obtain ⟨hord, S', hS'⟩ := @twoCentral_of_mulEquiv J NativeSporadic.J4 (Subgroup.toGroup J)
    Units.instGroup _ z ((seedEquiv hM).symm z) S hzS (seedEquiv hM).symm rfl
  have h4 := concreteJ4_typeJ4.2.2.2.2 ((seedEquiv hM).symm z) (hord.trans hz2) ⟨S', hS'⟩
  exact @IsTypeJ4Centralizer.of_mulEquiv NativeSporadic.J4 J Units.instGroup (Subgroup.toGroup J)
    _ _ _ h4 (seedEquiv hM) ((seedEquiv hM).apply_symm_apply z)

end H13

theorem false_of_le_centralizer
    {z : J} (hzE : z ∈ Eg uJ 11) (hz1 : z ≠ 1) (hfix : ∀ t ∈ P0, t * z = z * t)
    {B : Type} [Group B] (ι : B →* J) (hι : Function.Injective ι)
    (hBz : ∀ x, ι x ∈ Subgroup.centralizer ({z} : Set J)) (f : B →* A₈)
    (hf : Function.Surjective f) (hker : ∀ x : B, f x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1) : False := by
  obtain ⟨-, -, -, hX, -⟩ := isTypeJ4Centralizer_of_fixed hzE hz1 hfix
  obtain ⟨Z, hZn, hZ3, -⟩ := hX
  have : Finite J := CFSG.Quasithin.H13.J4.finite_J'
  set C : Subgroup J := Subgroup.centralizer ({z} : Set J) with hC
  have hP : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥C)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  refine false_of_normal_three (QuotientGroup.mk' (CFSG.pCore 2 ↥C))
    (QuotientGroup.mk'_surjective _) hP hZn hZ3 ?_ (ι.codRestrict C hBz)
    (fun x y hxy => hι (congrArg Subtype.val hxy)) f hf hker
  intro g hg5 h9
  have hg' : orderOf (g : J) = 5 := by rw [Subgroup.orderOf_coe, hg5]
  have h1 := card_centralizer_subgroup_dvd C g
  rw [card_centralizer_of_order_five hg'] at h1
  exact absurd (h9.trans h1) (by norm_num)

end CFSG.Quasithin.J4L4
