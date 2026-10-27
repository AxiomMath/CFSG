module

public import CFSG.RankThree.PartOne.S13K.BlockAt
public import CFSG.RankThree.PartOne.S13K.KFLiftRows
public import CFSG.RankThree.PartOne.KF.U4Multiplier
public import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Chevalley.RootCommutatorData
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearStep
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryLiftBlocks
public import CFSG.RankThree.PartOne.KF.R10Final
public import CFSG.RankThree.PartOne.S12.Sec138Loc
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.ThSchreier.GlobalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate119
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate9130
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.RankThree.PartOne.KF132

open CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover
  CFSG.RankThree.GroupTheory

theorem exists_inv_conj_sl2 {F : Type*} [Field F] [CharP F 2]
    (z : Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * z * w⁻¹ = z⁻¹ := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have key : ∀ (w : Matrix.SpecialLinearGroup (Fin 2) F),
      (w : Matrix (Fin 2) (Fin 2) F) * (z : Matrix (Fin 2) (Fin 2) F) =
        ((z⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          (w : Matrix (Fin 2) (Fin 2) F) →
      ∃ w : Matrix.SpecialLinearGroup (Fin 2) F, w * z * w⁻¹ = z⁻¹ := by
    intro w h
    refine ⟨w, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    simpa [Matrix.SpecialLinearGroup.coe_mul] using h
  have hz : (z : Matrix (Fin 2) (Fin 2) F) =
      !![(z : Matrix (Fin 2) (Fin 2) F) 0 0, (z : Matrix (Fin 2) (Fin 2) F) 0 1;
        (z : Matrix (Fin 2) (Fin 2) F) 1 0, (z : Matrix (Fin 2) (Fin 2) F) 1 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have hzi : ((z⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(z : Matrix (Fin 2) (Fin 2) F) 1 1, -(z : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(z : Matrix (Fin 2) (Fin 2) F) 1 0, (z : Matrix (Fin 2) (Fin 2) F) 0 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  set a := (z : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (z : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (z : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (z : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  by_cases hc0 : c ≠ 0
  · obtain ⟨w, hw⟩ : ∃ w : Matrix.SpecialLinearGroup (Fin 2) F,
        (w : Matrix (Fin 2) (Fin 2) F) = !![1, (a + d) / c; 0, 1] :=
      ⟨⟨!![1, (a + d) / c; 0, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
    apply key w
    rw [hw, hzi]
    conv_lhs => rw [hz]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
    all_goals (try simp only [CharTwo.neg_eq]) <;> ring_nf <;> simp [h2]
  · push Not at hc0
    by_cases hb0 : b ≠ 0
    · obtain ⟨w, hw⟩ : ∃ w : Matrix.SpecialLinearGroup (Fin 2) F,
          (w : Matrix (Fin 2) (Fin 2) F) = !![1, 0; (a + d) / b, 1] :=
        ⟨⟨!![1, 0; (a + d) / b, 1], by simp [Matrix.det_fin_two]⟩, rfl⟩
      apply key w
      rw [hw, hzi]
      conv_lhs => rw [hz]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc0] <;>
        field_simp
      all_goals (try simp only [CharTwo.neg_eq]) <;> ring_nf <;> simp [h2]
    · push Not at hb0
      obtain ⟨w, hw⟩ : ∃ w : Matrix.SpecialLinearGroup (Fin 2) F,
          (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] :=
        ⟨⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩, rfl⟩
      apply key w
      rw [hw, hzi]
      conv_lhs => rw [hz]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hc0, hb0]

theorem exists_inv_conj_of_model {X : Type} [Group X] {g : ℕ}
    (hX : StatedClassicalModel X .PSL 2 2 g) (z : X) : ∃ w : X, w * z * w⁻¹ = z⁻¹ := by
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hX
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := g) (by rw [Fintype.card_eq_nat_card, hK])
  obtain ⟨e0⟩ := KFU.nonempty_SL2_mulEquiv_statedProj (F := K)
  obtain ⟨w', hw'⟩ := exists_inv_conj_sl2 (e0.symm (e z))
  refine ⟨e.symm (e0 w'), ?_⟩
  apply e.injective
  rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
  have h1 := congrArg e0 hw'
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
    at h1
  exact h1

theorem card_multiplier_psl_two_even {g : ℕ} (hg : 3 ≤ g) :
    Nat.card (Blueprint.Multiplier.generic .PSL 2 2 g ×
      Blueprint.Multiplier.exceptional .PSL 2 2 g) = 1 := by
  have hcop : Nat.Coprime 2 (2 ^ g - 1) := by
    rw [Nat.coprime_two_left]
    have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    have h2 : Even (2 ^ g) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    obtain ⟨m, hm⟩ := h2
    exact ⟨m - 1, by omega⟩
  have hgen : Blueprint.Multiplier.genericOrders .PSL 2 2 g = (1, 1) := by
    change (Nat.gcd 2 (2 ^ g - 1), 1) = (1, 1)
    rw [hcop]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 2 2 g = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem psl2EvenCenterTrivial_of_multipliers
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {g : ℕ} (hg : 3 ≤ g) (hqs : IsQuasisimple X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 2 2 g) :
    Subgroup.center X = ⊥ := by
  have hm : Models.LieModel (X ⧸ Subgroup.center X) .PSL 2 2 g := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSL 2 2 g hm
  have : Group.IsPerfect (X ⧸ Subgroup.center X) := ⟨hcomm⟩
  have : Group.IsPerfect X := hqs.1
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _) hker
  have hdvd : Nat.card (QuotientGroup.mk' (Subgroup.center X)).ker ∣
      Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv,
    card_multiplier_psl_two_even hg, Nat.dvd_one, QuotientGroup.ker_mk'] at hdvd
  rw [← Subgroup.card_eq_one]
  exact hdvd

theorem kLayer_conj_mem {G : Type} [Group G] {L : Subgroup G} {b y k : G}
    (hy : y ∈ L ⊓ Subgroup.centralizer ({b} : Set G)) (hk : k ∈ kLayer L b) :
    y * k * y⁻¹ ∈ kLayer L b := by
  have h1 := Equivariance.inSubgroup_layer_conjBy y (L ⊓ Subgroup.centralizer ({b} : Set G))
  have h2 : conjBy y (L ⊓ Subgroup.centralizer ({b} : Set G)) =
      L ⊓ Subgroup.centralizer ({b} : Set G) :=
    Equivariance.conjBy_eq_of_mem_normalizer (Subgroup.le_normalizer hy)
  rw [h2] at h1
  have h3 : y * k * y⁻¹ ∈ conjBy y (kLayer L b) := Subgroup.mem_map_of_mem _ hk
  have h4 : kLayer L b = inSubgroup (fun K _ => layer K) (L ⊓ Subgroup.centralizer ({b} : Set G)) :=
    rfl
  rw [h4, h1]
  rw [h4] at h3
  exact h3

open CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.PartOne.KFU in
theorem kfAt_of_layer {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hE3 : Nat.card E = p ^ 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcL : c ∉ L)
    {t : MulAut E} (htr : IsAutReflection p E t) (htL : t ∈ torusImage E L)
    (hsplit : E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
      Nat.card ↥(autMovedInG E t) = p)
    {b : G} (hbE : b ∈ E) (hbL : b ∈ L) (hb1 : b ≠ 1) (hbt : ((t ⟨b, hbE⟩ : E) : G) = b)
    {g : ℕ} (hAK : Nat.card ↥(E ⊓ kLayer L b) = p)
    (hmodel : StatedClassicalModel (↥(kLayer L b) ⧸ Subgroup.center ↥(kLayer L b)) .PSL 2 2 g)
    (hZ : Subgroup.center ↥(kLayer L b) = ⊥) :
    KFAt p E g t ∧ kZero p E t = kLayer L b := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp3 := h.three_lt
  have hEel := h.E_elem
  set K := kLayer L b with hK
  obtain ⟨hEsup, hCM, hM'card⟩ := hsplit
  have hKle : K ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := hKle.trans inf_le_right
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKL.trans hLc
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨x, hxmem, hxt⟩ := Subgroup.mem_map.mp htL
  have hlL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hxmem
  have hteq : ∀ e : E, ((t e : E) : G) = (x : G) * (e : G) * (x : G)⁻¹ := fun e => by
    rw [← hxt]
    rfl
  have hfixiff : ∀ {e : G}, e ∈ autFixedInG E t ↔ ∃ he : e ∈ E, t ⟨e, he⟩ = ⟨e, he⟩ :=
    mem_autFixedInG_iff
  have hbC : b ∈ autFixedInG E t := hfixiff.mpr ⟨hbE, Subtype.ext hbt⟩
  have hlc : (x : G) * c = c * (x : G) := Subgroup.mem_centralizer_singleton_iff.mp (hLc hlL)
  have hcC : c ∈ autFixedInG E t := hfixiff.mpr ⟨hcE, Subtype.ext (by
    rw [hteq]
    show (x : G) * c * (x : G)⁻¹ = c
    rw [hlc]
    group)⟩
  have hlb : (x : G) * b = b * (x : G) := by
    have h1 := hteq ⟨b, hbE⟩
    rw [hbt] at h1
    have h2 : b * (x : G) = (x : G) * b := by
      have : b = (x : G) * b * (x : G)⁻¹ := h1
      calc b * (x : G) = ((x : G) * b * (x : G)⁻¹) * (x : G) := by rw [← this]
        _ = (x : G) * b := by group
    exact h2.symm
  have hlcb : (x : G) ∈ L ⊓ Subgroup.centralizer ({b} : Set G) :=
    ⟨hlL, Subgroup.mem_centralizer_singleton_iff.mpr hlb⟩
  have hbp : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) b hbE
  have hcp : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) c hcE
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbc : b * c = c * b := hEcomm b hbE c hcE
  have hdiscbc : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro y hyb hyc
    by_contra hy1
    have hzx : Subgroup.zpowers y = Subgroup.zpowers c :=
      zpowers_eq_of_mem_of_ne_one hp hcord hyc hy1
    have hcx : c ∈ Subgroup.zpowers y := hzx ▸ Subgroup.mem_zpowers c
    have hyL : y ∈ L := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyb
      exact Subgroup.zpow_mem _ hbL k
    exact hcL (Subgroup.zpowers_le.2 hyL hcx)
  have hBCcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = p ^ 2 := by
    rw [card_sup_of_commute_disjoint (fun y hy y' hy' => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
        exact ((Commute.zpow_zpow (show Commute b c from hbc) i j)).eq) hdiscbc,
      Nat.card_zpowers, Nat.card_zpowers, hbord, hcord]
    ring
  have hBCleC : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ autFixedInG E t :=
    sup_le (Subgroup.zpowers_le.2 hbC) (Subgroup.zpowers_le.2 hcC)
  have hCleE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  have hM'leE : autMovedInG E t ≤ E := Subgroup.map_subtype_le _
  have hCcard : Nat.card ↥(autFixedInG E t) = p ^ 2 := by
    have h1 := card_sup_of_commute_disjoint (K := autFixedInG E t) (L := autMovedInG E t)
      (fun y hy y' hy' => hEcomm y (hCleE hy) y' (hM'leE hy')) (disjoint_iff.mpr hCM)
    have h2 : Nat.card ↥E = Nat.card ↥(autFixedInG E t ⊔ autMovedInG E t) := by rw [← hEsup]
    rw [h1, hM'card, hE3] at h2
    have h3 : p ^ 3 = p ^ 2 * p := by ring
    rw [h3] at h2
    exact (Nat.eq_of_mul_eq_mul_right hp.pos h2).symm
  have hCeq : Subgroup.zpowers b ⊔ Subgroup.zpowers c = autFixedInG E t :=
    Subgroup.eq_of_le_of_card_ge hBCleC (by rw [hBCcard, hCcard])
  have hCcentK : autFixedInG E t ≤ Subgroup.centralizer (K : Set G) := by
    rw [← hCeq]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKb hk)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKc hk)
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' p (G := ↥(E ⊓ K)) (by rw [hAK])
  set z : G := (z0 : G) with hzdef
  have hzE : z ∈ E := (Subgroup.mem_inf.mp z0.2).1
  have hzK : z ∈ K := (Subgroup.mem_inf.mp z0.2).2
  have hzord : orderOf z = p := by
    rw [hzdef, Subgroup.orderOf_coe]
    exact hz0
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzord
    exact hp.one_lt.ne hzord
  have hEKz : E ⊓ K = Subgroup.zpowers z :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (Subgroup.mem_inf.2 ⟨hzE, hzK⟩))
      (by rw [Nat.card_zpowers, hzord, hAK])).symm
  have hzC : z ∉ autFixedInG E t := by
    intro hzC
    have hzcen : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hCcentK hzC) (k : G) k.2
    rw [hZ, Subgroup.mem_bot] at hzcen
    exact hz1 (congrArg Subtype.val hzcen)
  have hnormK : ∀ k ∈ K, (x : G) * k * (x : G)⁻¹ ∈ K := fun k hk => kLayer_conj_mem hlcb hk
  have ht2 : ∀ e : E, t (t e) = e := by
    intro e
    have h1 : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [htr.1, sq] at this
    exact DFunLike.congr_fun h1 e
  have htzmem : ((t ⟨z, hzE⟩ : E) : G) ∈ Subgroup.zpowers z := by
    rw [← hEKz]
    refine Subgroup.mem_inf.2 ⟨(t ⟨z, hzE⟩).2, ?_⟩
    rw [hteq]
    exact hnormK z hzK
  obtain ⟨s, hs⟩ := Subgroup.mem_zpowers_iff.mp htzmem
  have hts : t ⟨z, hzE⟩ = ⟨z, hzE⟩ ^ s := Subtype.ext (by rw [← hs]; rfl)
  have hss : (⟨z, hzE⟩ : E) ^ (s * s) = ⟨z, hzE⟩ := by
    have h1 := ht2 ⟨z, hzE⟩
    rw [hts, map_zpow, hts, ← zpow_mul] at h1
    exact h1
  have hss' : z ^ (s * s - 1) = 1 := by
    have h1 : z ^ (s * s) = z := congrArg Subtype.val hss
    rw [zpow_sub, h1, zpow_one, mul_inv_cancel]
  have hdvd : (p : ℤ) ∣ (s - 1) * (s + 1) := by
    have := (orderOf_dvd_iff_zpow_eq_one).2 hss'
    rw [hzord] at this
    have e : s * s - 1 = (s - 1) * (s + 1) := by ring
    rwa [e] at this
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have htz : ((t ⟨z, hzE⟩ : E) : G) = z⁻¹ := by
    rcases hpz.dvd_or_dvd hdvd with h1 | h1
    · exfalso
      apply hzC
      have h2 : z ^ (s - 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).1 (by rw [hzord]; exact h1)
      have h3 : z ^ s = z := by
        rw [zpow_sub, zpow_one, mul_inv_eq_one] at h2
        exact h2
      refine hfixiff.mpr ⟨hzE, ?_⟩
      rw [hts]
      exact Subtype.ext h3
    · have h2 : z ^ (s + 1) = 1 := (orderOf_dvd_iff_zpow_eq_one).1 (by rw [hzord]; exact h1)
      rw [← hs]
      rw [zpow_add, zpow_one, mul_eq_one_iff_eq_inv] at h2
      exact h2
  have hlz : (x : G) * z * (x : G)⁻¹ = z⁻¹ := by rw [← hteq ⟨z, hzE⟩]; exact htz
  have hlu : ∀ u ∈ autFixedInG E t, (x : G) * u * (x : G)⁻¹ = u := by
    intro u hu
    obtain ⟨hu', hu''⟩ := hfixiff.mp hu
    have := congrArg Subtype.val hu''
    rw [hteq] at this
    exact this
  have hdisjCz : Disjoint (autFixedInG E t) (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro y hyC hyz
    by_contra hy1
    have hzx : Subgroup.zpowers y = Subgroup.zpowers z :=
      zpowers_eq_of_mem_of_ne_one hp hzord hyz hy1
    have hzy : z ∈ Subgroup.zpowers y := hzx ▸ Subgroup.mem_zpowers z
    exact hzC (Subgroup.zpowers_le.2 hyC hzy)
  have hzcomm : ∀ y ∈ autFixedInG E t, ∀ y' ∈ Subgroup.zpowers z, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    exact (Commute.zpow_right (show Commute y z from hEcomm y (hCleE hy) z hzE) i).eq
  have hEeq : E = autFixedInG E t ⊔ Subgroup.zpowers z := by
    have hle : autFixedInG E t ⊔ Subgroup.zpowers z ≤ E :=
      sup_le hCleE (Subgroup.zpowers_le.2 hzE)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_sup_of_commute_disjoint hzcomm hdisjCz, Nat.card_zpowers, hzord, hCcard, hE3]
    exact (by ring : p ^ 3 = p ^ 2 * p).le
  have hdec : ∀ e ∈ E, ∃ u ∈ autFixedInG E t, ∃ i : ℤ, e = u * z ^ i := by
    intro e he
    rw [hEeq] at he
    obtain ⟨u, hu, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hzcomm he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨u, hu, i, rfl⟩
  have hlconj : ∀ (u : G) (i : ℤ), u ∈ autFixedInG E t →
      (x : G) * (u * z ^ i) * (x : G)⁻¹ = u * (z⁻¹) ^ i := by
    intro u i hu
    rw [show (x : G) * (u * z ^ i) * (x : G)⁻¹ = ((x : G) * u * (x : G)⁻¹) *
      ((x : G) * z * (x : G)⁻¹) ^ i by rw [conj_zpow]; group, hlu u hu, hlz]
  have hKmodel : StatedClassicalModel ↥K .PSL 2 2 g :=
    Equivariance.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  obtain ⟨w', hw'⟩ := exists_inv_conj_of_model hKmodel (⟨z, hzK⟩ : ↥K)
  set w : G := (w' : G) with hwdef
  have hwK : w ∈ K := w'.2
  have hwz : w * z * w⁻¹ = z⁻¹ := congrArg Subtype.val hw'
  have hwz' : w⁻¹ * z * w = z⁻¹ := by
    have h1 : z = w⁻¹ * z⁻¹ * w := by
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = w⁻¹ * z⁻¹ * w := by rw [hwz]
    have h2 := congrArg (fun y => y⁻¹) h1
    simp only [mul_inv_rev, inv_inv] at h2
    calc w⁻¹ * z * w = (w⁻¹ * z⁻¹ * w)⁻¹ := by group
      _ = z⁻¹ := by rw [← h1]
  have hcommw : ∀ (v : G), v ∈ K → ∀ u ∈ autFixedInG E t, v * u * v⁻¹ = u := by
    intro v hv u hu
    have := Subgroup.mem_centralizer_iff.mp (hCcentK hu) v hv
    rw [this]
    group
  have hconjE : ∀ v : G, v ∈ K → v * z * v⁻¹ = z⁻¹ → ∀ e ∈ E, v * e * v⁻¹ ∈ E := by
    intro v hv hvz e he
    obtain ⟨u, hu, i, rfl⟩ := hdec e he
    have h1 : v * (u * z ^ i) * v⁻¹ = u * (z⁻¹) ^ i := by
      rw [show v * (u * z ^ i) * v⁻¹ = (v * u * v⁻¹) * (v * z * v⁻¹) ^ i by
        rw [conj_zpow]; group, hcommw v hv u hu, hvz]
    rw [h1]
    exact E.mul_mem (hCleE hu) (E.zpow_mem (E.inv_mem hzE) i)
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := by
    refine mem_normalizer_of_conj_mem (fun y hy => hconjE w hwK hwz y hy) (fun y hy => ?_)
    have := hconjE w⁻¹ (K.inv_mem hwK) (by rw [inv_inv]; exact hwz') y hy
    simpa using this
  have hind : E.normalizerMonoidHom ⟨w, hwN⟩ = t := by
    refine DFunLike.ext _ _ fun e => Subtype.ext ?_
    obtain ⟨u, hu, i, he⟩ := hdec (e : G) e.2
    rw [hteq]
    show w * (e : G) * w⁻¹ = (x : G) * (e : G) * (x : G)⁻¹
    rw [he, hlconj u i hu]
    rw [show w * (u * z ^ i) * w⁻¹ = (w * u * w⁻¹) * (w * z * w⁻¹) ^ i by
      rw [conj_zpow]; group, hcommw w hwK u hu, hwz]
  have hmov : autMovedInG E t ≤ K := by
    rw [Sec12Three.autMovedInG_eq_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨e, rfl⟩
    obtain ⟨u, hu, i, he⟩ := hdec (e : G) e.2
    have hcz : Commute u z := hEcomm u (hCleE hu) z hzE
    have h1 : ((t e : E) : G) * (e : G)⁻¹ = z ^ (-2 * i) := by
      rw [hteq, he, hlconj u i hu, mul_inv_rev, ← zpow_neg, zpow_neg]
      have hc' : Commute u (z ^ i) := hcz.zpow_right i
      calc u * (z⁻¹) ^ i * ((z ^ i)⁻¹ * u⁻¹) = u * ((z⁻¹) ^ i * (z ^ i)⁻¹) * u⁻¹ := by
            simp only [mul_assoc]
        _ = u * z ^ (-2 * i) * u⁻¹ := by
            rw [inv_zpow', ← zpow_neg, ← zpow_add]
            congr 3
            ring
        _ = z ^ (-2 * i) := by
            have := (hcz.zpow_right (-2 * i)).eq
            rw [this]
            group
    show ((t e : E) : G) * (e : G)⁻¹ ∈ K
    rw [h1]
    exact K.zpow_mem hzK _
  have hBnorm : ∀ y ∈ L ⊓ Subgroup.centralizer (autFixedInG E t : Set G), ∀ k ∈ K,
      y * k * y⁻¹ ∈ K := by
    rintro y ⟨hyL, hyC⟩ k hk
    refine kLayer_conj_mem ⟨hyL, ?_⟩ hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hyC b hbC).symm
  have hBX : K ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_iff.mpr fun u hu =>
      (Subgroup.mem_centralizer_iff.mp (hCcentK hu) k hk).symm
  exact S13K.kfAt_of_block_gen h t hcC hKL hBX hBnorm hKmodel hzK hzE hz1 hdec hmov
    ⟨w, hwN, hwK, hind⟩

open CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.PartOne.KFU in
theorem exists_reflection_of_layer {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G}
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hE3 : Nat.card E = p ^ 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcL : c ∉ L)
    {b : G} (hbE : b ∈ E) (hbL : b ∈ L) (hb1 : b ≠ 1) {g : ℕ}
    (hAK : Nat.card ↥(E ⊓ kLayer L b) = p)
    (hmodel : StatedClassicalModel (↥(kLayer L b) ⧸ Subgroup.center ↥(kLayer L b)) .PSL 2 2 g)
    (hZ : Subgroup.center ↥(kLayer L b) = ⊥) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      ((t ⟨b, hbE⟩ : E) : G) = b ∧
      (E = autFixedInG E t ⊔ autMovedInG E t ∧ autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧
        Nat.card ↥(autMovedInG E t) = p) ∧
      KFAt p E g t ∧ kZero p E t = kLayer L b := by
  classical
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp3 := h.three_lt
  have hp2 : p ≠ 2 := by omega
  have hEel := h.E_elem
  set K := kLayer L b with hK
  have hKle : K ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _
  have hKL : K ≤ L := hKle.trans inf_le_left
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := hKle.trans inf_le_right
  have hKc : K ≤ Subgroup.centralizer ({c} : Set G) := hKL.trans hLc
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hbp : b ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) b hbE
  have hcp : c ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) c hcE
  have hbord : orderOf b = p := orderOf_eq_prime hbp hb1
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbc : b * c = c * b := hEcomm b hbE c hcE
  set C₀ : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c with hC₀
  have hdiscbc : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers c) := by
    rw [Subgroup.disjoint_def]
    intro y hyb hyc
    by_contra hy1
    have hzx : Subgroup.zpowers y = Subgroup.zpowers c :=
      zpowers_eq_of_mem_of_ne_one hp hcord hyc hy1
    have hcx : c ∈ Subgroup.zpowers y := hzx ▸ Subgroup.mem_zpowers c
    have hyL : y ∈ L := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyb
      exact Subgroup.zpow_mem _ hbL k
    exact hcL (Subgroup.zpowers_le.2 hyL hcx)
  have hC₀card : Nat.card ↥C₀ = p ^ 2 := by
    rw [hC₀, card_sup_of_commute_disjoint (fun y hy y' hy' => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
        exact ((Commute.zpow_zpow (show Commute b c from hbc) i j)).eq) hdiscbc,
      Nat.card_zpowers, Nat.card_zpowers, hbord, hcord]
    ring
  have hC₀E : C₀ ≤ E := sup_le (Subgroup.zpowers_le.2 hbE) (Subgroup.zpowers_le.2 hcE)
  have hC₀K : C₀ ≤ Subgroup.centralizer (K : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKb hk)
    · exact Subgroup.mem_centralizer_iff.2 fun k hk => Subgroup.mem_centralizer_singleton_iff.1 (hKc hk)
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' p (G := ↥(E ⊓ K)) (by rw [hAK])
  set z : G := (z0 : G) with hzdef
  have hzE : z ∈ E := (Subgroup.mem_inf.mp z0.2).1
  have hzK : z ∈ K := (Subgroup.mem_inf.mp z0.2).2
  have hzord : orderOf z = p := by
    rw [hzdef, Subgroup.orderOf_coe]
    exact hz0
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzord
    exact hp.one_lt.ne hzord
  have hzC₀ : z ∉ C₀ := by
    intro hzC
    have hzcen : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hC₀K hzC) (k : G) k.2
    rw [hZ, Subgroup.mem_bot] at hzcen
    exact hz1 (congrArg Subtype.val hzcen)
  have hdisjCz : Disjoint C₀ (Subgroup.zpowers z) := by
    rw [Subgroup.disjoint_def]
    intro y hyC hyz
    by_contra hy1
    have hzx : Subgroup.zpowers y = Subgroup.zpowers z :=
      zpowers_eq_of_mem_of_ne_one hp hzord hyz hy1
    have hzy : z ∈ Subgroup.zpowers y := hzx ▸ Subgroup.mem_zpowers z
    exact hzC₀ (Subgroup.zpowers_le.2 hyC hzy)
  have hzcomm : ∀ y ∈ C₀, ∀ y' ∈ Subgroup.zpowers z, y * y' = y' * y := by
    intro y hy y' hy'
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    exact (Commute.zpow_right (show Commute y z from hEcomm y (hC₀E hy) z hzE) i).eq
  have hEeq : E = C₀ ⊔ Subgroup.zpowers z := by
    have hle : C₀ ⊔ Subgroup.zpowers z ≤ E := sup_le hC₀E (Subgroup.zpowers_le.2 hzE)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_sup_of_commute_disjoint hzcomm hdisjCz, Nat.card_zpowers, hzord, hC₀card, hE3]
    exact (by ring : p ^ 3 = p ^ 2 * p).le
  have hdec : ∀ e ∈ E, ∃ u ∈ C₀, ∃ i : ℤ, e = u * z ^ i := by
    intro e he
    rw [hEeq] at he
    obtain ⟨u, hu, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hzcomm he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ⟨u, hu, i, rfl⟩
  have hKmodel : StatedClassicalModel ↥K .PSL 2 2 g :=
    Equivariance.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hmodel
  obtain ⟨w', hw'⟩ := exists_inv_conj_of_model hKmodel (⟨z, hzK⟩ : ↥K)
  set w : G := (w' : G) with hwdef
  have hwK : w ∈ K := w'.2
  have hwz : w * z * w⁻¹ = z⁻¹ := congrArg Subtype.val hw'
  have hwz' : w⁻¹ * z * w = z⁻¹ := by
    have h1 : z = w⁻¹ * z⁻¹ * w := by
      calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
        _ = w⁻¹ * z⁻¹ * w := by rw [hwz]
    calc w⁻¹ * z * w = (w⁻¹ * z⁻¹ * w)⁻¹ := by group
      _ = z⁻¹ := by rw [← h1]
  have hcommw : ∀ (v : G), v ∈ K → ∀ u ∈ C₀, v * u * v⁻¹ = u := by
    intro v hv u hu
    have := Subgroup.mem_centralizer_iff.mp (hC₀K hu) v hv
    rw [this]
    group
  have hconjE : ∀ v : G, v ∈ K → v * z * v⁻¹ = z⁻¹ → ∀ e ∈ E, v * e * v⁻¹ ∈ E := by
    intro v hv hvz e he
    obtain ⟨u, hu, i, rfl⟩ := hdec e he
    have h1 : v * (u * z ^ i) * v⁻¹ = u * (z⁻¹) ^ i := by
      rw [show v * (u * z ^ i) * v⁻¹ = (v * u * v⁻¹) * (v * z * v⁻¹) ^ i by
        rw [conj_zpow]; group, hcommw v hv u hu, hvz]
    rw [h1]
    exact E.mul_mem (hC₀E hu) (E.zpow_mem (E.inv_mem hzE) i)
  have hwN : w ∈ Subgroup.normalizer (E : Set G) := by
    refine mem_normalizer_of_conj_mem (fun y hy => hconjE w hwK hwz y hy) (fun y hy => ?_)
    have := hconjE w⁻¹ (K.inv_mem hwK) (by rw [inv_inv]; exact hwz') y hy
    simpa using this
  set t : MulAut E := E.normalizerMonoidHom ⟨w, hwN⟩ with ht
  have htw : ∀ e : E, ((t e : E) : G) = w * (e : G) * w⁻¹ := fun e => rfl
  have hwL : w ∈ L := hKL hwK
  have htL : t ∈ torusImage E L :=
    Subgroup.mem_map.mpr ⟨⟨w, hwN⟩, Subgroup.mem_subgroupOf.mpr hwL, rfl⟩
  have hmemE : ∀ (u : G) (i : ℤ), u ∈ C₀ → u * z ^ i ∈ E := fun u i hu =>
    E.mul_mem (hC₀E hu) (E.zpow_mem hzE i)
  have htf : ∀ (u : G) (i : ℤ) (hu : u ∈ C₀),
      t ⟨u * z ^ i, hmemE u i hu⟩ = ⟨u * z ^ (-i), hmemE u (-i) hu⟩ := by
    intro u i hu
    apply Subtype.ext
    rw [htw]
    show w * (u * z ^ i) * w⁻¹ = u * z ^ (-i)
    rw [show w * (u * z ^ i) * w⁻¹ = (w * u * w⁻¹) * (w * z * w⁻¹) ^ i by
      rw [conj_zpow]; group, hcommw w hwK u hu, hwz, inv_zpow, zpow_neg]
  have hb0 : b ∈ C₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hc0 : c ∈ C₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hbt : ((t ⟨b, hbE⟩ : E) : G) = b := by
    have := htf b 0 hb0
    simpa using congrArg Subtype.val this
  have hzt : ((t ⟨z, hzE⟩ : E) : G) = z⁻¹ := by
    have := htf 1 1 (Subgroup.one_mem _)
    simpa using congrArg Subtype.val this
  have hzsq : z ^ 2 ≠ 1 := by
    intro h2
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hzord] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have ht2 : t * t = 1 := by
    refine DFunLike.ext _ _ fun e => ?_
    obtain ⟨u, hu, i, he⟩ := hdec (e : G) e.2
    have he' : e = ⟨u * z ^ i, hmemE u i hu⟩ := Subtype.ext he
    rw [he', MulAut.mul_apply, htf u i hu, htf u (-i) hu]
    apply Subtype.ext
    simp
  have ht1 : t ≠ 1 := by
    intro h1
    have := congrArg (fun φ : MulAut E => ((φ ⟨z, hzE⟩ : E) : G)) h1
    simp only [hzt, MulAut.one_apply] at this
    apply hzsq
    have h2 : z⁻¹ * z = z * z := by rw [this]
    rw [inv_mul_cancel] at h2
    rw [sq]
    exact h2.symm
  have hord : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ht1
    rw [sq]
    exact ht2
  have hfix : autFixedInG E t = C₀ := by
    apply le_antisymm
    · intro e he
      obtain ⟨he', hfe⟩ := mem_autFixedInG_iff.mp he
      obtain ⟨u, hu, i, rfl⟩ := hdec e he'
      have h1 := htf u i hu
      rw [hfe] at h1
      have h2 : u * z ^ i = u * z ^ (-i) := congrArg Subtype.val h1
      have h3 : z ^ i = z ^ (-i) := mul_left_cancel h2
      have h4 : z ^ (2 * i) = 1 := by
        rw [two_mul, zpow_add]
        nth_rewrite 2 [h3]
        rw [← zpow_add, add_neg_cancel, zpow_zero]
      have h5 : (p : ℤ) ∣ 2 * i := by
        have := (orderOf_dvd_iff_zpow_eq_one (x := z) (i := 2 * i)).2 h4
        rwa [hzord] at this
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have h6 : (p : ℤ) ∣ i := by
        rcases hpz.dvd_or_dvd h5 with h7 | h7
        · exfalso
          have := Int.le_of_dvd (by norm_num) h7
          omega
        · exact h7
      have h8 : z ^ i = 1 := (orderOf_dvd_iff_zpow_eq_one).1 (by rw [hzord]; exact h6)
      rw [h8, mul_one]
      exact hu
    · intro u hu
      refine mem_autFixedInG_iff.mpr ⟨hC₀E hu, ?_⟩
      apply Subtype.ext
      rw [htw]
      exact hcommw w hwK u hu
  have hmoved : autMovedInG E t = Subgroup.zpowers z := by
    apply le_antisymm
    · rw [Sec12Three.autMovedInG_eq_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨e, rfl⟩
      obtain ⟨u, hu, i, he⟩ := hdec (e : G) e.2
      have hcz : Commute u z := hEcomm u (hC₀E hu) z hzE
      have he' : e = ⟨u * z ^ i, hmemE u i hu⟩ := Subtype.ext he
      have h1 : ((t e : E) : G) * (e : G)⁻¹ = z ^ (-2 * i) := by
        rw [he', htf u i hu]
        show u * z ^ (-i) * (u * z ^ i)⁻¹ = z ^ (-2 * i)
        rw [mul_inv_rev]
        have hc' : Commute u (z ^ i) := hcz.zpow_right i
        calc u * z ^ (-i) * ((z ^ i)⁻¹ * u⁻¹) = u * (z ^ (-i) * (z ^ i)⁻¹) * u⁻¹ := by
              simp only [mul_assoc]
          _ = u * z ^ (-2 * i) * u⁻¹ := by
              rw [← zpow_neg, ← zpow_add]
              congr 3
              ring
          _ = z ^ (-2 * i) := by
              have := (hcz.zpow_right (-2 * i)).eq
              rw [this]
              group
      show ((t e : E) : G) * (e : G)⁻¹ ∈ Subgroup.zpowers z
      rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _
    · have hmem : z ^ (-2 : ℤ) ∈ autMovedInG E t := by
        rw [Sec12Three.autMovedInG_eq_closure]
        refine Subgroup.subset_closure ⟨⟨z, hzE⟩, ?_⟩
        show ((t ⟨z, hzE⟩ : E) : G) * z⁻¹ = z ^ (-2 : ℤ)
        rw [hzt, show (-2 : ℤ) = -1 + -1 by norm_num, zpow_add, zpow_neg_one]
      have hne : z ^ (-2 : ℤ) ≠ 1 := by
        intro h1
        apply hzsq
        have : z ^ (2 : ℤ) = 1 := by
          have := congrArg (fun y => y⁻¹) h1
          simpa [zpow_neg] using this
        simpa using this
      have hzp : z ^ (-2 : ℤ) ∈ Subgroup.zpowers z := Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _
      have h1 : Subgroup.zpowers (z ^ (-2 : ℤ)) = Subgroup.zpowers z :=
        zpowers_eq_of_mem_of_ne_one hp hzord hzp hne
      rw [← h1]
      exact Subgroup.zpowers_le.2 hmem
  have hMcard : Nat.card ↥(autMovedInG E t) = p := by
    rw [hmoved, Nat.card_zpowers, hzord]
  have hsplit : E = autFixedInG E t ⊔ autMovedInG E t ∧
      autFixedInG E t ⊓ autMovedInG E t = ⊥ ∧ Nat.card ↥(autMovedInG E t) = p := by
    rw [hfix, hmoved]
    exact ⟨hEeq, disjoint_iff.mp hdisjCz, by rw [← hmoved]; exact hMcard⟩
  have htr : IsAutReflection p E t :=
    ⟨hord, by rw [← Sec12Three.natCard_autMovedInG]; exact hMcard⟩
  have hres := kfAt_of_layer h hE3 hLc hcL htr htL hsplit hbE hbL hb1 hbt hAK hmodel hZ
  exact ⟨t, htL, htr, hbt, hsplit, hres.1, hres.2⟩

end CFSG.RankThree.PartOne.KF132
