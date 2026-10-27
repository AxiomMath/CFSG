module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieF
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Pt
public import CFSG.LocalAnalysis.EvenBN.U5.ModelA2N2Two
public import CFSG.LocalAnalysis.EvenBN.U5.ModelA2N2
public import CFSG.LocalAnalysis.EvenBN.U5.ModelParabolic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3V
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleOddCenterNormalAbsorption
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoReeF4
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Reduction
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieE
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYamStd
public import CFSG.Quasithin.Vol2.KGFactC31RuRef
public import CFSG.Quasithin.Vol2.KGFactC31RuRefBase
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.BRANCH.RankRee
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.N143.Weyl613Defs
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.RF4.FinalSec66
public import CFSG.RankThree.PartOne.S11c.Sec66TModels
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartTwo.Sec8.Steps
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Certificate7233Base

public section

namespace CFSG.Quasithin.Stroth

open scoped Pointwise
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.RankThree.PartOne.U5K.Hyp Matrix
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.EvenBN.U5
open CFSG.Quasithin.H13.Sec53F.Unit
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K]
  (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K)

private theorem normal_two_eq_bot_of_quasisimple {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.GorensteinWalter.IsQuasisimple Q)
    (hZ : Odd (Nat.card (Subgroup.center Q)))
    {R : Subgroup Q} (hR : R.Normal) (hR2 : IsPGroup 2 R) : R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.GorensteinWalter.normal_subgroup_le_center_or_eq_top hQ R hR with hle | htop
  · by_contra hne
    have hcard_ne : Nat.card R ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq R h)
    have hdvd : 2 ∣ Nat.card R := (hR2.card_eq_or_dvd).resolve_left hcard_ne
    exact hZ.not_two_dvd_nat (hdvd.trans (Subgroup.card_dvd_of_le hle))
  · subst htop
    have hQ2 : IsPGroup 2 Q := hR2.of_equiv Subgroup.topEquiv
    haveI : Nontrivial Q := hQ.1
    have hc : Nontrivial ↥(Subgroup.center Q) := hQ2.center_nontrivial
    have hc2 : IsPGroup 2 (Subgroup.center Q) :=
      IsPGroup.of_injective hQ2 (Subgroup.center Q).subtype Subtype.val_injective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hc2
    have hk0 : k = 0 := by
      have hodd : Odd (2 ^ k) := hk ▸ hZ
      exact Nat.eq_zero_of_not_pos fun hkpos => hodd.not_two_dvd_nat (by
        exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos))
    have hcard1 : Nat.card (Subgroup.center Q) = 1 := by rw [hk, hk0, pow_zero]
    exfalso
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc (Subgroup.eq_bot_of_card_eq _ hcard1)

private theorem a2_inf_n2 (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K) :
    A₂sub h ⊓ N₂sub h = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨hgA, hgN⟩ := Subgroup.mem_inf.1 hg
  have hgU : g ∈ hypUnitriangular h 2 1 := A₂sub_le_U hgA
  obtain ⟨hcol1, hcol2⟩ := (mem_N₂sub (h := h)).1 hgN
  obtain ⟨-, a1, a2, a3⟩ := mem_A₂sub.1 hgA
  obtain ⟨r1, r2, r3⟩ := A₂_rel hgA
  have e12 : mat g ιe₁ ιe₂ = 0 := by
    apply h.bar.injective
    have hb : h.bar (mat g ιe₁ ιe₂) = 0 := by
      rw [← r1]
      exact (hcol2 _).trans (one_apply_ne (by decide))
    simpa using hb
  have e1z : mat g ιe₁ ιz = 0 := by
    apply h.bar.injective
    have hb : h.bar (mat g ιe₁ ιz) = 0 := by
      rw [← r2]
      exact (hcol2 _).trans (one_apply_ne (by decide))
    simpa using hb
  have e1f2 : mat g ιe₁ ιf₂ = 0 := by
    apply h.bar.injective
    have hb : h.bar (mat g ιe₁ ιf₂) = 0 := by
      rw [← r3]
      exact (hcol2 _).trans (one_apply_ne (by decide))
    simpa using hb
  refine CFSG.LocalAnalysis.EvenBN.U5.eq_one_of_U_entries (h := h) hgU e12 e1z e1f2
    ((hcol2 _).trans (one_apply_ne (by decide))) a1 a3
    ((hcol2 _).trans (one_apply_ne (by decide))) a2
    ((hcol2 _).trans (one_apply_ne (by decide)))
    ((hcol2 _).trans (one_apply_ne (by decide)))

private theorem n2_quasisimple (hf : 2 ≤ f) :
    CFSG.GorensteinWalter.IsQuasisimple (N₂sub h) := by
  have hmq : (2 * 1 + 1, 2 ^ f) ≠ (3, 2) := by
    intro he
    have h2 : 2 ^ f = 2 := (Prod.mk.inj he).2
    have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  obtain ⟨hq, -⟩ := CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le (s := 1) (ε := 1) h
    (by norm_num) hmq
  have hqN : CFSG.Open.IsQuasisimple (N₂sub h) := hq.of_mulEquiv (N₂equiv h).symm
  refine ⟨?_, hqN.1, hqN.2⟩
  haveI : Nontrivial (↥(N₂sub h) ⧸ Subgroup.center ↥(N₂sub h)) := hqN.2.1
  exact (QuotientGroup.mk'_surjective (Subgroup.center ↥(N₂sub h))).nontrivial

private theorem n2_center_odd (hf : 2 ≤ f) :
    Odd (Nat.card (Subgroup.center ↥(N₂sub h))) := by
  letI : Finite K := h.finite
  letI : CharP K 2 := h.charP
  have hF : Nat.card K = (2 ^ f) ^ 2 := by
    rw [h.card, mul_comm, pow_mul]
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport h (r := 1) (ε := 1)
  have hSUiso : ↥(hypSU h 1 1) ≃* CFSG.Open.StatedSU 3 (2 ^ f) K :=
    CFSG.ClassicalGroups.UnitaryFlag.hypTransport h hR
  have hSUodd : Odd (Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) K))) :=
    (CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo.isQuasisimple_statedSU_three_odd_center hF hf).2
  have h1 : Nat.card (Subgroup.center ↥(N₂sub h)) =
      Nat.card (Subgroup.center ↥(hypSU h 1 1)) := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv (N₂equiv h)]
    exact Subgroup.card_map_of_injective (f := (N₂equiv h).toMonoidHom) (N₂equiv h).injective
  have h2 : Nat.card (Subgroup.center ↥(hypSU h 1 1)) =
      Nat.card (Subgroup.center (CFSG.Open.StatedSU 3 (2 ^ f) K)) := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv hSUiso]
    exact (Subgroup.card_map_of_injective (f := hSUiso.toMonoidHom) hSUiso.injective).symm
  rw [h1, h2]
  exact hSUodd

private theorem isub_conj_mem_n2 {t g : hypSU h 2 1} (ht : t ∈ Isub h)
    (hg : g ∈ N₂sub h) : t * g * t⁻¹ ∈ N₂sub h := by
  rw [mem_N₂sub] at hg ⊢
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [torus_conj_apply ht, hg.1 a]
    by_cases ha : a = ιe₁
    · subst ha
      rw [one_apply_eq, mul_one, mul_inv_cancel₀ (torus_ne_zero ht _)]
    · rw [one_apply_ne ha, mul_zero, zero_mul]
  · rw [torus_conj_apply ht, hg.2 a]
    by_cases ha : a = ιf₁
    · subst ha
      rw [one_apply_eq, mul_one, mul_inv_cancel₀ (torus_ne_zero ht _)]
    · rw [one_apply_ne ha, mul_zero, zero_mul]

private theorem isub_le_normalizer_n2 :
    Isub h ≤ Subgroup.normalizer (N₂sub h : Set (hypSU h 2 1)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · exact isub_conj_mem_n2 (h := h) ht
  · intro hg
    have h := isub_conj_mem_n2 (h := h) (inv_mem ht) hg
    have e : t⁻¹ * (t * g * t⁻¹) * (t⁻¹)⁻¹ = g := by group
    rwa [e] at h

private theorem a2_le_u5PtStab : A₂sub h ≤ u5PtStab h :=
  (A₂sub_le_U.trans (hypUnitriangular_le_hypBorel h)).trans
    (hypBorel_le_isoStabilizer h (d := 1) (by norm_num) (by norm_num))

private theorem i_le_u5PtStab : Isub h ≤ u5PtStab h :=
  (hypTorus_le_hypBorel h).trans
    (hypBorel_le_isoStabilizer h (d := 1) (by norm_num) (by norm_num))

theorem u5PtStab_eq_sup :
    u5PtStab h = (A₂sub h ⊔ N₂sub h) ⊔ Isub h := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a, ha, n, hn, i, hi, rfl⟩ :=
      exists_A₂sub_mul_N₂sub_mul_Isub (h := h) ((mem_u5PtStab_iff (h := h) g).1 hg)
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left
      (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hn)))
      (Subgroup.mem_sup_right hi)
  · exact sup_le (sup_le (a2_le_u5PtStab h) N₂sub_le_u5PtStab) (i_le_u5PtStab h)

private theorem n2_le_normalizer_a2 :
    N₂sub h ≤ Subgroup.normalizer (A₂sub h : Set (hypSU h 2 1)) :=
  le_sup_left.trans (N₂sub_sup_Isub_le_normalizer_A₂sub (h := h))

private theorem a2_le_normalizer_H :
    A₂sub h ≤ Subgroup.normalizer ((A₂sub h ⊔ N₂sub h : Subgroup (hypSU h 2 1)) :
      Set (hypSU h 2 1)) := by
  set H : Subgroup (hypSU h 2 1) := A₂sub h ⊔ N₂sub h with hHdef
  have hcoe : (H : Set (hypSU h 2 1)) = (A₂sub h : Set _) * (N₂sub h : Set _) :=
    by
    rw [hHdef]
    exact Subgroup.coe_mul_of_right_le_normalizer_left
      (G := hypSU h 2 1) (N := (A₂sub h : Subgroup _)) (H := (N₂sub h : Subgroup _))
      (n2_le_normalizer_a2 h)
  have key : ∀ a ∈ A₂sub h, ∀ x : hypSU h 2 1, x ∈ H → a * x * a⁻¹ ∈ H := by
    intro a ha x hx
    change x ∈ (H : Set (hypSU h 2 1)) at hx
    rw [hcoe, Set.mem_mul] at hx
    obtain ⟨a', ha', n', hn', rfl⟩ := hx
    have h1 : a * a' * a⁻¹ ∈ A₂sub h :=
      A₂sub h |>.mul_mem (A₂sub h |>.mul_mem ha ha') (A₂sub h |>.inv_mem ha)
    have h2 : n' * a⁻¹ * n'⁻¹ ∈ A₂sub h :=
      (Subgroup.mem_normalizer_iff.mp (n2_le_normalizer_a2 h hn') a⁻¹).mp
        (A₂sub h |>.inv_mem ha)
    have h3 : a * n' * a⁻¹ ∈ H := by
      have e : a * n' * a⁻¹ = (a * (n' * a⁻¹ * n'⁻¹)) * n' := by group
      rw [e]
      exact H.mul_mem (Subgroup.mem_sup_left (A₂sub h |>.mul_mem ha h2))
        (Subgroup.mem_sup_right hn')
    have e2 : a * (a' * n') * a⁻¹ = (a * a' * a⁻¹) * (a * n' * a⁻¹) := by group
    rw [e2]
    exact H.mul_mem (Subgroup.mem_sup_left h1) h3
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key a ha x
  · intro hx
    have h := key a⁻¹ (A₂sub h |>.inv_mem ha) (a * x * a⁻¹) hx
    simpa [mul_assoc] using h

private theorem i_le_normalizer_H :
    Isub h ≤ Subgroup.normalizer ((A₂sub h ⊔ N₂sub h : Subgroup (hypSU h 2 1)) :
      Set (hypSU h 2 1)) := by
  set H : Subgroup (hypSU h 2 1) := A₂sub h ⊔ N₂sub h with hHdef
  have hcoe : (H : Set (hypSU h 2 1)) = (A₂sub h : Set _) * (N₂sub h : Set _) :=
    by
    rw [hHdef]
    exact Subgroup.coe_mul_of_right_le_normalizer_left
      (G := hypSU h 2 1) (N := (A₂sub h : Subgroup _)) (H := (N₂sub h : Subgroup _))
      (n2_le_normalizer_a2 h)
  have hIA : Isub h ≤ Subgroup.normalizer (A₂sub h : Set (hypSU h 2 1)) :=
    le_sup_right.trans (N₂sub_sup_Isub_le_normalizer_A₂sub (h := h))
  have key : ∀ i ∈ Isub h, ∀ x : hypSU h 2 1, x ∈ H → i * x * i⁻¹ ∈ H := by
    intro i hi x hx
    change x ∈ (H : Set (hypSU h 2 1)) at hx
    rw [hcoe, Set.mem_mul] at hx
    obtain ⟨a, ha, n, hn, rfl⟩ := hx
    have hia : i * a * i⁻¹ ∈ A₂sub h :=
      (Subgroup.mem_normalizer_iff.mp (hIA hi) a).mp ha
    have hin : i * n * i⁻¹ ∈ N₂sub h :=
      (Subgroup.mem_normalizer_iff.mp (isub_le_normalizer_n2 h hi) n).mp hn
    have e : i * (a * n) * i⁻¹ = (i * a * i⁻¹) * (i * n * i⁻¹) := by group
    rw [e]
    exact H.mul_mem (Subgroup.mem_sup_left hia) (Subgroup.mem_sup_right hin)
  intro i hi
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key i hi x
  · intro hx
    have h := key i⁻¹ (Isub h |>.inv_mem hi) (i * x * i⁻¹) hx
    simpa [mul_assoc] using h

private theorem n2_le_normalizer_H :
    N₂sub h ≤ Subgroup.normalizer ((A₂sub h ⊔ N₂sub h : Subgroup (hypSU h 2 1)) :
      Set (hypSU h 2 1)) := by
  set H : Subgroup (hypSU h 2 1) := A₂sub h ⊔ N₂sub h with hHdef
  have hcoe : (H : Set (hypSU h 2 1)) = (A₂sub h : Set _) * (N₂sub h : Set _) :=
    by
    rw [hHdef]
    exact Subgroup.coe_mul_of_right_le_normalizer_left
      (G := hypSU h 2 1) (N := (A₂sub h : Subgroup _)) (H := (N₂sub h : Subgroup _))
      (n2_le_normalizer_a2 h)
  have key : ∀ n ∈ N₂sub h, ∀ x : hypSU h 2 1, x ∈ H → n * x * n⁻¹ ∈ H := by
    intro n hn x hx
    change x ∈ (H : Set (hypSU h 2 1)) at hx
    rw [hcoe, Set.mem_mul] at hx
    obtain ⟨a, ha, m, hm, rfl⟩ := hx
    have hna : n * a * n⁻¹ ∈ A₂sub h :=
      (Subgroup.mem_normalizer_iff.mp (n2_le_normalizer_a2 h hn) a).mp ha
    have hnm : n * m * n⁻¹ ∈ N₂sub h :=
      (N₂sub h).mul_mem ((N₂sub h).mul_mem hn hm) ((N₂sub h).inv_mem hn)
    have e : n * (a * m) * n⁻¹ = (n * a * n⁻¹) * (n * m * n⁻¹) := by group
    rw [e]
    exact H.mul_mem (Subgroup.mem_sup_left hna) (Subgroup.mem_sup_right hnm)
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key n hn x
  · intro hx
    have h := key n⁻¹ (N₂sub h |>.inv_mem hn) (n * x * n⁻¹) hx
    simpa [mul_assoc] using h

private theorem u5PtStab_le_normalizer_H :
    u5PtStab h ≤ Subgroup.normalizer ((A₂sub h ⊔ N₂sub h : Subgroup (hypSU h 2 1)) :
      Set (hypSU h 2 1)) := by
  rw [u5PtStab_eq_sup]
  exact sup_le (sup_le (a2_le_normalizer_H h) (n2_le_normalizer_H h)) (i_le_normalizer_H h)

theorem perfectCore_u5PtStab (hf : 2 ≤ f) :
    perfectCore (u5PtStab h) = A₂sub h ⊔ N₂sub h := by
  set H : Subgroup (hypSU h 2 1) := A₂sub h ⊔ N₂sub h with hHdef
  have hHP : H ≤ u5PtStab h :=
    sup_le (a2_le_u5PtStab h) N₂sub_le_u5PtStab
  have hHn : (H.subgroupOf (u5PtStab h)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHP).2
      (u5PtStab_le_normalizer_H h)
  have hsolv : Group.IsSolvable ↥(Isub h) :=
    isSolvable_of_comm fun a b => Subtype.ext (torus_comm (h := h) a.2 b.2)
  apply le_antisymm
  · have hP : u5PtStab h = H ⊔ Isub h := by
      rw [u5PtStab_eq_sup]
    exact perfectCore_le_of_sup_solvable hHP hHn hP hsolv
  · refine le_perfectCore_of_perfect hHP ?_
    rw [hHdef]
    exact commutator_A₂sub_sup_N₂sub (h := h) hf

section PCore

open scoped Pointwise

private theorem a2_isPGroup : IsPGroup 2 (A₂sub h) :=
  (CFSG.RankThree.CentralLiftU.isPGroup_hypUnitriangular (h := h) (r := 2) (ε := 1)
    (ℓ := 2) le_rfl).of_injective (Subgroup.inclusion (A₂sub_le_U (h := h)))
    (Subgroup.inclusion_injective _)

theorem pCoreOf_a2sub_sup_n2sub (hf : 2 ≤ f) :
    pCoreOf 2 (N₂sub h ⊔ A₂sub h) = A₂sub h := by
  set A : Subgroup (hypSU h 2 1) := A₂sub h with hAdef
  set N : Subgroup (hypSU h 2 1) := N₂sub h with hNdef
  set H : Subgroup (hypSU h 2 1) := N ⊔ A with hHdef
  have hNA : N ≤ Subgroup.normalizer (A : Set (hypSU h 2 1)) := n2_le_normalizer_a2 h
  have hAN' : A.subgroupOf N = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hmem : (x : hypSU h 2 1) ∈ A₂sub h ⊓ N₂sub h := ⟨hx, x.2⟩
    rw [a2_inf_n2 (h := h)] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hA_le : A ≤ pCoreOf 2 H := by
    refine CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer (hNK := le_sup_right) ?_ ?_
    · rw [hHdef]
      exact sup_le (by simpa [hAdef, hNdef] using hNA) (Subgroup.le_normalizer)
    · simpa [hAdef] using a2_isPGroup (h := h)
  haveI hAN_normal : (A.subgroupOf N).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNA
  have hH_le_normA : H ≤ Subgroup.normalizer (A : Set (hypSU h 2 1)) := by
    rw [hHdef]
    exact sup_le hNA (Subgroup.le_normalizer)
  haveI hAH_normal : (A.subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hH_le_normA
  have hNA' : (N ⊔ A) ≤ Subgroup.normalizer (A : Set (hypSU h 2 1)) :=
    sup_le hNA (Subgroup.le_normalizer)
  haveI hAN_normal2 : (A.subgroupOf (N ⊔ A)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNA'
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient N A hNA
  let eN : (↥H ⧸ A.subgroupOf H) ≃* ↥N :=
    (e.symm.trans (QuotientGroup.quotientMulEquivOfEq hAN')).trans QuotientGroup.quotientBot
  let q : ↥H →* ↥N := eN.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf H))
  have hq : Function.Surjective q :=
    eN.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = A.subgroupOf H := by
    ext x
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' (A.subgroupOf H) x = 1 := by
        apply eN.injective
        simpa [q] using hx
      exact (QuotientGroup.eq_one_iff x).mp (by simpa using h1)
    · intro hx
      rw [MonoidHom.mem_ker]
      have h1 : QuotientGroup.mk' (A.subgroupOf H) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr hx
      simp only [q, MonoidHom.comp_apply, h1, map_one]
  let R : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H
  have hRnorm : R.Normal := by
    have hEq : R = CFSG.Open.pCore 2 ↥H := by
      rw [show R = (pCoreOf 2 H).subgroupOf H from rfl]
      rw [pCoreOf, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hEq]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hR2 : IsPGroup 2 R :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).symm
  have hmap : R.map q = ⊥ :=
    normal_two_eq_bot_of_quasisimple (n2_quasisimple (h := h) hf) (n2_center_odd (h := h) hf)
      (hRnorm.map q hq) (hR2.map q)
  have hle : R ≤ q.ker := (Subgroup.map_eq_bot_iff R).mp hmap
  rw [hqker] at hle
  apply le_antisymm
  · intro x hx
    have hxH : x ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hx
    have hx' : (⟨x, hxH⟩ : ↥H) ∈ R := Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (hle hx')
  · exact hA_le

end PCore

theorem injOn_hypProj_a2sub_sup_n2sub :
    Function.Injective (fun x : ↥(A₂sub h ⊔ N₂sub h) => hypProj h 2 1 x) := by
  intro x y hxy
  change hypProj h 2 1 (x : hypSU h 2 1) = hypProj h 2 1 (y : hypSU h 2 1) at hxy
  apply Subtype.ext
  have hker : (x : hypSU h 2 1)⁻¹ * y ∈ (hypProj h 2 1).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hcol : ∀ z ∈ (A₂sub h ⊔ N₂sub h), z ∈ (hypProj h 2 1).ker → z = 1 := by
    intro z hz hzk
    rw [ker_hypProj] at hzk
    obtain ⟨c, hc0, hcm⟩ := exists_scalar_of_mem_hypScalars (h := h) hzk
    have hcoe : ((A₂sub h ⊔ N₂sub h : Subgroup (hypSU h 2 1)) : Set (hypSU h 2 1)) =
        (A₂sub h : Set _) * (N₂sub h : Set _) :=
      Subgroup.coe_mul_of_right_le_normalizer_left (N := A₂sub h) (H := N₂sub h)
        (n2_le_normalizer_a2 (h := h))
    change z ∈ ((A₂sub h ⊔ N₂sub h : Subgroup (hypSU h 2 1)) : Set (hypSU h 2 1)) at hz
    rw [hcoe, Set.mem_mul] at hz
    obtain ⟨a, ha, n, hn, rfl⟩ := hz
    have haU : a ∈ hypUnitriangular h 2 1 := A₂sub_le_U ha
    have hncol := (mem_N₂sub (h := h)).1 hn
    have hcol1 : ∀ b, mat (a * n) b ιe₁ =
        (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) b ιe₁ := by
      intro b
      rw [mat_mul, Matrix.mul_apply]
      have ha1 : mat a b ιe₁ = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) b ιe₁ :=
        U_col_e₁ (h := h) haU b
      have hn1 : ∀ d, mat n d ιe₁ =
          (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) d ιe₁ := hncol.1
      by_cases hb : b = ιe₁
      · subst hb
        rw [Finset.sum_eq_single ιe₁]
        · rw [ha1, hn1]; simp
        · intro d _ hd; rw [hn1, one_apply_ne hd, mul_zero]
        · intro hb; exact absurd (Finset.mem_univ ιe₁) hb
      · rw [Finset.sum_eq_zero]
        · rw [one_apply_ne hb]
        · intro d _
          by_cases hd : d = ιe₁
          · subst hd; rw [ha1, one_apply_ne hb, zero_mul]
          · rw [hn1, one_apply_ne hd, mul_zero]
    have hμ : c = 1 := by
      have h1 := hcol1 ιe₁
      rw [hcm ιe₁ ιe₁] at h1
      simpa using h1
    ext b d
    change mat (a * n) b d = mat (1 : hypSU h 2 1) b d
    rw [hcm b d, hμ]
    by_cases hbd : b = d
    · subst hbd
      rw [if_pos rfl]
      change (1 : K) = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) b b
      rw [one_apply_eq]
    · rw [if_neg hbd]
      change (0 : K) = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) b d
      rw [one_apply_ne hbd]
  have hx1 : (x : hypSU h 2 1) = y := by
    have hz := hcol ((x : hypSU h 2 1)⁻¹ * y) ?_ hker
    · exact inv_mul_eq_one.mp hz
    · exact (A₂sub h ⊔ N₂sub h).mul_mem ((A₂sub h ⊔ N₂sub h).inv_mem x.2) y.2
  exact hx1

private theorem pCoreOf_map_inj_of_injOn {G H : Type*} [Group G] [Group H]
    (f : G →* H) (X : Subgroup G)
    (hfinj : Function.Injective fun x : ↥X => f x) :
    pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := by
  have hinj : Function.Injective (f.subgroupMap X) := by
    intro a b hab
    apply hfinj
    exact congrArg Subtype.val hab
  let e : ↥X ≃* ↥(X.map f) :=
    MulEquiv.ofBijective (f.subgroupMap X) ⟨hinj, f.subgroupMap_surjective X⟩
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hy
    exact ⟨x, (CFSG.Quasithin.F112R.mem_pCoreOf_iff_of_mulEquiv e 2 ⟨x, hx⟩).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (CFSG.Quasithin.F112R.mem_pCoreOf_iff_of_mulEquiv e 2
      ⟨x, CFSG.LieType.BorelTits.pCoreOf_le 2 X hx⟩).mp hx

theorem pCoreOf_perfectCore_u5PtP (hf : 2 ≤ f) :
    pCoreOf 2 (perfectCore (u5PtP h)) = (A₂sub h).map (hypProj h 2 1) := by
  have hpc : perfectCore (u5PtP h) = (A₂sub h ⊔ N₂sub h).map (hypProj h 2 1) := by
    rw [u5PtP, projIsoStabilizer, ← map_perfectCore, perfectCore_u5PtStab (h := h) hf]
  rw [hpc]
  rw [pCoreOf_map_inj_of_injOn (hypProj h 2 1) (A₂sub h ⊔ N₂sub h)
    (injOn_hypProj_a2sub_sup_n2sub (h := h))]
  rw [show pCoreOf 2 (A₂sub h ⊔ N₂sub h) = pCoreOf 2 (N₂sub h ⊔ A₂sub h) by
    rw [sup_comm]]
  rw [pCoreOf_a2sub_sup_n2sub (h := h) hf]

section Special

theorem isSpecialPow_A2 (hf : 2 ≤ f) :
    IsSpecialPow 2 (2 ^ f) 3 ↥(A₂sub h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup (hypSU h 2 1) := A₂sub h with hAdef
  have hP : IsPGroup 2 ↥A := a2_isPGroup (h := h)
  haveI : Fact (IsPGroup 2 ↥A) := ⟨hP⟩
  have hcommAmb : ⁅A, A⁆ = ZPsub h := by
    apply le_antisymm
    · refine Subgroup.commutator_le.mpr ?_
      intro x hx y hy
      exact (elemAbMod_ZPsub_A₂sub (h := h)).2 (x : hypSU h 2 1) hx (y : hypSU h 2 1) hy
    · exact ZPsub_le_commutator_A₂sub (h := h)
  have hcenterAmb : (Subgroup.center ↥A).map A.subtype = ZPsub h := by
    rw [← CFSG.centerIn_eq_map_center]
    simpa [hAdef] using centerIn_A₂sub (h := h)
  have hcomm : commutator ↥A = Subgroup.center ↥A := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subtype_commutator, hcommAmb, hcenterAmb]
  have hsq : ∀ x : ↥A, x ^ 2 ∈ Subgroup.center ↥A := by
    intro x
    have hmem : A.subtype (x ^ 2) ∈ Subgroup.map A.subtype (Subgroup.center ↥A) := by
      rw [hcenterAmb]
      simpa [sq, Subgroup.coe_pow] using (elemAbMod_ZPsub_A₂sub (h := h)).1 (x : hypSU h 2 1) x.2
    exact (Subgroup.mem_map_iff_mem A.subtype_injective).mp hmem
  have hfrattini : frattini ↥A = Subgroup.center ↥A := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2)]
    apply le_antisymm
    · refine (Subgroup.closure_le (Subgroup.center ↥A)).mpr ?_
      intro x hx
      rcases hx with hx | ⟨y, rfl⟩
      · simpa [hcomm] using hx
      · exact hsq y
    · intro x hx
      rw [← hcomm] at hx
      exact Subgroup.subset_closure (Or.inl hx)
  have hcenter_sq : ∀ z ∈ Subgroup.center ↥A, z ^ 2 = 1 := by
    intro z hz
    have hzAmb : A.subtype z ∈ ZPsub h := by
      rw [← hcenterAmb]
      exact Subgroup.mem_map_of_mem _ hz
    have h := Vsub_sq (ZPsub_le_Vsub (h := h) hzAmb)
    exact Subtype.ext (by simpa [sq, Subgroup.coe_mul, Subgroup.coe_one] using h)
  refine ⟨⟨hP, Or.inr ⟨hcomm, hfrattini, hcenter_sq⟩⟩, ?_, ?_⟩
  · rw [card_A₂sub (h := h)]
  · calc Nat.card (Subgroup.center ↥A)
        = Nat.card ((Subgroup.center ↥A).map A.subtype) :=
          (Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective).symm
      _ = Nat.card (ZPsub h) := by rw [hcenterAmb]
      _ = 2 ^ f := card_ZPsub (h := h)

end Special

theorem isSpecialPow_A2_map (hf : 2 ≤ f) :
    IsSpecialPow 2 (2 ^ f) 3 ↥((A₂sub h).map (hypProj h 2 1)) := by
  let f : ↥(A₂sub h) →* ↥((A₂sub h).map (hypProj h 2 1)) :=
    (hypProj h 2 1).subgroupMap (A₂sub h)
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact CFSG.Quasithin.H13.F431.Un.hypProj_eq_of_mem_U
      (A₂sub_le_U a.2) (A₂sub_le_U b.2) (congrArg Subtype.val hab)
  let e : ↥(A₂sub h) ≃* ↥((A₂sub h).map (hypProj h 2 1)) :=
    MulEquiv.ofBijective f ⟨hinj, (hypProj h 2 1).subgroupMap_surjective (A₂sub h)⟩
  exact CFSG.Quasithin.IsSpecialPow.of_mulEquiv e (isSpecialPow_A2 (h := h) hf)

theorem isSpecialPow_pCoreOf_perfectCore_u5PtP (hf : 2 ≤ f) :
    IsSpecialPow 2 (2 ^ f) 3 ↥(pCoreOf 2 (perfectCore (u5PtP h))) := by
  rw [pCoreOf_perfectCore_u5PtP (h := h) hf]
  exact isSpecialPow_A2_map (h := h) hf

end CFSG.Quasithin.Stroth
