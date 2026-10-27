module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompLie2BigL2
public import CFSG.Quasithin.H13.L32ACSkPfG2
public import CFSG.LocalAnalysis.EvenBN.G2.Radicals
public import CFSG.LieType.Chevalley.E6GraphInvolutionForms
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB42G2FOff
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22G
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsG
public import CFSG.Quasithin.Vol2.Ch11StatementsH
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L32A.C.SkPf
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial

theorem xT_eq_uSL {K : Type} [Field K] (c : K) : xT c = uSL c :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j => by
    fin_cases i <;> fin_cases j <;> simp [coe_xT, coe_uSL]


section G2

variable {K : Type} [Field K]

theorem cbAt_g2 [CharP K 2] : CBAt (adjointGroup Tag.G2 K)
    ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) := by
  intro b _ hc
  have hbX : (b : ModGL Tag.G2 K) ∈ adjointGroup Tag.G2 K ⊓
      Subgroup.centralizer (CFSG.LocalAnalysis.EvenBN.G2.Model.X K : Set (ModGL Tag.G2 K)) := by
    refine ⟨b.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hxS : x ∈ posUnipotent Tag.G2 K := CFSG.LocalAnalysis.EvenBN.G2.Model.X_le_S hx
    have := hc ⟨x, posUnipotent_le_adjointGroup hxS⟩ (by rw [Subgroup.mem_subgroupOf]; exact hxS)
    exact (congrArg Subtype.val this).symm
  rw [CFSG.LocalAnalysis.EvenBN.G2.Model.adjointGroup_inf_centralizer_X] at hbX
  rw [Subgroup.mem_subgroupOf]
  exact CFSG.LocalAnalysis.EvenBN.G2.Model.X_le_S hbX

theorem invAt_g2 [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f) :
    InvAt (adjointGroup Tag.G2 K) ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)) := by
  intro z hz hz1 hzc
  have hzU : (z : ModGL Tag.G2 K) ∈ CFSG.LocalAnalysis.EvenBN.G2.Model.U K := by
    rw [← CFSG.LocalAnalysis.EvenBN.G2.Model.S_inf_centralizer_S]
    refine ⟨hz, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := hzc ⟨x, posUnipotent_le_adjointGroup hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx)
    exact (congrArg Subtype.val this).symm
  obtain ⟨c, hc⟩ := mem_rootSubgroup.mp hzU
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  let φ : SL2 K →* adjointGroup Tag.G2 K :=
    (rootSL2 Tag.G2 K CFSG.ComponentClassification.UnbalancedCatalog.g2c).codRestrict _
      (rootSL2_mem_adjointGroup _)
  have hφ : Function.Injective φ := fun A B hAB =>
    CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_injective_of_two h2 _
      (congrArg Subtype.val hAB)
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hz1
    apply Subtype.ext
    rw [← hc, pinnedX_zero]
    rfl
  have hφz : φ (xT c) = z := Subtype.ext (by
    change rootSL2 Tag.G2 K CFSG.ComponentClassification.UnbalancedCatalog.g2c (xT c) = z
    rw [xT_eq_uSL, CFSG.LieType.Chevalley.E6GraphInvolution.rootSL2_uSL_of_two h2, hc])
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_inv_of_hom hK hf φ hφ hc0
  rw [hφz] at hy2
  exact ⟨y, hy1, hy2, hy3⟩

end G2

theorem ordG2_ne {q : ℕ} (hq : 8 ≤ q) : CFSG.Open.ordG2 q ≠ 20160 := by
  intro h
  have a1 : 262144 ≤ q ^ 6 := by
    calc 262144 = 8 ^ 6 := by norm_num
      _ ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
  have a2 : 1 ≤ q ^ 6 - 1 := by omega
  have a3 : 64 ≤ q ^ 2 := by
    calc 64 = 8 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have a4 : 1 ≤ q ^ 2 - 1 := by omega
  unfold CFSG.Open.ordG2 at h
  have := Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a4
  omega

theorem false_of_autConf_g2 {M : Type} [Group M] {f : ℕ} (hf : 3 ≤ f)
    (hM : ChevalleyExceptionalModel M .G2 2 f) {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}
    (h : AutConf M ν Lb Pb) : False := by
  have hcard : Nat.card M = CFSG.Open.ordG2 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hM
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hM
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega) hK
  have h8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by omega
  have := finite_modGL (τ := Tag.G2) (K := K)
  let e' : M ≃* adjointGroup Tag.G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have h34 : ¬ IsPSL 3 2 2 (adjointGroup Tag.G2 K) := fun h34 => by
    have h1 := card_of_isPSL34 h34
    rw [← Nat.card_congr e'.toEquiv, hcard] at h1
    exact ordG2_ne h8 h1
  exact not_autConf_of_at isSylowTwoOf_g2U (n4At_g2 hK4) h34 cbAt_g2 (invAt_g2 hK hf) (h.map e')

end CFSG.Quasithin.H13.S126C
