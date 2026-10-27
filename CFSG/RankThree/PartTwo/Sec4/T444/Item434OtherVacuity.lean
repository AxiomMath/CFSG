module

public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
public import CFSG.LieType.SeitzGeneration.HeisSmallModel
public meta import CFSG.LieType.SeitzGeneration.HeisSmallModel
public import CFSG.Adapters.LinearFieldTransport
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration.HeisSmall (GF8)
open CFSG.Assembly.RankThreeEven (projSL projSU)

abbrev vacX : GF8 := GF8.mk 2

def vacA : Matrix (Fin 3) (Fin 3) GF8 := !![0, 1, 0; 1, vacX, 0; 0, 0, 1]

def vacB : Matrix (Fin 3) (Fin 3) GF8 := !![vacX, 1, 0; 1, 0, 0; 0, 0, 1]

theorem vacA_mul_vacB : vacA * vacB = 1 := by
  letI : DecidableEq GF8 := fun
    | ⟨a⟩, ⟨b⟩ =>
      if h : a = b then isTrue (congrArg GF8.mk h)
      else isFalse (fun heq => h (congrArg GF8.val heq))
  decide

theorem vacB_mul_vacA : vacB * vacA = 1 := by
  letI : DecidableEq GF8 := fun
    | ⟨a⟩, ⟨b⟩ =>
      if h : a = b then isTrue (congrArg GF8.mk h)
      else isFalse (fun heq => h (congrArg GF8.val heq))
  decide

theorem vacA_pow_nine : vacA ^ 9 = 1 := by
  letI : DecidableEq GF8 := fun
    | ⟨a⟩, ⟨b⟩ =>
      if h : a = b then isTrue (congrArg GF8.mk h)
      else isFalse (fun heq => h (congrArg GF8.val heq))
  have h3 : vacA ^ 3 =
      !![vacX, GF8.mk 5, 0; GF8.mk 5, GF8.mk 3, 0; 0, 0, 1] := by decide
  rw [show (9 : ℕ) = 3 * 3 by decide, pow_mul, h3]
  decide

theorem vacA_pow_three_apply : (vacA ^ 3) 0 0 = vacX ∧ (vacA ^ 3) 2 2 = 1 := by
  letI : DecidableEq GF8 := fun
    | ⟨a⟩, ⟨b⟩ =>
      if h : a = b then isTrue (congrArg GF8.mk h)
      else isFalse (fun heq => h (congrArg GF8.val heq))
  decide

theorem vacX_ne_one : vacX ≠ 1 := by
  letI : DecidableEq GF8 := fun
    | ⟨a⟩, ⟨b⟩ =>
      if h : a = b then isTrue (congrArg GF8.mk h)
      else isFalse (fun heq => h (congrArg GF8.val heq))
  decide

def vacU : GL (Fin 3) GF8 := ⟨vacA, vacB, vacA_mul_vacB, vacB_mul_vacA⟩

theorem vacU_pow_nine : vacU ^ 9 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact vacA_pow_nine)

noncomputable def vacE : GF8 ≃+* GaloisField 2 3 :=
  CFSG.ClassicalModels.finiteFieldEquivGaloisField GF8 2 3 (by norm_num)
    (by rw [Nat.card_eq_fintype_card, GF8.card_eq]; norm_num)

noncomputable def vacG : GL (Fin 3) (GaloisField 2 3) :=
  Matrix.GeneralLinearGroup.map vacE.toRingHom vacU

theorem vacG_pow_nine : vacG ^ 9 = 1 := by
  rw [vacG, ← map_pow, vacU_pow_nine, map_one]

theorem vacG_pow_three_apply :
    ((vacG ^ 3 : GL (Fin 3) (GaloisField 2 3)) : Matrix (Fin 3) (Fin 3) (GaloisField 2 3)) 0 0 =
        vacE vacX ∧
      ((vacG ^ 3 : GL (Fin 3) (GaloisField 2 3)) : Matrix (Fin 3) (Fin 3) (GaloisField 2 3)) 2 2 =
        1 := by
  have h3 : ((vacU ^ 3 : GL (Fin 3) GF8) : Matrix (Fin 3) (Fin 3) GF8) = vacA ^ 3 :=
    Units.val_pow_eq_pow_val _ _
  obtain ⟨h00, h22⟩ := vacA_pow_three_apply
  have hmap : ∀ i j, ((vacG ^ 3 : GL (Fin 3) (GaloisField 2 3)) : Matrix (Fin 3) (Fin 3)
      (GaloisField 2 3)) i j = vacE ((vacA ^ 3) i j) := by
    intro i j
    rw [vacG, ← map_pow, Matrix.GeneralLinearGroup.map_apply]
    rw [← h3]
    simp [Matrix.map_apply]
  exact ⟨by rw [hmap, h00], by rw [hmap, h22, map_one]⟩

theorem card_le_three_of_exp_three_of_nine {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hG : Nat.card G = 9 * m) (hm : ¬ 3 ∣ m) (g : G) (hg : orderOf g = 9)
    {E : Subgroup G} (hE : ∀ x ∈ E, x ^ 3 = 1) : Nat.card E ≤ 3 := by
  have hZ : Nat.card (Subgroup.zpowers g) = 3 ^ 2 := by
    rw [Nat.card_zpowers, hg]; norm_num
  have hZp : IsPGroup 3 (Subgroup.zpowers g) := IsPGroup.of_card hZ
  have hZidx : ¬ 3 ∣ (Subgroup.zpowers g).index := by
    have h := (Subgroup.zpowers g).card_mul_index
    rw [hZ, hG] at h
    have hidx : (Subgroup.zpowers g).index = m := by
      have h9 : 3 ^ 2 * (Subgroup.zpowers g).index = 3 ^ 2 * m := by
        rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h9
    rw [hidx]; exact hm
  set S : Sylow 3 G := hZp.toSylow hZidx with hSdef
  have hS : (S : Subgroup G) = Subgroup.zpowers g := rfl
  have hexp : Monoid.exponent E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by simpa using hE x x.2)
  have hEp : IsPGroup 3 E := IsPGroup.of_exponent_dvd_pow (n := 1) (by rwa [pow_one])
  obtain ⟨R, hR⟩ := hEp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G R S
  have hRS : (S : Subgroup G) = (R : Subgroup G).map (MulAut.conj c).toMonoidHom := by
    rw [← hc]; rfl
  have hR9 : Nat.card (R : Subgroup G) = 3 ^ 2 := by
    rw [← hZ, ← hS, hRS, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  have hEdvd : Nat.card E ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hR
    rwa [hR9] at this
  obtain ⟨i, hi, hEi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hEdvd
  interval_cases i
  · rw [hEi]; norm_num
  · rw [hEi]; norm_num
  ·
    exfalso
    have hER : E = (R : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hR (le_of_eq (by rw [hR9, hEi]))
    have hgS : g ∈ (S : Subgroup G) := by
      rw [hS]; exact Subgroup.mem_zpowers g
    rw [hRS] at hgS
    obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hgS
    have hy3 : y ^ 3 = 1 := hE y (by rw [hER]; exact hy)
    have hg3 : g ^ 3 = 1 := by
      rw [← hyg, ← map_pow, hy3, map_one]
    have h9 := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at h9
    norm_num at h9

noncomputable abbrev vacSc : (GaloisField 2 3)ˣ →* GL (Fin 3) (GaloisField 2 3) :=
  Matrix.GeneralLinearGroup.scalar (Fin 3)

theorem vacScalars_injective : Function.Injective vacSc := by
  rw [injective_iff_map_eq_one]
  intro c hc
  have h00 := congrArg
    (fun M : GL (Fin 3) (GaloisField 2 3) => (M : Matrix (Fin 3) (Fin 3) (GaloisField 2 3)) 0 0) hc
  simp [vacSc, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply] at h00
  exact Units.ext (by simpa using h00)

theorem vacCard_scalars :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3)) = 7 := by
  have hr : CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3) =
      vacSc.range := rfl
  rw [hr, ← Nat.card_congr (MonoidHom.ofInjective vacScalars_injective).toEquiv]
  first
    | (rw [Nat.card_units, GaloisField.card 2 3 (by norm_num)]) <;> norm_num
    | (rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
        GaloisField.card 2 3 (by norm_num)]) <;> norm_num
    | (simp [Nat.card_units, GaloisField.card])

theorem vacCard_GL : Nat.card (GL (Fin 3) (GaloisField 2 3)) = 115379712 := by
  haveI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]; norm_num
  rw [Matrix.card_GL_field, hc, Fin.prod_univ_three]
  norm_num

theorem vacCard_quot :
    Nat.card (GL (Fin 3) (GaloisField 2 3) ⧸
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3)) = 16482816 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3))
  rw [vacCard_GL, vacCard_scalars] at h
  omega

theorem vacScalar_apply (c : (GaloisField 2 3)ˣ) (i : Fin 3) :
    ((vacSc c : GL (Fin 3) (GaloisField 2 3)) : Matrix (Fin 3) (Fin 3) (GaloisField 2 3)) i i =
      c := by
  simp [vacSc, Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply]

noncomputable def vacP : GL (Fin 3) (GaloisField 2 3) ⧸
    CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3) :=
  QuotientGroup.mk' _ vacG

theorem vacP_pow_nine : vacP ^ 9 = 1 := by
  rw [vacP, ← map_pow, vacG_pow_nine, map_one]

theorem vacP_pow_three_ne_one : vacP ^ 3 ≠ 1 := by
  intro h
  rw [vacP, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  obtain ⟨c, hc⟩ := h
  have e00 := congrArg
    (fun M : GL (Fin 3) (GaloisField 2 3) => (M : Matrix (Fin 3) (Fin 3) (GaloisField 2 3)) 0 0) hc
  have e22 := congrArg
    (fun M : GL (Fin 3) (GaloisField 2 3) => (M : Matrix (Fin 3) (Fin 3) (GaloisField 2 3)) 2 2) hc
  rw [vacScalar_apply, vacG_pow_three_apply.1] at e00
  rw [vacScalar_apply, vacG_pow_three_apply.2] at e22
  apply vacX_ne_one
  apply vacE.injective
  rw [map_one, ← e00, e22]

theorem vacP_orderOf : orderOf vacP = 9 := by
  have hnot : ¬ vacP ^ (3 ^ 1) = 1 := by
    rw [pow_one]; exact vacP_pow_three_ne_one
  have hfin : vacP ^ (3 ^ (1 + 1)) = 1 := vacP_pow_nine
  exact orderOf_eq_prime_pow hnot hfin

theorem card_inf_linearAutGroup_eight_le_three
    {B : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 3)))}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card (B ⊓ linearAutGroup 3 (GaloisField 2 3) : Subgroup _) ≤ 3 := by
  have hNr := linearAutGroup_three_eq_range (K := GaloisField 2 3)
  set e : GL (Fin 3) (GaloisField 2 3) ⧸
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3) ≃*
      (conjAut 3 (GaloisField 2 3)).range :=
    (QuotientGroup.quotientMulEquivOfEq (ker_conjAut_three (K := GaloisField 2 3)).symm).trans
      (QuotientGroup.quotientKerEquivRange _)
  have hle : B ⊓ linearAutGroup 3 (GaloisField 2 3) ≤ (conjAut 3 (GaloisField 2 3)).range :=
    hNr ▸ inf_le_right
  set E : Subgroup (GL (Fin 3) (GaloisField 2 3) ⧸
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3)) :=
    ((B ⊓ linearAutGroup 3 (GaloisField 2 3)).subgroupOf (conjAut 3 (GaloisField 2 3)).range).map
      e.symm.toMonoidHom with hEdef
  have hcard : Nat.card E = Nat.card (B ⊓ linearAutGroup 3 (GaloisField 2 3) : Subgroup _) := by
    rw [hEdef, Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [← hcard]
  have hexp : ∀ x ∈ E, x ^ 3 = 1 := by
    rw [hEdef]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have h3 : x ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
    rw [h3, map_one]
  have hG : Nat.card (GL (Fin 3) (GaloisField 2 3) ⧸
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) (GaloisField 2 3)) = 9 * 1831424 :=
    vacCard_quot.trans (by norm_num)
  exact card_le_three_of_exp_three_of_nine hG (by norm_num) vacP vacP_orderOf hexp

theorem vacCard_le_nine_of_inf_le_three {K : Type} [Field K] [Finite K]
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (h2 : Nat.card (B ⊓ linearAutGroup 3 K : Subgroup _) ≤ 3) :
    Nat.card B ≤ 9 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, f, hp, hK⟩ := FiniteField.card' K
  have hcycK := (card_ringAut_and_isCyclic hp K (by rw [Nat.card_eq_fintype_card, hK])).2
  have hcyc : IsCyclic (fieldAut 3 K).range :=
    isCyclic_of_surjective (fieldAut 3 K).rangeRestrict (fieldAut 3 K).rangeRestrict_surjective
  have hCN : (fieldAut 3 K).range ≤
      Subgroup.normalizer
        ((linearAutGroup 3 K : Subgroup _) : Set (MulAut (projectiveSL 3 K))) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    rw [linearAutGroup_three_eq_range] at hx ⊢
    obtain ⟨A, rfl⟩ := hx
    refine ⟨Matrix.GeneralLinearGroup.map (σ : K →+* K) A, ?_⟩
    rw [fieldAut_mul_conjAut, mul_inv_cancel_right]
  have hBNC : ∀ b ∈ B, ∃ n ∈ linearAutGroup 3 K, ∃ c ∈ (fieldAut 3 K).range, b = n * c := by
    intro b hb
    by_cases hbN : b ∈ linearAutGroup 3 K
    · exact ⟨b, hbN, 1, one_mem _, (mul_one b).symm⟩
    · obtain ⟨σ, -, H, hH⟩ :=
        KFacts.linear_order_three_field_descent (by norm_num) b (hB.2 b hb) hbN
      refine ⟨conjAut 3 K H * conjAut 3 K (Matrix.GeneralLinearGroup.map (σ : K →+* K) H⁻¹),
        ?_, fieldAut 3 K σ, ⟨σ, rfl⟩, ?_⟩
      · rw [linearAutGroup_three_eq_range]
        exact ⟨_, map_mul _ _ _⟩
      · rw [hH, ← map_inv, mul_assoc, fieldAut_mul_conjAut, ← mul_assoc]
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  omega

theorem vacCard_le_nine_mulAut_eight (B : Subgroup (MulAut (projectiveSL 3 (GaloisField 2 3))))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 :=
  vacCard_le_nine_of_inf_le_three B hB (card_inf_linearAutGroup_eight_le_three hB)

theorem vacPRank_le_two_of_card_le {X : Type*} [Group X]
    (h : ∀ B : Subgroup X, CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9) :
    CFSG.pRank 3 X ≤ 2 := by
  refine csSup_le' ?_
  rintro r ⟨B, hB, hcard⟩
  have hB' : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨hB.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian (A := B) x hx⟩
  have h9 := h B hB'
  rw [hcard, show (9 : ℕ) = 3 ^ 2 by norm_num] at h9
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h9

theorem vacCard_le_nine_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ B : Subgroup (MulAut Y), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B ≤ 9)
    (B : Subgroup (MulAut X)) (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 9 := by
  have := h (B.map (MulAut.congr e).toMonoidHom) (isElemAbelian_map _ hB)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at this

theorem pRank_three_mulAut_projSL_three_eight_le_two :
    CFSG.pRank 3 (MulAut (projSL 3 (GaloisField 2 3))) ≤ 2 :=
  vacPRank_le_two_of_card_le
    (vacCard_le_nine_of_mulEquiv (projSLEquivProjectiveSL 3 (GaloisField 2 3))
      vacCard_le_nine_mulAut_eight)

end CFSG.RankThree.PartTwo.Sec4
