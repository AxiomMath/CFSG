module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.Foundations
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LieType.Chevalley.LangRootArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec8.Statements
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec14.Res148

open Matrix CFSG.Assembly.RankThreeEven

section Uni

variable {F : Type} [Field F]

@[expose] def uniMat (a b c : F) : Matrix (Fin 3) (Fin 3) F := !![1, a, b; 0, 1, c; 0, 0, 1]

theorem uniMat_mul (a b c a' b' c' : F) :
    uniMat a b c * uniMat a' b' c' = uniMat (a + a') (b + b' + a * c') (c + c') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat, mul_apply, Fin.sum_univ_three] <;> ring

theorem uniMat_zero : uniMat (0 : F) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat]

@[expose] def uniGL (a b c : F) : GL (Fin 3) F :=
  ⟨uniMat a b c, uniMat (-a) (a * c - b) (-c),
    by rw [uniMat_mul, ← uniMat_zero]; congr 1 <;> ring,
    by rw [uniMat_mul, ← uniMat_zero]; congr 1 <;> ring⟩

theorem coe_uniGL (a b c : F) : ((uniGL a b c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
    uniMat a b c :=
  rfl

theorem uniGL_mul (a b c a' b' c' : F) :
    uniGL a b c * uniGL a' b' c' = uniGL (a + a') (b + b' + a * c') (c + c') :=
  Units.ext (uniMat_mul a b c a' b' c')

theorem uniGL_inv (a b c : F) : (uniGL a b c)⁻¹ = uniGL (-a) (a * c - b) (-c) := by
  rw [inv_eq_iff_mul_eq_one, uniGL_mul]
  apply Units.ext
  rw [Units.val_one, coe_uniGL, ← uniMat_zero]
  congr 1 <;> ring

theorem uniGL_injective : Function.Injective (fun v : F × F × F => uniGL v.1 v.2.1 v.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [coe_uniGL] at h'
  have h1 := congrFun (congrFun h' 0) 1
  have h2 := congrFun (congrFun h' 0) 2
  have h3 := congrFun (congrFun h' 1) 2
  simp only [uniMat, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two,
    empty_val', cons_val_fin_one, head_cons, tail_cons] at h1 h2 h3
  simp [h1, h2, h3]

@[expose] def uniSub : Subgroup (GL (Fin 3) F) where
  carrier := Set.range (fun v : F × F × F => uniGL v.1 v.2.1 v.2.2)
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, c⟩, rfl⟩ ⟨⟨a', b', c'⟩, rfl⟩
    exact ⟨⟨a + a', b + b' + a * c', c + c'⟩, (uniGL_mul a b c a' b' c').symm⟩
  one_mem' := ⟨⟨0, 0, 0⟩, Units.ext uniMat_zero⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, c⟩, rfl⟩
    exact ⟨⟨-a, a * c - b, -c⟩, (uniGL_inv a b c).symm⟩

theorem mem_uniSub_iff {g : GL (Fin 3) F} : g ∈ uniSub ↔ ∃ a b c : F, g = uniGL a b c := by
  constructor
  · rintro ⟨⟨a, b, c⟩, rfl⟩
    exact ⟨a, b, c, rfl⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨⟨a, b, c⟩, rfl⟩

theorem card_uniSub [Finite F] : Nat.card (uniSub : Subgroup (GL (Fin 3) F)) = Nat.card F ^ 3 := by
  have h : Nat.card (uniSub : Subgroup (GL (Fin 3) F)) = Nat.card (F × F × F) :=
    Nat.card_range_of_injective uniGL_injective
  rw [h, Nat.card_prod, Nat.card_prod]
  ring

theorem uniSub_le_ker_det : (uniSub : Subgroup (GL (Fin 3) F)) ≤
    (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker := by
  rintro _ ⟨⟨a, b, c⟩, rfl⟩
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one]
  change (uniMat a b c).det = 1
  simp [uniMat, Matrix.det_fin_three]

theorem eq_one_of_mem_uniSub_of_mk_eq_one {g : GL (Fin 3) F} (hg : g ∈ uniSub)
    (h1 : ProjGenLinGroup.mk g = 1) : g = 1 := by
  obtain ⟨a, b, c, rfl⟩ := mem_uniSub_iff.mp hg
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨μ, hμ⟩ := h1
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hμ
  simp only [GeneralLinearGroup.coe_scalar, coe_uniGL] at h'
  have h01 : a = 0 := by
    have := congrFun (congrFun h' 0) 1
    simpa [uniMat, Matrix.scalar_apply, diagonal_apply] using this.symm
  have h02 : b = 0 := by
    have := congrFun (congrFun h' 0) 2
    simpa [uniMat, Matrix.scalar_apply, diagonal_apply] using this.symm
  have h12 : c = 0 := by
    have := congrFun (congrFun h' 1) 2
    simpa [uniMat, Matrix.scalar_apply, diagonal_apply] using this.symm
  apply Units.ext
  rw [coe_uniGL, Units.val_one, h01, h02, h12, uniMat_zero]

@[expose] noncomputable def uniBar : Subgroup (ProjGenLinGroup (Fin 3) F) :=
  (uniSub : Subgroup (GL (Fin 3) F)).map ProjGenLinGroup.mk

theorem card_uniBar [Finite F] : Nat.card (uniBar : Subgroup (ProjGenLinGroup (Fin 3) F)) =
    Nat.card F ^ 3 := by
  rw [← card_uniSub]
  have hinj : Function.Injective
      ((ProjGenLinGroup.mk : GL (Fin 3) F →* ProjGenLinGroup (Fin 3) F).comp uniSub.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hu
    rw [Subgroup.mem_bot]
    exact Subtype.ext (eq_one_of_mem_uniSub_of_mk_eq_one u.2 hu)
  have hr : ((ProjGenLinGroup.mk : GL (Fin 3) F →* ProjGenLinGroup (Fin 3) F).comp
      uniSub.subtype).range = uniBar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  rw [← hr]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem uniBar_le_projSL : (uniBar : Subgroup (ProjGenLinGroup (Fin 3) F)) ≤ projSL 3 F :=
  Subgroup.map_mono uniSub_le_ker_det

end Uni

section Torus

variable {F : Type} [Field F]

theorem diagTau_mul_uniGL {τ : F} (hτ : τ ^ 3 = 1) (a b c : F) :
    Sec4.diagTau hτ * uniGL a b c * (Sec4.diagTau hτ)⁻¹ =
      uniGL (τ ^ 2 * a) (τ * b) (τ ^ 2 * c) := by
  apply Units.ext
  have hinv : (((Sec4.diagTau hτ)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![τ ^ 2, 0, 0; 0, τ, 0; 0, 0, 1] := rfl
  rw [Units.val_mul, Units.val_mul, hinv, Sec4.coe_diagTau, coe_uniGL, coe_uniGL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uniMat, mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hτ

theorem diagTau_mem_ker_det {τ : F} (hτ : τ ^ 3 = 1) :
    Sec4.diagTau hτ ∈ (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker := by
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, Units.val_one, Sec4.coe_diagTau]
  simp [Matrix.det_fin_three]
  rw [← pow_succ']
  exact hτ

theorem diagTau_pow_three {τ : F} (hτ : τ ^ 3 = 1) : Sec4.diagTau hτ ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Sec4.coe_diagTau, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination hτ | linear_combination (τ ^ 3 + 1) * hτ

theorem mk_diagTau_ne_one {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    ProjGenLinGroup.mk (Sec4.diagTau hτ) ≠ 1 := by
  intro h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨μ, hμ⟩ := h
  have h' := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) hμ
  simp only [GeneralLinearGroup.coe_scalar, Sec4.coe_diagTau] at h'
  have h00 : (μ : F) = τ := by
    have := congrFun (congrFun h' 0) 0
    simpa [Matrix.scalar_apply] using this
  have h22 : (μ : F) = 1 := by
    have := congrFun (congrFun h' 2) 2
    simpa [Matrix.scalar_apply] using this
  exact hτ1 (h00.symm.trans h22)

theorem mk_diagTau_mem_normalizer {τ : F} (hτ : τ ^ 3 = 1) :
    ProjGenLinGroup.mk (Sec4.diagTau hτ) ∈
      Subgroup.normalizer ((uniBar : Subgroup (ProjGenLinGroup (Fin 3) F)) : Set _) := by
  have key : ∀ g : GL (Fin 3) F, g ∈ uniSub →
      Sec4.diagTau hτ * g * (Sec4.diagTau hτ)⁻¹ ∈ uniSub := by
    intro g hg
    obtain ⟨a, b, c, rfl⟩ := mem_uniSub_iff.mp hg
    rw [diagTau_mul_uniGL]
    exact mem_uniSub_iff.mpr ⟨_, _, _, rfl⟩
  have key' : ∀ g : GL (Fin 3) F, g ∈ uniSub →
      (Sec4.diagTau hτ)⁻¹ * g * Sec4.diagTau hτ ∈ uniSub := by
    intro g hg
    set d := Sec4.diagTau hτ with hd
    have hdd : d * d = d⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ← pow_three', hd, diagTau_pow_three]
    have h1 := key _ (key g hg)
    have he : d⁻¹ * g * d = d * (d * g * d⁻¹) * d⁻¹ := by
      calc d⁻¹ * g * d = (d * d) * g * (d * d)⁻¹ := by rw [hdd, inv_inv]
        _ = d * (d * g * d⁻¹) * d⁻¹ := by group
    rw [he]
    exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨_, key g hg, by simp only [map_mul, map_inv]⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨_, key' g hg, ?_⟩
    rw [map_mul, map_mul, map_inv, hgx]
    group

end Torus

instance finite_projSL_res148 {F : Type} [Field F] [Finite F] (n : ℕ) :
    Finite ↥(projSL n F) := by
  have : Finite (ProjGenLinGroup (Fin n) F) := by
    unfold ProjGenLinGroup
    infer_instance
  infer_instance

section Seven

variable [Fact (Nat.Prime 7)]

local notation "L₃₇" => projSL 3 (GaloisField 7 1)

theorem card_galoisField_seven : Nat.card (GaloisField 7 1) = 7 := by
  rw [GaloisField.card 7 1 (by norm_num), pow_one]

theorem card_l37 : Nat.card (L₃₇) = 7 ^ 3 * 5472 := by
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 7 1)
  rw [card_galoisField_seven] at h
  norm_num at h
  omega

theorem two_pow_three_galoisField_seven : (2 : GaloisField 7 1) ^ 3 = 1 := by
  have h7 : ((7 : ℕ) : GaloisField 7 1) = 0 := CharP.cast_eq_zero _ 7
  have : (2 : GaloisField 7 1) ^ 3 = 1 + ((7 : ℕ) : GaloisField 7 1) := by push_cast; ring
  rw [this, h7, add_zero]

theorem two_ne_one_galoisField_seven : (2 : GaloisField 7 1) ≠ 1 := by
  intro h
  have : (1 : GaloisField 7 1) = 0 := by
    calc (1 : GaloisField 7 1) = 2 - 1 := by ring
      _ = 0 := by rw [h, sub_self]
  exact one_ne_zero this

@[expose] noncomputable def uniSeven : Subgroup L₃₇ :=
  (uniBar : Subgroup (ProjGenLinGroup (Fin 3) (GaloisField 7 1))).subgroupOf L₃₇

theorem card_uniSeven : Nat.card uniSeven = 7 ^ 3 := by
  rw [uniSeven, Nat.card_congr (Subgroup.subgroupOfEquivOfLe uniBar_le_projSL).toEquiv,
    card_uniBar, card_galoisField_seven]

theorem card_sylow_seven_l37 (S : Sylow 7 L₃₇) : Nat.card S = 7 ^ 3 := by
  have hp : IsPGroup 7 uniSeven := IsPGroup.of_card card_uniSeven
  obtain ⟨S₀, hS₀⟩ := hp.exists_le_sylow
  have hS₀card : Nat.card S₀ = 7 ^ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S₀.isPGroup'
    have hdvd : 7 ^ k ∣ 7 ^ 3 * 5472 := by
      rw [← hk, ← card_l37]
      exact Subgroup.card_subgroup_dvd_card _
    have hcop : Nat.Coprime (7 ^ k) 5472 := Nat.Coprime.pow_left _ (by norm_num)
    have hle : 7 ^ k ∣ 7 ^ 3 := hcop.dvd_of_dvd_mul_right hdvd
    have hge : 7 ^ 3 ≤ 7 ^ k := by
      rw [← card_uniSeven, ← hk]
      exact Subgroup.card_le_of_le hS₀
    rw [hk]
    exact le_antisymm (Nat.le_of_dvd (by norm_num) hle) hge
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity S₀, hS₀card]

theorem three_dvd_card_normalizer_sylow_seven_l37 (S : Sylow 7 L₃₇) :
    3 ∣ Nat.card (Subgroup.normalizer ((S : Subgroup L₃₇) : Set L₃₇)) := by
  have hτ := two_pow_three_galoisField_seven
  have hp : IsPGroup 7 uniSeven := IsPGroup.of_card card_uniSeven
  obtain ⟨S₀, hS₀⟩ := hp.exists_le_sylow
  have hS₀eq : (S₀ : Subgroup L₃₇) = uniSeven := by
    refine (Subgroup.eq_of_le_of_card_ge hS₀ ?_).symm
    rw [card_uniSeven, card_sylow_seven_l37]
  have hdL : ProjGenLinGroup.mk (Sec4.diagTau hτ) ∈ L₃₇ :=
    ⟨_, diagTau_mem_ker_det hτ, rfl⟩
  set d : L₃₇ := ⟨_, hdL⟩ with hd
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hd, ← map_pow, diagTau_pow_three, map_one, Subgroup.coe_one]
  have hd1 : d ≠ 1 := by
    intro h
    exact mk_diagTau_ne_one hτ two_ne_one_galoisField_seven (congrArg Subtype.val h)
  have hdord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdN : d ∈ Subgroup.normalizer ((S₀ : Subgroup L₃₇) : Set L₃₇) := by
    rw [hS₀eq, Subgroup.mem_normalizer_iff]
    intro x
    have hN := Subgroup.mem_normalizer_iff.mp (mk_diagTau_mem_normalizer hτ) (x : _)
    simp only [uniSeven, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L₃₇ S₀ S
  have hmem : g * d * g⁻¹ ∈ Subgroup.normalizer ((S : Subgroup L₃₇) : Set L₃₇) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.smul_def, MulAut.conj_inv_apply, MulAut.conj_inv_apply]
    have h := Subgroup.mem_normalizer_iff.mp hdN (g⁻¹ * x * g)
    convert h using 2
    group
  have hord : orderOf (g * d * g⁻¹) = 3 := by
    rw [show g * d * g⁻¹ = MulAut.conj g d from rfl, MulEquiv.orderOf_eq, hdord]
  have h := orderOf_dvd_natCard
    (⟨g * d * g⁻¹, hmem⟩ : Subgroup.normalizer ((S : Subgroup L₃₇) : Set L₃₇))
  rwa [Subgroup.orderOf_mk, hord] at h

end Seven

end CFSG.RankThree.PartTwo.Sec14.Res148
