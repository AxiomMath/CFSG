module

import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenOuterPSUPSp
import CFSG.LieType.Ree.SuzukiSplitTorusCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExterior

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Open
open Matrix
open scoped Matrix
open CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)


private theorem mulAut_congr_symm_congr {P Q : Type} [Group P] [Group Q]
    (e : P ≃* Q) (α : MulAut P) : MulAut.congr e.symm (MulAut.congr e α) = α := by
  ext x
  simp [MulAut.congr_apply]

private theorem exists_prime_centralizer_not_le_normalizer_congr
    {P Q : Type} [Group P] [Group Q] (e : P ≃* Q) (α : MulAut P)
    (h : ∃ A : Subgroup P, A ≤ fixedSubgroup α ∧ (Nat.card A).Prime ∧ Nat.card A ≠ 2 ∧
      ∃ g ∈ centralizer (A : Set P), g ∉ normalizer ((fixedSubgroup α : Subgroup P) : Set P)) :
    ∃ A : Subgroup Q, A ≤ fixedSubgroup (MulAut.congr e α) ∧ (Nat.card A).Prime ∧
      Nat.card A ≠ 2 ∧
      ∃ g ∈ centralizer (A : Set Q),
        g ∉ normalizer ((fixedSubgroup (MulAut.congr e α) : Subgroup Q) : Set Q) := by
  obtain ⟨A, hA, hprime, hne, g, hgcent, hgnormP⟩ := h
  refine ⟨A.map e.toMonoidHom, ?_, ?_, ?_, e g, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    show MulAut.congr e α (e x) = e x
    have hconj : MulAut.congr e α (e x) = e (α x) := by
      rw [MulAut.congr_apply]
      simp
    rw [hconj]
    exact congrArg e (hA hx)
  · rwa [Subgroup.card_map_of_injective e.injective]
  · rwa [Subgroup.card_map_of_injective e.injective]
  · rw [Subgroup.mem_centralizer_iff] at hgcent ⊢
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    show e x * e g = e g * e x
    rw [← map_mul, ← map_mul, hgcent x hx]
  · intro hgnormQ
    rw [Subgroup.mem_normalizer_iff] at hgnormQ
    have hA' : fixedSubgroup (MulAut.congr e α) = (fixedSubgroup α).map e.toMonoidHom :=
      CFSG.ComponentClassification.ExcSelector.fixedSubgroup_congr e α
    have hgN : g ∈ normalizer ((fixedSubgroup α : Subgroup P) : Set P) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hx := hgnormQ (e x)
      rw [hA'] at hx
      have hmul : e g * e.toMonoidHom x * (e g)⁻¹ = e.toMonoidHom (g * x * g⁻¹) := by
        rw [map_mul, map_mul, map_inv]
        rfl
      rw [show e x = e.toMonoidHom x from rfl, hmul] at hx
      rw [Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective] at hx
      rw [Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective] at hx
      exact hx
    exact hgnormP hgN

private theorem exceptionalAut_pow_apply_proj {F : Type} [Field F] [Finite F] [CharP F 2]
    (j : ℕ) (g : StatedSp 2 F) :
    (exceptionalAut F ^ j) (proj 2 F g) = proj 2 F ((exceptionalSpAut F ^ j) g) := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, MulAut.mul_apply, exceptionalAut_proj, ih, pow_succ, MulAut.mul_apply]

private theorem suzukiInner_eq_conj {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hK : Nat.card F = 2 ^ (2 * m + 1)) (g : suzukiGroup m F) :
    suzukiInner F m hK g = MulAut.conj
      (((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩) := by
  rw [suzukiInner_apply, spInner_eq_conj]
  rfl

private theorem fixed_psi_mem_suzukiGroup {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hK : Nat.card F = 2 ^ (2 * m + 1))
    (g : suzukiGroup m F) :
    ((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩ ∈
      fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) := by
  change (exceptionalAut F ^ (2 * m + 1))
      (((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩) =
    ((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩
  have hfix : (minorAut F ^ (2 * m + 1)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩ =
      ⟨g, suzukiGroup_le_antiSp hK g.2⟩ :=
    (eta_apply_eq_iff (m := m) hK ⟨g, suzukiGroup_le_antiSp hK g.2⟩).mpr g.2
  calc (exceptionalAut F ^ (2 * m + 1))
        (((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩)
      = proj 2 F ((exceptionalSpAut F ^ (2 * m + 1))
          (antiSpEquiv F ⟨g, suzukiGroup_le_antiSp hK g.2⟩)) := by
        rw [show ((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩ =
          proj 2 F (antiSpEquiv F ⟨g, suzukiGroup_le_antiSp hK g.2⟩) from rfl,
          exceptionalAut_pow_apply_proj]
    _ = proj 2 F (antiSpEquiv F ((minorAut F ^ (2 * m + 1))
          ⟨g, suzukiGroup_le_antiSp hK g.2⟩)) := by
        rw [exceptionalSpAut_pow_apply]
    _ = proj 2 F (antiSpEquiv F ⟨g, suzukiGroup_le_antiSp hK g.2⟩) := by rw [hfix]
    _ = ((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩ := rfl

private theorem mem_fixedSubgroup_eta_iff {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hK : Nat.card F = 2 ^ (2 * m + 1))
    (x : StatedProj (StatedSp 2 F)) :
    x ∈ fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) ↔
      ∃ g : suzukiGroup m F,
        x = ((antiSpEquiv F).trans (projSpEquiv F)) ⟨g, suzukiGroup_le_antiSp hK g.2⟩ := by
  constructor
  · intro hx
    have hcj :=
      CFSG.ComponentClassification.CatLeafProof.conj_injective_statedProj_statedSp_charTwo
        (r := 2) (K := F)
    have hmap : (fixedSubgroup (exceptionalAut F ^ (2 * m + 1))).map MulAut.conj =
        (suzukiInner F m hK).range := by
      rw [CFSG.ComponentClassification.CatLeafProof.conj_map_fixedSubgroup_eq_inner hcj,
        inner_inf_centralizer_eta hK]
    have hmem : MulAut.conj x ∈ (suzukiInner F m hK).range := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem MulAut.conj hx
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, hcj ?_⟩
    rw [suzukiInner_eq_conj hK] at hg
    exact hg.symm
  · rintro ⟨g, rfl⟩
    exact fixed_psi_mem_suzukiGroup hK g

private theorem centralizer_fixedSubgroup_eta_eq_bot {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ}
    (hK : Nat.card F = 2 ^ (2 * m + 1))
    (hinf : inner (StatedProj (StatedSp 2 F)) ⊓
      Subgroup.zpowers (exceptionalAut F) = ⊥) :
    Subgroup.centralizer
      ((fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :
        Subgroup (StatedProj (StatedSp 2 F))) :
        Set (StatedProj (StatedSp 2 F))) = ⊥ := by
  apply le_antisymm
  · intro c hc
    have hcj :=
      CFSG.ComponentClassification.CatLeafProof.conj_injective_statedProj_statedSp_charTwo
        (r := 2) (K := F)
    have hcent : MulAut.conj c ∈
        Subgroup.centralizer ((suzukiInner F m hK).range :
          Set (MulAut (StatedProj (StatedSp 2 F)))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro φ hφ
      obtain ⟨g, rfl⟩ := hφ
      rw [suzukiInner_eq_conj hK, ← map_mul, ← map_mul]
      exact congrArg MulAut.conj
        ((Subgroup.mem_centralizer_iff.mp hc) _ (fixed_psi_mem_suzukiGroup hK g))
    rw [centralizer_range_suzukiInner hK] at hcent
    have hle : Subgroup.zpowers (exceptionalAut F ^ (2 * m + 1)) ≤
        Subgroup.zpowers (exceptionalAut F) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.npow_mem_zpowers (exceptionalAut F) (2 * m + 1)
    have hmem : MulAut.conj c ∈
        inner (StatedProj (StatedSp 2 F)) ⊓ Subgroup.zpowers (exceptionalAut F) :=
      ⟨⟨c, rfl⟩, hle hcent⟩
    rw [hinf] at hmem
    have hc1 : MulAut.conj c = 1 := Subgroup.mem_bot.mp hmem
    exact Subgroup.mem_bot.mpr (hcj (by rw [hc1, map_one]))
  · exact bot_le

private theorem normalizer_fixedSubgroup_eta_le {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ}
    (hcent : Subgroup.centralizer
      ((fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :
        Subgroup (StatedProj (StatedSp 2 F))) :
        Set (StatedProj (StatedSp 2 F))) = ⊥) :
    Subgroup.normalizer
      ((fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :
        Subgroup (StatedProj (StatedSp 2 F))) :
        Set (StatedProj (StatedSp 2 F))) ≤
      fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) := by
  intro g hg
  change (exceptionalAut F ^ (2 * m + 1)) g = g
  have hu : g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g) ∈
      Subgroup.centralizer
        ((fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :
          Subgroup (StatedProj (StatedSp 2 F))) :
          Set (StatedProj (StatedSp 2 F))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : (exceptionalAut F ^ (2 * m + 1)) d = d := hd
    have hgd : g * d * g⁻¹ ∈ fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :=
      (Subgroup.mem_normalizer_iff.mp hg d).mp hd
    have hgd' : (exceptionalAut F ^ (2 * m + 1)) (g * d * g⁻¹) = g * d * g⁻¹ := hgd
    have heq : (exceptionalAut F ^ (2 * m + 1)) g * d *
        ((exceptionalAut F ^ (2 * m + 1)) g)⁻¹ = g * d * g⁻¹ := by
      calc (exceptionalAut F ^ (2 * m + 1)) g * d *
            ((exceptionalAut F ^ (2 * m + 1)) g)⁻¹
          = (exceptionalAut F ^ (2 * m + 1)) (g * d * g⁻¹) := by
            rw [map_mul, map_mul, map_inv, hd']
        _ = g * d * g⁻¹ := hgd'
    have hcomm : (g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g)) * d *
        (g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g))⁻¹ = d := by
      calc (g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g)) * d *
            (g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g))⁻¹
          = g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g * d *
              ((exceptionalAut F ^ (2 * m + 1)) g)⁻¹) * g := by group
        _ = g⁻¹ * (g * d * g⁻¹) * g := by rw [heq]
        _ = d := by group
    exact (mul_inv_eq_iff_eq_mul.mp hcomm).symm
  rw [hcent] at hu
  have hu1 : g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g) = 1 := Subgroup.mem_bot.mp hu
  calc (exceptionalAut F ^ (2 * m + 1)) g =
        g * (g⁻¹ * ((exceptionalAut F ^ (2 * m + 1)) g)) := by group
    _ = g := by rw [hu1, mul_one]

private noncomputable def diagAntiSp {F : Type} [Field F] (lam : Fˣ) : antiSp F :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
    (Matrix.diagonal ![(lam : F), 1, 1, (↑(lam⁻¹) : F)])
    (by
      rw [Matrix.det_diagonal, Fin.prod_univ_four]
      simp),
   by
    rw [mem_antiSp]
    change (Matrix.diagonal ![(lam : F), 1, 1, (↑(lam⁻¹) : F)])ᵀ * minorJ F *
        Matrix.diagonal ![(lam : F), 1, 1, (↑(lam⁻¹) : F)] = minorJ F
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_four, minorJ_apply]⟩

private theorem diagAntiSp_apply_zero_zero {F : Type} [Field F] (lam : Fˣ) :
    glMat (diagAntiSp lam : GL (Fin 4) F) 0 0 = (lam : F) := rfl

private theorem diagAntiSp_apply_one_one {F : Type} [Field F] (lam : Fˣ) :
    glMat (diagAntiSp lam : GL (Fin 4) F) 1 1 = 1 := rfl

private theorem suzukiD_apply_zero_zero {F : Type} [Field F] {m : ℕ} (μ : Fˣ) :
    Blueprint.suzukiD m μ 0 0 = (μ : F) ^ (1 + 2 ^ m) := by
  rw [Blueprint.suzukiD, Matrix.diagonal_apply, if_pos rfl]
  simp only [Matrix.cons_val_zero]
  have hcast : (1 + (2 ^ m : ℤ)) = ((1 + 2 ^ m : ℕ) : ℤ) := by push_cast; ring
  rw [Units.val_zpow_eq_zpow_val, hcast, zpow_natCast]

private theorem suzukiD_apply_one_one {F : Type} [Field F] {m : ℕ} (μ : Fˣ) :
    Blueprint.suzukiD m μ 1 1 = (μ : F) ^ 2 ^ m := by
  rw [Blueprint.suzukiD, Matrix.diagonal_apply, if_pos rfl]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [Units.val_zpow_eq_zpow_val]
  have hcast : ((2 : ℤ) ^ m) = ((2 ^ m : ℕ) : ℤ) := (Nat.cast_pow 2 m).symm
  rw [hcast, zpow_natCast]

private theorem diagAntiSp_commute_suzukiD {F : Type} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hK : Nat.card F = 2 ^ (2 * m + 1)) (lam μ : Fˣ) :
    (diagAntiSp lam) * (⟨CFSG.LieType.Ree.suzukiDElt m F μ,
        suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩ : antiSp F) =
      (⟨CFSG.LieType.Ree.suzukiDElt m F μ,
        suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩ : antiSp F) *
        (diagAntiSp lam) := by
  apply Subtype.ext
  apply Units.ext
  change glMat (diagAntiSp lam : GL (Fin 4) F) *
      glMat ((⟨CFSG.LieType.Ree.suzukiDElt m F μ,
        suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩ : antiSp F) :
        GL (Fin 4) F) =
    glMat ((⟨CFSG.LieType.Ree.suzukiDElt m F μ,
        suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩ : antiSp F) :
        GL (Fin 4) F) * glMat (diagAntiSp lam : GL (Fin 4) F)
  rw [show glMat (diagAntiSp lam : GL (Fin 4) F) =
      Matrix.diagonal ![(lam : F), 1, 1, (↑(lam⁻¹) : F)] from rfl,
    show glMat ((⟨CFSG.LieType.Ree.suzukiDElt m F μ,
        suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩ : antiSp F) :
        GL (Fin 4) F) = Blueprint.suzukiD m μ from
      CFSG.LieType.Ree.coe_suzukiDElt m F μ]
  unfold Blueprint.suzukiD
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem diagAntiSp_eq_one_of_eq_suzukiDElt {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ}
    (hK : Nat.card F = 2 ^ (2 * m + 1)) (hm : 1 ≤ m) {lam μ : Fˣ}
    (h : (diagAntiSp lam : antiSp F) =
      ⟨CFSG.LieType.Ree.suzukiDElt m F μ,
        suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩) :
    lam = 1 := by
  have hmat : glMat (diagAntiSp lam : GL (Fin 4) F) = Blueprint.suzukiD m μ := by
    have h1 := congrArg (fun y : antiSp F => (y : GL (Fin 4) F)) h
    have h2 := congrArg (fun y : GL (Fin 4) F => (y : Matrix (Fin 4) (Fin 4) F)) h1
    exact h2.trans (CFSG.LieType.Ree.coe_suzukiDElt m F μ)
  have h11 := congrFun (congrFun hmat 1) 1
  have h00 := congrFun (congrFun hmat 0) 0
  rw [diagAntiSp_apply_one_one, suzukiD_apply_one_one] at h11
  rw [diagAntiSp_apply_zero_zero, suzukiD_apply_zero_zero] at h00
  have hμpow : μ ^ (2 ^ m) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h11.symm
  have hodd : Odd (Nat.card Fˣ) := CFSG.LieType.Ree.odd_card_units hK
  have hcop : Nat.Coprime (2 ^ m) (Nat.card Fˣ) :=
    (Nat.coprime_pow_left_iff (by omega : 0 < m) 2 (Nat.card Fˣ)).mpr
      (Odd.coprime_two_left hodd)
  have hμord : orderOf μ = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hμpow) (orderOf_dvd_natCard μ)
  have hμ1 : μ = 1 := orderOf_eq_one_iff.mp hμord
  have hlam1 : (lam : F) = 1 := by
    simpa [hμ1] using h00
  exact Units.ext hlam1

private theorem exists_prime_centralizer_not_le_normalizer_eta {F : Type} [Field F] [Finite F]
    [CharP F 2] {m : ℕ}
    (hK : Nat.card F = 2 ^ (2 * m + 1)) (hm : 1 ≤ m)
    (hinf : inner (StatedProj (StatedSp 2 F)) ⊓ Subgroup.zpowers (exceptionalAut F) = ⊥) :
    ∃ A : Subgroup (StatedProj (StatedSp 2 F)),
      A ≤ fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) ∧ (Nat.card A).Prime ∧
      Nat.card A ≠ 2 ∧
      ∃ g ∈ Subgroup.centralizer (A : Set (StatedProj (StatedSp 2 F))),
        g ∉ Subgroup.normalizer
          ((fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :
            Subgroup (StatedProj (StatedSp 2 F))) :
            Set (StatedProj (StatedSp 2 F))) := by
  classical
  obtain ⟨lam, hlamgen⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hlamord : orderOf lam = Nat.card Fˣ := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    exact hlamgen
  have hodd : Odd (Nat.card Fˣ) := CFSG.LieType.Ree.odd_card_units hK
  have hq7 : 7 ≤ Nat.card Fˣ := by
    rw [Nat.card_units, hK]
    have hp : 8 ≤ 2 ^ (2 * m + 1) := by
      simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 3 ≤ 2 * m + 1)
    omega
  have hqne1 : Nat.card Fˣ ≠ 1 := by omega
  obtain ⟨r, hrprime, hrdvd⟩ := Nat.exists_prime_and_dvd hqne1
  have hr2 : r ≠ 2 := by
    intro h
    subst h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hrdvd)
  let l0 : Fˣ := lam ^ (Nat.card Fˣ / r)
  have hl0ord : orderOf l0 = r := by
    have hpow : l0 = lam ^ (orderOf lam / r) := by
      rw [hlamord]
    rw [hpow]
    exact orderOf_pow_orderOf_div (orderOf_pos lam).ne' (by rwa [hlamord])
  have hl0ne : l0 ≠ 1 := by
    intro h
    have h1 : orderOf l0 = 1 := orderOf_eq_one_iff.mpr h
    rw [hl0ord] at h1
    exact hrprime.ne_one h1
  let t : suzukiGroup m F := CFSG.LieType.Ree.suzukiDElt m F l0
  have htord : orderOf t = r := by
    let D : Fˣ →* suzukiGroup m F :=
      { toFun := CFSG.LieType.Ree.suzukiDElt m F
        map_one' := CFSG.LieType.Ree.suzukiDElt_one
        map_mul' := fun a b => (CFSG.LieType.Ree.suzukiDElt_mul a b).symm }
    have hD : D l0 = t := rfl
    have h := orderOf_injective D (CFSG.LieType.Ree.suzukiDElt_injective hK) l0
    rw [hD, hl0ord] at h
    exact h
  let Psi : antiSp F ≃* StatedProj (StatedSp 2 F) :=
    (antiSpEquiv F).trans (projSpEquiv F)
  let x : StatedProj (StatedSp 2 F) := Psi ⟨t, suzukiGroup_le_antiSp hK t.2⟩
  have hxfix : x ∈ fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :=
    fixed_psi_mem_suzukiGroup hK t
  have hxord : orderOf x = r := by
    have h1 : orderOf x = orderOf (⟨t, suzukiGroup_le_antiSp hK t.2⟩ : antiSp F) :=
      orderOf_injective Psi.toMonoidHom Psi.injective _
    rw [h1]
    have h2 : orderOf (⟨t, suzukiGroup_le_antiSp hK t.2⟩ : antiSp F) = orderOf t :=
      (Subgroup.orderOf_coe (⟨t, suzukiGroup_le_antiSp hK t.2⟩ : antiSp F)).symm.trans
        (Subgroup.orderOf_coe t)
    rw [h2, htord]
  let g0 : antiSp F := diagAntiSp lam
  let g : StatedProj (StatedSp 2 F) := Psi g0
  have hcomm0 : g0 * ⟨t, suzukiGroup_le_antiSp hK t.2⟩ =
      ⟨t, suzukiGroup_le_antiSp hK t.2⟩ * g0 :=
    diagAntiSp_commute_suzukiD hK lam l0
  have hcommg : g * x = x * g := by
    change Psi g0 * Psi ⟨t, suzukiGroup_le_antiSp hK t.2⟩ =
      Psi ⟨t, suzukiGroup_le_antiSp hK t.2⟩ * Psi g0
    rw [← map_mul, ← map_mul, hcomm0]
  refine ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxfix, ?_, ?_, g, ?_, ?_⟩
  · rw [Nat.card_zpowers, hxord]
    exact hrprime
  · rw [Nat.card_zpowers, hxord]
    exact hr2
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_right (show Commute g x from hcommg) k).symm
  · intro hgnorm
    have hgfix : g ∈ fixedSubgroup (exceptionalAut F ^ (2 * m + 1)) :=
      normalizer_fixedSubgroup_eta_le
        (centralizer_fixedSubgroup_eta_eq_bot hK hinf) hgnorm
    obtain ⟨s, hs⟩ := (mem_fixedSubgroup_eta_iff hK g).mp hgfix
    have hanti : (⟨s, suzukiGroup_le_antiSp hK s.2⟩ : antiSp F) = g0 := by
      apply Psi.injective
      rw [← hs]
    have hcomm' : (⟨s, suzukiGroup_le_antiSp hK s.2⟩ : antiSp F) *
        ⟨t, suzukiGroup_le_antiSp hK t.2⟩ =
        ⟨t, suzukiGroup_le_antiSp hK t.2⟩ *
          ⟨s, suzukiGroup_le_antiSp hK s.2⟩ := by
      rw [hanti]
      exact hcomm0
    have hstGL : ((s : GL (Fin 4) F)) * (t : GL (Fin 4) F) =
        (t : GL (Fin 4) F) * ((s : GL (Fin 4) F)) := by
      have h2 := congrArg (fun y : antiSp F => (y : GL (Fin 4) F)) hcomm'
      simpa [Subgroup.coe_mul] using h2
    have hst : s * t = t * s := Subtype.ext (by simpa [Subgroup.coe_mul] using hstGL)
    have hsT : s ∈ CFSG.LieType.Ree.suzukiT m F := by
      rw [← CFSG.LieType.Ree.centralizer_suzukiDElt hK hl0ne]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hst
    obtain ⟨μ, hμ⟩ := CFSG.LieType.Ree.mem_suzukiT_iff.mp hsT
    have heq : (diagAntiSp lam : antiSp F) =
        ⟨CFSG.LieType.Ree.suzukiDElt m F μ,
          suzukiGroup_le_antiSp hK (CFSG.LieType.Ree.suzukiDElt m F μ).2⟩ := by
      refine (hanti.symm).trans ?_
      exact congrArg (fun y : suzukiGroup m F =>
        (⟨y, suzukiGroup_le_antiSp hK y.2⟩ : antiSp F)) hμ.symm
    have hlam1 : lam = 1 := diagAntiSp_eq_one_of_eq_suzukiDElt hK hm heq
    have hlamord1 : orderOf lam = 1 := orderOf_eq_one_iff.mpr hlam1
    rw [hlamord] at hlamord1
    omega


theorem exists_prime_centralizer_not_le_normalizer_psp
    {J : Type} [Group J] [Finite J] {n : ℕ} (hm : CFSG.Blueprint.LieModel J .PSp 2 2 n)
    (hn : Odd n) (β : MulAut J) (hβ : orderOf β = 2)
    (hβo : β ∉ (MulAut.conj : J →* MulAut J).range) :
    IsSimpleGroup ↥(fixedSubgroup β) ∧
      ∃ A : Subgroup J, A ≤ fixedSubgroup β ∧ (Nat.card A).Prime ∧ Nat.card A ≠ 2 ∧
        ∃ g ∈ centralizer (A : Set J), g ∉ normalizer ((fixedSubgroup β : Subgroup J) : Set J) := by
  obtain ⟨m, rfl⟩ := hn
  have hadm : StatedLieAdmissible .PSp 2 2 (2 * m + 1) := hm.admissible
  obtain ⟨F, hField, hFinite, hF, ⟨e⟩⟩ :=
    CFSG.ComponentClassification.CatLeafProof.nonempty_mulEquiv_psp_of_lieModel hadm hm
  have hf : 1 ≤ 2 * m + 1 := hadm.2.1
  have hchar : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two hf hF
  have hm1 : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    have h2 : 2 ^ (2 * m + 1) = 2 := by rw [hm0]; norm_num
    exact hadm.2.2.2 (by rw [h2])
  let G := StatedProj (StatedSp 2 F)
  let β' : MulAut G := MulAut.congr e β
  have hβ'ord : orderOf β' = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective β).trans hβ
  have hβ'o : β' ∉ inner G := by
    rw [CFSG.LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff e β]
    exact hβo
  have hβ'2 : β' * β' = 1 := by
    have h := pow_orderOf_eq_one β'
    rw [hβ'ord] at h
    simpa [pow_two] using h
  obtain ⟨-, -, -, -, ⟨γ, hγ⟩, hall⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_symplectic_two_exterior_square_automorphism
      (f := 2 * m + 1) (by omega) hF
  obtain ⟨-, hγord, hγE, huniq, hinf, hsup, hcyc, hcard, hEsup, hinf2, heven, hodd⟩ :=
    hall γ hγ
  have hγeq : γ = exceptionalAut F :=
    CFSG.ComponentClassification.UnbalancedCatalog.SpChain.eq_exceptionalAut hγ
  have hinf' : (MulAut.conj : G →* MulAut G).range ⊓
      Subgroup.zpowers (exceptionalAut F) = ⊥ := by
    rw [← hγeq]
    exact hinf
  obtain ⟨s, hs⟩ := hodd ⟨m, rfl⟩ β' hβ'ord hβ'o
  have hβ'eq : β' = spInner 2 F s * exceptionalAut F ^ (2 * m + 1) := by
    rw [hs, hγeq]
  have ha : (spInner 2 F s * exceptionalAut F ^ (2 * m + 1)) *
      (spInner 2 F s * exceptionalAut F ^ (2 * m + 1)) = 1 := by
    rw [← hβ'eq]
    exact hβ'2
  have hsimple : IsSimpleGroup
      ↥(fixedSubgroup (spInner 2 F s * exceptionalAut F ^ (2 * m + 1))) :=
    (CFSG.SeitzReduction.LinearPilot.psp_suzuki_fixed hm1 hF ha s rfl).1
  have hsimpleβ' : IsSimpleGroup ↥(fixedSubgroup β') := by
    rw [hβ'eq]
    exact hsimple
  have hsimpleβ : IsSimpleGroup ↥(fixedSubgroup β) :=
    (MulEquiv.isSimpleGroup_congr
      (CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv e β)).mpr hsimpleβ'
  refine ⟨hsimpleβ, ?_⟩
  have heta := exists_prime_centralizer_not_le_normalizer_eta hF hm1 hinf'
  obtain ⟨χ, hχinner, hχeq⟩ :=
    CFSG.ComponentClassification.OutcomeLocal.exists_inner_conj_eta hF ha
  have hβ'χ : β' = MulAut.congr χ (exceptionalAut F ^ (2 * m + 1)) := by
    rw [hβ'eq]
    exact hχeq.trans (MulEquiv.ext fun _ => rfl).symm
  have h1 := exists_prime_centralizer_not_le_normalizer_congr χ
    (exceptionalAut F ^ (2 * m + 1)) heta
  rw [← hβ'χ] at h1
  have h2 := exists_prime_centralizer_not_le_normalizer_congr (e := e.symm) β' h1
  have hsymm : MulAut.congr e.symm β' = β := mulAut_congr_symm_congr e β
  rw [hsymm] at h2
  exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
