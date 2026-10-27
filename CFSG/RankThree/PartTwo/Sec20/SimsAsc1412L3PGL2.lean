module

public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import CFSG.Quasithin.Vol2.Ch12Sec6KGCompPSL2A
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DeterminantSquare
import CFSG.Walter.PSL2Facts.Odd

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

section Helpers

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open Matrix.ProjectiveSpecialLinearGroup (toPGL)
open scoped commutatorElement

private instance factPrimeFive1412 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance factPrimeSeven1412 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

private theorem exists_mulEquiv_pgl2_of_normal1412 {R : Type} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (N : Subgroup R) [N.Normal] (e : N ≃* PSL2 (ZMod p))
    (hC : Subgroup.centralizer (N : Set R) = ⊥) (hcard : Nat.card R = p * (p ^ 2 - 1)) :
    ∃ Φ : R ≃* PGL2 (ZMod p), ∀ n : N, Φ (n : R) = toPGL (e n) := by
  have hp : p.Prime := Fact.out
  have hFc : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hpodd, le_rfl, by rw [hFc, pow_one]⟩
  have h3 : 3 < Nat.card (ZMod p) := by rw [hFc]; omega
  have hinj : Function.Injective (pglAction (ZMod p)) :=
    CFSG.Quasithin.H13.S126C.pglAction_injective hF h3
  let ψ : R →* MulAut (PSL2 (ZMod p)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := N))
  have hex : ∀ r : R, ∃ g : PGL2 (ZMod p), pglAction (ZMod p) g = ψ r := fun r => by
    obtain ⟨g, σ, hgσ⟩ := CFSG.RankThree.PartTwo.KFacts.exists_pglAction_mul_psl2FieldAut (ψ r)
    refine ⟨g, ?_⟩
    rw [hgσ, CFSG.Quasithin.H13.S126C.ringAut_eq_one hp hFc σ, map_one, mul_one]
  choose f hf using hex
  let Φ₀ : R →* PGL2 (ZMod p) :=
    MonoidHom.mk' f fun r s => hinj (by rw [map_mul, hf, hf, hf, map_mul])
  have hΦ₀ : ∀ r, pglAction (ZMod p) (Φ₀ r) = ψ r := hf
  have hΦinj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : ψ r = 1 := by rw [← hΦ₀, hr, map_one]
    have hcen : r ∈ Subgroup.centralizer (N : Set R) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h2 := DFunLike.congr_fun h1 (e ⟨n, hn⟩)
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h2
      have h3 := congrArg Subtype.val (e.injective h2)
      rw [MulAut.conjNormal_apply] at h3
      calc n * r = (r * n * r⁻¹) * r := by rw [h3]
        _ = r * n := by group
    rw [hC] at hcen
    exact hcen
  haveI : Finite (PGL2 (ZMod p)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hcardP : Nat.card (PGL2 (ZMod p)) = p * (p ^ 2 - 1) := by
    rw [pgl2_card_formula, hFc]
  have hbij : Function.Bijective Φ₀ :=
    hΦinj.bijective_of_nat_card_le (by rw [hcardP, hcard])
  refine ⟨MulEquiv.ofBijective Φ₀ hbij, fun n => ?_⟩
  have hψn : ψ (n : R) = MulAut.conj (e n) := by
    change MulAut.congr e (MulAut.conjNormal (n : R)) = _
    rw [MulAut.conjNormal_val]
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  apply hinj
  rw [MulEquiv.ofBijective_apply, hΦ₀, hψn, pglAction_toPGL]

section GroupSetup

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}

private theorem commutator_le_self1412 (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  simp only [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private theorem conj_mem_commutator1412 {g ω : G} (hg : g ∈ H) (hω : ω ∈ ⁅H, H⁆) :
    g * ω * g⁻¹ ∈ ⁅H, H⁆ := by
  have h1 : ⁅g, ω⁆ ∈ ⁅H, ⁅H, H⁆⁆ := Subgroup.commutator_mem_commutator hg hω
  have h2 : ⁅g, ω⁆ ∈ ⁅H, H⁆ := Subgroup.commutator_mono le_rfl (commutator_le_self1412 H) h1
  have : g * ω * g⁻¹ = ⁅g, ω⁆ * ω := by simp only [commutatorElement_def]; group
  rw [this]
  exact mul_mem h2 hω

private theorem exists_mulEquiv_pgl2_of_commutator1412 (hp5 : 5 ≤ p)
    (e : ↥⁅H, H⁆ ≃* PSL2 (ZMod p))
    (hC : H ⊓ Subgroup.centralizer ((⁅H, H⁆ : Subgroup G) : Set G) = ⊥)
    (hcard : Nat.card H = p * (p ^ 2 - 1)) :
    ∃ Φ : ↥H ≃* PGL2 (ZMod p),
      ∀ ω : ↥⁅H, H⁆, Φ (Subgroup.inclusion (commutator_le_self1412 H) ω) = toPGL (e ω) := by
  set N : Subgroup ↥H := (⁅H, H⁆).subgroupOf H with hN
  haveI : N.Normal := ⟨fun n hn g => by
    rw [hN, Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_commutator1412 g.2 hn⟩
  let e' : N ≃* PSL2 (ZMod p) :=
    (Subgroup.subgroupOfEquivOfLe (commutator_le_self1412 H)).trans e
  have hCN : Subgroup.centralizer (N : Set ↥H) = ⊥ := by
    rw [eq_bot_iff]
    intro h hh
    rw [Subgroup.mem_centralizer_iff] at hh
    have hmem : (h : G) ∈ H ⊓ Subgroup.centralizer ((⁅H, H⁆ : Subgroup G) : Set G) :=
      ⟨h.2, Subgroup.mem_centralizer_iff.2 fun ω hω =>
        congrArg Subtype.val (hh ⟨ω, commutator_le_self1412 H hω⟩ hω)⟩
    rw [hC, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_pgl2_of_normal1412 hp5 N e' hCN hcard
  refine ⟨Φ, fun ω => ?_⟩
  have h1 := hΦ ((Subgroup.subgroupOfEquivOfLe (commutator_le_self1412 H)).symm ω)
  have h2 : ((Subgroup.subgroupOfEquivOfLe (commutator_le_self1412 H)).symm ω : ↥H) =
      Subgroup.inclusion (commutator_le_self1412 H) ω := rfl
  have h3 : e' ((Subgroup.subgroupOfEquivOfLe (commutator_le_self1412 H)).symm ω) = e ω := by
    simp only [e', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rw [h2, h3] at h1
  exact h1

section Engine

private theorem mem_commutator_iff_Φ_mem_range1412
    (e : ↥⁅H, H⁆ ≃* PSL2 (ZMod p)) (Φ : ↥H ≃* PGL2 (ZMod p))
    (hΦ : ∀ ω : ↥⁅H, H⁆, Φ (Subgroup.inclusion (commutator_le_self1412 H) ω) = toPGL (e ω))
    (x : ↥H) : (x : G) ∈ ⁅H, H⁆ ↔ Φ x ∈ (toPGL : PSL2 (ZMod p) →* PGL2 (ZMod p)).range := by
  constructor
  · intro hx
    refine ⟨e ⟨x, hx⟩, ?_⟩
    rw [← hΦ ⟨x, hx⟩]
    rfl
  · rintro ⟨y, hy⟩
    have h1 : Φ (Subgroup.inclusion (commutator_le_self1412 H) (e.symm y)) = Φ x := by
      rw [hΦ, MulEquiv.apply_symm_apply, hy]
    have h2 := Φ.injective h1
    rw [← h2]
    exact (e.symm y).2

private theorem exists_word_of_conj_inv1412
    (e : ↥⁅H, H⁆ ≃* PSL2 (ZMod p)) (Φ : ↥H ≃* PGL2 (ZMod p))
    (hΦ : ∀ ω : ↥⁅H, H⁆, Φ (Subgroup.inclusion (commutator_le_self1412 H) ω) = toPGL (e ω))
    {x : G} (hxH : x ∈ H) (hx2 : x * x = 1) {y : PSL2 (ZMod p)} (hy : Odd (orderOf y))
    (hxy : Φ ⟨x, hxH⟩ * toPGL y * (Φ ⟨x, hxH⟩)⁻¹ = (toPGL y)⁻¹) :
    ∃ g ∈ H, orderOf (x * g * x * g⁻¹) = orderOf y := by
  set ω : ↥⁅H, H⁆ := e.symm y with hω
  have h1 : (⟨x, hxH⟩ : ↥H) * Subgroup.inclusion (commutator_le_self1412 H) ω *
      (⟨x, hxH⟩ : ↥H)⁻¹ = (Subgroup.inclusion (commutator_le_self1412 H) ω)⁻¹ := by
    apply Φ.injective
    rw [map_mul, map_mul, map_inv, map_inv, hΦ ω, hω, MulEquiv.apply_symm_apply, hxy]
  have h1G : x * (ω : G) * x⁻¹ = (ω : G)⁻¹ := congrArg Subtype.val h1
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  rw [hxinv] at h1G
  refine ⟨(ω : G), commutator_le_self1412 H ω.2, ?_⟩
  have h2 : x * (ω : G) * x * (ω : G)⁻¹ = ((ω : G) ^ 2)⁻¹ := by
    rw [h1G, pow_two, mul_inv_rev]
  have hord : orderOf (ω : G) = orderOf y := by
    rw [Subgroup.orderOf_coe, hω, MulEquiv.orderOf_eq]
  rw [h2, orderOf_inv, Nat.Coprime.orderOf_pow, hord]
  rw [hord]
  exact Nat.coprime_two_right.2 hy

end Engine

end GroupSetup

section PGLData

variable {F : Type} [Field F]

private def dmGL1412 (F : Type) [Field F] : GL (Fin 2) F :=
  ⟨!![-1, 0; 0, 1], !![-1, 0; 0, 1], by simp [Matrix.mul_fin_two, Matrix.one_fin_two],
    by simp [Matrix.mul_fin_two, Matrix.one_fin_two]⟩

private theorem dmGL1412_mul_self : dmGL1412 F * dmGL1412 F = 1 :=
  Units.ext (by simp [dmGL1412, Matrix.mul_fin_two, Matrix.one_fin_two])

private theorem dmGL1412_inv : (dmGL1412 F)⁻¹ = dmGL1412 F :=
  inv_eq_of_mul_eq_one_right dmGL1412_mul_self

private theorem coe_transvection_zero_one1412 (t : F) :
    ((Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t :
      Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply]

private theorem dmGL1412_conj_transvection (t : F) :
    dmGL1412 F * Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t) * (dmGL1412 F)⁻¹ =
      Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (-t)) := by
  rw [dmGL1412_inv]
  refine Units.ext ?_
  simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    coe_transvection_zero_one1412]
  change !![-1, 0; 0, 1] * !![1, t; 0, 1] * !![-1, 0; 0, 1] = !![1, -t; 0, 1]
  simp [Matrix.mul_fin_two]

private def wPGL1412 (F : Type) [Field F] : PGL2 F := Matrix.ProjGenLinGroup.mk (dmGL1412 F)

private def uPSL1412 (F : Type) [Field F] (t : F) : PSL2 F :=
  QuotientGroup.mk (Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t)

private theorem uPSL1412_inv (t : F) : (uPSL1412 F t)⁻¹ = uPSL1412 F (-t) := by
  unfold uPSL1412
  rw [← QuotientGroup.mk_inv, Matrix.SpecialLinearGroup.transvection_inv]

private theorem wPGL1412_conj_uPSL1412 (t : F) :
    wPGL1412 F * toPGL (uPSL1412 F t) * (wPGL1412 F)⁻¹ = (toPGL (uPSL1412 F t))⁻¹ := by
  rw [← map_inv, uPSL1412_inv]
  unfold wPGL1412 uPSL1412
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk, Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  change Matrix.ProjGenLinGroup.mk (dmGL1412 F) * Matrix.ProjGenLinGroup.mk _ *
    (Matrix.ProjGenLinGroup.mk (dmGL1412 F))⁻¹ = Matrix.ProjGenLinGroup.mk _
  rw [← map_inv, ← map_mul, ← map_mul, dmGL1412_conj_transvection]

private theorem isInvolution_wPGL1412 (h2 : (2 : F) ≠ 0) :
    CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (wPGL1412 F) := by
  refine ⟨?_, ?_⟩
  · intro h1
    unfold wPGL1412 at h1
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨u, hu⟩ := h1
    have h00 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hu
    have h11 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 1 1) hu
    simp [dmGL1412, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h00 h11
    have h3 : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := congrArg Units.val (h00.symm.trans h11)
    simp only [Units.val_neg, Units.val_one] at h3
    exact h2 (by linear_combination -h3)
  · unfold wPGL1412
    rw [sq, ← map_mul, dmGL1412_mul_self, map_one]

private theorem val_det_dmGL1412 : (((dmGL1412 F).det : Fˣ) : F) = -1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  simp [dmGL1412, Matrix.det_fin_two]

private theorem wPGL1412_mem_range_iff :
    wPGL1412 F ∈ (toPGL : PSL2 F →* PGL2 F).range ↔ IsSquare (-1 : F) := by
  unfold wPGL1412
  rw [pgl2_mk_mem_psl2_range_iff_det_isSquare, val_det_dmGL1412]

end PGLData

section Fusion

private theorem exists_inv_order_eq_of_isConj_wPGL1412 {p : ℕ} [Fact p.Prime] {g : PGL2 (ZMod p)}
    (hg : IsConj (wPGL1412 (ZMod p)) g) :
    ∃ y : PSL2 (ZMod p), orderOf y = p ∧ g * toPGL y * g⁻¹ = (toPGL y)⁻¹ := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hg
  have hJn : (toPGL : PSL2 (ZMod p) →* PGL2 (ZMod p)).range.Normal :=
    pglPSLRange_normal (ZMod p)
  have hord : orderOf (uPSL1412 (ZMod p) 1) = p :=
    CFSG.Quasithin.H13.S126C.orderOf_mk_transvection (by decide) one_ne_zero
  obtain ⟨y, hy⟩ : a * toPGL (uPSL1412 (ZMod p) 1) * a⁻¹ ∈
      (toPGL : PSL2 (ZMod p) →* PGL2 (ZMod p)).range := hJn.conj_mem _ ⟨_, rfl⟩ a
  refine ⟨y, ?_, ?_⟩
  · calc orderOf y = orderOf (toPGL y) :=
          (orderOf_injective toPGL Matrix.ProjectiveSpecialLinearGroup.toPGL_injective y).symm
      _ = orderOf (a * toPGL (uPSL1412 (ZMod p) 1) * a⁻¹) := by rw [hy]
      _ = orderOf (toPGL (uPSL1412 (ZMod p) 1)) := MulEquiv.orderOf_eq (MulAut.conj a) _
      _ = orderOf (uPSL1412 (ZMod p) 1) :=
          orderOf_injective toPGL Matrix.ProjectiveSpecialLinearGroup.toPGL_injective _
      _ = p := hord
  · rw [← ha, hy]
    calc a * wPGL1412 (ZMod p) * a⁻¹ * (a * toPGL (uPSL1412 (ZMod p) 1) * a⁻¹) *
          (a * wPGL1412 (ZMod p) * a⁻¹)⁻¹
        = a * (wPGL1412 (ZMod p) * toPGL (uPSL1412 (ZMod p) 1) * (wPGL1412 (ZMod p))⁻¹) *
            a⁻¹ := by group
      _ = a * (toPGL (uPSL1412 (ZMod p) 1))⁻¹ * a⁻¹ := by rw [wPGL1412_conj_uPSL1412]
      _ = (a * toPGL (uPSL1412 (ZMod p) 1) * a⁻¹)⁻¹ := by group

private theorem exists_inv_order_five1412 {g : PGL2 (ZMod 5)}
    (hgJ : g ∈ (toPGL : PSL2 (ZMod 5) →* PGL2 (ZMod 5)).range)
    (hg : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g) :
    ∃ y : PSL2 (ZMod 5), orderOf y = 5 ∧ g * toPGL y * g⁻¹ = (toPGL y)⁻¹ := by
  have hF : IsOddPrimePower (Nat.card (ZMod 5)) :=
    ⟨5, 1, by norm_num, by decide, le_rfl, by simp⟩
  have h3 : 3 < Nat.card (ZMod 5) := by simp
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three (ZMod 5) hF h3
  have hw : wPGL1412 (ZMod 5) ∈ commutator (PGL2 (ZMod 5)) := by
    rw [hcomm, wPGL1412_mem_range_iff]
    exact ⟨2, by decide⟩
  obtain ⟨a, -, ha⟩ := pgl2_inner_involutions_conjugate hF h3 hw
    (isInvolution_wPGL1412 (by decide)) (hcomm ▸ hgJ) hg
  exact exists_inv_order_eq_of_isConj_wPGL1412 (isConj_iff.mpr ⟨a, ha⟩)

private theorem exists_inv_order_seven1412 {g : PGL2 (ZMod 7)}
    (hgJ : g ∉ (toPGL : PSL2 (ZMod 7) →* PGL2 (ZMod 7)).range)
    (hg : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g) :
    ∃ y : PSL2 (ZMod 7), orderOf y = 7 ∧ g * toPGL y * g⁻¹ = (toPGL y)⁻¹ := by
  have hF : IsOddPrimePower (Nat.card (ZMod 7)) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by simp⟩
  have h3 : 3 < Nat.card (ZMod 7) := by simp
  have hcomm := pgl2_commutator_eq_psl2_range_of_card_gt_three (ZMod 7) hF h3
  have hw : wPGL1412 (ZMod 7) ∉ commutator (PGL2 (ZMod 7)) := by
    rw [hcomm, wPGL1412_mem_range_iff]
    decide
  exact exists_inv_order_eq_of_isConj_wPGL1412 (pgl2_outer_involutions_conjugate (ZMod 7) hF h3
    (isInvolution_wPGL1412 (by decide)) hg hw (hcomm ▸ hgJ))

private theorem exists_inv_odd_order_large1412 {p : ℕ} [Fact p.Prime] (hp11 : 11 ≤ p)
    {g : PGL2 (ZMod p)} (hg : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution g) :
    ∃ (y : PSL2 (ZMod p)) (n : ℕ), orderOf y = n ∧ Odd n ∧ 5 ≤ n ∧
      g * toPGL y * g⁻¹ = (toPGL y)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hFc : Nat.card (ZMod p) = p := Nat.card_zmod p
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hF : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, hp, hpodd, le_rfl, by rw [hFc, pow_one]⟩
  have h3 : 3 < Nat.card (ZMod p) := by rw [hFc]; omega
  have key : ∀ y : PSL2 (ZMod p), pglAction (ZMod p) g y = y⁻¹ →
      g * toPGL y * g⁻¹ = (toPGL y)⁻¹ := fun y hy => by
    rw [← toPGL_pglAction, hy, map_inv]
  obtain ⟨m, hm⟩ := hpodd
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨y, hy1, hy2⟩ := CFSG.Quasithin.H13.S126C.exists_pglAction_inv_nonsplit hF h3 hg
    rw [hFc] at hy1
    exact ⟨y, (p + 1) / 2, hy1, ⟨k, by omega⟩, by omega, key y hy2⟩
  · obtain ⟨y, hy1, hy2⟩ := CFSG.Quasithin.H13.S126C.exists_pglAction_inv_split hF h3 hg
    rw [hFc] at hy1
    exact ⟨y, (p - 1) / 2, hy1, ⟨k, by omega⟩, by omega, key y hy2⟩

private theorem exists_odd_prime_pow_dvd1412 {n : ℕ} (hn : Odd n) (h5 : 5 ≤ n) :
    ∃ q k : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧ ¬ q ^ k ∣ 3 ∧ q ^ k ∣ n := by
  have hodd : ∀ q : ℕ, q ∣ n → q ≠ 2 := fun q hq h2 => by
    rw [h2] at hq
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 hq)
  by_cases h : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ q ≠ 3
  · obtain ⟨q, hq, hqn, hq3⟩ := h
    refine ⟨q, 1, hq, hodd q hqn, le_rfl, fun h3 => hq3 ?_, by simpa using hqn⟩
    rw [pow_one] at h3
    exact (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 h3
  · push Not at h
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hq3 : q = 3 := h q hq hqn
    subst hq3
    obtain ⟨m, hm⟩ := hqn
    have hm2 : m ≠ 1 := by
      rintro rfl
      omega
    obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd hm2
    have hrn : r ∣ n := hm ▸ Dvd.dvd.mul_left hrm 3
    have hr3 : r = 3 := h r hr hrn
    subst hr3
    refine ⟨3, 2, Nat.prime_three, by norm_num, by norm_num, by norm_num, ?_⟩
    obtain ⟨t, ht⟩ := hrm
    exact ⟨t, by rw [hm, ht]; ring⟩

end Fusion

private instance factPrimeTwo1412 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private def fibGL1412 : GL (Fin 2) (ZMod 7) :=
  ⟨!![0, 1; 1, 1], !![-1, 1; 1, 0], by decide, by decide⟩

private theorem orderOf_mk_fibGL1412 :
    orderOf (Matrix.ProjGenLinGroup.mk fibGL1412 : PGL2 (ZMod 7)) = 8 := by
  have h := orderOf_eq_prime_pow
    (x := (Matrix.ProjGenLinGroup.mk fibGL1412 : PGL2 (ZMod 7))) (p := 2) (n := 2) ?_ ?_
  · simpa using h
  · rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar]
    rintro ⟨u, hu⟩
    revert u
    decide
  · rw [← map_pow, Matrix.ProjGenLinGroup.mk_eq_one,
      Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨-1, ?_⟩
    decide

private noncomputable def sl71412 (a b c d : ZMod 7) (h : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
  ⟨!![a, b; c, d], by simpa [Matrix.det_fin_two] using h⟩

private noncomputable def a0_1412 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
  sl71412 0 1 6 0 (by decide)

private noncomputable def a1_1412 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
  sl71412 0 2 3 0 (by decide)

private noncomputable def a2_1412 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
  sl71412 1 2 6 6 (by decide)

private theorem orderOf_mk_eq_prime1412 {A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)} {r : ℕ}
    [Fact r.Prime] (h1 : A ^ r ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)))
    (h2 : A ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 7))) :
    orderOf (QuotientGroup.mk A : PSL2 (ZMod 7)) = r :=
  orderOf_eq_prime (by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact h1)
    (by rw [Ne, QuotientGroup.eq_one_iff]; exact h2)

private theorem orderOf_a0_1412 : orderOf (QuotientGroup.mk a0_1412 : PSL2 (ZMod 7)) = 2 :=
  orderOf_mk_eq_prime1412
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)

private theorem orderOf_a1_1412 : orderOf (QuotientGroup.mk a1_1412 : PSL2 (ZMod 7)) = 2 :=
  orderOf_mk_eq_prime1412
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)

private theorem orderOf_a2_1412 : orderOf (QuotientGroup.mk a2_1412 : PSL2 (ZMod 7)) = 2 :=
  orderOf_mk_eq_prime1412
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)

private theorem orderOf_a01_1412 :
    orderOf (QuotientGroup.mk (a0_1412 * a1_1412) : PSL2 (ZMod 7)) = 3 :=
  orderOf_mk_eq_prime1412
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)

private theorem orderOf_a12_1412 :
    orderOf (QuotientGroup.mk (a1_1412 * a2_1412) : PSL2 (ZMod 7)) = 4 := by
  have h := orderOf_eq_prime_pow
    (x := (QuotientGroup.mk (a1_1412 * a2_1412) : PSL2 (ZMod 7))) (p := 2) (n := 1) ?_ ?_
  · simpa using h
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    decide
  · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff,
      Matrix.SpecialLinearGroup.mem_center_iff]
    decide

private theorem orderOf_a012_1412 :
    orderOf (QuotientGroup.mk (a0_1412 * a1_1412 * a2_1412) : PSL2 (ZMod 7)) = 7 :=
  orderOf_mk_eq_prime1412
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)
    (by rw [Matrix.SpecialLinearGroup.mem_center_iff]; decide)

private noncomputable def t0_1412 : PSL2 (ZMod 7) := QuotientGroup.mk a0_1412
private noncomputable def t1_1412 : PSL2 (ZMod 7) := QuotientGroup.mk a1_1412
private noncomputable def t2_1412 : PSL2 (ZMod 7) := QuotientGroup.mk a2_1412

private theorem closure_t_eq_top1412 :
    Subgroup.closure ({t0_1412, t1_1412, t2_1412} : Set (PSL2 (ZMod 7))) = ⊤ := by
  set M := Subgroup.closure ({t0_1412, t1_1412, t2_1412} : Set (PSL2 (ZMod 7))) with hM
  have hFc : Nat.card (ZMod 7) = 7 := Nat.card_zmod 7
  have hF : IsOddPrimePower (Nat.card (ZMod 7)) :=
    ⟨7, 1, by norm_num, by decide, le_rfl, by simp⟩
  have hQ : Nat.card (PSL2 (ZMod 7)) = 168 := by
    rw [psl2_card_formula (ZMod 7) hF, hFc]
    norm_num
  have h0 : t0_1412 ∈ M := Subgroup.subset_closure (by simp)
  have h1 : t1_1412 ∈ M := Subgroup.subset_closure (by simp)
  have h2 : t2_1412 ∈ M := Subgroup.subset_closure (by simp)
  have hdvd : ∀ {m : M}, orderOf m ∣ Nat.card M := fun {m} => orderOf_dvd_natCard m
  have h3 : 3 ∣ Nat.card M := by
    have := hdvd (m := ⟨t0_1412 * t1_1412, mul_mem h0 h1⟩)
    rwa [Subgroup.orderOf_mk,
      show t0_1412 * t1_1412 = QuotientGroup.mk (a0_1412 * a1_1412) from rfl,
      orderOf_a01_1412] at this
  have h4 : 4 ∣ Nat.card M := by
    have := hdvd (m := ⟨t1_1412 * t2_1412, mul_mem h1 h2⟩)
    rwa [Subgroup.orderOf_mk,
      show t1_1412 * t2_1412 = QuotientGroup.mk (a1_1412 * a2_1412) from rfl,
      orderOf_a12_1412] at this
  have h7 : 7 ∣ Nat.card M := by
    have := hdvd (m := ⟨t0_1412 * t1_1412 * t2_1412, mul_mem (mul_mem h0 h1) h2⟩)
    rwa [Subgroup.orderOf_mk,
      show t0_1412 * t1_1412 * t2_1412 = QuotientGroup.mk (a0_1412 * a1_1412 * a2_1412) from rfl,
      orderOf_a012_1412] at this
  have hle : Nat.card M ≤ 168 :=
    Nat.le_of_dvd (by norm_num) (hQ ▸ Subgroup.card_subgroup_dvd_card M)
  have hpos : 0 < Nat.card M := Nat.card_pos
  have hcases : Nat.card M = 84 ∨ Nat.card M = 168 := by omega
  haveI : IsSimpleGroup (PSL2 (ZMod 7)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hFc]; norm_num)
  rcases hcases with h84 | h168
  · exfalso
    have hidx : M.index = 2 := by
      have := Subgroup.card_mul_index M
      rw [hQ, h84] at this
      omega
    haveI : M.Normal := Subgroup.normal_of_index_eq_two hidx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hb | ht
    · rw [hb, Subgroup.card_bot] at h84
      omega
    · rw [ht, Subgroup.index_top] at hidx
      omega
  · exact Subgroup.eq_top_of_card_eq M (by rw [h168, hQ])

private theorem exists_conj_closure_eq1412 {G : Type} [Group G] {Ω : Subgroup G}
    (e : ↥Ω ≃* PSL2 (ZMod 7)) {x : G} (hx : x ∈ Ω) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g₁ ∈ Ω, ∃ g₂ ∈ Ω, Ω ≤ Subgroup.closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set G) := by
  have hFc : Nat.card (ZMod 7) = 7 ^ 1 := by rw [Nat.card_zmod, pow_one]
  set t : PSL2 (ZMod 7) := e ⟨x, hx⟩ with htdef
  have ht : orderOf t = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : (⟨x, hx⟩ : ↥Ω) ^ 2 = 1 := Subtype.ext (by rw [sq]; exact hx2)
      rw [htdef, ← map_pow, h1, map_one]
    · intro h1
      apply hx1
      have := e.injective (h1.trans e.map_one.symm)
      exact congrArg Subtype.val this
  have hconj : ∀ T U : PSL2 (ZMod 7), orderOf T = 2 → orderOf U = 2 → ∃ c, c * T * c⁻¹ = U :=
    fun T U hT hU => isConj_iff.mp (CFSG.Walter.psl2_isConj_of_orderOf_eq_two (ZMod 7) hFc
      (by decide) one_pos hT hU)
  obtain ⟨a, ha⟩ := hconj t0_1412 t orderOf_a0_1412 ht
  obtain ⟨b₁, hb₁⟩ := hconj t0_1412 t1_1412 orderOf_a0_1412 orderOf_a1_1412
  obtain ⟨b₂, hb₂⟩ := hconj t0_1412 t2_1412 orderOf_a0_1412 orderOf_a2_1412
  set h₁ : PSL2 (ZMod 7) := a * b₁ * a⁻¹ with hh₁
  set h₂ : PSL2 (ZMod 7) := a * b₂ * a⁻¹ with hh₂
  let f : PSL2 (ZMod 7) →* G := Ω.subtype.comp e.symm.toMonoidHom
  have hfe : ∀ w : ↥Ω, f (e w) = (w : G) := fun w => by simp [f]
  have hft : f t = x := hfe ⟨x, hx⟩
  have hS : ({t, h₁ * t * h₁⁻¹, h₂ * t * h₂⁻¹} : Set (PSL2 (ZMod 7))) =
      (MulAut.conj a).toMonoidHom '' ({t0_1412, t1_1412, t2_1412} : Set (PSL2 (ZMod 7))) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    have e0 : (MulAut.conj a).toMonoidHom t0_1412 = t := ha
    have e1 : (MulAut.conj a).toMonoidHom t1_1412 = h₁ * t * h₁⁻¹ := by
      rw [← hb₁, ← ha, hh₁]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have e2 : (MulAut.conj a).toMonoidHom t2_1412 = h₂ * t * h₂⁻¹ := by
      rw [← hb₂, ← ha, hh₂]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e0, e1, e2]
  have hStop : Subgroup.closure ({t, h₁ * t * h₁⁻¹, h₂ * t * h₂⁻¹} : Set (PSL2 (ZMod 7))) =
      ⊤ := by
    rw [hS, ← MonoidHom.map_closure, closure_t_eq_top1412]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj a).surjective
  refine ⟨f h₁, (e.symm h₁).2, f h₂, (e.symm h₂).2, fun z hz => ?_⟩
  have h1 : e ⟨z, hz⟩ ∈ Subgroup.closure ({t, h₁ * t * h₁⁻¹, h₂ * t * h₂⁻¹} :
      Set (PSL2 (ZMod 7))) := by rw [hStop]; trivial
  have h2 := Subgroup.mem_map_of_mem f h1
  rw [MonoidHom.map_closure] at h2
  have himg : f '' ({t, h₁ * t * h₁⁻¹, h₂ * t * h₂⁻¹} : Set (PSL2 (ZMod 7))) =
      ({x, f h₁ * x * (f h₁)⁻¹, f h₂ * x * (f h₂)⁻¹} : Set G) := by
    rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    simp only [map_mul, map_inv, hft]
  rw [himg, hfe] at h2
  exact h2

private theorem exists_ne_of_two_lt_card1412 {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (a : Y) (h : 2 < Nat.card N) : ∃ x ∈ N, x ≠ 1 ∧ x ≠ a := by
  by_contra hall
  push Not at hall
  have hsub : (N : Set Y) ⊆ {1, a} := by
    intro x hx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr (hall x hx hx1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq] at h
  have h2 : ({1, a} : Set Y).ncard ≤ 2 := by
    have := Set.ncard_insert_le 1 ({a} : Set Y)
    rwa [Set.ncard_singleton] at this
  omega

private theorem exists_ne_one_mem_range1412 {G : Type} [Group G] [Finite G] {p : ℕ}
    {H : Subgroup G}
    (Φ : ↥H ≃* PGL2 (ZMod p)) {E : Subgroup G} (hEH : E ≤ H) (hE : Sec3.IsElemTwo E)
    (hE4 : Nat.card E = 4)
    (hJ : (toPGL : PSL2 (ZMod p) →* PGL2 (ZMod p)).range.index = 2) :
    ∃ (x : G) (hx : x ∈ E), x ≠ 1 ∧
      Φ ⟨x, hEH hx⟩ ∈ (toPGL : PSL2 (ZMod p) →* PGL2 (ZMod p)).range := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haE, ha1, -⟩ := exists_ne_of_two_lt_card1412 (N := E) (1 : G) (by omega)
  obtain ⟨b, hbE, hb1, hba⟩ := exists_ne_of_two_lt_card1412 (N := E) a (by omega)
  have hab : a * b ∈ E := E.mul_mem haE hbE
  have hab1 : a * b ≠ 1 := by
    intro h
    have h2 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    have h3 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hE.2 a haE)
    exact hba (h2.trans h3)
  have h1 := hcon a haE ha1
  have h2 := hcon b hbE hb1
  have h3 := hcon (a * b) hab hab1
  apply h3
  have : (⟨a * b, hEH hab⟩ : ↥H) = ⟨a, hEH haE⟩ * ⟨b, hEH hbE⟩ := rfl
  rw [this, map_mul, Subgroup.mul_mem_iff_of_index_two hJ]
  exact iff_of_false h1 h2

private theorem isInvolution_Φ1412 {G : Type} [Group G] {p : ℕ} {H : Subgroup G}
    (Φ : ↥H ≃* PGL2 (ZMod p)) {x : G} (hxH : x ∈ H) (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (Φ ⟨x, hxH⟩) := by
  refine ⟨fun h => hx1 ?_, ?_⟩
  · have : (⟨x, hxH⟩ : ↥H) = 1 := Φ.injective (h.trans (map_one Φ).symm)
    exact congrArg Subtype.val this
  · rw [← map_pow]
    have : (⟨x, hxH⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by rw [sq]; exact hx2)
    rw [this, map_one]

private theorem eq_five_or_seven1412 {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (h11 : p < 11) :
    p = 5 ∨ p = 7 := by
  interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)

private theorem isOddPrimePower_zmod1412 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl,
    by rw [Nat.card_zmod, pow_one]⟩

end Helpers

theorem words_four_group1412 {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {H : Subgroup G}
    (e : ↥⁅H, H⁆ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (hC : H ⊓ centralizer ((⁅H, H⁆ : Subgroup G) : Set G) = ⊥)
    (hcard : Nat.card H = p * (p ^ 2 - 1)) {E : Subgroup G} (hEH : E ≤ H)
    (hE : Sec3.IsElemTwo E) (hE4 : Nat.card E = 4) :
    (∃ x ∈ E, ∃ g ∈ H, ∃ q k : ℕ, q.Prime ∧ q ≠ 2 ∧ 1 ≤ k ∧ ¬ q ^ k ∣ 3 ∧
        q ^ k ∣ orderOf (x * g * x * g⁻¹)) ∨
      (p = 7 ∧ E ≤ ⁅H, H⁆ ∧ (∃ y ∈ H, orderOf y = 8) ∧
        ∀ x ∈ E, x ≠ 1 → ∃ g₁ ∈ H, ∃ g₂ ∈ H,
          ⁅H, H⁆ ≤ closure ({x, g₁ * x * g₁⁻¹, g₂ * x * g₂⁻¹} : Set G)) := by
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_pgl2_of_commutator1412 hp5 e hC hcard
  have hx2 : ∀ x ∈ E, x * x = 1 := hE.2
  have hJ : (Matrix.ProjectiveSpecialLinearGroup.toPGL :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) →*
        Matrix.ProjGenLinGroup (Fin 2) (ZMod p)).range.index = 2 :=
    CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two (ZMod p) (isOddPrimePower_zmod1412 hp5)
  by_cases hp11 : 11 ≤ p
  · left
    obtain ⟨x, hxE, hx1, -⟩ := exists_ne_of_two_lt_card1412 (N := E) (1 : G) (by omega)
    have hxH := hEH hxE
    obtain ⟨y, n, hyn, hodd, h5, hxy⟩ := exists_inv_odd_order_large1412 hp11
      (isInvolution_Φ1412 Φ hxH (hx2 x hxE) hx1)
    obtain ⟨g, hgH, hg⟩ := exists_word_of_conj_inv1412 e Φ hΦ hxH (hx2 x hxE)
      (by rw [hyn]; exact hodd) hxy
    obtain ⟨q, k, hq, hq2, hk, hq3, hqn⟩ := exists_odd_prime_pow_dvd1412 hodd h5
    exact ⟨x, hxE, g, hgH, q, k, hq, hq2, hk, hq3, by rw [hg, hyn]; exact hqn⟩
  · rcases eq_five_or_seven1412 Fact.out hp5 (by omega) with rfl | rfl
    ·
      left
      obtain ⟨x, hxE, hx1, hxJ⟩ := exists_ne_one_mem_range1412 Φ hEH hE hE4 hJ
      have hxH := hEH hxE
      obtain ⟨y, hy5, hxy⟩ := exists_inv_order_five1412 hxJ
        (isInvolution_Φ1412 Φ hxH (hx2 x hxE) hx1)
      obtain ⟨g, hgH, hg⟩ := exists_word_of_conj_inv1412 e Φ hΦ hxH (hx2 x hxE)
        (by rw [hy5]; decide) hxy
      exact ⟨x, hxE, g, hgH, 5, 1, by norm_num, by norm_num, le_rfl, by norm_num,
        by rw [hg, hy5]; simp⟩
    ·
      by_cases hEΩ : E ≤ ⁅H, H⁆
      · right
        refine ⟨rfl, hEΩ, ?_, fun x hxE hx1 => ?_⟩
        · refine ⟨((Φ.symm (Matrix.ProjGenLinGroup.mk fibGL1412) : ↥H) : G),
            (Φ.symm (Matrix.ProjGenLinGroup.mk fibGL1412)).2, ?_⟩
          rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_mk_fibGL1412]
        · obtain ⟨g₁, hg₁, g₂, hg₂, hcl⟩ :=
            exists_conj_closure_eq1412 e (hEΩ hxE) (hx2 x hxE) hx1
          exact ⟨g₁, commutator_le_self1412 H hg₁, g₂, commutator_le_self1412 H hg₂, hcl⟩
      · left
        obtain ⟨x, hxE, hxΩ⟩ := SetLike.not_le_iff_exists.1 hEΩ
        have hxH := hEH hxE
        have hx1 : x ≠ 1 := fun h => hxΩ (h ▸ (⁅H, H⁆).one_mem)
        have hxJ : Φ ⟨x, hxH⟩ ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) →*
              Matrix.ProjGenLinGroup (Fin 2) (ZMod 7)).range := fun h =>
          hxΩ ((mem_commutator_iff_Φ_mem_range1412 e Φ hΦ ⟨x, hxH⟩).2 h)
        obtain ⟨y, hy7, hxy⟩ := exists_inv_order_seven1412 hxJ
          (isInvolution_Φ1412 Φ hxH (hx2 x hxE) hx1)
        obtain ⟨g, hgH, hg⟩ := exists_word_of_conj_inv1412 e Φ hΦ hxH (hx2 x hxE)
          (by rw [hy7]; decide) hxy
        exact ⟨x, hxE, g, hgH, 7, 1, by norm_num, by norm_num, le_rfl, by norm_num,
          by rw [hg, hy7]; simp⟩

end CFSG.RankThree.PartTwo.Sec20
