module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Index
import CFSG.Quasithin.Vol2.Ch11SecU1L3IX
import CFSG.Quasithin.Vol2.Ch11SecU1U3N
import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Mod
import CFSG.Models.PGL
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.Quasithin.Vol2.Ch11SecU1L3IQ
import CFSG.Quasithin.Vol2.Ch11SecU1L3IV

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

section L3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
  CFSG.QuasithinUnique.Ch1 CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
open scoped MatrixGroups

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

theorem outerData_L3 (hp : 5 ≤ p) {L : Subgroup G} [L.Normal]
    (hC : centralizer (L : Set G) = ⊥) (e : ↥L ≃* PSL3 p) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) :
    Nonempty (↥⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ∧
      centralizer ({b} : Set G) ≤
        normalizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) ∧
      L ⊓ centralizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) = ⊥ ∧
      Nat.card ↥(L ⊓ centralizer ({b} : Set G)) = p * (p ^ 2 - 1) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨A, hA, hβ⟩ := exists_graph_of_outer hp2 hC e hbL hb2
  set ψ := e.trans (psl3EquivP p) with hψ
  set f : projectiveSL 3 (ZMod p) →* G := L.subtype.comp ψ.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp ψ.symm.injective
  have hfψ : ∀ (x : G) (hx : x ∈ L), f (ψ ⟨x, hx⟩) = x := fun x hx => by simp [hf]
  set R := ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hR
  have hRt : Rᵀ = R := transpose_inv_of_transpose_eq' A hA
  have hRd : R.det ≠ 0 := GeneralLinearGroup.det_ne_zero _
  have hR0 : R ≠ 0 := fun h => hRd (by rw [h]; exact Matrix.det_zero)
  have hfix : ∀ x, b * f x * b⁻¹ = f x ↔
      (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x := by
    intro x
    have hβx : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x =
        ψ (MulAut.conjNormal b (ψ.symm x)) := by
      rw [← hβ]
      rfl
    rw [hβx]
    constructor
    · intro h
      apply ψ.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact h
    · intro h
      have h1 := congrArg (fun y => ((ψ.symm y : ↥L) : G)) h
      simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h1
      exact h1
  set F := f.comp (proj 3 (ZMod p)) with hF
  set H := L ⊓ Subgroup.centralizer ({b} : Set G) with hH
  have hLC : H = (soForm R).map F := by
    ext g
    constructor
    · rintro ⟨hgL, hgC⟩
      have hgb := Subgroup.mem_centralizer_singleton_iff.mp hgC
      obtain ⟨x, hx⟩ : ∃ x, f x = g := ⟨ψ ⟨g, hgL⟩, hfψ g hgL⟩
      have hxf : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x := by
        refine (hfix x).mp ?_
        rw [hx]
        calc b * g * b⁻¹ = g * b * b⁻¹ := by rw [hgb]
          _ = g := by group
      obtain ⟨s, hs⟩ := (fixed_iff_mem_range_soProj hA x).mp hxf
      refine ⟨s, s.2, ?_⟩
      have h1 : F s = f (soProj R s) := rfl
      rw [h1, hs, hx]
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(ψ.symm (proj 3 (ZMod p) s)).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p))
          (proj 3 (ZMod p) s) = proj 3 (ZMod p) s :=
        (fixed_iff_mem_range_soProj hA _).mpr ⟨⟨s, hs⟩, rfl⟩
      have h1 := (hfix _).mpr hx
      have h2 : F s = f (proj 3 (ZMod p) s) := rfl
      rw [h2]
      calc f (proj 3 (ZMod p) s) * b = (b * f (proj 3 (ZMod p) s) * b⁻¹) * b := by rw [h1]
        _ = b * f (proj 3 (ZMod p) s) := by group
  set W : Subgroup SL(3, ZMod p) := ⁅soForm R, soForm R⁆ with hW
  have hL₀ : ⁅H, H⁆ = W.map F := by rw [hLC, ← Subgroup.map_commutator]
  have hFW : Function.Injective (F.comp W.subtype) := by
    intro a a' h
    have h0 : f (proj 3 (ZMod p) a) = f (proj 3 (ZMod p) a') := h
    have h1 : ((proj 3 (ZMod p)).comp W.subtype) a = ((proj 3 (ZMod p)).comp W.subtype) a' :=
      hfinj h0
    exact injective_proj_commutator_soForm hR0 h1
  have hrange : (F.comp W.subtype).range = W.map F := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨eW⟩ := nonempty_commutator_soForm_equiv hp hRt hRd
  let e₀ : ↥⁅H, H⁆ ≃* PSL(2, ZMod p) := (MulEquiv.subgroupCongr (hL₀.trans hrange.symm)).trans
    ((MonoidHom.ofInjective hFW).symm.trans eW)
  have key : ∀ g ∈ Subgroup.centralizer ({b} : Set G), ∀ h ∈ H, g * h * g⁻¹ ∈ H := by
    rintro g hg h ⟨hhL, hhC⟩
    have hgb : Commute g b := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hhb : Commute h b := Subgroup.mem_centralizer_singleton_iff.mp hhC
    exact ⟨‹L.Normal›.conj_mem h hhL g, Subgroup.mem_centralizer_singleton_iff.mpr
      ((hgb.mul_left hhb).mul_left hgb.inv_left).eq⟩
  refine ⟨⟨e₀⟩, fun g hg => ?_, ?_, ?_⟩
  · apply mem_normalizer_commutator
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hh => ?_⟩
    have h1 := key g⁻¹ (Subgroup.inv_mem _ hg) _ hh
    simpa [mul_assoc] using h1
  · rw [eq_bot_iff]
    rintro l ⟨hlL, hlC⟩
    rw [Subgroup.mem_bot]
    obtain ⟨x, hx⟩ : ∃ x, f x = l := ⟨ψ ⟨l, hlL⟩, hfψ l hlL⟩
    have hx1 : x = 1 := by
      refine eq_one_of_commute_commutator_soForm hp hRt hRd fun ω hω => hfinj ?_
      have hω' : f (proj 3 (ZMod p) ω) ∈ ⁅H, H⁆ := by
        rw [hL₀]
        exact ⟨ω, hω, rfl⟩
      rw [map_mul, map_mul, hx]
      exact (Subgroup.mem_centralizer_iff.mp hlC _ hω').symm
    rw [← hx, hx1, map_one]
  ·
    have hodd : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
    have hinj : Function.Injective (F.comp (soForm R).subtype) :=
      hfinj.comp (soProj_injective hR0)
    have hrange' : (F.comp (soForm R).subtype).range = H := by
      rw [hLC, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Nat.card ↥(soForm R) = Nat.card ↥H := by
      rw [← hrange']
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← h1]
    have h2 := card_soForm hodd (A⁻¹) hRt
    rwa [Nat.card_zmod] at h2

end L3

section U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin.A312U3 (uniData)
open CFSG.QuasithinUnique.Ch1 (transAut_apply)
open CFSG.Quasithin.Vol2.Ch11.SecU1.U3
open CFSG.LocalAnalysis.ComponentInitial.FourGroupOddBilinear (isometrySL)
open CFSG.RankThree.SubgroupLists (soGL card_soGL_three)
open scoped MatrixGroups

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

theorem outerData_U3 {F : Type} [Field F] (hp5 : 5 ≤ p) (hF : Nat.card F = p ^ 2)
    {L : Subgroup G} [L.Normal] (hC : centralizer (L : Set G) = ⊥) (ψ : PSU3F p F ≃* ↥L)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    Nonempty (↥⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ∧
      centralizer ({b} : Set G) ≤
        normalizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) ∧
      L ⊓ centralizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) = ⊥ ∧
      Nat.card ↥(L ⊓ centralizer ({b} : Set G)) = p * (p ^ 2 - 1) := by
  have hp2 : p ≠ 2 := by omega
  have hLn : L.Normal := inferInstance
  obtain ⟨ψh⟩ := exists_hyp_equiv hF ψ
  obtain ⟨A, σ, hx, hA, hσ, ⟨c, hc0, hAc⟩, hΦ⟩ :=
    exists_rep_bar_data (uniData hF) hp2 hC ψh hbL hb2
  have : Finite F := (uniData hF).finite
  have : CharP F p := (uniData hF).charP
  have : Fintype (uniData hF).fixedField := Fintype.ofFinite _
  have hcardF : Fintype.card (uniData hF).fixedField = p := by
    rw [← Nat.card_eq_fintype_card, (uniData hF).card_fixedField, pow_one]
  obtain ⟨R, φ, Hm, Wm, hRdet, hRs, hφinj, hHW, hWH, hM, hmat⟩ :=
    exists_fixed_data (uniData hF) hp2 hA hc0 hAc hσ hx
  set e := ZMod.ringEquiv (uniData hF).fixedField hcardF with he
  set M := φ.range with hMdef
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) = M.map (embU ψh.symm) := by
    ext g
    constructor
    · rintro ⟨hgL, hgb⟩
      have hgb' : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp hgb
      refine ⟨ψh ⟨g, hgL⟩, (hM _).mpr ?_, ?_⟩
      · rw [hΦ, transAut_apply]
        congr 1
        apply Subtype.ext
        rw [MulAut.conjNormal_apply]
        show b * g * b⁻¹ = g
        rw [← hgb', mul_inv_cancel_right]
      · show ((ψh.symm (ψh ⟨g, hgL⟩) : ↥L) : G) = g
        rw [MulEquiv.symm_apply_apply]
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(ψh.symm y).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hα := (hM y).mp hy
      rw [hΦ, ← ψh.apply_symm_apply y, transAut_apply] at hα
      have h1 := congrArg Subtype.val (ψh.injective hα)
      rw [MulAut.conjNormal_apply] at h1
      show ((ψh.symm y : ↥L) : G) * b = b * ((ψh.symm y : ↥L) : G)
      calc ((ψh.symm y : ↥L) : G) * b = b * ((ψh.symm y : ↥L) : G) * b⁻¹ * b := by rw [h1]
        _ = b * ((ψh.symm y : ↥L) : G) := by rw [inv_mul_cancel_right]
  have hL₀ : (⁅M, M⁆).map (embU ψh.symm) = ⁅L ⊓ Subgroup.centralizer ({b} : Set G),
      L ⊓ Subgroup.centralizer ({b} : Set G)⁆ := by
    rw [hLb, Subgroup.map_commutator]
  have hMM : ⁅M, M⁆ = (commutator ↥(isometrySL R)).map φ := by
    rw [hMdef, MonoidHom.range_eq_map, _root_.commutator_def, Subgroup.map_commutator]
  obtain ⟨E₂⟩ := nonempty_commutator_equiv_psl2 e hp5 hRs hRdet
  refine ⟨⟨(MulEquiv.subgroupCongr hL₀.symm).trans
      (((⁅M, M⁆).equivMapOfInjective (embU ψh.symm) (embU_injective ψh.symm)).symm.trans
        ((MulEquiv.subgroupCongr hMM).trans
          (((commutator ↥(isometrySL R)).equivMapOfInjective φ hφinj).symm.trans E₂)))⟩,
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer _ _ _
      (centralizer_le_normalizer_inf hLn b) (centralizer_le_normalizer_inf hLn b), ?_, ?_⟩
  · rw [← hL₀, inf_centralizer_map_embU ψh.symm, hMM,
      centralizer_map_commutator_eq_bot (uniData hF) hp5 hRdet hRs hHW hWH hmat, Subgroup.map_bot]
  ·
    rw [hLb, ← Nat.card_congr (M.equivMapOfInjective (embU ψh.symm)
      (embU_injective ψh.symm)).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
      Nat.card_congr (isometryEquivSO e R).toEquiv]
    exact card_soGL_three hp2 (transpose_map_symm e hRs) (det_map_symm_ne_zero e hRdet)

end U3

theorem outerData1412 {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hC : centralizer (L : Set G) = ⊥) {p : ℕ} [Fact p.Prime] (hL : IsL3eps1412 ↥L p)
    {b : G} (hbL : b ∉ L) (hb2 : orderOf b = 2) :
    Nonempty (↥⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) ∧
      centralizer ({b} : Set G) ≤
        normalizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) ∧
      L ⊓ centralizer ((⁅L ⊓ centralizer ({b} : Set G), L ⊓ centralizer ({b} : Set G)⁆ :
          Subgroup G) : Set G) = ⊥ ∧
      Nat.card ↥(L ⊓ centralizer ({b} : Set G)) = p * (p ^ 2 - 1) := by
  have hp5 : 5 ≤ p := by
    have h3 := hL.1
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ (Fact.out : p.Prime)) (by norm_num)
  obtain ⟨hp3, ⟨hp, ⟨e⟩⟩ | ⟨hp, ⟨e⟩⟩⟩ := hL
  ·
    have hadm : CFSG.Open.StatedLieAdmissible .PSL 3 p 1 :=
      ⟨Fact.out, le_rfl, by norm_num, fun h => absurd (Prod.mk.inj h).1 (by norm_num),
        fun h => absurd (Prod.mk.inj h).1 (by norm_num)⟩
    obtain ⟨e'⟩ := CFSG.Quasithin.E2P.Asc80.exists_equiv_psl3 (K := L)
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e)
    exact outerData_L3 hp5 hC e' hbL hb2
  ·
    have hadm : CFSG.Open.StatedLieAdmissible .PSU 3 p 1 :=
      ⟨Fact.out, le_rfl, le_rfl, fun h => by
        have h2 := (Prod.mk.inj h).2
        rw [pow_one] at h2
        omega⟩
    obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := CFSG.Quasithin.E2P.Asc80.exists_equiv_psu3 (K := L)
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e)
    exact outerData_U3 hp5 hF hC e'.symm hbL hb2

end CFSG.RankThree.PartTwo.Sec20
