module

import CFSG.Quasithin.MS93.S4AVtx
import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.S45Crit

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

omit [Finite G] [Fintype F] in
theorem commutator_sup_left_le {Γ : Type*} [Group Γ] {H₁ H₂ A N : Subgroup Γ}
    (hN₁ : H₁ ≤ Subgroup.normalizer (N : Set Γ)) (hN₂ : H₂ ≤ Subgroup.normalizer (N : Set Γ))
    (h₁ : ⁅H₁, A⁆ ≤ N) (h₂ : ⁅H₂, A⁆ ≤ N) : ⁅H₁ ⊔ H₂, A⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = y₁ * ⁅y₂, x⁆ * y₁⁻¹ * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp hy₁ _).mp (h₂ x hx)) (h₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, h⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]; group
        rw [e]
        have hy' : y⁻¹ ∈ Subgroup.normalizer (N : Set Γ) := inv_mem hy
        have := (Subgroup.mem_normalizer_iff.mp hy' _).mp (inv_mem (h x hx))
        simpa [mul_assoc] using this }
  have hH₁ : H₁ ≤ S := fun y hy =>
    ⟨hN₁ hy, fun x hx => h₁ (Subgroup.commutator_mem_commutator hy hx)⟩
  have hH₂ : H₂ ≤ S := fun y hy =>
    ⟨hN₂ hy, fun x hx => h₂ (Subgroup.commutator_mem_commutator hy hx)⟩
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (sup_le hH₁ hH₂ hy).2 x hx

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem vv_le_qv' {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    Vv (puAmalgam c.hyp.le) δ ≤ Qv _ δ :=
  vv_le_qv c.hyp (by rw [c.b8]; norm_num) hδ

theorem commutator_vv_stab_le {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    ⁅Vv (puAmalgam c.hyp.le) δ, stab _ δ⁆ ≤ Vcirc c.hyp.le L δ ⊔ ZM _ δ := by
  have h := c.hyp
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ δ := (c.vv_le_qv' hδ).trans (qv_le_stab _ δ)
  have hVn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Vv (puAmalgam h.le) δ : Set _) :=
    stab_le_normalizer_vv h δ
  have hLn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Ltil h.le L δ : Set _) :=
    stab_le_normalizer_ltil h δ
  have hNn : stab (puAmalgam h.le) δ ≤
      Subgroup.normalizer ((Vcirc h.le L δ ⊔ ZM (puAmalgam h.le) δ : Subgroup _) : Set _) := by
    refine le_normalizer_sup ?_ (stab_le_normalizer_zm _ δ)
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [Vcirc, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hVn hg),
      map_conj_eq_of_mem_normalizer (hLn hg)]
  rw [stab_eq_ltil_sup_qv h c.full hδ, Subgroup.commutator_comm]
  refine commutator_sup_left_le ?_ ?_ ?_ ?_
  · exact (ltil_le_stab h δ).trans (stab_eq_ltil_sup_qv h c.full hδ ▸ hNn)
  · exact (qv_le_stab _ δ).trans (stab_eq_ltil_sup_qv h c.full hδ ▸ hNn)
  · rw [Subgroup.commutator_comm, Vcirc]; exact le_sup_left
  · rw [Subgroup.commutator_comm]
    exact (c.commutator_vv_qv_le_zloc hδ).trans ((zloc_le_zm h c.full hδ).trans le_sup_right)

theorem exists_natural_vcirc {δ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F') (ψ' : ↥(stab (puAmalgam c.hyp.le) δ) →*
      ↥(StatedSL 3 F')), Fintype.card F' = Fintype.card F ∧ Function.Surjective ψ' ∧
      IsSumOfNaturalModulesVia (stab _ δ) (Vcirc c.hyp.le L δ ⊔ ZM _ δ) (ZM _ δ) ψ' false 1 := by
  have h := c.hyp
  obtain ⟨β, hβ⟩ := exists_adj _ δ
  obtain ⟨-, C, -, -, -, -, -, F', iF, fF, ψ', hq, hs, hnat⟩ := (c.c1 δ β hδ hβ).1
  have e1 : ⁅Vv (puAmalgam h.le) δ, Qv _ δ⁆ ⊔ ZM _ δ = ZM _ δ :=
    sup_eq_right.mpr ((c.commutator_vv_qv_le_zloc hδ).trans (zloc_le_zm h c.full hδ))
  have e2 : ⁅Vv (puAmalgam h.le) δ, stab _ δ⁆ ⊔ ZM _ δ = Vcirc h.le L δ ⊔ ZM _ δ :=
    le_antisymm (sup_le (c.commutator_vv_stab_le hδ) le_sup_right)
      (sup_le_sup_right (Subgroup.commutator_mono le_rfl (ltil_le_stab h δ)) _)
  rw [e1, e2] at hnat
  exact ⟨F', iF, fF, ψ', hq, hs, hnat⟩

theorem zm_le_vv_of_dist {δ μ : Vtx (puAmalgam c.hyp.le)} (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ = 2) : ZM (puAmalgam c.hyp.le) μ ≤ Vv _ δ := by
  have := zv_le_vi (puAmalgam c.hyp.le) (δ := δ) (ρ := μ) (i := 2) hd.le
  rwa [zv_of_isMVtx _ hμ] at this

theorem vcirc_sup_zm_le {δ μ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ = 2) (hB : ¬ ZM _ μ ≤ Bloc c.hyp.le L δ) :
    Vcirc c.hyp.le L δ ⊔ ZM _ δ ≤ conjCl (stab (puAmalgam c.hyp.le) δ) (ZM _ μ) ⊔ ZM _ δ := by
  have h := c.hyp
  have hb2 : 2 < critDist (puAmalgam h.le) := by rw [c.b8]; norm_num
  obtain ⟨F', iF, fF, ψ', -, hs, hnat⟩ := c.exists_natural_vcirc hδ
  set N := NatSec.ofIsSum hnat
  set Y := conjCl (stab (puAmalgam h.le) δ) (ZM _ μ) ⊔ ZM _ δ with hYdef
  have hYn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Y : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) (stab_le_normalizer_zm _ δ)
  have hY : ∀ l : ↥(stab (puAmalgam h.le) δ), ∀ y ∈ Y, (l : (puAmalgam h.le).Universal) * y *
      (l : (puAmalgam h.le).Universal)⁻¹ ∈ Y :=
    fun l y hy => (Subgroup.mem_normalizer_iff.mp (hYn l.2) y).mp hy
  obtain ⟨z, hzμ, hzB⟩ := Set.not_subset.mp hB
  have hzV : z ∈ Vv (puAmalgam h.le) δ := c.zm_le_vv_of_dist hμ hd hzμ
  have : ∃ l ∈ Ltil h.le L δ, ⁅z, l⁆ ∉ ZM (puAmalgam h.le) δ := by
    by_contra hcon
    push Not at hcon
    exact hzB ((mem_bloc_iff h hb2 hδ).mpr ⟨hzV, hcon⟩)
  obtain ⟨l, hl, hzl⟩ := this
  have hzY : z ∈ Y := Subgroup.mem_sup_left (S4A.le_conjCl _ _ hzμ)
  have hwY : ⁅z, l⁆ ∈ Y := by
    have hls : l ∈ stab (puAmalgam h.le) δ := ltil_le_stab h δ hl
    have h1 := hY ⟨l, hls⟩ z⁻¹ (inv_mem hzY)
    have : ⁅z, l⁆ = z * (l * z⁻¹ * l⁻¹) := by rw [commutatorElement_def]; group
    rw [this]
    exact mul_mem hzY h1
  have hwV : ⁅z, l⁆ ∈ Vcirc h.le L δ ⊔ ZM (puAmalgam h.le) δ :=
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hzV hl)
  intro v hv
  obtain ⟨w, hwY', -, hwv⟩ := N.exists_inv_mul_mem_of_invariant hs hY hwY hwV hzl hv
  have : v = w * (w⁻¹ * v) := by group
  rw [this]
  exact mul_mem hwY' (Subgroup.mem_sup_right hwv)

theorem hloc_le_commutator {δ μ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ) (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ = 2) (hB : ¬ ZM _ μ ≤ Bloc c.hyp.le L δ) :
    Hloc c.hyp.le L δ ≤ ⁅ZM (puAmalgam c.hyp.le) μ, Qv _ δ⁆ := by
  have h := c.hyp
  have hZμs : ZM (puAmalgam h.le) μ ≤ stab _ δ :=
    (c.zm_le_vv_of_dist hμ hd).trans ((c.vv_le_qv' hδ).trans (qv_le_stab _ δ))
  have hNz : ⁅ZM (puAmalgam h.le) μ, Qv _ δ⁆ ≤ Zloc h.le L δ :=
    (Subgroup.commutator_mono (c.zm_le_vv_of_dist hμ hd) le_rfl).trans
      (c.commutator_vv_qv_le_zloc hδ)
  have hNn : stab (puAmalgam h.le) δ ≤
      Subgroup.normalizer ((⁅ZM (puAmalgam h.le) μ, Qv _ δ⁆ : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have hc := Subgroup.mem_centralizer_iff.mp
        (zloc_le_centralizer_stab h c.full hδ (hNz hn)) g hg
      rw [hc, mul_inv_cancel_right]; exact hn
    · intro hn
      have hc := Subgroup.mem_centralizer_iff.mp
        (zloc_le_centralizer_stab h c.full hδ (hNz hn)) g⁻¹ (inv_mem hg)
      have : n = g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ := by group
      rw [this, hc, mul_inv_cancel_right]; exact hn
  rw [Hloc]
  refine (Subgroup.commutator_mono ((le_sup_left.trans (c.vcirc_sup_zm_le hδ hμ hd hB)))
    le_rfl).trans ?_
  refine commutator_sup_left_le ((S4A.conjCl_le_of_le hZμs).trans hNn)
    ((zm_le_qv_self _ hδ h.critDist_pos).trans ((qv_le_stab _ δ).trans hNn)) ?_ ?_
  · exact S4A.commutator_conjCl_le hNn (stab_le_normalizer_qv _ δ) (hZμs.trans hNn) le_rfl
  · rw [commutator_zm_qv _ h.hyp20 hδ]; exact bot_le

theorem not_zm_le_bloc {δ δ' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) δ δ') :
    ¬ ZM (puAmalgam c.hyp.le) (geo _ δ δ' 2) ≤ Bloc c.hyp.le L δ := by
  have h := c.hyp
  have hδ := hc.1
  have hb2 : 2 < critDist (puAmalgam h.le) := by rw [c.b8]; norm_num
  intro hle
  apply ms22_v _ h.hyp20 c.bpos c.cent c.s43 hc
  rw [xm_eq_zm h c.full hδ, stab_eq_ltil_sup_qv h c.full hδ]
  set y := geo (puAmalgam h.le) δ δ' 2
  have hd : (puAmalgam h.le).treeGraph.dist δ y = 2 :=
    dist_geo _ (by rw [c.dist_of_isCritical hc]; omega)
  have hy : IsMVtx (puAmalgam h.le) y := by
    rw [isMVtx_geo _ (by rw [c.dist_of_isCritical hc]; omega)]
    exact ⟨fun _ => even_two, fun _ => hδ⟩
  have hyV : ZM (puAmalgam h.le) y ≤ Vv _ δ := c.zm_le_vv_of_dist hy hd
  have crit : ∀ g : (puAmalgam h.le).Universal, g ∈ stab (puAmalgam h.le) δ →
      (∀ x ∈ ZM (puAmalgam h.le) y, ⁅x⁻¹, g⁆ ∈ ZM (puAmalgam h.le) δ) →
      (ZM (puAmalgam h.le) y ⊔ ZM _ δ).map (MulAut.conj g).toMonoidHom ≤ ZM _ y ⊔ ZM _ δ := by
    intro g hg hx
    rw [Subgroup.map_sup]
    refine sup_le ?_ ((map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ δ hg)).le.trans
      le_sup_right)
    rintro _ ⟨x, hxy, rfl⟩
    have e : g * x * g⁻¹ = x * ⁅x⁻¹, g⁆ := by rw [commutatorElement_def]; group
    show g * x * g⁻¹ ∈ _
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hxy) (Subgroup.mem_sup_right (hx x hxy))
  refine sup_le (le_normalizer_of_map_conj_le fun l hl => crit l (ltil_le_stab h δ hl) ?_)
    (le_normalizer_of_map_conj_le fun q hq => crit q (qv_le_stab _ δ hq) ?_)
  · intro x hx
    exact commutator_bloc_le h hb2 hδ (Subgroup.commutator_mem_commutator (hle (inv_mem hx)) hl)
  · intro x hx
    exact (c.commutator_vv_qv_le_zloc hδ).trans (zloc_le_zm h c.full hδ)
      (Subgroup.commutator_mem_commutator (hyV (inv_mem hx)) hq)

end Ctx

end CFSG.Quasithin.MS93.S45
