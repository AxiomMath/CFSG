module

import CFSG.Quasithin.MS93.S4A35
public import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.S45Crit
public import CFSG.Quasithin.MS93.S45Path
public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Pairs

variable {F : Type} [Field F]

theorem exists_mulVec_e0_e1 {u w : Fin 3 → F} (hu : u ≠ 0) (hw : ∀ t : F, w ≠ t • u) :
    ∃ x : SL3 F, ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = u ∧
      ((x : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = w := by
  obtain ⟨x₁, hx₁⟩ := exists_mulVec_e0_eq hu
  set w' := ((x₁⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w with hw'
  have hx₁w : ((x₁ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w' = w := by
    rw [hw', Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]
  have h12 : w' 1 ≠ 0 ∨ w' 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw (w' 0)
    have e : w' = w' 0 • ![1, 0, 0] := by
      funext k; fin_cases k <;> simp [hcon.1, hcon.2]
    rw [← hx₁w]
    nth_rewrite 1 [e]
    rw [Matrix.mulVec_smul, hx₁]
  obtain ⟨x₂, hx₂0, hx₂1⟩ : ∃ x₂ : SL3 F,
      ((x₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      ((x₂ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 1, 0] = w' := by
    rcases h12 with h1 | h2
    · refine ⟨⟨!![1, w' 0, 0; 0, w' 1, 0; 0, w' 2, (w' 1)⁻¹], ?_⟩, ?_, ?_⟩
      · rw [Matrix.det_fin_three]; simp [h1]
      · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · by_cases h1 : w' 1 = 0
      · refine ⟨⟨!![1, w' 0, 0; 0, 0, -(w' 2)⁻¹; 0, w' 2, 0], ?_⟩, ?_, ?_⟩
        · rw [Matrix.det_fin_three]; simp [h2]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1]
      · refine ⟨⟨!![1, w' 0, 0; 0, w' 1, 0; 0, w' 2, (w' 1)⁻¹], ?_⟩, ?_, ?_⟩
        · rw [Matrix.det_fin_three]; simp [h1]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
        · funext k; fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  refine ⟨x₁ * x₂, ?_, ?_⟩
  · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hx₂0, hx₁]
  · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hx₂1, hx₁w]

theorem exists_not_mem_of_commN [CharP F 2] {E : Subgroup (SL3 F)}
    (hE2 : ∀ g ∈ E, g * g = 1) (hEc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g)
    {H : Submodule F (Fin 3 → F)} {u : Fin 3 → F} (hu : u ∈ commN E) (huH : u ∉ H)
    (hHu : H ⊔ Submodule.span F {u} = ⊤) :
    ∃ e ∈ E, ∃ h ∈ H, ((e : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ h ∉ H := by
  by_contra hcon
  push Not at hcon
  apply huH
  have hufix : u ∈ fixN E := commN_le_fixN_of_elemAb hE2 hEc hu
  have hle : commN E ≤ H := by
    rw [commN, Submodule.span_le]
    rintro _ ⟨e, he, y, rfl⟩
    have hy : y ∈ H ⊔ Submodule.span F {u} := by rw [hHu]; trivial
    obtain ⟨h, hh, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have heu : ((e : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (t • u) = t • u := by
      rw [Matrix.mulVec_smul, hufix e he]
    rw [Matrix.mulVec_add, heu, add_sub_add_right_eq_sub]
    exact H.sub_mem (hcon e he h hh) hh
  exact hle hu

theorem sup_span_eq_top [Finite F] {H : Submodule F (Fin 3 → F)} (hH : Module.finrank F H = 2)
    {u : Fin 3 → F} (huH : u ∉ H) : H ⊔ Submodule.span F {u} = ⊤ := by
  have hu0 : u ≠ 0 := fun h0 => huH (h0 ▸ H.zero_mem)
  have hinf : H ⊓ Submodule.span F {u} = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy.2
    by_cases ht : t = 0
    · simp [ht]
    · exfalso
      apply huH
      have := H.smul_mem t⁻¹ hy.1
      rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq H (Submodule.span F {u})
  rw [hinf, finrank_bot, add_zero, hH, finrank_span_singleton hu0] at h1
  apply Submodule.eq_top_of_finrank_eq
  rw [h1, Module.finrank_fin_fun]

end Pairs

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem mem_usup_smul_iff {δ ρ : Vtx (puAmalgam c.hyp.le)}
    {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ)
    (g : ↥(stab (puAmalgam c.hyp.le) δ)) (v : ↥(Uloc c.hyp.le L δ)) :
    (v : (puAmalgam c.hyp.le).Universal) ∈ Usup _ δ ((g : (puAmalgam c.hyp.le).Universal) • ρ) ↔
      ((toSL3 ψ g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ v ∈
        fixN (natImage ψ (Qv (puAmalgam c.hyp.le) ρ)) := by
  have hgδ : (g : (puAmalgam c.hyp.le).Universal) • δ = δ := (mem_stab _).mp g.2
  have hU : Usup (puAmalgam c.hyp.le) δ ((g : (puAmalgam c.hyp.le).Universal) • ρ) =
      (Usup _ δ ρ).map (MulAut.conj (g : (puAmalgam c.hyp.le).Universal)).toMonoidHom := by
    have := usup_smul (puAmalgam c.hyp.le) (g : (puAmalgam c.hyp.le).Universal) δ ρ
    rwa [hgδ] at this
  have hvu : (g : (puAmalgam c.hyp.le).Universal)⁻¹ * (v : (puAmalgam c.hyp.le).Universal) *
      (g : (puAmalgam c.hyp.le).Universal)⁻¹⁻¹ ∈ Uloc c.hyp.le L δ :=
    (Subgroup.mem_normalizer_iff.mp (hψ.1 (inv_mem g.2)) _).mp v.2
  set v' : ↥(Uloc c.hyp.le L δ) := ⟨_, hvu⟩ with hv'
  have hnat := natVec_conj hψ g⁻¹ v v' rfl
  rw [hU, ← hnat, ← c.mem_usup_iff hψ hδ hρ v']
  constructor
  · rintro ⟨w, hw, hwv⟩
    have e : (v' : (puAmalgam c.hyp.le).Universal) = w := by
      have hwv' : (g : (puAmalgam c.hyp.le).Universal) * w *
          (g : (puAmalgam c.hyp.le).Universal)⁻¹ =
          v := hwv
      show (g : (puAmalgam c.hyp.le).Universal)⁻¹ * (v : (puAmalgam c.hyp.le).Universal) *
        (g : (puAmalgam c.hyp.le).Universal)⁻¹⁻¹ = w
      rw [← hwv']
      group
    rw [e]
    exact hw
  · intro h1
    refine ⟨v', h1, ?_⟩
    show (g : (puAmalgam c.hyp.le).Universal) * ((g : (puAmalgam c.hyp.le).Universal)⁻¹ *
      (v : (puAmalgam c.hyp.le).Universal) * (g : (puAmalgam c.hyp.le).Universal)⁻¹⁻¹) *
        (g : (puAmalgam c.hyp.le).Universal)⁻¹ = v
    group

theorem exists_adj_not_le_normalizer {δ δ' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) δ δ') :
    ∃ γ, (puAmalgam c.hyp.le).treeGraph.Adj δ γ ∧
      ¬ ZM _ δ' ≤ Subgroup.normalizer (Usup _ δ γ : Set (puAmalgam c.hyp.le).Universal) := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  have hδ := hc.1
  have hd := c.dist_of_isCritical hc
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hδ
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h c.via (c.isCritical_symm hc).1
  set ρ := geo (puAmalgam h.le) δ δ' 1 with hρdef
  have hρ : (puAmalgam h.le).treeGraph.Adj δ ρ := adj_geo_one _ (by omega)
  have hZs : ZM (puAmalgam h.le) δ' ≤ stab _ δ := zm_le_stab_of_isCritical _ h20 c.bpos hc
  set E := natImage ψ (ZM (puAmalgam h.le) δ') with hEdef
  have hZab := isElemAbelian_zm _ h20 c.bpos (c.isCritical_symm hc).1
  have hE2 : ∀ g ∈ E, g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hg
    rw [← map_mul, ← sq]
    have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZab.2 _ ha)
    rw [this, map_one]
  have hEc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hg
    obtain ⟨b, hb, rfl⟩ := mem_natImage.mp hg'
    have hcomm := hZab.1
    rw [isMulCommutative_subgroup_iff] at hcomm
    have : a * b = b * a := Subtype.ext (by
      simp only [Subgroup.coe_mul]; exact hcomm _ ha _ hb)
    rw [← map_mul, ← map_mul, this]
  have hE : E ≠ ⊥ := (s35_core h c.cent c.via hc hψ hψ').2.2.2.2.2
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (commN_ne_bot hE)
  have hfix := c.fixN_natImage_zm hc hψ
  have hW := (c.fixN_eq_commN_qv hψ hδ hρ).2
  set W := fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) with hWdef
  have huW : u ∈ W := hfix ▸ commN_le_fixN_of_elemAb hE2 hEc hu
  have hWtop : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at hW
    omega
  obtain ⟨v, -, hvW⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hWtop)
  have hv0 : v ≠ 0 := fun h0 => hvW (h0 ▸ W.zero_mem)
  obtain ⟨x₁, hx₁⟩ := exists_mulVec_e0_eq hu0
  obtain ⟨x₂, hx₂⟩ := exists_mulVec_e0_eq hv0
  obtain ⟨g, hg⟩ := toSL3_surjective hψs (x₁ * x₂⁻¹)
  have hx₁' : ((x₁⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = ![1, 0, 0] := by
    rw [← hx₁, Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3,
      Matrix.one_mulVec]
  have hgu : ((toSL3 ψ g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = v := by
    rw [map_inv, hg, _root_.mul_inv_rev, inv_inv, coe_mul_SL3, ← Matrix.mulVec_mulVec, hx₁',
      hx₂]
  set γ := (g : (puAmalgam h.le).Universal) • ρ with hγdef
  have hgδ : (g : (puAmalgam h.le).Universal) • δ = δ := (mem_stab _).mp g.2
  have hγ : (puAmalgam h.le).treeGraph.Adj δ γ := by
    rw [← hgδ]; exact (adj_smul _ _ _ _).mpr hρ
  refine ⟨γ, hγ, fun hN => ?_⟩
  set H := W.comap (Matrix.SpecialLinearGroup.toLin' (toSL3 ψ g⁻¹) : (Fin 3 → F) →ₗ[F] _) with hH
  have hmemH : ∀ y, y ∈ H ↔ ((toSL3 ψ g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y ∈ W := by
    intro y
    rw [hH, Submodule.mem_comap]
    simp only [LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  have huH : u ∉ H := by rw [hmemH, hgu]; exact hvW
  have hHrank : Module.finrank F H = 2 := by
    rw [hH, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, hW]
  obtain ⟨e, he, y, hy, hey⟩ := exists_not_mem_of_commN hE2 hEc hu huH (sup_span_eq_top hHrank huH)
  obtain ⟨z, hz, rfl⟩ := mem_natImage.mp he
  obtain ⟨w, rfl⟩ := natVec_surjective hψ y
  have hwU : (w : (puAmalgam h.le).Universal) ∈ Usup _ δ γ :=
    (c.mem_usup_smul_iff hψ hδ hρ g w).mpr ((hmemH _).mp hy)
  have h1 := (Subgroup.mem_normalizer_iff.mp (hN hz) _).mp hwU
  have hzw : (z : (puAmalgam h.le).Universal) * w * (z : (puAmalgam h.le).Universal)⁻¹ ∈
      Uloc h.le L δ := (Subgroup.mem_normalizer_iff.mp (hψ.1 z.2) _).mp w.2
  apply hey
  rw [← natVec_conj hψ z w ⟨_, hzw⟩ rfl]
  exact (hmemH _).mpr ((c.mem_usup_smul_iff hψ hδ hρ g ⟨_, hzw⟩).mp h1)

theorem exists_isGoodPath_of_ctx :
    ∀ n : ℕ, ∃ p : ℕ → Vtx (puAmalgam c.hyp.le), IsGoodPath _ p (8 + 2 * n) :=
  exists_isGoodPath c.hyp c.b8 c.exStr c.c444 fun _ _ hc => c.exists_adj_not_le_normalizer hc

theorem exists_extend {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ} (hp : IsGoodPath _ p N)
    (hN : 8 ≤ N) (hNe : Even N) (n : ℕ) :
    ∃ p' : ℕ → Vtx (puAmalgam c.hyp.le), (∀ i, i ≤ N → p' i = p i) ∧
      IsGoodPath _ p' (N + 2 * n) := by
  induction n with
  | zero => exact ⟨p, fun _ _ => rfl, hp⟩
  | succ n ih =>
    obtain ⟨p₁, hp₁e, hp₁⟩ := ih
    obtain ⟨p₂, hp₂e, hp₂⟩ := hp₁.extend c.hyp c.b8 c.c444
      (fun _ _ hc => c.exists_adj_not_le_normalizer hc) (by omega)
      (hNe.add (even_two_mul n))
    exact ⟨p₂, fun i hi => (hp₂e i (by omega)).trans (hp₁e i hi), by
      rwa [show N + 2 * (n + 1) = N + 2 * n + 2 by omega]⟩

end Ctx

end CFSG.Quasithin.MS93.S45
