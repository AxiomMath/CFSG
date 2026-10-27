module

public import CFSG.Quasithin.MS93.MSPSix
public import CFSG.Quasithin.MS93.MSPHeis
public import CFSG.Quasithin.MS93.MSPQuad
public import CFSG.Quasithin.MS93.S5AGeo2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatContract

public section

namespace CFSG.Quasithin.MS93.S51

open Matrix MSP CFSG.LocalAnalysis.ComponentInitial
open scoped LinearAlgebra.Projectivization

variable {F : Type} [Field F]

abbrev pE₂ (F : Type) [Field F] : Submodule F (V4 F) := F ∙ e₂ F

theorem isPoint_pE₂ : IsPoint (pE₂ F) := isPoint_span e₂_ne_zero

@[expose] def xMat [CharP F 2] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 1], by rw [Matrix.det_fin_two_of]; simp [CharTwo.neg_eq]⟩

@[expose] noncomputable def xBar (F : Type) [Field F] [CharP F 2] : Sp4 F := levHom₂ xMat

variable [CharP F 2]

theorem xBar_mulVec (v : V4 F) :
    mat (xBar F) *ᵥ v = v (.inl 0) • e₁ F + v (.inr 1) • e₂ F + v (.inr 0) • f₁ F +
      (v (.inl 1) + v (.inr 1)) • f₂ F := by
  rw [xBar, mat_levHom₂, iotaM_mulVec]
  simp [xMat]

theorem xBar_mem_lev₂ : xBar F ∈ lev₂ F := by
  rw [← range_levHom₂]
  exact ⟨_, rfl⟩

theorem xBar_mulVec_e₂ : mat (xBar F) *ᵥ e₂ F = f₂ F := by
  rw [xBar_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem xBar_mulVec_f₂ : mat (xBar F) *ᵥ f₂ F = e₂ F + f₂ F := by
  rw [xBar_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem xBar_mulVec_e₁ : mat (xBar F) *ᵥ e₁ F = e₁ F := by
  rw [xBar_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

theorem xBar_pow_three : xBar F ^ 3 = 1 := by
  refine ext_mulVec fun v => ?_
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [pow_succ, pow_succ, pow_one, mat_mul_mulVec, mat_mul_mulVec, xBar_mulVec, xBar_mulVec,
    xBar_mulVec, mat_one, one_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp <;> ring_nf <;> (try simp [h2])
  linear_combination v (.inr 1) * h2

theorem xBar_ne_one : xBar F ≠ 1 := by
  intro h
  have := congrArg (fun g => mat g *ᵥ e₂ F) h
  simp only [xBar_mulVec_e₂, mat_one, one_mulVec] at this
  have h' := congrFun this (.inr 1)
  simp at h'

theorem xBar_inv_mulVec_e₂ : mat (xBar F)⁻¹ *ᵥ e₂ F = e₂ F + f₂ F := by
  have h3 : (xBar F)⁻¹ = xBar F * xBar F := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ', xBar_pow_three]
  rw [h3, mat_mul_mulVec, xBar_mulVec_e₂, xBar_mulVec_f₂]

theorem eq_top_of_qPoint_pE₂_le {Y : Subgroup (Sp4 F)} (hQ : qPoint (pE₂ F) ≤ Y)
    {y : Sp4 F} (hy : y ∈ Y) (hopp : form F (e₂ F) (mat y *ᵥ e₂ F) ≠ 0) : Y = ⊤ := by
  have hx0 : mat y *ᵥ e₂ F ≠ 0 := fun h => hopp (by rw [h, map_zero])
  have hp' : IsPoint (F ∙ (mat y *ᵥ e₂ F)) := isPoint_span hx0
  have hmap : (pE₂ F).map (mulVecLin (mat y)) = F ∙ (mat y *ᵥ e₂ F) := by
    rw [Submodule.map_span, Set.image_singleton, mulVecLin_apply]
  have hQ' : qPoint (F ∙ (mat y *ᵥ e₂ F)) ≤ Y := by
    rw [← hmap, ← qPoint_map_conj]
    rintro _ ⟨x, hx, rfl⟩
    exact Y.mul_mem (Y.mul_mem hy (hQ hx)) (Y.inv_mem hy)
  have hnot : ¬ F ∙ (mat y *ᵥ e₂ F) ≤ perp (pE₂ F) := by
    rw [Submodule.span_singleton_le_iff_mem, mem_perp_span]
    exact hopp
  rw [eq_top_iff, ← qPoint_sup_qPoint_eq_top isPoint_pE₂ hp' hnot]
  exact sup_le hQ hQ'

theorem form_e₂_xBar : form F (e₂ F) (mat (xBar F) *ᵥ e₂ F) ≠ 0 := by
  rw [xBar_mulVec_e₂, form_e₂]
  simp

theorem form_e₂_xBar_inv : form F (e₂ F) (mat (xBar F)⁻¹ *ᵥ e₂ F) ≠ 0 := by
  rw [xBar_inv_mulVec_e₂, form_e₂]
  simp

theorem map_pt₀_wAlpha : (pt₀ F).map (mulVecLin (mat (wAlpha F))) = pE₂ F := by
  have h : mat (wAlpha F) *ᵥ e₁ F = e₂ F := by
    rw [wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  rw [pt₀_eq_span, Submodule.map_span, Set.image_singleton, mulVecLin_apply, h]

theorem qPoint_pE₂_le [Finite F] {Y : Subgroup (Sp4 F)} (hQ : Q₁ F ≤ Y) (hw : wAlpha F ∈ Y)
    {y : Sp4 F} (hy : y ∈ Y) (hy₁ : mat y *ᵥ e₁ F = e₁ F) (hy₂ : mat y *ᵥ e₂ F ∉ ln₀ F) :
    qPoint (pE₂ F) ≤ Y := by
  set l' := (ln₀ F).map (mulVecLin (mat y)) with hl'
  have hl'line : IsLine l' := isLine_map isLine_ln₀ y
  have hpl' : pt₀ F ≤ l' := by
    rw [pt₀_eq_span, Submodule.span_singleton_le_iff_mem]
    exact ⟨e₁ F, pt₀_le_ln₀ (by rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _),
      by rw [mulVecLin_apply, hy₁]⟩
  have he₂ : e₂ F ∈ ln₀ F := mem_ln₀.2 (by simp)
  have hne : ln₀ F ≠ l' := fun h => hy₂ (h ▸ ⟨e₂ F, he₂, rfl⟩)
  have hQ' : qLine l' ≤ Y := by
    rw [hl', qLine_map]
    rintro _ ⟨x, hx, rfl⟩
    exact Y.mul_mem (Y.mul_mem hy (hQ hx)) (Y.inv_mem hy)
  have hQ₂ : qPoint (pt₀ F) ≤ Y := by
    rw [← S5.qLine_inf_qPoint_sup isPoint_pt₀ isLine_ln₀ hl'line hne pt₀_le_ln₀ hpl']
    exact sup_le (inf_le_left.trans hQ) (inf_le_left.trans hQ')
  rw [← map_pt₀_wAlpha, ← qPoint_map_conj]
  rintro _ ⟨x, hx, rfl⟩
  exact Y.mul_mem (Y.mul_mem hw (hQ₂ hx)) (Y.inv_mem hw)

omit [CharP F 2] in
theorem levHom₂_unipotent (t : F) :
    levHom₂ (SL2MinimalFaithful.unipotent t) = transv (e₂ F) t := by
  refine ext_mulVec fun v => ?_
  rw [mat_levHom₂, iotaM_mulVec, transv_mulVec, form_e₂]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [SL2MinimalFaithful.coe_unipotent]

omit [CharP F 2] in
theorem map_rootGrp_pt0 :
    (QuasithinUnique.Setup.Campbell.rootGrp
      (QuasithinUnique.Setup.Campbell.pt0 : ℙ F (Fin 2 → F))).map levHom₂ = xPoint (pE₂ F) := by
  rw [QuasithinUnique.Setup.Campbell.rootGrp_pt0]
  ext g
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    have : levHom₂ (SL2MinimalFaithful.unipotentHom t) = transv (e₂ F) (Multiplicative.toAdd t) :=
      levHom₂_unipotent _
    rw [this]
    exact transv_mem_xPoint _ _
  · intro hg
    obtain ⟨c, rfl⟩ := (mem_xPoint_span e₂_ne_zero).1 hg
    exact ⟨SL2MinimalFaithful.unipotentHom (Multiplicative.ofAdd c), ⟨_, rfl⟩,
      levHom₂_unipotent c⟩

omit [CharP F 2] in
theorem xPoint_pE₂_le_lev₂ : xPoint (pE₂ F) ≤ lev₂ F := by
  rw [← map_rootGrp_pt0, ← range_levHom₂]
  exact Subgroup.map_le_range _ _

variable [Finite F]

omit [CharP F 2] in
theorem le_normalizer_or_eq_lev₂ {Y : Subgroup (Sp4 F)} (hYl : Y ≤ lev₂ F)
    (hXY : xPoint (pE₂ F) ≤ Y) :
    Y ≤ Subgroup.normalizer (xPoint (pE₂ F) : Set (Sp4 F)) ∨ Y = lev₂ F := by
  classical
  set Y' := Y.comap levHom₂ with hY'
  have hR : QuasithinUnique.Setup.Campbell.rootGrp
      (QuasithinUnique.Setup.Campbell.pt0 : ℙ F (Fin 2 → F)) ≤ Y' := by
    rw [← Subgroup.map_le_iff_le_comap, map_rootGrp_pt0]
    exact hXY
  have hYmap : Y'.map levHom₂ = Y := by
    rw [Subgroup.map_comap_eq, range_levHom₂, inf_eq_right.2 hYl]
  by_cases hN : Y' ≤ Subgroup.normalizer (QuasithinUnique.Setup.Campbell.rootGrp
      (QuasithinUnique.Setup.Campbell.pt0 : ℙ F (Fin 2 → F)) : Set _)
  · left
    rw [← hYmap, ← map_rootGrp_pt0]
    exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map _)
  · right
    obtain ⟨y, hyY, hyN⟩ := Set.not_subset.1 hN
    have hyp : y • (QuasithinUnique.Setup.Campbell.pt0 : ℙ F (Fin 2 → F)) ≠
        QuasithinUnique.Setup.Campbell.pt0 := fun h =>
      hyN (QuasithinUnique.Setup.Campbell.mem_normalizer_rootGrp_iff.2 h)
    have hsup : QuasithinUnique.Setup.Campbell.rootGrp
        (QuasithinUnique.Setup.Campbell.pt0 : ℙ F (Fin 2 → F)) ⊔
        QuasithinUnique.Setup.Campbell.rootGrp (y • QuasithinUnique.Setup.Campbell.pt0) ≤ Y' := by
      refine sup_le hR ?_
      rw [QuasithinUnique.Setup.Campbell.rootGrp_smul_eq_map]
      rintro _ ⟨x, hx, rfl⟩
      exact Y'.mul_mem (Y'.mul_mem hyY (hR hx)) (Y'.inv_mem hyY)
    rw [QuasithinUnique.Setup.Campbell.rootGrp_sup_rootGrp hyp.symm, top_le_iff] at hsup
    rw [← hYmap, hsup, ← MonoidHom.range_eq_map, range_levHom₂]

omit [CharP F 2] in
theorem card_lev₂ : Nat.card (lev₂ F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← range_levHom₂, ← SL2MinimalFaithful.card_specialLinearGroup_fin_two F]
  exact (Nat.card_congr (MonoidHom.ofInjective levHom₂_injective).toEquiv).symm

theorem eq_xPoint_pE₂_of_isPGroup {P : Subgroup (Sp4 F)} (hP : IsPGroup 2 P)
    (hPl : P ≤ lev₂ F) (hXP : xPoint (pE₂ F) ≤ P) : P = xPoint (pE₂ F) := by
  classical
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [← card_lev₂]
    exact Subgroup.card_dvd_of_le hPl
  have hodd : Odd (Nat.card F ^ 2 - 1) := by
    rw [hq]
    have hpos : 0 < (n : ℕ) := n.2
    have h4 : 2 ≤ (2 ^ (n : ℕ)) ^ 2 := by
      calc 2 ≤ 2 ^ (n : ℕ) := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hpos
        _ ≤ (2 ^ (n : ℕ)) ^ 2 := Nat.le_self_pow (by norm_num) _
    have heven : Even ((2 ^ (n : ℕ)) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow.2 ⟨even_two, by positivity⟩)
    exact Nat.Even.sub_odd (by omega) heven odd_one
  have hcop : Nat.Coprime (Nat.card P) (Nat.card F ^ 2 - 1) := by
    rw [hm]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  have h1 : Nat.card P ∣ Nat.card F := hcop.dvd_of_dvd_mul_right hdvd
  have h2 : Nat.card P ≤ Nat.card (xPoint (pE₂ F)) := by
    rw [card_xPoint isPoint_pE₂]
    exact Nat.le_of_dvd Nat.card_pos h1
  exact (Subgroup.eq_of_le_of_card_ge hXP h2).symm

omit [Finite F] [CharP F 2] in
theorem conj_eq_of_mem_X₂ {z g : Sp4 F} (hz : z ∈ X₂ F) (hg : g ∈ lev₂ F) : g * z * g⁻¹ = z := by
  obtain ⟨c, rfl⟩ := mem_X₂_iff.1 hz
  rw [transv_conj, (mem_lev₂_iff.1 hg).1]

omit [Finite F] [CharP F 2] in
theorem le_normalizer_lev₂ {Zb : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F) :
    Zb ≤ Subgroup.normalizer (lev₂ F : Set (Sp4 F)) := by
  have key : ∀ w ∈ Zb, ∀ g' ∈ lev₂ F, w * g' * w⁻¹ = g' := by
    intro w hw g' hg'
    have h := conj_eq_of_mem_X₂ (hZ hw) hg'
    calc w * g' * w⁻¹ = (g' * w * g'⁻¹) * g' * w⁻¹ := by rw [h]
      _ = g' := by group
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [key z hz g hg]
    exact hg
  · intro hg
    have h1 := key z⁻¹ (Zb.inv_mem hz) _ hg
    rw [show z⁻¹ * (z * g * z⁻¹) * z⁻¹⁻¹ = g by group] at h1
    rw [h1]
    exact hg

omit [Finite F] [CharP F 2] in
theorem lev₂_le_normalizer {Zb : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F) :
    lev₂ F ≤ Subgroup.normalizer (Zb : Set (Sp4 F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [conj_eq_of_mem_X₂ (hZ hz) hg]
    exact hz
  · intro hz
    have h := conj_eq_of_mem_X₂ (hZ hz) ((lev₂ F).inv_mem hg)
    rw [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h
    rw [h]
    exact hz

omit [Finite F] [CharP F 2] in
theorem eq_sup_inf_lev₂ {Zb Y : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F) (hZY : Zb ≤ Y)
    (hYF : Y ≤ Zb ⊔ lev₂ F) : Y = Zb ⊔ (Y ⊓ lev₂ F) := by
  refine le_antisymm (fun y hy => ?_) (sup_le hZY inf_le_left)
  have hmem : y ∈ ((Zb ⊔ lev₂ F : Subgroup (Sp4 F)) : Set (Sp4 F)) := hYF hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (le_normalizer_lev₂ hZ)] at hmem
  obtain ⟨z, hz, l, hl, rfl⟩ := hmem
  have hlY : l ∈ Y := by
    have : l = z⁻¹ * (z * l) := by group
    rw [this]
    exact Y.mul_mem (Y.inv_mem (hZY hz)) hy
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right ⟨hlY, hl⟩)

omit [CharP F 2] in
theorem le_normalizer_or_eq_Fbar {Zb Y : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F)
    (hJY : Zb ⊔ xPoint (pE₂ F) ≤ Y) (hYF : Y ≤ Zb ⊔ lev₂ F) :
    Y ≤ Subgroup.normalizer ((Zb ⊔ xPoint (pE₂ F) : Subgroup (Sp4 F)) : Set (Sp4 F)) ∨
      Y = Zb ⊔ lev₂ F := by
  have hZY : Zb ≤ Y := le_sup_left.trans hJY
  have hdec := eq_sup_inf_lev₂ hZ hZY hYF
  rcases le_normalizer_or_eq_lev₂ (inf_le_right : Y ⊓ lev₂ F ≤ lev₂ F)
      (le_inf (le_sup_right.trans hJY) xPoint_pE₂_le_lev₂) with hN | hE
  · left
    rw [hdec]
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun y hy => ?_
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨lev₂_le_normalizer hZ hy.2, hN hy⟩
  · right
    rw [hdec, hE]

theorem eq_Jbar_of_isPGroup {Zb P : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F) (hP : IsPGroup 2 P)
    (hJP : Zb ⊔ xPoint (pE₂ F) ≤ P) (hPF : P ≤ Zb ⊔ lev₂ F) : P = Zb ⊔ xPoint (pE₂ F) := by
  have hdec := eq_sup_inf_lev₂ hZ (le_sup_left.trans hJP) hPF
  have h := eq_xPoint_pE₂_of_isPGroup (hP.to_le inf_le_left) inf_le_right
    (le_inf (le_sup_right.trans hJP) xPoint_pE₂_le_lev₂)
  rw [hdec, h]

omit [Finite F] [CharP F 2] in
theorem pE₂_le_ln₀ : pE₂ F ≤ ln₀ F := by
  rw [Submodule.span_singleton_le_iff_mem, mem_ln₀]
  simp

omit [Finite F] [CharP F 2] in
theorem Jbar_le_Q₁ {Zb : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F) : Zb ⊔ xPoint (pE₂ F) ≤ Q₁ F :=
  sup_le (hZ.trans X₂_le_Q₁) (xPoint_le_qLine isLine_ln₀ pE₂_le_ln₀)

omit [Finite F] in
theorem xBar_not_mem_normalizer {Zb : Subgroup (Sp4 F)} (hZ : Zb ≤ X₂ F) :
    xBar F ∉ Subgroup.normalizer ((Zb ⊔ xPoint (pE₂ F) : Subgroup (Sp4 F)) : Set (Sp4 F)) := by
  intro hN
  have hmap : (xPoint (pE₂ F)).map (MulAut.conj (xBar F)).toMonoidHom = xPoint (F ∙ f₂ F) := by
    rw [xPoint, fixer_map_conj, ← perp_map, Submodule.map_span, Set.image_singleton,
      mulVecLin_apply, xBar_mulVec_e₂]
  have hle : xPoint (F ∙ f₂ F) ≤ Q₁ F := by
    rw [← hmap]
    rintro _ ⟨x, hx, rfl⟩
    exact Jbar_le_Q₁ hZ ((Subgroup.mem_normalizer_iff.1 hN x).1 (Subgroup.mem_sup_right hx))
  have h := (xPoint_le_qLine_iff (isPoint_span f₂_ne_zero) isLine_ln₀).1 hle
  have hf : f₂ F ∈ ln₀ F := h (Submodule.mem_span_singleton_self _)
  simp [mem_ln₀] at hf

omit [Finite F] [CharP F 2] in
theorem Q₁_le_normalizer {A : Subgroup (Sp4 F)} (hA : A ≤ Q₁ F) :
    Q₁ F ≤ Subgroup.normalizer (A : Set (Sp4 F)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [Q₁_comm hg (hA hx), mul_inv_cancel_right]
    exact hx
  · intro hx
    have hxQ : x ∈ Q₁ F := by
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this]
      exact (Q₁ F).mul_mem ((Q₁ F).mul_mem ((Q₁ F).inv_mem hg) (hA hx)) hg
    rwa [Q₁_comm hg hxQ, mul_inv_cancel_right] at hx

omit [Finite F] in
theorem wAlpha_mem_normalizer :
    wAlpha F ∈ Subgroup.normalizer ((X₂ F ⊔ xPoint (pE₂ F) : Subgroup (Sp4 F)) : Set (Sp4 F)) := by
  have h1 : (xPoint (pt₀ F)).map (MulAut.conj (wAlpha F)).toMonoidHom = xPoint (pE₂ F) := by
    rw [xPoint, fixer_map_conj, ← perp_map, map_pt₀_wAlpha]
  have he : mat (wAlpha F) *ᵥ e₂ F = e₁ F := by
    rw [wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have h2 : (xPoint (pE₂ F)).map (MulAut.conj (wAlpha F)).toMonoidHom = xPoint (pt₀ F) := by
    rw [xPoint, fixer_map_conj, ← perp_map, Submodule.map_span, Set.image_singleton,
      mulVecLin_apply, he, ← pt₀_eq_span]
  rw [mem_normalizer_iff_map_conj, Subgroup.map_sup, h1, h2, sup_comm]

theorem eq_bot_of_normal_isPGroup_sl2 (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    [hNn : N.Normal] (hN : IsPGroup 2 N) : N = ⊥ := by
  set e := QuasithinUnique.Setup.Campbell.slGammaEquiv F with he
  set A : Subgroup (QuasithinUnique.Setup.Campbell.Gamma F) :=
    (N.map e.toMonoidHom).map (QuasithinUnique.Setup.Campbell.slGamma F).subtype with hA
  have hA2 : IsPGroup 2 A := (hN.map _).map _
  have hAbot : A = ⊥ := by
    refine QuasithinUnique.Setup.Campbell.eq_bot_of_normal_isPGroup A hA2 ?_
    rintro g hg _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    obtain ⟨B, hB⟩ := e.surjective ⟨g, hg⟩
    refine ⟨e (B * n * B⁻¹), ⟨B * n * B⁻¹, hNn.conj_mem n hn B, rfl⟩, ?_⟩
    have hg' : g = ((e B : QuasithinUnique.Setup.Campbell.slGamma F) :
        QuasithinUnique.Setup.Campbell.Gamma F) := by rw [hB]
    rw [hg']
    simp [map_mul, map_inv]
  rw [hA, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hAbot
  exact (Subgroup.map_eq_bot_iff_of_injective N (f := e.toMonoidHom) e.injective).1 hAbot

omit [Finite F] in
theorem xBar_eq_transv_mul : xBar F = transv (e₂ F) 1 * transv (f₂ F) 1 := by
  refine ext_mulVec fun v => ?_
  rw [xBar_mulVec, mat_mul_mulVec, transv_mulVec, transv_mulVec, form_e₂, form_f₂]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp [CharTwo.neg_eq] <;> ring_nf
  simp [CharTwo.two_eq_zero]

omit [Field F] [CharP F 2] [Finite F] in
theorem isThreeCycle_of_isSwap_mul {α : Type*} [DecidableEq α] [Fintype α] {σ₁ σ₂ : Equiv.Perm α}
    (h1 : σ₁.IsSwap) (h2 : σ₂.IsSwap) (hne : σ₁ * σ₂ ≠ 1) (h3 : (σ₁ * σ₂) ^ 3 = 1) :
    (σ₁ * σ₂).IsThreeCycle := by
  obtain ⟨a, b, hab, rfl⟩ := h1
  obtain ⟨c, d, hcd, rfl⟩ := h2
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      exact absurd (Equiv.swap_mul_self a b) hne
    · exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hcd hbd
  by_cases had : a = d
  · subst had
    rw [Equiv.swap_comm c a]
    by_cases hbc : b = c
    · subst hbc
      exact absurd (by rw [Equiv.swap_comm b a, Equiv.swap_mul_self]) hne
    · exact Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  by_cases hbc : b = c
  · subst hbc
    rw [Equiv.swap_comm a b]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hcd had
  by_cases hbd : b = d
  · subst hbd
    rw [Equiv.swap_comm a b, Equiv.swap_comm c b]
    exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) (Ne.symm hcd) hac
  exfalso
  have hdis : (Equiv.swap a b).Disjoint (Equiv.swap c d) :=
    Equiv.Perm.disjoint_swap_swap (by simp [hab, hac, had, hbc, hbd, hcd])
  have hsq : (Equiv.swap a b * Equiv.swap c d) ^ 2 = 1 := by
    rw [sq, show Equiv.swap a b * Equiv.swap c d * (Equiv.swap a b * Equiv.swap c d) =
      Equiv.swap a b * (Equiv.swap c d * Equiv.swap a b) * Equiv.swap c d by group,
      ← hdis.commute.eq]
    simp
  apply hne
  calc Equiv.swap a b * Equiv.swap c d = (Equiv.swap a b * Equiv.swap c d) ^ 3 *
        ((Equiv.swap a b * Equiv.swap c d) ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, hsq, inv_one, one_mul]

theorem commutator_le_of_xBar_mem {N : Subgroup (Sp4 F)} [hN : N.Normal] (hx : xBar F ∈ N) :
    commutator (Sp4 F) ≤ N := by
  classical
  by_cases hq : Nat.card F = 2
  · obtain ⟨c⟩ := nonempty_ringEquiv_of_card_two hq
    set θ := CFSG.Quasithin.B5FinSp.theta c with hθ
    have h1 : (θ.symm (transv (e₂ F) 1)).IsSwap := isSwap_theta_symm_transv c e₂_ne_zero
    have h2 : (θ.symm (transv (f₂ F) 1)).IsSwap := isSwap_theta_symm_transv c f₂_ne_zero
    have hτ : θ.symm (xBar F) = θ.symm (transv (e₂ F) 1) * θ.symm (transv (f₂ F) 1) := by
      rw [xBar_eq_transv_mul, map_mul]
    have hτ1 : θ.symm (xBar F) ≠ 1 := fun h => xBar_ne_one (θ.symm.injective (h.trans
      (map_one θ.symm).symm))
    have hτ3 : θ.symm (xBar F) ^ 3 = 1 := by rw [← map_pow, xBar_pow_three, map_one]
    rw [hτ] at hτ1 hτ3
    have h3 := isThreeCycle_of_isSwap_mul h1 h2 hτ1 hτ3
    rw [← hτ] at h3
    set N' := N.comap θ.toMonoidHom with hN'
    have hN'n : N'.Normal := hN.comap _
    have hτN : θ.symm (xBar F) ∈ N' := by
      show θ (θ.symm (xBar F)) ∈ N
      rw [MulEquiv.apply_symm_apply]
      exact hx
    have h3c : ∀ σ : Equiv.Perm (Fin 6), σ.IsThreeCycle → σ ∈ N' := by
      intro σ hσ
      obtain ⟨g, hg⟩ := isConj_iff.1 (Equiv.Perm.isConj_iff_cycleType_eq.2 (h3.trans hσ.symm))
      rw [← hg]
      exact hN'n.conj_mem _ hτN g
    have hA : alternatingGroup (Fin 6) ≤ N' := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
      exact (Subgroup.closure_le N').2 h3c
    intro g hg
    rw [mem_commutator_iff_sign c] at hg
    have h4 := hA (Equiv.Perm.mem_alternatingGroup.2 hg)
    have h5 : θ (θ.symm g) ∈ N := h4
    rwa [MulEquiv.apply_symm_apply] at h5
  · have hq1 : 1 < Nat.card F := Finite.one_lt_card
    have hq2 : 2 < Nat.card F := by omega
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    have h2n : 2 ≤ (n : ℕ) := by
      by_contra h
      have h1 : (n : ℕ) = 1 := by have := n.pos; omega
      rw [hcard, h1] at hq
      exact hq rfl
    have hq4 : 4 ≤ Fintype.card F := by
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h2n
    have h4 : ∃ s : Finset F, s.card = 4 := by
      obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (n := 4) (s := (Finset.univ : Finset F))
        (by rw [Finset.card_univ]; exact hq4)
      exact ⟨t, ht⟩
    set N' := N.comap (levHom₂ (F := F)) with hN'
    have hN'n : N'.Normal := hN.comap _
    have hxN' : (xMat : Matrix.SpecialLinearGroup (Fin 2) F) ∈ N' := hx
    have hN'ne : N' ≠ ⊥ := by
      intro h
      rw [h, Subgroup.mem_bot] at hxN'
      apply xBar_ne_one (F := F)
      rw [xBar, hxN', map_one]
    have htop := QuasithinUnique.Setup.Campbell.normal_sl2_eq_top h4 N' hN'ne
    have hlev : lev₂ F ≤ N := by
      rw [← range_levHom₂]
      rintro _ ⟨A, rfl⟩
      have : A ∈ N' := by rw [htop]; trivial
      exact this
    obtain ⟨g, hg⟩ := exists_four_conj_xPoint hq2 isPoint_pE₂
    have htopN : N = ⊤ := by
      rw [eq_top_iff, ← hg]
      refine iSup_le fun i => ?_
      rintro _ ⟨x, hx', rfl⟩
      exact hN.conj_mem x (hlev (xPoint_pE₂_le_lev₂ hx')) (g i)
    rw [htopN]
    exact le_top

omit [Finite F] in
theorem wAlpha_mulVec_e₁ : mat (wAlpha F) *ᵥ e₁ F = e₂ F := by
  rw [wAlpha_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

omit [Finite F] in
theorem wAlpha_mulVec_e₂ : mat (wAlpha F) *ᵥ e₂ F = e₁ F := by
  rw [wAlpha_mulVec]
  refine ext4 ?_ ?_ ?_ ?_ <;> simp

omit [Finite F] [CharP F 2] in
theorem map_span_mat (g : Sp4 F) (x : V4 F) :
    (F ∙ x).map (mulVecLin (mat g)) = F ∙ (mat g *ᵥ x) := by
  rw [Submodule.map_span, Set.image_singleton, mulVecLin_apply]

omit [Finite F] in
theorem exists_map_pE₂_eq {p : Submodule F (V4 F)} (hp : IsPoint p) :
    ∃ g : Sp4 F, (pE₂ F).map (mulVecLin (mat g)) = p := by
  obtain ⟨g₀, hg₀⟩ := exists_map_pt₀_eq hp
  refine ⟨g₀ * wAlpha F, ?_⟩
  rw [map_span_mat, mat_mul_mulVec, wAlpha_mulVec_e₂, ← hg₀, pt₀_eq_span, map_span_mat]

omit [Finite F] in
theorem exists_map_pE₂_pt₀_eq {p₁ p₂ : Submodule F (V4 F)} (hp₁ : IsPoint p₁) (hp₂ : IsPoint p₂)
    (hne : p₁ ≠ p₂) (hperp : p₂ ≤ perp p₁) :
    ∃ g : Sp4 F, (pE₂ F).map (mulVecLin (mat g)) = p₁ ∧ (pt₀ F).map (mulVecLin (mat g)) = p₂ := by
  have hperp' : p₁ ≤ perp p₂ := by
    intro x hx
    rw [mem_perp]
    intro w hw
    rw [form_swap, neg_eq_zero]
    exact (mem_perp.1 (hperp hw)) x hx
  have hl : IsLine (p₂ ⊔ p₁) := S5.isLine_sup hp₂ hp₁ (Ne.symm hne) hperp'
  obtain ⟨g₀, h₁, h₂⟩ := exists_map_flag (show IsFlag p₂ (p₂ ⊔ p₁) from ⟨hp₂, hl, le_sup_left⟩)
  obtain ⟨v, hv0, hv⟩ := exists_eq_span_of_isPoint hp₁
  set w := mat g₀⁻¹ *ᵥ v with hw
  have hwl : w ∈ ln₀ F := by
    have : v ∈ (ln₀ F).map (mulVecLin (mat g₀)) := by
      rw [h₂]
      exact Submodule.mem_sup_right (hv ▸ Submodule.mem_span_singleton_self v)
    rw [mem_map_mulVecLin] at this
    exact this
  have hwp : w ∉ pt₀ F := by
    intro hwp
    apply hne
    have h1 : v ∈ p₂ := by
      rw [← h₁, mem_map_mulVecLin]
      exact hwp
    have h2 : p₁ ≤ p₂ := by rw [hv, Submodule.span_singleton_le_iff_mem]; exact h1
    exact Submodule.eq_of_le_of_finrank_eq h2 (by rw [hp₁, hp₂])
  rw [mem_ln₀] at hwl
  have hw2 : w (.inl 1) ≠ 0 := fun h => hwp (mem_pt₀.2 ⟨h, hwl.1, hwl.2⟩)
  set a := w (.inl 0) / w (.inl 1) with ha
  set h := wAlpha F * muE a * wAlpha F with hh
  have hh₁ : mat h *ᵥ e₁ F = e₁ F := by
    rw [hh, mat_mul_mulVec, mat_mul_mulVec, wAlpha_mulVec_e₁, muE_mulVec, wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
  have hh₂ : mat h *ᵥ e₂ F = (w (.inl 1))⁻¹ • w := by
    rw [hh, mat_mul_mulVec, mat_mul_mulVec, wAlpha_mulVec_e₂, muE_mulVec, wAlpha_mulVec]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp [ha, hwl.1, hwl.2, hw2]
    field_simp
  refine ⟨g₀ * h, ?_, ?_⟩
  · rw [map_span_mat, mat_mul_mulVec, hh₂, mulVec_smul, hw, mat_mulVec_inv, hv]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (inv_ne_zero hw2)) v
  · rw [pt₀_eq_span, map_span_mat, mat_mul_mulVec, hh₁, ← map_span_mat, ← pt₀_eq_span, h₁]

end CFSG.Quasithin.MS93.S51
