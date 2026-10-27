module

import CFSG.Quasithin.MS93.S4AFMain
public import CFSG.Quasithin.MS93.S45IV

public section

namespace CFSG.Quasithin.MS93.S45Q4

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S45
open scoped Matrix

section SL3

variable {F : Type} [Field F]

theorem mem_normalizer_of_mulVec_mem [Finite F] {A : Subgroup (SL3 F)}
    (hA : Nat.card A = Nat.card F ^ 2) (hfc : fixN A = commN A)
    (h2 : Module.finrank F (fixN A) = 2) {s : SL3 F}
    (hs : ∀ w ∈ fixN A, ((s : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ fixN A) :
    s ∈ Subgroup.normalizer (A : Set (SL3 F)) := by
  set W := fixN A with hW
  have hinv : ∀ (g : SL3 F) (y : Fin 3 → F),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y)
        = y := fun g y => by
    rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, Matrix.one_mulVec]
  let A' : Subgroup (SL3 F) :=
    { carrier := {g | (∀ w ∈ W, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w) ∧
        ∀ x, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ W}
      mul_mem' := by
        rintro g k ⟨hg1, hg2⟩ ⟨hk1, hk2⟩
        refine ⟨fun w hw => ?_, fun x => ?_⟩
        · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec, hk1 w hw, hg1 w hw]
        · rw [coe_mul_SL3, ← Matrix.mulVec_mulVec]
          have := W.add_mem (hg2 (((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x)) (hk2 x)
          rwa [sub_add_sub_cancel] at this
      one_mem' := ⟨fun w _ => by simp, fun x => by simp⟩
      inv_mem' := by
        rintro g ⟨hg1, hg2⟩
        have key : ∀ y, ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y - y ∈ W := by
          intro y
          have h1 := hg2 (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y)
          rw [hinv] at h1
          have := W.neg_mem h1
          rwa [neg_sub] at this
        refine ⟨fun w hw => ?_, key⟩
        have hy : ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
          have := W.add_mem (key w) hw
          rwa [sub_add_cancel] at this
        have := hg1 _ hy
        rw [hinv] at this
        exact this.symm }
  have hmemA' : ∀ g : SL3 F, g ∈ A' ↔ (∀ w ∈ W, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w) ∧
      ∀ x, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x ∈ W := fun _ => Iff.rfl
  have hAA' : A ≤ A' := fun a ha =>
    (hmemA' a).mpr ⟨fun w hw => hw a ha, fun x => by rw [hfc]; exact sub_mem_commN ha x⟩
  have hWtop : W ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h2
    omega
  obtain ⟨e, -, heW⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hWtop)
  have hspan := sup_span_eq_top h2 heW
  let f : ↥A' → ↥W := fun g =>
    ⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e - e, ((hmemA' g).mp g.2).2 e⟩
  have hf : Function.Injective f := by
    intro g k hgk
    have he : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e =
        ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ e := by
      have := congrArg Subtype.val hgk
      simpa [f] using this
    have hall : ∀ x, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
        ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x := by
      intro x
      have hx : x ∈ LinearMap.eqLocus (Matrix.toLin' ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F))
          (Matrix.toLin' ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F)) := by
        have hle : W ⊔ Submodule.span F {e} ≤ LinearMap.eqLocus
            (Matrix.toLin' ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F))
            (Matrix.toLin' ((k : SL3 F) : Matrix (Fin 3) (Fin 3) F)) := by
          refine sup_le (fun w hw => ?_) ?_
          · rw [LinearMap.mem_eqLocus, Matrix.toLin'_apply, Matrix.toLin'_apply,
              ((hmemA' g).mp g.2).1 w hw, ((hmemA' k).mp k.2).1 w hw]
          · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
              LinearMap.mem_eqLocus, Matrix.toLin'_apply, Matrix.toLin'_apply]
            exact he
        rw [hspan] at hle
        exact hle Submodule.mem_top
      rwa [LinearMap.mem_eqLocus, Matrix.toLin'_apply, Matrix.toLin'_apply] at hx
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.ext_of_mulVec_single fun i => hall _
  have : Finite ↥A' := Finite.of_injective f hf
  have hcard : Nat.card ↥A' ≤ Nat.card F ^ 2 := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Module.natCard_eq_pow_finrank (K := F) (V := ↥W), h2] at this
  have hEq : A = A' := Subgroup.eq_of_le_of_card_ge hAA' (by rw [hA]; exact hcard)
  have hsW : ∀ w ∈ W, ((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
    set σ := Matrix.SpecialLinearGroup.toLin' s with hσ
    have hle : W.map (σ : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) ≤ W := by
      rintro _ ⟨w, hw, rfl⟩
      have := hs w hw
      simpa [hσ, Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using this
    have heq : W.map (σ : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) = W :=
      Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq σ W)
    intro w hw
    rw [← heq] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    have e1 : ((s⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        ((σ : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) w') = w' := by
      simp only [hσ, LinearEquiv.coe_coe, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.toLin'_apply]
      rw [Matrix.mulVec_mulVec, ← coe_mul_SL3, inv_mul_cancel, coe_one_SL3, Matrix.one_mulVec]
    rw [e1]
    exact hw'
  have key : ∀ t : SL3 F, (∀ w ∈ W, ((t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) →
      (∀ w ∈ W, ((t⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W) →
      ∀ a ∈ A', t * a * t⁻¹ ∈ A' := by
    intro t ht ht' a ha
    obtain ⟨ha1, ha2⟩ := (hmemA' a).mp ha
    refine (hmemA' _).mpr ⟨fun w hw => ?_, fun x => ?_⟩
    · rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ha1 _ (ht' w hw), hinv]
    · have h1 := ht _ (ha2 (((t⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x))
      rw [Matrix.mulVec_sub, hinv] at h1
      rw [coe_mul_SL3, coe_mul_SL3, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro a
  rw [hEq]
  refine ⟨key s hs hsW a, fun ha => ?_⟩
  have := key s⁻¹ hsW (by rw [inv_inv]; exact hs) _ ha
  simpa [mul_assoc] using this

end SL3

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : S45.Ctx M T L φ)
include c

theorem mem_normalizer_qv_of_usup {δ ρ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) {g : (puAmalgam c.hyp.le).Universal}
    (hg : g ∈ stab (puAmalgam c.hyp.le) δ)
    (hgU : g ∈ Subgroup.normalizer (Usup (puAmalgam c.hyp.le) δ ρ : Set _)) :
    g ∈ Subgroup.normalizer (Qv (puAmalgam c.hyp.le) ρ : Set _) := by
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.hyp c.via hδ
  obtain ⟨-, hcard, hfc, h2⟩ := c.natImage_qv_props hδ hρ hψ
  have hA : Subgroup.zpowers g ≤ stab (puAmalgam c.hyp.le) δ := Subgroup.zpowers_le.mpr hg
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (Usup (puAmalgam c.hyp.le) δ ρ : Set _) :=
    Subgroup.zpowers_le.mpr hgU
  have hfix := (c.le_normalizer_usup_iff hψ hδ hρ hA (c.mem_usup_iff hψ hδ hρ)).mp hN
  have hs : toSL3 ψ ⟨g, hg⟩ ∈ Subgroup.normalizer
      ((natImage ψ (Qv (puAmalgam c.hyp.le) ρ) : Subgroup (SL3 F)) : Set (SL3 F)) := by
    refine mem_normalizer_of_mulVec_mem hcard hfc (by rw [hfc]; exact h2) fun w hw => ?_
    exact hfix _ (mem_natImage.mpr ⟨⟨g, hg⟩, Subgroup.mem_zpowers g, rfl⟩) w hw
  exact c.mem_normalizer_qv_of hδ hρ hψ hs

theorem relIndex_inf_qv_le {δ ρ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) {X : Subgroup (puAmalgam c.hyp.le).Universal}
    (hX : X ≤ Qv _ ρ) (hXc : Nat.card ↥⁅Uloc c.hyp.le L δ, X⁆ ≤ Fintype.card F) :
    (X ⊓ Qv _ δ).relIndex X ≤ Fintype.card F := by
  have h := c.hyp
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hXs : X ≤ stab (puAmalgam h.le) δ := hX.trans (qv_le_stab_of_adj _ hρ.symm)
  have hYC : X ⊓ Qv (puAmalgam h.le) δ =
      X ⊓ Subgroup.centralizer (Uloc h.le L δ : Set (puAmalgam h.le).Universal) := by
    rw [← c.qv_inf_centralizer_uloc hδ hρ, ← inf_assoc, inf_eq_left.mpr hX]
  set E := natImage ψ X with hEdef
  have hET : E ≤ natImage ψ (Qv (puAmalgam h.le) ρ) := natImage_mono hX
  have hT := c.fixN_eq_commN_qv hψ hδ hρ
  have hq := Fintype.one_lt_card (α := F)
  have hqq : Fintype.card F < Fintype.card F ^ 2 := by
    calc Fintype.card F = Fintype.card F * 1 := (mul_one _).symm
      _ < Fintype.card F * Fintype.card F := Nat.mul_lt_mul_of_pos_left hq (by omega)
      _ = Fintype.card F ^ 2 := (sq _).symm
  have hcommE : Module.finrank F ↥(commN E) ≤ 1 := by
    have h1 := card_commutator_eq hψ hXs
    rw [← hEdef, Module.natCard_eq_pow_finrank (K := F) (V := ↥(commN E)),
      Nat.card_eq_fintype_card (α := F)] at h1
    rw [h1] at hXc
    by_contra hlt
    push Not at hlt
    have : Fintype.card F ^ 2 ≤ Fintype.card F ^ Module.finrank F ↥(commN E) :=
      Nat.pow_le_pow_right Fintype.card_pos (by omega)
    omega
  have hEq : Nat.card ↥E ≤ Fintype.card F := by
    have hb := card_le_pow_finrank E
    have hfixE : 2 ≤ Module.finrank F ↥(fixN E) := hT.2 ▸ Submodule.finrank_mono (fixN_anti hET)
    have hexp : (3 - Module.finrank F ↥(fixN E)) * Module.finrank F ↥(commN E) ≤ 1 := by
      calc (3 - Module.finrank F ↥(fixN E)) * Module.finrank F ↥(commN E)
          ≤ 1 * 1 := Nat.mul_le_mul (by omega) hcommE
        _ = 1 := rfl
    rw [Nat.card_eq_fintype_card (α := F)] at hb
    calc Nat.card ↥E ≤ _ := hb
      _ ≤ Fintype.card F ^ 1 := Nat.pow_le_pow_right Fintype.card_pos hexp
      _ = Fintype.card F := pow_one _
  have h1 := card_natImage_mul hψ hXs
  have h2 := Subgroup.relIndex_mul_card (X ⊓ Qv (puAmalgam h.le) δ) X
  have hYX : X ⊓ Qv (puAmalgam h.le) δ ⊓ X = X ⊓ Qv (puAmalgam h.le) δ :=
    inf_eq_left.mpr inf_le_left
  rw [hYX] at h2
  rw [← hYC] at h1
  have : Finite ↥(stab (puAmalgam h.le) δ) := S4A.finite_stab h hδ
  have : Finite ↥(X ⊓ Qv (puAmalgam h.le) δ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans hXs))
  have hpos : 0 < Nat.card ↥(X ⊓ Qv (puAmalgam h.le) δ) := Nat.card_pos
  have : (X ⊓ Qv (puAmalgam h.le) δ).relIndex X = Nat.card ↥E :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
  rw [this]
  exact hEq

theorem le_zm_sup_qv {x x' : Vtx (puAmalgam c.hyp.le)} (hc : IsCritical (puAmalgam c.hyp.le) x x')
    {Y : Subgroup (puAmalgam c.hyp.le).Universal} (hYV : Y ≤ Vv (puAmalgam c.hyp.le) x)
    (hYT : Y ≤ Qv (puAmalgam c.hyp.le) (geo _ x' x 1)) (hZY : ZM (puAmalgam c.hyp.le) x ≤ Y)
    (hW : ¬ Usup (puAmalgam c.hyp.le) x' (geo _ x' x 1) ≤ Vv _ x) :
    Y ≤ ZM (puAmalgam c.hyp.le) x ⊔ Qv _ x' := by
  have h := c.hyp
  have hc' := c.isCritical_symm hc
  have hx' := hc'.1
  have hd := c.dist_of_isCritical hc
  have hd' := c.dist_of_isCritical hc'
  set ρ := geo (puAmalgam h.le) x' x 1 with hρdef
  have hρa : (puAmalgam h.le).treeGraph.Adj x' ρ := adj_geo_one _ (by omega)
  have hYs : Y ≤ stab (puAmalgam h.le) x' := hYT.trans (qv_le_stab_of_adj _ hρa.symm)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hx'
  set E := natImage ψ Y with hEdef
  have hET : E ≤ natImage ψ (Qv (puAmalgam h.le) ρ) := natImage_mono hYT
  have hT := c.fixN_eq_commN_qv hψ hx' hρa
  have hEq : Nat.card ↥E ≤ Fintype.card F := by
    by_contra hlt
    push Not at hlt
    apply hW
    have hE : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hlt
      have := Fintype.one_lt_card (α := F)
      omega
    have hfix : Module.finrank F ↥(fixN E) = 2 := by
      have h1 : 2 ≤ Module.finrank F ↥(fixN E) := hT.2 ▸ Submodule.finrank_mono (fixN_anti hET)
      have h2 : Module.finrank F ↥(fixN E) < 3 := by
        have := Submodule.finrank_lt (fixN_ne_top hE)
        rwa [Module.finrank_fin_fun] at this
      omega
    have hcomm : commN E = fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) := by
      have hle : commN E ≤ fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) := hT.1 ▸ commN_mono hET
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      rw [hT.2]
      by_contra hlt2
      push Not at hlt2
      have hb := card_le_pow_finrank E
      rw [hfix, show 3 - 2 = 1 by rfl, one_mul, Nat.card_eq_fintype_card (α := F)] at hb
      have : Fintype.card F ^ Module.finrank F ↥(commN E) ≤ Fintype.card F ^ 1 :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)
      rw [pow_one] at this
      omega
    intro w hw
    have hwU : w ∈ Uloc h.le L x' := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hx' hρa] at hw; exact hw.1
    have h1 : w ∈ ⁅Uloc h.le L x', Y⁆ := by
      refine (S4A.mem_commutator_iff_natVec hψ hYs ⟨w, hwU⟩).mpr ?_
      rw [← hEdef, hcomm]
      exact (c.mem_usup_iff hψ hx' hρa ⟨w, hwU⟩).mp hw
    have hUn : Uloc h.le L x' ≤ Subgroup.normalizer (Vv (puAmalgam h.le) x : Set _) :=
      (uloc_le_zm h c.full hx').trans ((c.zm_le_qv_geo_one hc).trans
        ((qv_le_stab_of_adj _ (adj_geo_one _ (by omega)).symm).trans
          (stab_le_normalizer_vv h _)))
    have h2 : ⁅Uloc h.le L x', Y⁆ ≤ Vv (puAmalgam h.le) x := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hYV le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp hUn)
    exact h2 h1
  have hZE : natImage ψ (ZM (puAmalgam h.le) x) ≤ E := natImage_mono hZY
  have hcardZ : Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) x)) = Fintype.card F :=
    c.card_natImage_zm hc' hψ
  have hfinE : Finite ↥E := Nat.finite_of_card_ne_zero (by
    have := Nat.card_pos (α := ↥(natImage ψ (ZM (puAmalgam h.le) x)))
    have := Subgroup.card_le_of_le hZE
    omega)
  have hEeq : E = natImage ψ (ZM (puAmalgam h.le) x) :=
    (Subgroup.eq_of_le_of_card_ge hZE (by rw [hcardZ]; exact hEq)).symm
  intro y hy
  have hyE : toSL3 ψ ⟨y, hYs hy⟩ ∈ natImage ψ (ZM (puAmalgam h.le) x) :=
    hEeq ▸ mem_natImage.mpr ⟨⟨y, hYs hy⟩, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := mem_natImage.mp hyE
  have hk : toSL3 ψ (z⁻¹ * ⟨y, hYs hy⟩) = 1 := by rw [map_mul, map_inv, hzy, inv_mul_cancel]
  rw [toSL3_eq_one_iff hψ] at hk
  have hq : (z : (puAmalgam h.le).Universal)⁻¹ * y ∈ Qv (puAmalgam h.le) x' := by
    rw [← S4A.stab_inf_centralizer_uloc h c.via hx']
    refine ⟨(z⁻¹ * ⟨y, hYs hy⟩ : ↥(stab _ _)).2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 := hk v hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc v * ((z : (puAmalgam h.le).Universal)⁻¹ * y) =
        ((z : (puAmalgam h.le).Universal)⁻¹ * y * v * ((z : (puAmalgam h.le).Universal)⁻¹ * y)⁻¹) *
          ((z : (puAmalgam h.le).Universal)⁻¹ * y) := by rw [h1]
      _ = (z : (puAmalgam h.le).Universal)⁻¹ * y * v := by group
  have e : y = (z : (puAmalgam h.le).Universal) * ((z : (puAmalgam h.le).Universal)⁻¹ * y) := by
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hq)

theorem mem_of_mem_bloc {x x' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) x x') {Y : Subgroup (puAmalgam c.hyp.le).Universal}
    (hYV : Y ≤ Vv (puAmalgam c.hyp.le) x)
    (hYi : Y.relIndex (Vv (puAmalgam c.hyp.le) x) ≤ Fintype.card F)
    (hY : Y ≤ ZM (puAmalgam c.hyp.le) x ⊔ Qv _ x') {z : (puAmalgam c.hyp.le).Universal}
    (hzZ : z ∈ ZM (puAmalgam c.hyp.le) x') (hzQ : z ∉ Qv (puAmalgam c.hyp.le) x)
    {v : (puAmalgam c.hyp.le).Universal} (hv : v ∈ Vv (puAmalgam c.hyp.le) x)
    (hvz : v⁻¹ * (z * v * z⁻¹) ∈ Bloc c.hyp.le L x) : v ∈ Y := by
  have h := c.hyp
  have h20 := h.hyp20
  have hc' := c.isCritical_symm hc
  have hM0 := hc.1
  have hM8 := hc'.1
  have hd' := c.dist_of_isCritical hc'
  have hVs : Vv (puAmalgam h.le) x ≤ stab _ x := (c.vv_le_qv' hM0).trans (qv_le_stab _ _)
  obtain ⟨ψ₀, hψ₀s, hψ₀⟩ := exists_natural_Uloc h c.via hM0
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hM0 hψ₀s hψ₀
  have hdB := c.isSum_bloc hM0 hd
  set Nn := NatSec.ofIsSum hdB with hNn
  have hzs : z ∈ stab (puAmalgam h.le) x := zm_le_stab_of_isCritical _ h20 c.bpos hc hzZ
  set g := toSL3 ψ₀ ⟨z, hzs⟩ with hg
  have hg1 : g ≠ 1 := by
    intro h1
    have : (⟨z, hzs⟩ : ↥(stab (puAmalgam h.le) x)) ∈ (toSL3 ψ₀).ker := h1
    rw [c.ker_toSL3_eq hM0 hψ₀, Subgroup.mem_subgroupOf] at this
    exact hzQ this
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Fin 3 → F, natAct d g *ᵥ y₀ ≠ y₀ := by
    by_contra hcon
    push Not at hcon
    exact hg1 (eq_one_of_natAct_mulVec_eq_self d hcon)
  let Sfix : AddSubgroup (Fin 3 → F) :=
    { carrier := {y | natAct d g *ᵥ y = y}
      zero_mem' := Matrix.mulVec_zero _
      add_mem' := fun {y y'} hy hy' => by
        show natAct d g *ᵥ (y + y') = y + y'
        rw [Matrix.mulVec_add, show natAct d g *ᵥ y = y from hy,
          show natAct d g *ᵥ y' = y' from hy']
      neg_mem' := fun {y} hy => by
        show natAct d g *ᵥ (-y) = -y
        rw [Matrix.mulVec_neg, show natAct d g *ᵥ y = y from hy] }
  set C := Nn.pre Sfix with hCdef
  have hCV : C ≤ Vv (puAmalgam h.le) x := fun v hv => (Nn.mem_pre.mp hv).1
  have hvC : v ∈ C := by
    refine Nn.mem_pre.mpr ⟨hv, ?_⟩
    have hcz := Nn.coord_conj ⟨z, hzs⟩ hv
    have h0 := (Nn.coord_eq_zero_iff (Subgroup.mul_mem _ (inv_mem hv)
      (Nn.conj_mem ⟨z, hzs⟩ hv))).mpr hvz
    rw [Nn.coord_mul (inv_mem hv) (Nn.conj_mem ⟨z, hzs⟩ hv), Nn.coord_inv hv,
      neg_add_eq_zero] at h0
    show natAct d g *ᵥ Nn.coord v = Nn.coord v
    rw [← hcz]
    exact h0.symm
  have hYC' : Y ≤ C := by
    intro v hv
    have hvV : v ∈ Vv (puAmalgam h.le) x := hYV hv
    refine Nn.mem_pre.mpr ⟨hvV, ?_⟩
    have hv2 := hY hv
    have hZn : ZM (puAmalgam h.le) x ≤
        Subgroup.normalizer (Qv (puAmalgam h.le) x' : Set _) :=
      (c.zm_le_qv_geo_one hc').trans
        ((qv_le_stab_of_adj _ (adj_geo_one _ (by omega)).symm).trans (stab_le_normalizer_qv _ _))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZn] at hv2
    obtain ⟨w, hw, q, hq, rfl⟩ := Set.mem_mul.mp hv2
    have hzq : z * q = q * z :=
      (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hzZ) q hq).symm
    have hr : w⁻¹ * (z * w * z⁻¹) ∈ critR (puAmalgam h.le) x x' := by
      have : w⁻¹ * (z * w * z⁻¹) = ⁅w⁻¹, z⁆ := by rw [commutatorElement_def]; group
      rw [this]
      exact Subgroup.commutator_mem_commutator (inv_mem hw) hzZ
    have hrq : q⁻¹ * (w⁻¹ * (z * w * z⁻¹)) * q = w⁻¹ * (z * w * z⁻¹) := by
      have hmem := (uloc_le_zm h c.full hM8) (c.critR_le_uloc' hc hr)
      have := (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hM8 hmem) q hq)
      calc q⁻¹ * (w⁻¹ * (z * w * z⁻¹)) * q = q⁻¹ * (q * (w⁻¹ * (z * w * z⁻¹))) := by
            rw [mul_assoc, this]
        _ = _ := by group
    have hzq' : z⁻¹ * q = q * z⁻¹ := by
      calc z⁻¹ * q = z⁻¹ * (q * z) * z⁻¹ := by group
        _ = z⁻¹ * (z * q) * z⁻¹ := by rw [hzq]
        _ = q * z⁻¹ := by group
    have he : (w * q)⁻¹ * (z * (w * q) * z⁻¹) = w⁻¹ * (z * w * z⁻¹) := by
      rw [← hrq]
      calc (w * q)⁻¹ * (z * (w * q) * z⁻¹) = q⁻¹ * w⁻¹ * z * w * (q * z⁻¹) := by group
        _ = q⁻¹ * w⁻¹ * z * w * (z⁻¹ * q) := by rw [hzq']
        _ = _ := by group
    have hB : (w * q)⁻¹ * (z * (w * q) * z⁻¹) ∈ Bloc h.le L x := by
      rw [he]
      exact zm_le_bloc h (by rw [c.b8]; norm_num) hM0
        (uloc_le_zm h c.full hM0 (c.critR_le_uloc hc hr))
    have hcz := Nn.coord_conj ⟨z, hzs⟩ hvV
    have h0 := (Nn.coord_eq_zero_iff (Subgroup.mul_mem _ (inv_mem hvV)
      (Nn.conj_mem ⟨z, hzs⟩ hvV))).mpr hB
    rw [Nn.coord_mul (inv_mem hvV) (Nn.conj_mem ⟨z, hzs⟩ hvV), Nn.coord_inv hvV,
      neg_add_eq_zero] at h0
    show natAct d g *ᵥ Nn.coord (w * q) = Nn.coord (w * q)
    rw [← hcz]
    exact h0.symm
  have hCidx : Fintype.card F ≤ C.relIndex (Vv (puAmalgam h.le) x) := by
    have hv : ∀ t : F, ∃ v ∈ Vv (puAmalgam h.le) x, Nn.coord v = t • y₀ :=
      fun t => Nn.exists_coord_eq (t • y₀)
    choose v hvV hvc using hv
    rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]
    have : Finite ↥(stab (puAmalgam h.le) x) := S4A.finite_stab h hM0
    have : Finite ↥(Vv (puAmalgam h.le) x) :=
      Finite.of_injective _ (Subgroup.inclusion_injective hVs)
    have : Finite (↥(Vv (puAmalgam h.le) x) ⧸ C.subgroupOf (Vv (puAmalgam h.le) x)) :=
      Finite.of_surjective _ QuotientGroup.mk_surjective
    refine Nat.card_le_card_of_injective (fun t => (⟨v t, hvV t⟩ : ↥(Vv _ x))) ?_
    intro t t' htt
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at htt
    have h1 := (Nn.mem_pre.mp htt).2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [Nn.coord_mul (inv_mem (hvV t)) (hvV t'), Nn.coord_inv (hvV t), hvc, hvc] at h1
    have h2 : natAct d g *ᵥ ((t' - t) • y₀) = (t' - t) • y₀ := by
      rw [sub_smul]
      have := h1
      rw [neg_add_eq_sub] at this
      exact this
    rw [Matrix.mulVec_smul] at h2
    by_contra hne
    apply hy₀
    have hts : t' - t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    exact smul_right_injective _ hts h2
  have hmul := Subgroup.relIndex_mul_relIndex Y C (Vv (puAmalgam h.le) x) hYC' hCV
  have hq0 := Fintype.card_pos (α := F)
  have hCpos : 0 < C.relIndex (Vv (puAmalgam h.le) x) := by omega
  have : Finite ↥(stab (puAmalgam h.le) x) := S4A.finite_stab h hM0
  have : Finite ↥C := Finite.of_injective _ (Subgroup.inclusion_injective (hCV.trans hVs))
  have hYC1 : Y.relIndex C = 1 := by
    have hYCpos : Y.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : Y.relIndex C * C.relIndex (Vv (puAmalgam h.le) x) ≤
        1 * C.relIndex (Vv (puAmalgam h.le) x) := by
      rw [hmul, one_mul]; omega
    have := Nat.le_of_mul_le_mul_right this hCpos
    omega
  exact Subgroup.relIndex_eq_one.mp hYC1 hvC

end CFSG.Quasithin.MS93.S45Q4
