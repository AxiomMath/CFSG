module

public import CFSG.LocalAnalysis.StandardType.GGF4N2ChartDefs
import CFSG.LocalAnalysis.StandardType.GGHalfFiveTraceSplit
import CFSG.LinearAlgebra.LinearGroups.SubspaceSpecialLinear

public section

namespace CFSG.StandardType.N2Chart

open Matrix

theorem exists_fixed_line_decomposition {W : Type*} [AddCommGroup W] [Module F4 W]
    [FiniteDimensional F4 W] (hdim : Module.finrank F4 W = 4)
    (rho : Matrix.SpecialLinearGroup (Fin 3) F4 →* (W ≃ₗ[F4] W))
    (hrho : Function.Injective rho) :
    ∃ (alpha : Matrix.SpecialLinearGroup (Fin 3) F4 ≃*
        Matrix.SpecialLinearGroup (Fin 3) F4)
      (eta : W ≃ₗ[F4] (F4 × (Fin 3 → F4))),
      ∀ s v, eta (rho s v) =
        ((eta v).1, (alpha s : Matrix (Fin 3) (Fin 3) F4) *ᵥ (eta v).2) := by
  let b : Module.Basis (Fin 4) F4 W := Module.finBasisOfFinrankEq F4 W hdim
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F4) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  let d : Matrix.SpecialLinearGroup (Fin 3) F4 →* F4ˣ := LinearEquiv.det.comp rho
  haveI : Group.IsPerfect d.range := Group.IsPerfect.range (f := d)
  have hd : ∀ s, (rho s).det = 1 := by
    intro s
    have h := Subsingleton.elim (⟨d s, ⟨s, rfl⟩⟩ : d.range) 1
    exact congrArg Subtype.val h
  let rSL : Matrix.SpecialLinearGroup (Fin 3) F4 →* _root_.SpecialLinearGroup F4 W :=
    { toFun := fun s => ⟨rho s, hd s⟩
      map_one' := Subtype.ext (map_one rho)
      map_mul' := fun s t => Subtype.ext (map_mul rho s t) }
  let e4 := Matrix.SpecialLinearGroup.toLin_equiv b
  let R : Matrix.SpecialLinearGroup (Fin 3) F4 →*
      Matrix.SpecialLinearGroup (Fin 4) F4 := e4.symm.toMonoidHom.comp rSL
  have hR : Function.Injective R := by
    intro s t hst
    apply hrho
    have h := congrArg (fun g => e4 g) hst
    have h' : rSL s = rSL t := by simpa [R] using h
    exact congrArg (fun g : _root_.SpecialLinearGroup F4 W => (g : W ≃ₗ[F4] W)) h'
  obtain ⟨alpha, eta, hact⟩ := GGHalf.exists_natural_three_fixed_line R hR
  have hmat : ∀ s, (R s : Matrix (Fin 4) (Fin 4) F4) =
      LinearMap.toMatrix b b (rho s).toLinearMap := by
    intro s
    exact Matrix.SpecialLinearGroup.toLin_equiv.symm_toLinearMap_eq b (rSL s)
  have hrepr : ∀ s v,
      (R s : Matrix (Fin 4) (Fin 4) F4) *ᵥ b.equivFun v = b.equivFun (rho s v) := by
    intro s v
    rw [hmat]
    exact LinearMap.toMatrix_mulVec_repr b b (rho s).toLinearMap v
  refine ⟨alpha, b.equivFun.trans eta, ?_⟩
  intro s v
  change eta (b.equivFun (rho s v)) =
    ((eta (b.equivFun v)).1,
      (alpha s : Matrix (Fin 3) (Fin 3) F4) *ᵥ (eta (b.equivFun v)).2)
  rw [← hrepr]
  exact hact s (b.equivFun v)

theorem exists_fourSpace_intertwiner (T : Subgroup SL6) (A F : Submodule F4 V6)
    (hT : Nonempty (T ≃* Matrix.SpecialLinearGroup (Fin 3) F4))
    (hAF : IsCompl A F) (hFdim : Module.finrank F4 F = 4)
    (hfix : ∀ g ∈ T, ∀ v ∈ A, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v)
    (hmap : ∀ g ∈ T, ∀ v ∈ F, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ F) :
    ∃ (alpha : T ≃* Matrix.SpecialLinearGroup (Fin 3) F4)
      (eta : F ≃ₗ[F4] (F4 × (Fin 3 → F4))),
      ∀ (t : T) (v : F),
        eta ⟨(t.val : Matrix (Fin 6) (Fin 6) F4) *ᵥ (v : V6),
          hmap t.val t.property v v.property⟩ =
          ((eta v).1, (alpha t : Matrix (Fin 3) (Fin 3) F4) *ᵥ (eta v).2) := by
  let rho : T →* (V6 ≃ₗ[F4] V6) := Matrix.SpecialLinearGroup.toLin'.comp T.subtype
  have hrho : Function.Injective rho :=
    Matrix.SpecialLinearGroup.toLin'_injective.comp T.subtype_injective
  have hFmap : ∀ t : T, F.map (rho t).toLinearMap = F := by
    intro t
    apply le_antisymm
    · rintro v ⟨w, hw, rfl⟩
      exact hmap t.val t.property w hw
    · intro v hv
      have hinv : (rho t).symm = rho (t⁻¹) := (map_inv rho t).symm
      refine ⟨(rho t).symm v, ?_, (rho t).apply_symm_apply v⟩
      rw [hinv]
      exact hmap (t⁻¹).val (t⁻¹).property v hv
  let rhoF : T →* (F ≃ₗ[F4] F) :=
    { toFun := fun t => (rho t).ofSubmodules F F (hFmap t)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        change rho 1 (v : V6) = (v : V6)
        rw [map_one]
        rfl
      map_mul' := by
        intro s t
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        change rho (s * t) (v : V6) = rho s (rho t (v : V6))
        rw [map_mul]
        rfl }
  have hrhoF : Function.Injective rhoF := by
    intro s t hst
    apply hrho
    apply LinearEquiv.ext
    intro v
    obtain ⟨⟨a, w⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A F hAF).surjective v
    change rho s ((a : V6) + (w : V6)) = rho t ((a : V6) + (w : V6))
    have hs : rho s (a : V6) = (a : V6) := hfix s.val s.property a a.property
    have ht : rho t (a : V6) = (a : V6) := hfix t.val t.property a a.property
    have hw : rho s (w : V6) = rho t (w : V6) :=
      congrArg (fun f : F ≃ₗ[F4] F => (f w : V6)) hst
    rw [map_add, map_add, hs, ht, hw]
  obtain ⟨eT⟩ := hT
  obtain ⟨alpha, eta, hact⟩ := exists_fixed_line_decomposition hFdim
    (rhoF.comp eT.symm.toMonoidHom) (hrhoF.comp eT.symm.injective)
  refine ⟨eT.trans alpha, eta, ?_⟩
  intro t v
  have h := hact (eT t) v
  have hval : rhoF t v =
      (⟨(t.val : Matrix (Fin 6) (Fin 6) F4) *ᵥ (v : V6),
        hmap t.val t.property v v.property⟩ : F) := by
    apply Subtype.ext
    change (Matrix.SpecialLinearGroup.toLin' t.val).toLinearMap (v : V6) =
      Matrix.toLin' (t.val : Matrix (Fin 6) (Fin 6) F4) (v : V6)
    rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap]
  have h' : eta (rhoF t v) =
      ((eta v).1, (alpha (eT t) : Matrix (Fin 3) (Fin 3) F4) *ᵥ (eta v).2) := by
    simpa [MonoidHom.comp_apply] using h
  rw [hval] at h'
  exact h'

theorem eq_stabSub_of_le_of_card_eq (T : Subgroup SL6) (P E : Submodule F4 V6)
    (h : IsCompl E P) (hE : Module.finrank F4 E = 3)
    (hle : T ≤ stabSub P E)
    (hcard : Nat.card T = Nat.card (Matrix.SpecialLinearGroup (Fin 3) F4)) :
    T = stabSub P E := by
  let theta : SL6 →* (V6 ≃ₗ[F4] V6) := Matrix.SpecialLinearGroup.toLin'
  let beta := Submodule.specialLinearEmbedding E P h
  have hbeta : Function.Injective beta := Submodule.specialLinearEmbedding_injective h
  let b : Module.Basis (Fin 3) F4 E := Module.finBasisOfFinrankEq F4 E hE
  let e3 := Matrix.SpecialLinearGroup.toLin_equiv b
  letI : Finite (_root_.SpecialLinearGroup F4 E) :=
    Finite.of_equiv (Matrix.SpecialLinearGroup (Fin 3) F4) e3.toEquiv
  letI : Finite beta.range :=
    Finite.of_equiv (_root_.SpecialLinearGroup F4 E) (MonoidHom.ofInjective hbeta).toEquiv
  have hbc : Nat.card beta.range = Nat.card (Matrix.SpecialLinearGroup (Fin 3) F4) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hbeta).symm.toEquiv,
      Nat.card_congr e3.symm.toEquiv]
  have hmap : (stabSub P E).map theta ≤ beta.range := by
    rintro f ⟨g, hg, rfl⟩
    apply Submodule.mem_range_specialLinearEmbedding_of_det_eq_one h
    · change LinearMap.det (Matrix.SpecialLinearGroup.toLin' g).toLinearMap = 1
      rw [Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.det_toLin',
        Matrix.SpecialLinearGroup.det_coe]
    · intro v hv
      exact hg.1 v hv
    · intro v hv
      exact hg.2.1 v hv
    · intro v hv
      have hinv : (theta g).symm = theta (g⁻¹) := (map_inv theta g).symm
      rw [hinv]
      exact hg.2.2 v hv
  have hc := Subgroup.card_le_of_le hmap
  have hm : Nat.card ((stabSub P E).map theta) = Nat.card (stabSub P E) :=
    Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toLin'_injective
  rw [hm, hbc, ← hcard] at hc
  exact Subgroup.eq_of_le_of_card_ge hle hc

theorem ggN2FourSpaceSliceInput_holds :
    ∀ (T : Subgroup SL6) (A F : Submodule F4 V6),
      Nonempty (T ≃* Matrix.SpecialLinearGroup (Fin 3) F4) → IsCompl A F →
      Module.finrank F4 F = 4 →
      (∀ g ∈ T, ∀ v ∈ A, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v) →
      (∀ g ∈ T, ∀ v ∈ F, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ F) →
      ∃ E L₀ : Submodule F4 V6, E ≤ F ∧ L₀ ≤ F ∧ Disjoint E L₀ ∧
        Module.finrank F4 E = 3 ∧ Module.finrank F4 L₀ = 1 ∧ T = stabSub (A ⊔ L₀) E := by
  intro T A F hT hAF hFdim hfix hmap
  obtain ⟨alpha, eta, hact⟩ := exists_fourSpace_intertwiner T A F hT hAF hFdim hfix hmap
  let iE : (Fin 3 → F4) →ₗ[F4] V6 := F.subtype.comp
    (eta.symm.toLinearMap.comp (LinearMap.inr F4 F4 (Fin 3 → F4)))
  let iL : F4 →ₗ[F4] V6 := F.subtype.comp
    (eta.symm.toLinearMap.comp (LinearMap.inl F4 F4 (Fin 3 → F4)))
  let E := LinearMap.range iE
  let L0 := LinearMap.range iL
  have hEF : E ≤ F := by
    rintro v ⟨u, rfl⟩
    exact (eta.symm (0, u)).property
  have hLF : L0 ≤ F := by
    rintro v ⟨l, rfl⟩
    exact (eta.symm (l, 0)).property
  have hiE : Function.Injective iE := by
    intro u v huv
    have h : eta.symm (0, u) = eta.symm (0, v) := Subtype.ext huv
    exact congrArg Prod.snd (eta.symm.injective h)
  have hiL : Function.Injective iL := by
    intro u v huv
    have h : eta.symm (u, 0) = eta.symm (v, 0) := Subtype.ext huv
    exact congrArg Prod.fst (eta.symm.injective h)
  have hErank : Module.finrank F4 E = 3 := by
    have h := (LinearEquiv.ofInjective iE hiE).finrank_eq
    simpa using h.symm
  have hLrank : Module.finrank F4 L0 = 1 := by
    have h := (LinearEquiv.ofInjective iL hiL).finrank_eq
    simpa using h.symm
  have hEL : Disjoint E L0 := by
    rw [disjoint_iff_inf_le]
    rintro v ⟨⟨u, hu⟩, ⟨l, hl⟩⟩
    have h : eta.symm (0, u) = eta.symm (l, 0) := Subtype.ext (hu.trans hl.symm)
    have hu0 : u = 0 := congrArg Prod.snd (eta.symm.injective h)
    change v = 0
    rw [← hu, hu0, map_zero]
  have hsum : E ⊔ L0 = F := by
    apply le_antisymm (sup_le hEF hLF)
    intro v hv
    let z : F := ⟨v, hv⟩
    refine Submodule.mem_sup.mpr ⟨iE (eta z).2, ⟨(eta z).2, rfl⟩,
      iL (eta z).1, ⟨(eta z).1, rfl⟩, ?_⟩
    have h : eta.symm (0, (eta z).2) + eta.symm ((eta z).1, 0) = z := by
      rw [← map_add]
      simpa using eta.symm_apply_apply z
    exact congrArg Subtype.val h
  have hEact : ∀ (t : T) (u : Fin 3 → F4),
      (t.val : Matrix (Fin 6) (Fin 6) F4) *ᵥ iE u =
        iE ((alpha t : Matrix (Fin 3) (Fin 3) F4) *ᵥ u) := by
    intro t u
    have h := hact t (eta.symm (0, u))
    have hv : (⟨(t.val : Matrix (Fin 6) (Fin 6) F4) *ᵥ
        (eta.symm (0, u) : V6),
        hmap t.val t.property (eta.symm (0, u)) (eta.symm (0, u)).property⟩ : F) =
        eta.symm (0, (alpha t : Matrix (Fin 3) (Fin 3) F4) *ᵥ u) := by
      apply eta.injective
      simpa using h
    exact congrArg Subtype.val hv
  have hLact : ∀ (t : T) (l : F4),
      (t.val : Matrix (Fin 6) (Fin 6) F4) *ᵥ iL l = iL l := by
    intro t l
    have h := hact t (eta.symm (l, 0))
    have hv : (⟨(t.val : Matrix (Fin 6) (Fin 6) F4) *ᵥ
        (eta.symm (l, 0) : V6),
        hmap t.val t.property (eta.symm (l, 0)) (eta.symm (l, 0)).property⟩ : F) =
        eta.symm (l, 0) := by
      apply eta.injective
      simpa using h
    exact congrArg Subtype.val hv
  have hle : T ≤ stabSub (A ⊔ L0) E := by
    intro g hg
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨a, ha, l, hl, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨c, rfl⟩ := hl
      rw [Matrix.mulVec_add, hfix g hg a ha, hLact ⟨g, hg⟩ c]
    · rintro v ⟨u, rfl⟩
      exact ⟨(alpha ⟨g, hg⟩ : Matrix (Fin 3) (Fin 3) F4) *ᵥ u,
        (hEact ⟨g, hg⟩ u).symm⟩
    · rintro v ⟨u, rfl⟩
      exact ⟨(alpha ⟨g⁻¹, T.inv_mem hg⟩ : Matrix (Fin 3) (Fin 3) F4) *ᵥ u,
        (hEact ⟨g⁻¹, T.inv_mem hg⟩ u).symm⟩
  have hcompl : IsCompl E (A ⊔ L0) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro v ⟨hvE, hvA⟩
      obtain ⟨a, ha, l, hl, hsumv⟩ := Submodule.mem_sup.mp hvA
      have haF : a ∈ F := by
        have h : a = v - l := by rw [← hsumv, add_sub_cancel_right]
        rw [h]
        exact F.sub_mem (hEF hvE) (hLF hl)
      have ha0 : a = 0 := by
        have h : a ∈ A ⊓ F := ⟨ha, haF⟩
        rw [hAF.disjoint.eq_bot] at h
        simpa using h
      have hvl : v = l := by simpa only [ha0, zero_add] using hsumv.symm
      have hvL : v ∈ L0 := by rw [hvl]; exact hl
      have h : v ∈ E ⊓ L0 := ⟨hvE, hvL⟩
      rw [hEL.eq_bot] at h
      exact h
    · rw [codisjoint_iff_le_sup, sup_left_comm, hsum, hAF.sup_eq_top]
  have heq := eq_stabSub_of_le_of_card_eq T (A ⊔ L0) E hcompl hErank hle
    (Nat.card_congr alpha.toEquiv)
  exact ⟨E, L0, hEF, hLF, hEL, hErank, hLrank, heq⟩

theorem exists_fourSpace_support_lines (T : Subgroup SL6) (A F : Submodule F4 V6)
    (hT : Nonempty (T ≃* Matrix.SpecialLinearGroup (Fin 3) F4))
    (hAF : IsCompl A F) (hFdim : Module.finrank F4 F = 4)
    (hfix : ∀ g ∈ T, ∀ v ∈ A, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v)
    (hmap : ∀ g ∈ T, ∀ v ∈ F, (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ F)
    {u : SL6} (hu : u ∈ T) (hudim : Module.finrank F4 (suppSp u) = 2)
    (hucompl : IsCompl (suppSp u) (fixSp u)) :
    ∃ b b' : Submodule F4 V6,
      b ≤ F ⊓ fixSp u ∧ b' ≤ F ⊓ fixSp u ∧ Disjoint b b' ∧
      Module.finrank F4 b = 1 ∧ Module.finrank F4 b' = 1 ∧
      b ⊔ b' = F ⊓ fixSp u ∧ T = stabSub (A ⊔ b') (suppSp u ⊔ b) := by
  obtain ⟨E, L0, hEF, hLF, hEL, hErank, hLrank, heq⟩ :=
    ggN2FourSpaceSliceInput_holds T A F hT hAF hFdim hfix hmap
  have hsumrank : Module.finrank F4 ↥(E ⊔ L0) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq E L0
    rw [hEL.eq_bot, finrank_bot, hErank, hLrank, add_zero] at h
    exact h
  have hsum : E ⊔ L0 = F :=
    Submodule.eq_of_le_of_finrank_eq (sup_le hEF hLF) (hsumrank.trans hFdim.symm)
  have hcover : E ⊔ (A ⊔ L0) = ⊤ := by
    rw [sup_left_comm, hsum, hAF.sup_eq_top]
  have huS : u ∈ stabSub (A ⊔ L0) E := heq ▸ hu
  have hBE : suppSp u ≤ E := by
    change LinearMap.range (Matrix.toLin' (u : Matrix (Fin 6) (Fin 6) F4) -
      LinearMap.id) ≤ E
    rintro v ⟨x, rfl⟩
    have hx : x ∈ E ⊔ (A ⊔ L0) := by rw [hcover]; trivial
    obtain ⟨e, he, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
    change (u : Matrix (Fin 6) (Fin 6) F4) *ᵥ (e + p) - (e + p) ∈ E
    rw [Matrix.mulVec_add, huS.1 p hp, add_sub_add_right_eq_sub]
    exact E.sub_mem (huS.2.1 e he) he
  let W := F ⊓ fixSp u
  have hWF : W ≤ F := inf_le_left
  have hLW : L0 ≤ W := by
    intro v hv
    refine ⟨hLF hv, ?_⟩
    change (u : Matrix (Fin 6) (Fin 6) F4) *ᵥ v - v = 0
    rw [huS.1 v ((le_sup_right : L0 ≤ A ⊔ L0) hv), sub_self]
  have hBW : Disjoint (suppSp u) W := hucompl.disjoint.mono_right inf_le_right
  have hBS : suppSp u ⊔ W = F := by
    change suppSp u ⊔ (F ⊓ fixSp u) = F
    rw [inf_comm F (fixSp u), ← sup_inf_assoc_of_le (fixSp u) (hBE.trans hEF),
      hucompl.sup_eq_top, top_inf_eq]
  have hBD : Disjoint (suppSp u) (E ⊓ W) := hBW.mono_right inf_le_right
  have hES : suppSp u ⊔ (E ⊓ W) = E := by
    rw [inf_comm E W, ← sup_inf_assoc_of_le W hBE, hBS, inf_eq_right.mpr hEF]
  have hPD : Disjoint (E ⊓ W) L0 := hEL.mono_left inf_le_left
  have hWS : (E ⊓ W) ⊔ L0 = W := by
    have hsum' : L0 ⊔ E = F := by rw [sup_comm, hsum]
    rw [sup_comm, ← sup_inf_assoc_of_le E hLW, hsum', inf_eq_right.mpr hWF]
  have hd := Submodule.finrank_sup_add_finrank_inf_eq (suppSp u) (E ⊓ W)
  rw [hES, hBD.eq_bot, finrank_bot, hErank, hudim, add_zero] at hd
  have hb : Module.finrank F4 ↥(E ⊓ W) = 1 :=
    Nat.add_left_cancel (show 2 + Module.finrank F4 ↥(E ⊓ W) = 2 + 1 from hd.symm)
  refine ⟨E ⊓ W, L0, inf_le_right, hLW, hPD, hb, hLrank, hWS, ?_⟩
  rw [hES]
  exact heq

theorem ggN2SliceLinesInput_holds : GGN2SliceLinesInput := by
  intro u1 u2 T _ _ hdim1 hdim2 hcompl1 hcompl2 _ _ hT hTC hfix hu2
  have hFdim : Module.finrank F4 (fixSp u1) = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (suppSp u1) (fixSp u1)
    rw [hcompl1.sup_eq_top, hcompl1.disjoint.eq_bot, finrank_top, finrank_bot,
      Module.finrank_fin_fun, hdim1, add_zero] at h
    exact Nat.add_left_cancel (show 2 + Module.finrank F4 (fixSp u1) = 2 + 4 from h.symm)
  have hmap : ∀ g ∈ T, ∀ v ∈ fixSp u1,
      (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v ∈ fixSp u1 := by
    intro g hg v hv
    have hc : u1 * g = g * u1 := Subgroup.mem_centralizer_iff.mp (hTC hg) u1 rfl
    change (u1 : Matrix (Fin 6) (Fin 6) F4) *ᵥ v - v = 0 at hv
    have hfv : (u1 : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = v := sub_eq_zero.mp hv
    change (u1 : Matrix (Fin 6) (Fin 6) F4) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v) -
      (g : Matrix (Fin 6) (Fin 6) F4) *ᵥ v = 0
    apply sub_eq_zero.mpr
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, hc,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hfv]
  obtain ⟨b, b', hb, hb', hdisj, hbrank, hb'rank, -, heq⟩ :=
    exists_fourSpace_support_lines T (suppSp u1) (fixSp u1) hT hcompl1 hFdim hfix hmap
      hu2 hdim2 hcompl2
  exact ⟨b, b', hb, hb', hdisj, hbrank, hb'rank, heq⟩

end CFSG.StandardType.N2Chart
