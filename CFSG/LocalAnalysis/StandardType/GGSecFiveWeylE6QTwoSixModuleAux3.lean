module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux2

public section

namespace CFSG.StandardType.E6QTwo

open Module
open CFSG.Blueprint.Chevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V}

theorem orthogonal_of_invariant_compl
    (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hα : ∀ i, α i (h i) = 2) (hS_card : Nat.card (spanH h) = 3 ^ 5)
    {B' : LinearMap.BilinForm (ZMod 3) (spanH h)}
    (hB' : ∀ i s, B' (hIn h i) s = alphaIn α i s)
    {x : V} (hxS : x ∈ spanH h) (hx : x ≠ 0)
    (hxx2 : B' ⟨x, hxS⟩ ⟨x, hxS⟩ = 2)
    {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ e6Weyl hα)
    {E : Submodule (ZMod 3) V} (hES : E ≤ spanH h) (hEcard : Nat.card E = 3 ^ 4)
    (hxE : x ∉ E) (hEA : ∀ g ∈ A, ∀ v ∈ E, g v ∈ E)
    (hAx : ∀ g ∈ A, g x = x)
    (hfix : ∀ v, (∀ g ∈ A, g v - v ∈ (ZMod 3) ∙ x) → v ∈ (ZMod 3) ∙ x) :
    ∀ v (hv : v ∈ E), B' ⟨x, hxS⟩ ⟨v, hES hv⟩ = 0 := by
  classical
  let xS : spanH h := ⟨x, hxS⟩
  let xperp : Submodule (ZMod 3) (spanH h) := LinearMap.ker (B' xS)
  let ES : Submodule (ZMod 3) (spanH h) := E.comap (spanH h).subtype
  have hxS0 : xS ≠ 0 := by
    intro h0
    exact hx (by simpa [xS] using congrArg Subtype.val h0)
  have hES_card : Nat.card ES = 3 ^ 4 := by
    rw [Nat.card_congr (Submodule.comapSubtypeEquivOfLe hES).toEquiv, hEcard]
  have hES_fin : finrank (ZMod 3) ES = 4 := by
    have hc := natCard_submodule ES
    rw [hES_card] at hc
    exact (Nat.pow_right_injective (by norm_num) hc).symm
  have hS_fin : finrank (ZMod 3) (spanH h) = 5 := by
    have hc := natCard_submodule (spanH h)
    rw [hS_card] at hc
    exact (Nat.pow_right_injective (by norm_num) hc).symm
  have hspan_fin : finrank (ZMod 3) (Submodule.span (ZMod 3) {xS}) = 1 :=
    finrank_span_singleton hxS0
  have hdisj : Disjoint ES (Submodule.span (ZMod 3) {xS}) := by
    rw [disjoint_iff]
    refine le_antisymm ?_ bot_le
    intro y hy
    obtain ⟨hyES, hySpan⟩ := Submodule.mem_inf.mp hy
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hySpan
    have hyE : (y : V) ∈ E := hyES
    by_cases hc0 : c = 0
    · rw [Submodule.mem_bot, ← hc, hc0, zero_smul]
    · exfalso
      apply hxE
      have hxy : x = c⁻¹ • (y : V) := by
        rw [← hc, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul]
      rw [hxy]
      exact E.smul_mem _ hyE
  have hcompl : IsCompl ES (Submodule.span (ZMod 3) {xS}) :=
    (Submodule.isCompl_iff_disjoint ES (Submodule.span (ZMod 3) {xS}) (by omega)).mpr hdisj
  let projE : spanH h →ₗ[ZMod 3] spanH h := ES.projection _ hcompl
  let projX : spanH h →ₗ[ZMod 3] spanH h :=
    (Submodule.span (ZMod 3) {xS}).projection ES hcompl.symm
  have hproj_add : ∀ y, projE y + projX y = y :=
    fun y => Submodule.projection_add_projection_eq_self hcompl y
  have hprojE_mem : ∀ y, projE y ∈ ES := fun y => Submodule.projection_apply_mem hcompl y
  have hprojX_mem : ∀ y, projX y ∈ Submodule.span (ZMod 3) {xS} :=
    fun y => Submodule.projection_apply_mem hcompl.symm y
  have hprojX_x : projX xS = xS :=
    Submodule.projection_apply_of_mem_left hcompl.symm
      (Submodule.subset_span (Set.mem_singleton xS))
  have hprojX_ker : ∀ y ∈ ES, projX y = 0 := fun y hy =>
    Submodule.projection_apply_of_mem_right hcompl.symm hy
  let ψ : spanH h →ₗ[ZMod 3] ZMod 3 := (2⁻¹ : ZMod 3) • (B' xS).comp projX
  have hψ_apply : ∀ y, ψ y = (2⁻¹ : ZMod 3) * B' xS (projX y) := by
    intro y
    simp [ψ, smul_eq_mul]
  have hψx : ψ xS = 1 := by
    rw [hψ_apply, hprojX_x, hxx2]
    exact inv_mul_cancel₀ (by decide : (2 : ZMod 3) ≠ 0)
  have hψker : ∀ y ∈ ES, ψ y = 0 := by
    intro y hy
    rw [hψ_apply, hprojX_ker y hy]
    simp
  have hψinv : ∀ (g : V ≃ₗ[ZMod 3] V) (hg : g ∈ A)
      (e : spanH h ≃ₗ[ZMod 3] spanH h), (∀ s : spanH h, (e s : V) = g s) →
      ∀ y, ψ (e y) = ψ y := by
    intro g hg e heq y
    have hxfix : e xS = xS := by
      apply Subtype.ext
      rw [heq, hAx g hg]
    have hESinv : ∀ z ∈ ES, e z ∈ ES := by
      intro z hz
      change (e z : V) ∈ E
      rw [heq]
      exact hEA g hg (z : V) hz
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hprojX_mem y)
    have hy : y = projE y + projX y := (hproj_add y).symm
    have hψy : ψ y = c := by
      calc ψ y = ψ (projE y + projX y) := by conv_lhs => rw [hy]
        _ = ψ (projE y) + ψ (projX y) := by rw [map_add]
        _ = 0 + c := by
              rw [hψker (projE y) (hprojE_mem y), ← hc, map_smul, smul_eq_mul, hψx,
                mul_one]
        _ = c := zero_add c
    have hψhy : ψ (e y) = c := by
      have h1 : e y = e (projE y) + e (projX y) := by
        conv_lhs => rw [hy]
        rw [map_add]
      calc ψ (e y) = ψ (e (projE y)) + ψ (e (projX y)) := by rw [h1, map_add]
        _ = 0 + c := by
              rw [hψker (e (projE y)) (hESinv (projE y) (hprojE_mem y)), ← hc, map_smul,
                hxfix, map_smul, smul_eq_mul, hψx, mul_one]
        _ = c := zero_add c
    rw [hψhy, hψy]
  have hsymm : ∀ u v : spanH h, B' u v = B' v u :=
    bilinForm_symm (alphaIn_hIn hP) hS_card hB'
  have hB'nondeg : B'.Nondegenerate := by
    refine ⟨?_, ?_⟩
    · intro u hu
      exact bilinForm_nondegenerate (alphaIn_hIn hP) hS_card hB' hu
    · intro u hu
      exact bilinForm_nondegenerate (alphaIn_hIn hP) hS_card hB'
        (fun v => by rw [hsymm u v]; exact hu v)
  have hperp_orth : xperp = B'.orthogonal (Submodule.span (ZMod 3) {xS}) := by
    change LinearMap.ker (B' xS) = B'.orthogonal (Submodule.span (ZMod 3) {xS})
    rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    rfl
  have hperp_nondeg : (B'.restrict xperp).Nondegenerate := by
    have h := LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton B' hB'nondeg
      (show B'.IsRefl from (show B'.IsSymm from ⟨hsymm⟩).isRefl) (x := xS)
      (by rw [hxx2]; decide)
    rwa [← hperp_orth] at h
  have hperp_fin : finrank (ZMod 3) xperp = 4 := by
    change finrank (ZMod 3) (LinearMap.ker (B' xS)) = 4
    have hf : B' xS ≠ 0 := by
      intro h0
      have h1 : B' xS xS = 0 := by simp [h0]
      rw [hxx2] at h1
      exact absurd h1 (by decide)
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := B' xS) hf
    omega
  let φ : xperp →ₗ[ZMod 3] ZMod 3 := ψ.comp xperp.subtype
  let y0 : xperp := ((B'.restrict xperp).toDual hperp_nondeg).symm φ
  have hy0 : ∀ y : xperp, B' (y0 : spanH h) (y : spanH h) = φ y := by
    intro y
    have h := LinearMap.BilinForm.apply_toDual_symm_apply
      (B := B'.restrict xperp) (hB := hperp_nondeg) φ y
    simpa [y0, LinearMap.BilinForm.restrict_apply] using h
  have hperp_inv : ∀ (e : spanH h ≃ₗ[ZMod 3] spanH h), e ∈ e6Weyl (alphaIn_self hα) →
      e xS = xS → ∀ y ∈ xperp, e y ∈ xperp := by
    intro e he hex y hy
    change B' xS (e y) = 0
    change B' xS (y : spanH h) = 0 at hy
    have hiso := bilinForm_apply_e6Weyl (alphaIn_hIn hP) hS_card hB' (alphaIn_self hα) he
      (u := e.symm xS) (v := y)
    have h1 : e⁻¹ xS = xS := by
      conv_lhs => rw [← hex]
      exact LinearEquiv.symm_apply_apply e xS
    have h2 : B' xS (e (y : spanH h)) = B' xS (y : spanH h) := by
      calc B' xS (e (y : spanH h))
          = B' (e (e⁻¹ xS)) (e (y : spanH h)) := by
            conv_lhs => rw [← LinearEquiv.apply_symm_apply e xS]
            rfl
        _ = B' (e⁻¹ xS) (y : spanH h) := hiso
        _ = B' xS (y : spanH h) := by rw [h1]
    rw [h2, hy]
  have hy0fix : ∀ g ∈ A, g (y0 : V) = (y0 : V) := by
    intro g hg
    obtain ⟨g', hg', hg'eq⟩ := restrict_mem_e6Weyl (hα := hα) (hA hg)
    have hg'x : g' xS = xS := by
      apply Subtype.ext
      rw [hg'eq, hAx g hg]
    have hg'inv_eq : ∀ s : spanH h, (g'⁻¹ s : V) = g⁻¹ s := by
      intro s
      have h' : (s : V) = g (g'⁻¹ s) := by simpa using hg'eq (g'⁻¹ s)
      have h2 : g⁻¹ (s : V) = g⁻¹ (g (g'⁻¹ s)) := congrArg (fun z => g⁻¹ z) h'
      simpa using h2.symm
    have hg'invx : g'⁻¹ xS = xS := by
      apply Subtype.ext
      rw [hg'inv_eq, hAx g⁻¹ (A.inv_mem hg)]
    let z : xperp := ⟨g' (y0 : spanH h), hperp_inv g' hg' hg'x y0 y0.2⟩
    have hz : z = y0 := by
      have hsub : z - y0 = 0 := by
        apply hperp_nondeg.1
        intro y
        have h1 : B' (g' (y0 : spanH h)) (y : spanH h) = φ y := by
          calc B' (g' (y0 : spanH h)) (y : spanH h)
              = B' (y0 : spanH h) (g'⁻¹ (y : spanH h)) := by
                have hiso := bilinForm_apply_e6Weyl (alphaIn_hIn hP) hS_card hB'
                  (alphaIn_self hα) hg' (u := y0) (v := g'⁻¹ (y : spanH h))
                simpa using hiso
            _ = φ ⟨g'⁻¹ (y : spanH h), hperp_inv g'⁻¹ (inv_mem hg') hg'invx y y.2⟩ :=
                hy0 ⟨g'⁻¹ (y : spanH h), hperp_inv g'⁻¹ (inv_mem hg') hg'invx y y.2⟩
            _ = φ y := by
                show ψ (g'⁻¹ (y : spanH h)) = ψ (y : spanH h)
                exact hψinv g⁻¹ ((Subgroup.inv_mem_iff A).mpr hg) g'⁻¹ hg'inv_eq _
        have h2 : B' (y0 : spanH h) (y : spanH h) = φ y := hy0 y
        change B' ((z : spanH h) - (y0 : spanH h)) (y : spanH h) = 0
        rw [LinearMap.BilinForm.sub_left, h1, h2, sub_self]
      exact sub_eq_zero.mp hsub
    have hzy : g' (y0 : spanH h) = (y0 : spanH h) := by
      have h := congrArg Subtype.val hz
      simpa [z] using h
    have h1 : (g' (y0 : spanH h) : V) = g (y0 : V) := hg'eq y0
    rw [hzy] at h1
    exact h1.symm
  have hy0zero : y0 = 0 := by
    have hline : (y0 : V) ∈ (ZMod 3) ∙ x := by
      apply hfix (y0 : V)
      intro g hg
      rw [hy0fix g hg, sub_self]
      exact Submodule.zero_mem _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hline
    have hy0eq : (y0 : spanH h) = c • xS := Subtype.ext hc.symm
    have h1 : B' xS (y0 : spanH h) = 0 := y0.2
    rw [hy0eq, map_smul, smul_eq_mul, hxx2] at h1
    have hc0 : c = 0 := (mul_eq_zero.mp h1).resolve_right (by decide)
    apply Subtype.ext
    apply Subtype.ext
    rw [← hc, hc0, zero_smul]
    rfl
  have hφzero : φ = 0 := by
    ext y
    rw [← hy0 y, hy0zero]
    simp
  have hperp_le : xperp ≤ ES := by
    intro y hy
    have hψy : ψ y = 0 := by
      have h := congrArg (fun f : xperp →ₗ[ZMod 3] ZMod 3 => f ⟨y, hy⟩) hφzero
      simpa [φ] using h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hprojX_mem y)
    have hyeq : y = projE y + projX y := (hproj_add y).symm
    have hψy' : ψ y = c := by
      calc ψ y = ψ (projE y + projX y) := by
            conv_lhs => rw [hyeq]
        _ = ψ (projE y) + ψ (projX y) := by rw [map_add]
        _ = 0 + c := by
              rw [hψker (projE y) (hprojE_mem y), ← hc, map_smul, smul_eq_mul, hψx,
                mul_one]
        _ = c := zero_add c
    have hc0 : c = 0 := by rw [← hψy', hψy]
    rw [hyeq, ← hc, hc0, zero_smul, add_zero]
    exact hprojE_mem y
  have heq : ES = xperp := by
    exact (Submodule.eq_of_le_of_finrank_eq hperp_le (by rw [hperp_fin, hES_fin])).symm
  intro v hv
  have hvS : v ∈ spanH h := hES hv
  have hmem : (⟨v, hvS⟩ : spanH h) ∈ ES := hv
  rw [heq] at hmem
  exact hmem

end CFSG.StandardType.E6QTwo

end
