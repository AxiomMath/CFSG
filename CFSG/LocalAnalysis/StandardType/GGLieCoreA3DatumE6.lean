module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3GrpWeyl
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3GrpH
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3GrpCarry
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3GrpRat
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictPhi
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint
open Matrix

private theorem ggLieDE_familyKernel_eq (a₁ a₂ : Fin (langTag .E6).rank → GGLˣ) :
    familyKernel (K := GGL) ![a₁, a₂] = kernelRoots (jointChar a₁ a₂) := by
  ext α
  have h1 : ∀ a : Fin (langTag .E6).rank → GGLˣ,
      (rootCharHom a) (Multiplicative.ofAdd α) = rootChar a α := fun a => rfl
  simp only [familyKernel, kernelRoots, jointChar, MonoidHom.prod_apply, Set.mem_setOf_eq,
    Prod.mk_eq_one, h1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Fin.forall_fin_two]

private theorem ggLieDE_conj_mem_commutator {G : Type*} [Group G] (R : Subgroup G) (c n : G)
    (hc : c ∈ R) (hn : n ∈ ⁅R, R⁆) : c * n * c⁻¹ ∈ ⁅R, R⁆ := by
  have hmapR : R.map (MulAut.conj c).toMonoidHom = R := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      exact mul_mem (mul_mem hc hy) (inv_mem hc)
    · intro x hx
      refine ⟨c⁻¹ * x * c, mul_mem (mul_mem (inv_mem hc) hx) hc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hmap : (⁅R, R⁆).map (MulAut.conj c).toMonoidHom = ⁅R, R⁆ := by
    rw [Subgroup.map_commutator, hmapR]
  rw [← hmap]
  exact ⟨n, hn, rfl⟩

private theorem ggLieDE_x_fixes
    {β₀ β₁ : Fin (langTag .E6).rank → ℤ} (hβ₀ : IsRoot (langTag .E6) β₀)
    (hβ₁ : IsRoot (langTag .E6) β₁) :
    (fun γ => (rootReflection β₀ * rootReflection β₁) • γ) ''
      {γ | IsRoot (langTag .E6) γ ∧ iform γ β₀ = 0 ∧ iform γ β₁ = 0} =
    {γ | IsRoot (langTag .E6) γ ∧ iform γ β₀ = 0 ∧ iform γ β₁ = 0} := by
  apply le_antisymm
  · rintro γ ⟨δ, hδ, rfl⟩
    change (rootReflection β₀ * rootReflection β₁) • δ ∈
      {γ | IsRoot (langTag .E6) γ ∧ iform γ β₀ = 0 ∧ iform γ β₁ = 0}
    rw [mul_smul, rootReflection_smul_of_iform_eq_zero hβ₁ ((iform_comm β₁ δ).trans hδ.2.2),
      rootReflection_smul_of_iform_eq_zero hβ₀ ((iform_comm β₀ δ).trans hδ.2.1)]
    exact hδ
  · intro γ hγ
    refine ⟨γ, hγ, ?_⟩
    change (rootReflection β₀ * rootReflection β₁) • γ = γ
    rw [mul_smul, rootReflection_smul_of_iform_eq_zero hβ₁ ((iform_comm β₁ γ).trans hγ.2.2),
      rootReflection_smul_of_iform_eq_zero hβ₀ ((iform_comm β₀ γ).trans hγ.2.1)]

private theorem ggLieDE_conj_eq_of_mul_conj_eq {G : Type*} [Group G] {d z : G}
    (h : d * z * d⁻¹ = z) : z * d * z⁻¹ = d := by
  have h' : d * z = z * d := by
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [h]
  rw [← h', mul_assoc, mul_inv_cancel, mul_one]

private theorem ggLieDE_y_conj_d {G : Type*} [Group G] (g z c h n d e f : G)
    (hgz : g * z = c * h) (hz : z * d * z⁻¹ = d) (he : h * d * h⁻¹ = e)
    (hn : n * e * n⁻¹ = f) (hf : h * f * h⁻¹ = f) :
    (g⁻¹ * (c * n * c⁻¹) * g) * d * (g⁻¹ * (c * n * c⁻¹) * g)⁻¹ = z * f * z⁻¹ := by
  have hc : c = g * z * h⁻¹ := by rw [hgz]; group
  have hz' : z⁻¹ * d * z = d := by
    have h' : d * z = z * d := by
      calc d * z = z * d * z⁻¹ * z := by rw [hz]
        _ = z * d := by group
    calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
      _ = z⁻¹ * (z * d) := by rw [h']
      _ = d := by group
  have hf' : h⁻¹ * f * h = f := by
    have h' : f * h = h * f := by
      calc f * h = h * f * h⁻¹ * h := by rw [hf]
        _ = h * f := by group
    calc h⁻¹ * f * h = h⁻¹ * (f * h) := by group
      _ = h⁻¹ * (h * f) := by rw [h']
      _ = f := by group
  rw [hc]
  calc
    (g⁻¹ * ((g * z * h⁻¹) * n * (g * z * h⁻¹)⁻¹) * g) * d *
        (g⁻¹ * ((g * z * h⁻¹) * n * (g * z * h⁻¹)⁻¹) * g)⁻¹
        = z * h⁻¹ * n * (h * (z⁻¹ * d * z) * h⁻¹) * n⁻¹ * h * z⁻¹ := by group
    _ = z * h⁻¹ * (n * (h * d * h⁻¹) * n⁻¹) * h * z⁻¹ := by rw [hz']; group
    _ = z * h⁻¹ * (n * e * n⁻¹) * h * z⁻¹ := by rw [he]
    _ = z * h⁻¹ * f * h * z⁻¹ := by rw [hn]
    _ = z * (h⁻¹ * f * h) * z⁻¹ := by group
    _ = z * f * z⁻¹ := by rw [hf']

private theorem ggLieDE_Phi_conj_model
    (hΦ : IsSteinbergEnd (langTag .E6) GGL (2 ^ 1) (ggPhi .E6 1)) (w : WeylGroup (langTag .E6))
    (g : ModGL (langTag .E6) GGL) (hg : g ∈ adjointGroup (langTag .E6) GGL)
    (hlang : ggPhi .E6 1 g = g * canonicalRep (coxeterSystem (langTag .E6)) GGL w) :
    (ratPoints (ggPhi .E6 1)).map (MulAut.conj g⁻¹).toMonoidHom =
      (langDatumOfPosition hΦ w g hg hlang).model := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨r, hr, rfl⟩
    rw [LangDatum.mem_model]
    refine ⟨mul_mem (mul_mem (inv_mem hg) hr.1) hg, ?_⟩
    change canonicalRep (coxeterSystem (langTag .E6)) GGL w *
        ggPhi .E6 1 (g⁻¹ * r * g) * (canonicalRep (coxeterSystem (langTag .E6)) GGL w)⁻¹ =
      g⁻¹ * r * g
    have hr2 : ggPhi .E6 1 r = r := hr.2
    rw [map_mul, map_mul, map_inv, hlang, hr2]
    group
  · intro x hx
    rw [LangDatum.mem_model] at hx
    obtain ⟨hx_adj, hx_fix⟩ := hx
    rw [Subgroup.mem_map]
    refine ⟨g * x * g⁻¹, ⟨?_, ?_⟩, ?_⟩
    · exact (adjointGroup (langTag .E6) GGL).mul_mem
        ((adjointGroup (langTag .E6) GGL).mul_mem hg hx_adj)
        ((adjointGroup (langTag .E6) GGL).inv_mem hg)
    · change ggPhi .E6 1 (g * x * g⁻¹) = g * x * g⁻¹
      have hx_fix' : canonicalRep (coxeterSystem (langTag .E6)) GGL w * ggPhi .E6 1 x *
          (canonicalRep (coxeterSystem (langTag .E6)) GGL w)⁻¹ = x := hx_fix
      rw [map_mul, map_mul, map_inv, hlang]
      have : (g * canonicalRep (coxeterSystem (langTag .E6)) GGL w) * ggPhi .E6 1 x *
          ((g * canonicalRep (coxeterSystem (langTag .E6)) GGL w))⁻¹ =
          g * (canonicalRep (coxeterSystem (langTag .E6)) GGL w * ggPhi .E6 1 x *
            (canonicalRep (coxeterSystem (langTag .E6)) GGL w)⁻¹) * g⁻¹ := by group
      rw [this, hx_fix']
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem ggLieA3DatumE6_of_lattice
    (hL : GGLieA3LatticeE6) : GGLieA3DatumE6 := by
  intro hΦ w g hg hlang a₁ a₂ ρ i hh
  obtain ⟨hFrob, htorus₁, htorus₂, hcube₁, hcube₂, hcard, hrank, hncard, himage, htwist⟩ := hh
  let D : LangDatum (langTag .E6) GGL := langDatumOfPosition hΦ w g hg hlang
  let R : Subgroup (ModGL (langTag .E6) GGL) := ratPoints (ggPhi .E6 1)
  obtain ⟨w', hw'mem, hw'smul⟩ := htwist
  have hρw : ∀ γ, IsRoot (langTag .E6) γ → ρ γ = w • γ := by
    intro γ hγ
    have h := ggLie_frobRootMap_eq_on_roots (t := .E6) (Or.inl rfl) (f := 1) (by norm_num)
      hΦ w g hg hlang hFrob hγ
    change ρ γ = w • γ
    exact h
  have hlang₁ : ∀ γ, IsRoot (langTag .E6) γ → rootChar a₁ (w • γ) = rootChar a₁ γ ^ 2 := by
    intro γ hγ
    have h := hFrob.rootChar_eq a₁ htorus₁ γ hγ
    have hq : D.q = 2 := rfl
    rw [hρw γ hγ, hq] at h
    exact h
  have hlang₂ : ∀ γ, IsRoot (langTag .E6) γ → rootChar a₂ (w • γ) = rootChar a₂ γ ^ 2 := by
    intro γ hγ
    have h := hFrob.rootChar_eq a₂ htorus₂ γ hγ
    have hq : D.q = 2 := rfl
    rw [hρw γ hγ, hq] at h
    exact h
  have hsmul : ∀ γ ∈ componentRoots (jointChar a₁ a₂) i, w • γ = w' • γ := by
    intro γ hγ
    have hγroot : IsRoot (langTag .E6) γ := isRoot_of_mem_componentRoots hγ
    rw [← hρw γ hγroot]
    exact hw'smul γ hγ
  have ha₁cube : ∀ i, a₁ i ^ 3 = 1 := fun i => by
    have hfun : a₁ ^ 3 = (1 : Fin (langTag .E6).rank → GGLˣ) :=
      rootDiagUnit_injective (K := GGL) (τ := langTag .E6) (by
        rw [← rootDiagUnit_pow, hcube₁, rootDiagUnit_one])
    simpa using congrFun hfun i
  have ha₂cube : ∀ i, a₂ i ^ 3 = 1 := fun i => by
    have hfun : a₂ ^ 3 = (1 : Fin (langTag .E6).rank → GGLˣ) :=
      rootDiagUnit_injective (K := GGL) (τ := langTag .E6) (by
        rw [← rootDiagUnit_pow, hcube₂, rootDiagUnit_one])
    simpa using congrFun hfun i
  obtain ⟨β₀, β₁, hβ₀root, hβ₁root, hβorth, hker_eq_comp, hcomp_eq_orth, hw_eq, hψpair,
    hsum_hL, hplane⟩ :=
    hL w w' a₁ a₂ ha₁cube ha₂cube hlang₁ hlang₂ hcard i hncard hw'mem hsmul
  have hKcomp : familyKernel (K := GGL) ![a₁, a₂] =
      componentRoots (jointChar a₁ a₂) i :=
    (ggLieDE_familyKernel_eq a₁ a₂).trans hker_eq_comp
  have hu : w' ∈ Subgroup.closure (rootReflection '' familyKernel (K := GGL) ![a₁, a₂]) := by
    rw [hKcomp]
    have himg : rootReflection '' componentRoots (jointChar a₁ a₂) i =
        {s : WeylGroup (langTag .E6) |
          ∃ γ ∈ componentRoots (jointChar a₁ a₂) i, s = rootReflection γ} := by
      ext s
      simp only [Set.mem_image, Set.mem_setOf_eq]
      exact ⟨fun ⟨γ, hγ, h⟩ => ⟨γ, hγ, h.symm⟩, fun ⟨γ, hγ, h⟩ => ⟨γ, hγ, h.symm⟩⟩
    rw [himg]
    exact hw'mem
  have hx : (fun α => (rootReflection β₀ * rootReflection β₁) • α) ''
      familyKernel (K := GGL) ![a₁, a₂] = familyKernel (K := GGL) ![a₁, a₂] := by
    rw [hKcomp.trans hcomp_eq_orth]
    exact ggLieDE_x_fixes hβ₀root hβ₁root
  have hlang' : ggPhi .E6 1 g = g * canonicalRep (coxeterSystem (langTag .E6)) GGL
      (w' * (rootReflection β₀ * rootReflection β₁)) := by
    have h := hlang
    rw [hw_eq, mul_assoc] at h
    exact h
  obtain ⟨z, hz_fam, hz_Phi⟩ := ggLie_lang_step ![a₁, a₂] w'
    (rootReflection β₀ * rootReflection β₁) hu hx g hlang'
  obtain ⟨h, hh_adj, hh_Phi, hh_d0, hh_d1, hh_fix⟩ :=
    ggLie_exists_h (β₀ := β₀) (β₁ := β₁) hβ₀root hβ₁root hβorth
  obtain ⟨ψ₀, hψ₀comp, ψ₁, hψ₁comp, hψorth⟩ := hψpair
  obtain ⟨n, hn_mem, hn_f0, hn_f1⟩ := ggLie_weyl_carry (β₀ := β₀) (β₁ := β₁)
    (ψ₀ := ψ₀) (ψ₁ := ψ₁) hβ₀root hβ₁root
    (isRoot_of_mem_componentRoots hψ₀comp) (isRoot_of_mem_componentRoots hψ₁comp) hβorth hψorth
  set c : ModGL (langTag .E6) GGL := g * z * h⁻¹ with hc
  set v : ModGL (langTag .E6) GGL := c * n * c⁻¹ with hv
  set y : ModGL (langTag .E6) GGL := g⁻¹ * v * g with hy
  have hzC : z ∈ familyCentralizer (langTag .E6) GGL ![a₁, a₂] :=
    familyGroup_le_familyCentralizer ![a₁, a₂] hz_fam
  have hz_adj : z ∈ adjointGroup (langTag .E6) GGL := (Subgroup.mem_inf.1 hzC).1
  have hgz : g * z = c * h := by rw [hc]; group
  have hc_adj : c ∈ adjointGroup (langTag .E6) GGL := by
    rw [hc]
    exact mul_mem (mul_mem hg hz_adj) (inv_mem hh_adj)
  have hc_fix : ggPhi .E6 1 c = c := by
    rw [hc, map_mul, map_inv, hz_Phi, hh_Phi]
    group
  have hc_mem : c ∈ ratPoints (ggPhi .E6 1) := ⟨hc_adj, hc_fix⟩
  have hmap : R.map (MulAut.conj g⁻¹).toMonoidHom = D.model :=
    ggLieDE_Phi_conj_model hΦ w g hg hlang
  have hmapΓ : (⁅R, R⁆).map (MulAut.conj g⁻¹).toMonoidHom = D.Γ := by
    rw [Subgroup.map_commutator, hmap]
    rfl
  have hv_mem : v ∈ ⁅R, R⁆ := by
    rw [hv]
    exact ggLieDE_conj_mem_commutator R c n hc_mem hn_mem
  have hy_mem : y ∈ D.Γ := by
    rw [hy, ← hmapΓ]
    exact ⟨v, hv_mem, by simp [MulAut.conj_apply]⟩
  have hz_cent : ∀ d ∈ Subgroup.closure
      {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂}, z * d * z⁻¹ = d := by
    have hgen : ∀ c' ∈ ({rootDiagUnit (langTag .E6) a₁,
        rootDiagUnit (langTag .E6) a₂} : Set (ModGL (langTag .E6) GGL)),
        z * c' * z⁻¹ = c' := by
      intro c' hc'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc'
      rcases hc' with rfl | rfl
      · refine ggLieDE_conj_eq_of_mul_conj_eq ?_
        simpa using (mem_familyCentralizer.1 hzC).2 0
      · refine ggLieDE_conj_eq_of_mul_conj_eq ?_
        simpa using (mem_familyCentralizer.1 hzC).2 1
    have hle : Subgroup.closure {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂} ≤
        Subgroup.centralizer ({z} : Set (ModGL (langTag .E6) GGL)) := by
      rw [Subgroup.closure_le]
      intro c' hc'
      change c' ∈ Subgroup.centralizer ({z} : Set (ModGL (langTag .E6) GGL))
      rw [Subgroup.mem_centralizer_iff]
      intro w' hw'
      simp only [Set.mem_singleton_iff] at hw'
      rw [hw']
      calc z * c' = (z * c' * z⁻¹) * z := by group
        _ = c' * z := by rw [hgen c' hc']
    intro d hd
    have h2 := (Subgroup.mem_centralizer_iff.1 (hle hd)) z (Set.mem_singleton z)
    calc z * d * z⁻¹ = d * z * z⁻¹ := by rw [h2]
      _ = d := by group
  have hz_d0 : z * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀) * z⁻¹ =
      rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀) :=
    hz_cent _ (by rw [hplane]; exact Subgroup.subset_closure (by simp))
  have hz_d1 : z * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁) * z⁻¹ =
      rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁) :=
    hz_cent _ (by rw [hplane]; exact Subgroup.subset_closure (by simp))
  have hy_conj : ∀ (d e f : ModGL (langTag .E6) GGL), z * d * z⁻¹ = d →
      h * d * h⁻¹ = e → n * e * n⁻¹ = f → h * f * h⁻¹ = f →
      y * d * y⁻¹ = z * f * z⁻¹ := by
    intro d e f hzd hed hne hhf
    rw [hy, hv]
    exact ggLieDE_y_conj_d g z c h n d e f hgz hzd hed hne hhf
  have hh_f : ∀ ψ ∈ componentRoots (jointChar a₁ a₂) i,
      h * (pinnedX (langTag .E6) GGL ψ 1 * pinnedX (langTag .E6) GGL (-ψ) 1) * h⁻¹ =
        pinnedX (langTag .E6) GGL ψ 1 * pinnedX (langTag .E6) GGL (-ψ) 1 := by
    intro ψ hψ
    rw [hcomp_eq_orth] at hψ
    rw [show h * (pinnedX (langTag .E6) GGL ψ 1 * pinnedX (langTag .E6) GGL (-ψ) 1) * h⁻¹ =
        (h * pinnedX (langTag .E6) GGL ψ 1 * h⁻¹) *
          (h * pinnedX (langTag .E6) GGL (-ψ) 1 * h⁻¹) by group]
    rw [hh_fix ψ hψ.1 hψ.2.1 hψ.2.2 1,
      hh_fix (-ψ) (IsRoot.neg hψ.1) (by rw [iform_neg_left, hψ.2.1, neg_zero])
        (by rw [iform_neg_left, hψ.2.2, neg_zero]) 1]
  have hΨ : ∀ ψ ∈ componentRoots (jointChar a₁ a₂) i,
      IsRoot (langTag .E6) ψ ∧ ψ ∈ familyKernel (K := GGL) ![a₁, a₂] := by
    intro ψ hψ
    exact ⟨isRoot_of_mem_componentRoots hψ, by rw [hKcomp]; exact hψ⟩
  have hKsub : familyKernel (K := GGL) ![a₁, a₂] ⊆ componentRoots (jointChar a₁ a₂) i := by
    rw [hKcomp]
  have hneg : ∀ ψ ∈ componentRoots (jointChar a₁ a₂) i,
      -ψ ∈ componentRoots (jointChar a₁ a₂) i := by
    intro ψ hψ
    rw [hcomp_eq_orth] at hψ ⊢
    exact ⟨IsRoot.neg hψ.1, by rw [iform_neg_left, hψ.2.1, neg_zero],
      by rw [iform_neg_left, hψ.2.2, neg_zero]⟩
  have hh' : ∀ ψ ∈ componentRoots (jointChar a₁ a₂) i, ∀ t : GGL,
      h * pinnedX (langTag .E6) GGL ψ t * h⁻¹ = pinnedX (langTag .E6) GGL ψ t := by
    intro ψ hψ t
    rw [hcomp_eq_orth] at hψ
    exact hh_fix ψ hψ.1 hψ.2.1 hψ.2.2 t
  have hconj := ggLie_conj_mem_ratComp hΦ w g hg hlang ρ ![a₁, a₂]
    (componentRoots (jointChar a₁ a₂) i) hΨ hKsub hneg hsum_hL z c h hz_fam hgz hc_mem hh'
  refine ⟨y, hy_mem, ?_⟩
  rw [hplane, MonoidHom.map_closure, Subgroup.closure_le]
  rintro x ⟨d, hd, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl
  · have h1 : y * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀) * y⁻¹ =
        z * (pinnedX (langTag .E6) GGL ψ₀ 1 * pinnedX (langTag .E6) GGL (-ψ₀) 1) * z⁻¹ :=
      hy_conj _ _ _ hz_d0 hh_d0 hn_f0 (hh_f _ hψ₀comp)
    change y * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀) * y⁻¹ ∈
      ratComp (fun u => ρ u) (langDatumOfPosition hΦ w g hg hlang).Γ
        (componentRoots (jointChar a₁ a₂) i)
    rw [h1]
    exact hconj ψ₀ hψ₀comp
  · have h1 : y * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁) * y⁻¹ =
        z * (pinnedX (langTag .E6) GGL ψ₁ 1 * pinnedX (langTag .E6) GGL (-ψ₁) 1) * z⁻¹ :=
      hy_conj _ _ _ hz_d1 hh_d1 hn_f1 (hh_f _ hψ₁comp)
    change y * rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁) * y⁻¹ ∈
      ratComp (fun u => ρ u) (langDatumOfPosition hΦ w g hg hlang).Γ
        (componentRoots (jointChar a₁ a₂) i)
    rw [h1]
    exact hconj ψ₁ hψ₁comp

end CFSG.StandardType.LieCore
