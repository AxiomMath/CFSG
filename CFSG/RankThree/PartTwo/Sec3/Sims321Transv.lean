module

public import CFSG.RankThree.FFModules.Transvections
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.LargeExtraspecial.A2ModSL

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open scoped MatrixGroups
open Matrix CFSG.RankThree.FFModules CFSG.ComponentClassification CFSG.LargeExtraspecial

variable {F : Type*} [Field F] [CharP F 2]

private theorem exists_dotProduct_eq_one {s : Fin 3 → F} (hs : s ≠ 0) :
    ∃ φ : Fin 3 → F, φ ⬝ᵥ s = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hs
  exact ⟨Pi.single i (s i)⁻¹, by rw [single_dotProduct, inv_mul_cancel₀ hi]⟩

private theorem eq_top_of_forall_mulVec_mem {S : Submodule F (Fin 3 → F)} {s : Fin 3 → F}
    (hs : s ≠ 0) (h : ∀ g : SL(3, F), (g : Matrix (Fin 3) (Fin 3) F) *ᵥ s ∈ S) : S = ⊤ := by
  obtain ⟨φ, hφ⟩ := exists_dotProduct_eq_one hs
  have hsS : s ∈ S := by simpa using h 1
  refine eq_top_iff.mpr fun x _ => ?_
  have hv : φ ⬝ᵥ (x - (φ ⬝ᵥ x) • s) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hφ, smul_eq_mul, mul_one, sub_self]
  have h1 := h (A2Mod.tv (x - (φ ⬝ᵥ x) • s) φ)
  rw [A2Mod.tv_mulVec hv, hφ, one_smul] at h1
  have h2 : x - (φ ⬝ᵥ x) • s ∈ S := by simpa using S.sub_mem h1 hsS
  simpa using S.add_mem h2 (S.smul_mem (φ ⬝ᵥ x) hsS)

private theorem exists_sl_of_independent (b₀ b₁ b₂ : Fin 3 → F)
    (hind : ∀ a b c : F, a • b₀ + b • b₁ + c • b₂ = 0 → a = 0 ∧ b = 0 ∧ c = 0) :
    ∃ (h : SL(3, F)) (c : F), c ≠ 0 ∧ ∀ x : Fin 3 → F,
      (h : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x 0 • b₀ + x 1 • b₁ + (c * x 2) • b₂ := by
  set M : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => ![b₀, b₁, b₂] j i with hM
  have hMx : ∀ x : Fin 3 → F, M *ᵥ x = x 0 • b₀ + x 1 • b₁ + x 2 • b₂ := by
    intro x
    ext i
    simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, mul_comm]
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    rw [hMx] at hv
    obtain ⟨h0, h1, h2⟩ := hind _ _ _ hv
    apply hv0
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  refine ⟨⟨M * Matrix.diagonal ![1, 1, M.det⁻¹], ?_⟩, M.det⁻¹, inv_ne_zero hdet, fun x => ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hdet]
  · show (M * Matrix.diagonal ![1, 1, M.det⁻¹]) *ᵥ x = _
    rw [← Matrix.mulVec_mulVec, hMx]
    simp [Matrix.mulVec_diagonal]

private theorem mem_dotOrth_span_singleton {φ x : Fin 3 → F} :
    x ∈ dotOrth (Submodule.span F {φ}) ↔ φ ⬝ᵥ x = 0 := by
  constructor
  · intro h
    exact h φ (Submodule.mem_span_singleton_self φ)
  · intro h s hs
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    rw [smul_dotProduct, h, smul_zero]

private theorem finrank_dotOrth_span_singleton {φ : Fin 3 → F} (hφ : φ ≠ 0) :
    Module.finrank F (dotOrth (Submodule.span F {φ})) = 2 := by
  have h := finrank_dotOrth (Submodule.span F {φ})
  rw [finrank_span_singleton hφ] at h
  omega

private theorem exists_indep {φ u : Fin 3 → F} (hφ : φ ≠ 0) (hu : u ≠ 0) (hφu : φ ⬝ᵥ u = 0) :
    ∃ v : Fin 3 → F, φ ⬝ᵥ v = 0 ∧ ∀ a b : F, a • u + b • v = 0 → a = 0 ∧ b = 0 := by
  have hlt : Submodule.span F {u} < dotOrth (Submodule.span F {φ}) := by
    refine lt_of_le_of_ne ?_ fun h => ?_
    · rw [Submodule.span_singleton_le_iff_mem, mem_dotOrth_span_singleton]
      exact hφu
    · have := congrArg (fun T : Submodule F (Fin 3 → F) => Module.finrank F T) h
      simp only [finrank_span_singleton hu, finrank_dotOrth_span_singleton hφ] at this
      omega
  obtain ⟨v, hv, hvu⟩ := SetLike.exists_of_lt hlt
  refine ⟨v, mem_dotOrth_span_singleton.mp hv, fun a b hab => ?_⟩
  have hb : b = 0 := by
    by_contra hb
    refine hvu (Submodule.mem_span_singleton.mpr ⟨-(b⁻¹ * a), ?_⟩)
    have : b • v = -(a • u) := eq_neg_of_add_eq_zero_right hab
    calc (-(b⁻¹ * a)) • u = b⁻¹ • (-(a • u)) := by rw [neg_smul, smul_neg, mul_smul]
      _ = v := by rw [← this, smul_smul, inv_mul_cancel₀ hb, one_smul]
  subst hb
  rw [zero_smul, add_zero, smul_eq_zero] at hab
  exact ⟨hab.resolve_right hu, rfl⟩

private theorem exists_tv_of_involution {t : SL(3, F)} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ u φ : Fin 3 → F, u ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ u = 0 ∧ t = A2Mod.tv u φ := by
  have hN2 := subOne_comp_self ht
  have hN0 : subOne t ≠ 0 := fun h => ht1 ((subOne_eq_zero_iff t).mp h)
  have hker : LinearMap.range (subOne t) ≤ LinearMap.ker (subOne t) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hN2, LinearMap.zero_apply]
  have hrk : Module.finrank F (LinearMap.range (subOne t)) ≤ 1 := by
    have h2 := Submodule.finrank_mono hker
    have h3 := LinearMap.finrank_range_add_finrank_ker (subOne t)
    rw [finrank_fin3] at h3
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun h => hN0 (LinearMap.range_eq_bot.mp h) : LinearMap.range (subOne t) ≠ ⊥)
  have hspan : Submodule.span F {u} = LinearMap.range (subOne t) := by
    refine Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).mpr hu) ?_
    have h1 := Submodule.finrank_mono ((Submodule.span_singleton_le_iff_mem _ _).mpr hu)
    have h2 : Module.finrank F (Submodule.span F {u}) = 1 := finrank_span_singleton hu0
    omega
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hu0
  set φ : Fin 3 → F := (u i)⁻¹ • (((t : Matrix (Fin 3) (Fin 3) F) - 1) i) with hφ
  have hNx : ∀ x : Fin 3 → F, (t : Matrix (Fin 3) (Fin 3) F) *ᵥ x - x = (φ ⬝ᵥ x) • u := by
    intro x
    have hx : subOne t x ∈ Submodule.span F {u} := by
      rw [hspan]
      exact LinearMap.mem_range_self _ x
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
    rw [subOne_apply] at hc
    have hφx : φ ⬝ᵥ x = c := by
      have h1 : (((t : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ x) i = c * u i := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        have := congrFun hc i
        simpa using this.symm
      rw [hφ, smul_dotProduct, smul_eq_mul]
      change (u i)⁻¹ * ((((t : Matrix (Fin 3) (Fin 3) F) - 1) *ᵥ x) i) = c
      rw [h1, mul_left_comm, inv_mul_cancel₀ hi, mul_one]
    rw [hφx, ← hc]
  have hφu : φ ⬝ᵥ u = 0 := by
    have h1 : subOne t u = 0 := hker hu
    rw [subOne_apply, hNx u] at h1
    exact (smul_eq_zero.mp h1).resolve_right hu0
  refine ⟨u, φ, hu0, fun h0 => hN0 ?_, hφu, ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [subOne_apply, hNx x, h0, zero_dotProduct, zero_smul, LinearMap.zero_apply]
  · apply Subtype.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, A2Mod.tv_mulVec hφu, ← hNx x]
    abel

private theorem exists_conj_tv {u φ : Fin 3 → F} (hu : u ≠ 0) (hφ : φ ≠ 0) (hφu : φ ⬝ᵥ u = 0) :
    ∃ h : SL(3, F), h * A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) * h⁻¹ =
      A2Mod.tv u φ := by
  obtain ⟨w, hw⟩ := exists_dotProduct_eq_one hφ
  rw [dotProduct_comm] at hw
  obtain ⟨v, hv, hind⟩ := exists_indep hφ hu hφu
  obtain ⟨h, c, hc, hh⟩ := exists_sl_of_independent u w v (fun a b c' habc => by
    have h1 := congrArg (φ ⬝ᵥ ·) habc
    simp only [dotProduct_add, dotProduct_smul, hw, hφu, hv, smul_eq_mul, mul_one, mul_zero,
      zero_add, add_zero, dotProduct_zero] at h1
    subst h1
    simp only [zero_smul, add_zero] at habc
    obtain ⟨ha, hc'⟩ := hind _ _ habc
    exact ⟨ha, rfl, hc'⟩)
  have hs : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = u := by simp [hh]
  have hφ' : ∀ x, φ ⬝ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = x 1 := by
    intro x
    rw [hh]
    simp [dotProduct_add, dotProduct_smul, hw, hφu, hv]
  have hcontra : A2Mod.contra h (Pi.single 1 1) = φ := by
    refine dotProduct_eq _ _ fun y => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (h : Matrix (Fin 3) (Fin 3) F) *ᵥ x = y :=
      ⟨((h⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ y, mulVec_mulVec_inv h y⟩
    rw [A2Mod.contra_dotProduct_mulVec, hφ', single_dotProduct, one_mul]
  exact ⟨h, by rw [A2Mod.conj_tv, hs, hcontra]⟩

theorem exists_conj_eq_of_involution (τ τ' : SL(3, F)) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hτ' : τ' * τ' = 1) (hτ'1 : τ' ≠ 1) : ∃ h : SL(3, F), τ' = h * τ * h⁻¹ := by
  obtain ⟨u, φ, hu, hφ, hφu, rfl⟩ := exists_tv_of_involution hτ hτ1
  obtain ⟨u', φ', hu', hφ', hφu', rfl⟩ := exists_tv_of_involution hτ' hτ'1
  obtain ⟨a, ha⟩ := exists_conj_tv hu hφ hφu
  obtain ⟨b, hb⟩ := exists_conj_tv hu' hφ' hφu'
  refine ⟨b * a⁻¹, ?_⟩
  rw [← hb, ← ha]
  group

theorem conj_mem_transvectionGroup {S : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (hg : g ∈ transvectionGroup S) (h : SL(3, F)) :
    h * g * h⁻¹ ∈
      transvectionGroup (S.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) F))) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, fun v => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [Matrix.mulVecLin_apply, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      mulVec_inv_mulVec, hg1 s hs]
  · refine ⟨(g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((h⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) -
      ((h⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v, hg2 _, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_sub, mulVec_mulVec_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem conj_mulVec (A X Ai : Matrix (Fin 3) (Fin 3) F) (v : Fin 3 → F) :
    (A * X * Ai) *ᵥ v = A *ᵥ (X *ᵥ (Ai *ᵥ v)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

private theorem slConjugation_mem {S : Submodule F (Fin 3 → F)} {x : SL(3, F)}
    (hx : x ∈ transvectionGroup S) (B : GL (Fin 3) F) :
    CatalogueBHigherLinearAction.slConjugation 3 F B x ∈
      transvectionGroup (S.map (Matrix.mulVecLin (B : Matrix (Fin 3) (Fin 3) F))) := by
  obtain ⟨hx1, hx2⟩ := hx
  have e1 : ∀ w : Fin 3 → F, ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, B.inv_mul, Matrix.one_mulVec]
  have e2 : ∀ w : Fin 3 → F, (B : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, B.mul_inv, Matrix.one_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [Matrix.mulVecLin_apply, CatalogueBHigherLinearAction.slConjugation_matrix, conj_mulVec,
      e1, hx1 s hs]
  · refine ⟨(x : Matrix (Fin 3) (Fin 3) F) *ᵥ (((B⁻¹ : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ v) - ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v,
      hx2 _, ?_⟩
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_sub, e2,
      CatalogueBHigherLinearAction.slConjugation_matrix, conj_mulVec]

private theorem slGraphAut_mem {S : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (hg : g ∈ transvectionGroup S) :
    CatalogueBGraphForm.slGraphAut 3 F g ∈ transvectionGroup (FFModules.dotOrth S) := by
  have hdual : (CatalogueBGraphForm.slGraphAut 3 F g : Matrix (Fin 3) (Fin 3) F) = dualMat g :=
    rfl
  have hinv := (transvectionGroup S).inv_mem hg
  refine ⟨fun x hx => ?_, fun y => ?_⟩
  · rw [hdual, dualMat_mulVec_eq_iff]
    exact fun z => hx _ (hg.2 z)
  · intro s hs
    rw [hdual, dotProduct_sub, dualMat, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
      hinv.1 s hs, sub_self]

theorem graph_mem_transvectionGroup {S : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (hg : g ∈ transvectionGroup S) (B : GL (Fin 3) F) :
    CatalogueBHigherLinearAction.slConjugation 3 F B (CatalogueBGraphForm.slGraphAut 3 F g) ∈
      transvectionGroup
        ((FFModules.dotOrth S).map (Matrix.mulVecLin (B : Matrix (Fin 3) (Fin 3) F))) := by
  exact slConjugation_mem (slGraphAut_mem hg) B

private theorem pointGroup_sup_hyperplaneGroup_eq_top {s ψ p q : Fin 3 → F} (hψs : ψ ⬝ᵥ s = 1)
    (hψp : ψ ⬝ᵥ p = 0) (hψq : ψ ⬝ᵥ q = 0)
    (hind : ∀ a b : F, a • p + b • q = 0 → a = 0 ∧ b = 0) :
    A2Mod.pointGroup s ⊔ A2Mod.hyperplaneGroup ψ = ⊤ := by
  obtain ⟨h, c, hc, hh⟩ := exists_sl_of_independent s p q (fun a b c habc => by
    have h1 := congrArg (ψ ⬝ᵥ ·) habc
    simp only [dotProduct_add, dotProduct_smul, hψs, hψp, hψq, smul_eq_mul, mul_one, mul_zero,
      add_zero, dotProduct_zero] at h1
    subst h1
    simp only [zero_smul, zero_add] at habc
    obtain ⟨hb, hc'⟩ := hind _ _ habc
    exact ⟨rfl, hb, hc'⟩)
  have hs : (h : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 0 1 = s := by simp [hh]
  have hψ : ∀ x, ψ ⬝ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x) = x 0 := by
    intro x
    rw [hh]
    simp [dotProduct_add, dotProduct_smul, hψs, hψp, hψq]
  have hcontra : A2Mod.contra h (Pi.single 0 1) = ψ := by
    refine dotProduct_eq _ _ fun u => ?_
    obtain ⟨x, rfl⟩ : ∃ x, (h : Matrix (Fin 3) (Fin 3) F) *ᵥ x = u :=
      ⟨((h⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ u, mulVec_mulVec_inv h u⟩
    rw [A2Mod.contra_dotProduct_mulVec, hψ, single_dotProduct, one_mul]
  have h0 := A2Mod.pointGroup_sup_hyperplaneGroup (F := F) (0 : Fin 3)
  have hmap := congrArg (Subgroup.map (MulAut.conj h).toMonoidHom) h0
  rwa [Subgroup.map_sup, A2Mod.pointGroup_map_conj, A2Mod.hyperplaneGroup_map_conj, hs, hcontra,
    Subgroup.map_top_of_surjective _ (MulEquiv.surjective _)] at hmap

theorem transvectionGroup_sup_eq_top {S S' : Submodule F (Fin 3 → F)}
    (hS : Module.finrank F S = 1) (hS' : Module.finrank F S' = 2) (hSS' : ¬ S ≤ S') :
    transvectionGroup S ⊔ transvectionGroup S' = ⊤ := by
  obtain ⟨s₀, hsS, hsS'⟩ := SetLike.not_le_iff_exists.mp hSS'
  obtain ⟨ψ₀, hψS', hψs⟩ := exists_dotProduct_ne_zero hsS'
  set ψ := (ψ₀ ⬝ᵥ s₀)⁻¹ • ψ₀ with hψdef
  have hψs1 : ψ ⬝ᵥ s₀ = 1 := by rw [hψdef, smul_dotProduct, smul_eq_mul, inv_mul_cancel₀ hψs]
  have hψ0 : ψ ≠ 0 := fun h0 => by
    rw [h0, zero_dotProduct] at hψs1
    exact zero_ne_one hψs1
  have hψS'' : ∀ x ∈ S', ψ ⬝ᵥ x = 0 := fun x hx => by
    rw [hψdef, smul_dotProduct, hψS' x hx, smul_zero]
  have hS'eq : S' = dotOrth (Submodule.span F {ψ}) := by
    refine Submodule.eq_of_le_of_finrank_eq
      (fun x hx => mem_dotOrth_span_singleton.mpr (hψS'' x hx)) ?_
    rw [hS', finrank_dotOrth_span_singleton hψ0]
  have hs0 : s₀ ≠ 0 := fun h0 => hsS' (h0 ▸ S'.zero_mem)
  have hSeq : S = Submodule.span F {s₀} := by
    refine (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hsS) ?_).symm
    rw [hS, finrank_span_singleton hs0]
  have hS'0 : S' ≠ ⊥ := by
    rintro rfl
    simp at hS'
  obtain ⟨p, hpS', hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS'0
  obtain ⟨q, hq, hind⟩ := exists_indep hψ0 hp0 (hψS'' p hpS')
  have htop := pointGroup_sup_hyperplaneGroup_eq_top hψs1 (hψS'' p hpS') hq hind
  rw [← top_le_iff, ← htop]
  refine sup_le_sup ?_ ?_
  · intro g hg
    obtain ⟨φ, hφ, rfl⟩ := A2Mod.mem_pointGroup.mp hg
    have hφS : ∀ x ∈ S, φ ⬝ᵥ x = 0 := by
      intro x hx
      rw [hSeq] at hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [dotProduct_smul, hφ, smul_zero]
    have e : A2Mod.tv s₀ φ = transvectionOf s₀ φ hφ := Subtype.ext (A2Mod.coe_tv hφ)
    rw [e]
    exact transvectionOf_mem hsS hφS
  · intro g hg
    obtain ⟨v, hv, rfl⟩ := A2Mod.mem_hyperplaneGroup.mp hg
    have hvS' : v ∈ S' := by
      rw [hS'eq]
      exact mem_dotOrth_span_singleton.mpr hv
    have e : A2Mod.tv v ψ = transvectionOf v ψ hv := Subtype.ext (A2Mod.coe_tv hv)
    rw [e]
    exact transvectionOf_mem hvS' hψS''

theorem exists_not_le_map_of_line {S S' : Submodule F (Fin 3 → F)}
    (hS : Module.finrank F S = 1) (hS' : Module.finrank F S' = 2) :
    ∃ h : SL(3, F), ¬ S ≤ S'.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) F)) := by
  by_contra H
  push Not at H
  have hS0 : S ≠ ⊥ := by
    rintro rfl
    simp at hS
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have htop : S' = ⊤ := by
    refine eq_top_of_forall_mulVec_mem hs0 fun g => ?_
    obtain ⟨y, hy, hyg⟩ := H g⁻¹ hsS
    rw [Matrix.mulVecLin_apply] at hyg
    rw [← hyg, mulVec_mulVec_inv]
    exact hy
  rw [htop, finrank_top, finrank_fin3] at hS'
  omega

theorem exists_not_le_map_of_plane {S S' : Submodule F (Fin 3 → F)}
    (hS : Module.finrank F S = 2) (hS' : Module.finrank F S' = 1) :
    ∃ h : SL(3, F), ¬ S'.map (Matrix.mulVecLin (h : Matrix (Fin 3) (Fin 3) F)) ≤ S := by
  by_contra H
  push Not at H
  have hS0 : S' ≠ ⊥ := by
    rintro rfl
    simp at hS'
  obtain ⟨s, hsS, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have htop : S = ⊤ :=
    eq_top_of_forall_mulVec_mem hs0 fun g => H g (Submodule.mem_map_of_mem hsS)
  rw [htop, finrank_top, finrank_fin3] at hS
  omega

end CFSG.RankThree.PartTwo.Sec3.Sims321
