module

public import CFSG.RankThree.FFModules.Natural
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.SimpleModule.Basic

public section

namespace CFSG.RankThree.FFModules

open scoped MatrixGroups
open Matrix Module

variable {F : Type*} [Field F]

@[expose] def subOne (g : SL(3, F)) : Module.End F (Fin 3 → F) :=
  Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F) - LinearMap.id

theorem subOne_apply (g : SL(3, F)) (v : Fin 3 → F) :
    subOne g v = (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v := by
  simp [subOne, Matrix.toLin'_apply]

theorem subOne_eq_zero_iff (g : SL(3, F)) : subOne g = 0 ↔ g = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h v
    rw [subOne_apply, LinearMap.zero_apply, sub_eq_zero] at this
    rw [Matrix.toLin'_apply, this, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one]
    rfl
  · rintro rfl
    refine LinearMap.ext fun v => ?_
    rw [subOne_apply]
    simp

theorem mulVec_mulVec_inv (g : SL(3, F)) (v : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (g : SL(3, F)) (v : Fin 3 → F) :
    ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def transvectionGroup (S : Submodule F (Fin 3 → F)) : Subgroup SL(3, F) where
  carrier := {g | (∀ v ∈ S, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) ∧
    ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ S}
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh1 v hv, hg1 v hv]
    · rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      have e : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) - v =
          ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) -
            (h : Matrix (Fin 3) (Fin 3) F) *ᵥ v) + ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) := by
        abel
      rw [e]
      exact S.add_mem (hg2 _) (hh2 v)
  one_mem' := ⟨fun v _ => by simp, fun v => by simp⟩
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · conv_lhs => rw [← hg1 v hv]
      exact mulVec_inv_mulVec g v
    · have e : ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v =
          -((g : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) -
            ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
        rw [mulVec_mulVec_inv]
        abel
      rw [e]
      exact S.neg_mem (hg2 _)

theorem mem_transvectionGroup {S : Submodule F (Fin 3 → F)} {g : SL(3, F)} :
    g ∈ transvectionGroup S ↔ (∀ v ∈ S, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) ∧
      ∀ v, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∈ S :=
  Iff.rfl

theorem range_subOne_le {S : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (hg : g ∈ transvectionGroup S) : LinearMap.range (subOne g) ≤ S := by
  rintro _ ⟨v, rfl⟩
  rw [subOne_apply]
  exact hg.2 v

theorem le_ker_subOne {S : Submodule F (Fin 3 → F)} {g : SL(3, F)}
    (hg : g ∈ transvectionGroup S) : S ≤ LinearMap.ker (subOne g) := by
  intro v hv
  rw [LinearMap.mem_ker, subOne_apply, hg.1 v hv, sub_self]

theorem comp_eq_zero_of_comp_self {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hV : finrank F V = 3) {f g : Module.End F V} (hf : f ∘ₗ f = 0)
    (hg : g ∘ₗ g = 0) (hfg : f ∘ₗ g = g ∘ₗ f) : f ∘ₗ g = 0 := by
  have hrank : ∀ h : Module.End F V, h ∘ₗ h = 0 → finrank F (LinearMap.range h) ≤ 1 := by
    intro h hh
    have h1 : LinearMap.range h ≤ LinearMap.ker h := by
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hh, LinearMap.zero_apply]
    have h2 := Submodule.finrank_mono h1
    have h3 := LinearMap.finrank_range_add_finrank_ker h
    omega
  by_contra hne
  have hfgne : LinearMap.range (f ∘ₗ g) ≠ ⊥ := by
    rwa [Ne, LinearMap.range_eq_bot]
  have hpos : 1 ≤ finrank F (LinearMap.range (f ∘ₗ g)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact hfgne
  have hle_f : LinearMap.range (f ∘ₗ g) ≤ LinearMap.range f := LinearMap.range_comp_le_range g f
  have hle_g : LinearMap.range (f ∘ₗ g) ≤ LinearMap.range g := by
    rw [hfg]
    exact LinearMap.range_comp_le_range f g
  have hrf := hrank f hf
  have hrg := hrank g hg
  have e1 : LinearMap.range (f ∘ₗ g) = LinearMap.range f :=
    Submodule.eq_of_le_of_finrank_eq hle_f (le_antisymm (Submodule.finrank_mono hle_f) (by omega))
  have e2 : LinearMap.range (f ∘ₗ g) = LinearMap.range g :=
    Submodule.eq_of_le_of_finrank_eq hle_g (le_antisymm (Submodule.finrank_mono hle_g) (by omega))
  apply hfgne
  rw [LinearMap.range_comp, ← e2, e1, ← LinearMap.range_comp, hf, LinearMap.range_zero]

theorem finrank_fin3 : finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F

section CharTwo

variable [CharP F 2]

theorem subOne_comp_self {b : SL(3, F)} (hb : b * b = 1) : subOne b ∘ₗ subOne b = 0 := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, subOne_apply, subOne_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, hb, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec, LinearMap.zero_apply]
  have h2 : ∀ x : Fin 3 → F, x + x = 0 := fun x => by
    ext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero (x i)
  have e : v - (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v - ((b : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v) =
      (v + v) - ((b : Matrix (Fin 3) (Fin 3) F) *ᵥ v + (b : Matrix (Fin 3) (Fin 3) F) *ᵥ v) := by
    abel
  rw [e, h2, h2, sub_zero]

omit [CharP F 2] in
theorem subOne_comm {b c : SL(3, F)} (hbc : b * c = c * b) :
    subOne b ∘ₗ subOne c = subOne c ∘ₗ subOne b := by
  refine LinearMap.ext fun v => ?_
  simp only [LinearMap.comp_apply, subOne_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
    ← Matrix.SpecialLinearGroup.coe_mul, hbc]
  abel

theorem exists_le_transvectionGroup {B : Subgroup SL(3, F)} (hB2 : ∀ b ∈ B, b * b = 1)
    (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) (hB : B ≠ ⊥) :
    ∃ S : Submodule F (Fin 3 → F), (finrank F S = 1 ∨ finrank F S = 2) ∧
      B ≤ transvectionGroup S := by
  have hzero : ∀ b ∈ B, ∀ c ∈ B, subOne b ∘ₗ subOne c = 0 := fun b hb c hc =>
    comp_eq_zero_of_comp_self finrank_fin3 (subOne_comp_self (hB2 b hb))
      (subOne_comp_self (hB2 c hc)) (subOne_comm (hBc b hb c hc))
  let C : Submodule F (Fin 3 → F) := ⨆ b : B, LinearMap.range (subOne (b : SL(3, F)))
  let A : Submodule F (Fin 3 → F) := ⨅ b : B, LinearMap.ker (subOne (b : SL(3, F)))
  have hCA : C ≤ A := by
    refine iSup_le fun c => le_iInf fun b => ?_
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, hzero b b.2 c c.2, LinearMap.zero_apply]
  have hrange : ∀ b : B, LinearMap.range (subOne (b : SL(3, F))) ≤ C := fun b =>
    le_iSup (fun b : B => LinearMap.range (subOne (b : SL(3, F)))) b
  have hker : ∀ b : B, A ≤ LinearMap.ker (subOne (b : SL(3, F))) := fun b =>
    iInf_le (fun b : B => LinearMap.ker (subOne (b : SL(3, F)))) b
  obtain ⟨b₀, hb₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB
  have hb₀' : subOne (b₀ : SL(3, F)) ≠ 0 := by
    rw [Ne, subOne_eq_zero_iff]
    intro h
    exact hb₀ (Subtype.ext h)
  have hC : 1 ≤ finrank F C := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro hC0
    apply hb₀'
    rw [← LinearMap.range_eq_bot, eq_bot_iff, ← hC0]
    exact hrange b₀
  have hA : finrank F A ≤ 2 := by
    have h1 : A ≠ ⊤ := by
      intro hA
      apply hb₀'
      rw [← LinearMap.ker_eq_top, eq_top_iff, ← hA]
      exact hker b₀
    have := Submodule.finrank_lt h1
    rw [finrank_fin3] at this
    omega
  have hmono := Submodule.finrank_mono hCA
  by_cases h1 : finrank F C = 1
  · refine ⟨C, Or.inl h1, fun b hb => ⟨fun v hv => ?_, fun v => ?_⟩⟩
    · have := hker ⟨b, hb⟩ (hCA hv)
      rwa [LinearMap.mem_ker, subOne_apply, sub_eq_zero] at this
    · rw [← subOne_apply]
      exact hrange ⟨b, hb⟩ ⟨v, rfl⟩
  · refine ⟨A, Or.inr (by omega), fun b hb => ⟨fun v hv => ?_, fun v => ?_⟩⟩
    · have := hker ⟨b, hb⟩ hv
      rwa [LinearMap.mem_ker, subOne_apply, sub_eq_zero] at this
    · rw [← subOne_apply]
      exact hCA (hrange ⟨b, hb⟩ ⟨v, rfl⟩)

end CharTwo

@[expose] def transvectionOf (u w : Fin 3 → F) (h : w ⬝ᵥ u = 0) : SL(3, F) :=
  ⟨1 + Matrix.vecMulVec u w, by
    rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem transvectionOf_mulVec (u w : Fin 3 → F) (h : w ⬝ᵥ u = 0) (x : Fin 3 → F) :
    ((transvectionOf u w h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = x + (w ⬝ᵥ x) • u := by
  change (1 + Matrix.vecMulVec u w) *ᵥ x = _
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul]

theorem transvectionOf_mem {S : Submodule F (Fin 3 → F)} {u w : Fin 3 → F} (hu : u ∈ S)
    (hw : ∀ s ∈ S, w ⬝ᵥ s = 0) :
    transvectionOf u w (hw u hu) ∈ transvectionGroup S := by
  refine ⟨fun v hv => ?_, fun v => ?_⟩
  · rw [transvectionOf_mulVec, hw v hv, zero_smul, add_zero]
  · rw [transvectionOf_mulVec, add_sub_cancel_left]
    exact S.smul_mem _ hu

theorem exists_dotProduct_ne_zero {S : Submodule F (Fin 3 → F)} {v : Fin 3 → F} (hv : v ∉ S) :
    ∃ w : Fin 3 → F, (∀ s ∈ S, w ⬝ᵥ s = 0) ∧ w ⬝ᵥ v ≠ 0 := by
  classical
  obtain ⟨f, hfv, hSf⟩ := Submodule.exists_le_ker_of_notMem hv
  let w : Fin 3 → F := fun i => f fun j => if i = j then 1 else 0
  have hw : ∀ x, w ⬝ᵥ x = f x := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
  refine ⟨w, fun s hs => ?_, ?_⟩
  · rw [hw]
    exact hSf hs
  · rwa [hw]

theorem natFix_transvectionGroup {S : Submodule F (Fin 3 → F)} (hS : S ≠ ⊥) :
    natFix (transvectionGroup S) = S := by
  refine le_antisymm (fun v hv => ?_) (fun v hv g hg => hg.1 v hv)
  by_contra hvS
  obtain ⟨w, hwS, hwv⟩ := exists_dotProduct_ne_zero hvS
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have h := hv _ (transvectionOf_mem hu hwS)
  rw [transvectionOf_mulVec, add_eq_left, smul_eq_zero] at h
  exact h.elim hwv hu0

@[expose] def dotOrth (S : Submodule F (Fin 3 → F)) : Submodule F (Fin 3 → F) where
  carrier := {x | ∀ s ∈ S, s ⬝ᵥ x = 0}
  add_mem' {x y} hx hy s hs := by rw [dotProduct_add, hx s hs, hy s hs, add_zero]
  zero_mem' s _ := dotProduct_zero s
  smul_mem' c x hx s hs := by rw [dotProduct_smul, hx s hs, smul_zero]

theorem dualMat_mulVec_eq_iff (g : SL(3, F)) (x : Fin 3 → F) :
    dualMat g *ᵥ x = x ↔ ∀ y, ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ y - y) ⬝ᵥ x = 0 := by
  have key : dualMat g *ᵥ x = x ↔ ((g : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ x = x := by
    constructor
    · intro h
      conv_lhs => rw [← h]
      rw [Matrix.mulVec_mulVec, dualMat_inv_mul, Matrix.one_mulVec]
    · intro h
      conv_lhs => rw [← h]
      rw [Matrix.mulVec_mulVec, dualMat, ← Matrix.transpose_mul,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.transpose_one, Matrix.one_mulVec]
  rw [key]
  constructor
  · intro h y
    rw [sub_dotProduct, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, h, sub_self]
  · intro h
    ext i
    have hi := h (Pi.single i 1)
    rw [sub_dotProduct, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, sub_eq_zero,
      single_one_dotProduct, single_one_dotProduct] at hi
    exact hi

theorem dualFix_transvectionGroup {S : Submodule F (Fin 3 → F)} (hS : S ≠ ⊤) :
    dualFix (transvectionGroup S) = dotOrth S := by
  refine le_antisymm (fun x hx s hs => ?_) (fun x hx g hg => ?_)
  · by_cases hs0 : s = 0
    · rw [hs0, zero_dotProduct]
    obtain ⟨v, hvS⟩ : ∃ v, v ∉ S := by
      by_contra! h
      exact hS (eq_top_iff.mpr fun v _ => h v)
    obtain ⟨w, hwS, hwv⟩ := exists_dotProduct_ne_zero hvS
    have h := (dualMat_mulVec_eq_iff _ x).mp (hx _ (transvectionOf_mem hs hwS)) v
    rw [transvectionOf_mulVec, add_sub_cancel_left, smul_dotProduct, smul_eq_mul,
      mul_eq_zero] at h
    exact h.resolve_left hwv
  · rw [dualMat_mulVec_eq_iff]
    intro y
    exact hx _ (hg.2 y)

@[expose] def dotDual : (Fin 3 → F) →ₗ[F] Module.Dual F (Fin 3 → F) where
  toFun x :=
    { toFun := fun s => s ⬝ᵥ x
      map_add' := fun s t => add_dotProduct s t x
      map_smul' := fun c s => by simp only [smul_dotProduct, smul_eq_mul, RingHom.id_apply] }
  map_add' x y := by ext s; simp [dotProduct_add]
  map_smul' c x := by ext s; simp [dotProduct_smul, smul_eq_mul]

theorem dotDual_injective : Function.Injective (dotDual (F := F)) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [Submodule.mem_bot]
  ext i
  have := LinearMap.congr_fun hx (Pi.single i 1)
  simpa [dotDual, single_one_dotProduct] using this

theorem finrank_dotOrth (S : Submodule F (Fin 3 → F)) :
    finrank F (dotOrth S) + finrank F S = 3 := by
  have hbij : Function.Bijective (dotDual (F := F)) := by
    refine ⟨dotDual_injective, ?_⟩
    rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact dotDual_injective
    · rw [Subspace.dual_finrank_eq]
  let e := LinearEquiv.ofBijective _ hbij
  have hcomap : dotOrth S = S.dualAnnihilator.comap (e : (Fin 3 → F) →ₗ[F] _) := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    rfl
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [finrank_fin3] at h1
  rw [hcomap, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  omega

@[expose] noncomputable def toHom (S : Submodule F (Fin 3 → F)) (g : transvectionGroup S) :
    ((Fin 3 → F) ⧸ S) →ₗ[F] S :=
  S.liftQ ((subOne (g : SL(3, F))).codRestrict S fun v =>
      range_subOne_le g.2 (LinearMap.mem_range_self _ v))
    (by rw [LinearMap.ker_codRestrict]; exact le_ker_subOne g.2)

theorem toHom_injective (S : Submodule F (Fin 3 → F)) : Function.Injective (toHom S) := by
  intro g h hgh
  apply Subtype.ext
  apply Subtype.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  have key : ∀ x : transvectionGroup S, ((toHom S x (Submodule.Quotient.mk v) : S) : Fin 3 → F) =
      ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v := fun x => by
    rw [toHom, Submodule.liftQ_apply, LinearMap.codRestrict_apply, subOne_apply]
  have := congrArg (fun φ : ((Fin 3 → F) ⧸ S) →ₗ[F] S => ((φ (Submodule.Quotient.mk v) : S) :
    Fin 3 → F)) hgh
  simp only [key] at this
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact sub_left_injective this

variable [Fintype F]

theorem card_transvectionGroup_le {S : Submodule F (Fin 3 → F)}
    (hS : finrank F S = 1 ∨ finrank F S = 2) :
    Nat.card (transvectionGroup S) ≤ Fintype.card F ^ 2 := by
  have : Finite (((Fin 3 → F) ⧸ S) →ₗ[F] S) := Module.finite_of_finite F
  have h1 := Nat.card_le_card_of_injective _ (toHom_injective S)
  have h2 : Nat.card (((Fin 3 → F) ⧸ S) →ₗ[F] S) = Fintype.card F ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card, Module.finrank_linearMap]
    have h3 := Submodule.finrank_quotient_add_finrank S
    rw [finrank_fin3] at h3
    congr 1
    rcases hS with h | h <;> rw [h] at h3 ⊢ <;> omega
  omega

theorem card_le_sq_of_elementary [CharP F 2] {B : Subgroup SL(3, F)}
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b) :
    Nat.card B ≤ Fintype.card F ^ 2 := by
  by_cases hB : B = ⊥
  · rw [hB, Subgroup.card_bot]
    exact Nat.one_le_pow _ _ Fintype.card_pos
  obtain ⟨S, hS, hle⟩ := exists_le_transvectionGroup hB2 hBc hB
  exact (Subgroup.card_le_of_le hle).trans (card_transvectionGroup_le hS)

theorem eq_transvectionGroup_of_card [CharP F 2] {B : Subgroup SL(3, F)}
    (hB2 : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hcard : Nat.card B = Fintype.card F ^ 2) :
    ∃ S : Submodule F (Fin 3 → F), (finrank F S = 1 ∨ finrank F S = 2) ∧
      B = transvectionGroup S := by
  have hB : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 4 ≤ Fintype.card F ^ 2 := by nlinarith
    omega
  obtain ⟨S, hS, hle⟩ := exists_le_transvectionGroup hB2 hBc hB
  exact ⟨S, hS, Subgroup.eq_of_le_of_card_ge hle
    ((card_transvectionGroup_le hS).trans hcard.ge)⟩

theorem card_submodule (S : Submodule F (Fin 3 → F)) :
    Nat.card S = Fintype.card F ^ finrank F S := by
  rw [Module.natCard_eq_pow_finrank (K := F), Nat.card_eq_fintype_card]

theorem card_natFix_transvectionGroup {S : Submodule F (Fin 3 → F)} (hS : S ≠ ⊥) :
    Nat.card (natFix (transvectionGroup S)) = Fintype.card F ^ finrank F S := by
  rw [natFix_transvectionGroup hS, card_submodule]

theorem card_dualFix_transvectionGroup {S : Submodule F (Fin 3 → F)} (hS : S ≠ ⊤) :
    Nat.card (dualFix (transvectionGroup S)) = Fintype.card F ^ (3 - finrank F S) := by
  rw [dualFix_transvectionGroup hS, card_submodule]
  have := finrank_dotOrth S
  congr 1
  omega

@[expose] noncomputable def lineZero : Submodule F (Fin 3 → F) :=
  Submodule.span F {Pi.single 0 1}

omit [Fintype F] in
theorem finrank_lineZero : finrank F (lineZero (F := F)) = 1 :=
  finrank_span_singleton (by simp)

theorem not_exists_natural_dual_iso :
    ¬∃ φ : (Fin 3 → F) ≃+ (Fin 3 → F),
      ∀ (g : SL(3, F)) v, φ ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ v) = dualMat g *ᵥ φ v := by
  rintro ⟨φ, hφ⟩
  have h1 := card_natFix_eq_of_iso hφ (transvectionGroup lineZero)
  have hne : lineZero (F := F) ≠ ⊥ := by
    intro h
    have := finrank_lineZero (F := F)
    rw [h, finrank_bot] at this
    exact zero_ne_one this
  have hne' : lineZero (F := F) ≠ ⊤ := by
    intro h
    have := finrank_lineZero (F := F)
    rw [h, finrank_top, finrank_fin3] at this
    omega
  rw [card_natFix_transvectionGroup hne, card_dualFix_transvectionGroup hne', finrank_lineZero]
    at h1
  have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have : Fintype.card F ^ 1 < Fintype.card F ^ (3 - 1) :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end CFSG.RankThree.FFModules
