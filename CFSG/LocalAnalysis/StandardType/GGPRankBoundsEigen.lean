module

public import CFSG.RankThree.PartTwo.Sec4.Item413Eigen
public import CFSG.LieType.BorelTits.Flag
public import CFSG.LieType.BorelTits.FormFlag
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

namespace PRankBounds

open Matrix

section Eigen

variable {L : Type*} [Field L] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Subgroup (GL ι L)} {b : Module.Basis ι L (ι → L)} {d : GL ι L → ι → L}

@[expose] def sForm (τ : L →+* L) (M : Matrix ι ι L) (u w : ι → L) : L :=
  (fun i => τ (u i)) ⬝ᵥ (M *ᵥ w)

omit [DecidableEq ι] in
theorem sForm_add_left (τ : L →+* L) (M : Matrix ι ι L) (u u' w : ι → L) :
    sForm τ M (u + u') w = sForm τ M u w + sForm τ M u' w := by
  simp only [sForm, Pi.add_apply, map_add]
  rw [← add_dotProduct]
  rfl

omit [DecidableEq ι] in
theorem sForm_smul_left (τ : L →+* L) (M : Matrix ι ι L) (c : L) (u w : ι → L) :
    sForm τ M (c • u) w = τ c * sForm τ M u w := by
  simp only [sForm, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← smul_eq_mul, ← smul_dotProduct]
  rfl

omit [DecidableEq ι] in
theorem sForm_add_right (τ : L →+* L) (M : Matrix ι ι L) (u w w' : ι → L) :
    sForm τ M u (w + w') = sForm τ M u w + sForm τ M u w' := by
  simp only [sForm, Matrix.mulVec_add, dotProduct_add]

omit [DecidableEq ι] in
theorem sForm_smul_right (τ : L →+* L) (M : Matrix ι ι L) (c : L) (u w : ι → L) :
    sForm τ M u (c • w) = c * sForm τ M u w := by
  simp only [sForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem sForm_sum_left (τ : L →+* L) (M : Matrix ι ι L) (s : Finset ι) (u : ι → ι → L)
    (w : ι → L) : sForm τ M (∑ a ∈ s, u a) w = ∑ a ∈ s, sForm τ M (u a) w := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, sForm, Pi.zero_apply, map_zero]
    exact zero_dotProduct _
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sForm_add_left, ih]

theorem sForm_sum_right (τ : L →+* L) (M : Matrix ι ι L) (s : Finset ι) (u : ι → L)
    (w : ι → ι → L) : sForm τ M u (∑ a ∈ s, w a) = ∑ a ∈ s, sForm τ M u (w a) := by
  induction s using Finset.induction_on with
  | empty => simp [sForm]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sForm_add_right, ih]

omit [DecidableEq ι] in
theorem sForm_mulVec_mulVec (τ : L →+* L) (M : Matrix ι ι L) {x : Matrix ι ι L}
    (hx : (x.map τ)ᵀ * M * x = M) (u w : ι → L) :
    sForm τ M (x *ᵥ u) (x *ᵥ w) = sForm τ M u w := by
  have h : (fun i => τ ((x *ᵥ u) i)) = (x.map τ) *ᵥ (fun i => τ (u i)) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [sForm, sForm, h, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hx]

theorem sForm_eigen_ne_zero (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    (τ : L →+* L) (M : Matrix ι ι L)
    (hiso : ∀ x ∈ E, (((x : GL ι L) : Matrix ι ι L).map τ)ᵀ * M * (x : Matrix ι ι L) = M)
    {a c : ι} (hne : sForm τ M (b a) (b c) ≠ 0) {x : GL ι L} (hx : x ∈ E) :
    τ (d x a) * d x c = 1 := by
  have h1 := sForm_mulVec_mulVec τ M (hiso x hx) (b a) (b c)
  rw [hb x hx a, hb x hx c, sForm_smul_left, sForm_smul_right] at h1
  have : (τ (d x a) * d x c - 1) * sForm τ M (b a) (b c) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · linear_combination h
  · exact absurd h hne

theorem eq_zero_of_sum_eigen (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    (hdist : ∀ a c, (∀ x ∈ E, d x a = d x c) → a = c) (τ : L →+* L)
    (hτ : Function.Injective τ) (k : ι → L)
    (h : ∀ x ∈ E, ∑ a, k a * τ (d x a) = 0) : ∀ a, k a = 0 := by
  let χ : ι → (E →* L) := fun a => τ.toMonoidHom.comp
    { toFun := fun x => d x a
      map_one' := CFSG.RankThree.PartTwo.Sec4.eigen_one hb a
      map_mul' := fun x y => CFSG.RankThree.PartTwo.Sec4.eigen_mul hb x.2 y.2 a }
  have hχ : Function.Injective χ := by
    intro a c hac
    refine hdist a c fun x hx => hτ ?_
    have := congrArg (fun f : E →* L => f ⟨x, hx⟩) hac
    simpa [χ] using this
  have hli := (linearIndependent_monoidHom E L).comp χ hχ
  have hsum : ∑ a, k a • ((χ a : E →* L) : E → L) = 0 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact h x x.2
  exact Fintype.linearIndependent_iff.mp hli k hsum

theorem sForm_orbit_eq_sum (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    (τ : L →+* L) (M : Matrix ι ι L) {x : GL ι L} (hx : x ∈ E) (v : ι → L) :
    sForm τ M ((x : Matrix ι ι L) *ᵥ v) v =
      ∑ a, (τ (b.repr v a) * sForm τ M (b a) v) * τ (d x a) := by
  have hxv : (x : Matrix ι ι L) *ᵥ v = ∑ a, (b.repr v a * d x a) • b a := by
    conv_lhs => rw [← b.sum_repr v]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mulVec_smul, hb x hx a, smul_smul]
  rw [hxv, sForm_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sForm_smul_left, map_mul]
  ring

theorem coeff_mul_sForm_eq_zero (hb : ∀ x ∈ E, ∀ a, (x : Matrix ι ι L) *ᵥ b a = d x a • b a)
    (hdist : ∀ a c, (∀ x ∈ E, d x a = d x c) → a = c) (τ : L →+* L)
    (hτ : Function.Injective τ) (M : Matrix ι ι L) (v : ι → L)
    (hv : ∀ x ∈ E, sForm τ M ((x : Matrix ι ι L) *ᵥ v) v = 0) (a : ι) :
    τ (b.repr v a) * sForm τ M (b a) v = 0 :=
  eq_zero_of_sum_eigen hb hdist τ hτ _ (fun x hx => by
    rw [← sForm_orbit_eq_sum hb τ M hx v]
    exact hv x hx) a

omit [DecidableEq ι] in
theorem sForm_eq_sum_right (τ : L →+* L) (M : Matrix ι ι L) (u v : ι → L) :
    sForm τ M u v = ∑ c, b.repr v c * sForm τ M u (b c) := by
  classical
  conv_lhs => rw [← b.sum_repr v]
  rw [sForm_sum_right]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sForm_smul_right]

theorem exists_sForm_ne_zero (τ : L →+* L) (hτ : Function.Injective τ) {M : Matrix ι ι L}
    (hM : M.det ≠ 0) {u : ι → L} (hu : u ≠ 0) : ∃ c, sForm τ M u (b c) ≠ 0 := by
  by_contra hc
  push Not at hc
  have hall : ∀ w, sForm τ M u w = 0 := fun w => by
    rw [sForm_eq_sum_right (b := b)]
    exact Finset.sum_eq_zero fun c _ => by rw [hc c, mul_zero]
  have hτu : (fun i => τ (u i)) = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero hM (dotProduct_eq_zero_iff.mp fun w => ?_)
    rw [← Matrix.dotProduct_mulVec]
    exact hall w
  apply hu
  funext i
  have := congrFun hτu i
  exact hτ (by rw [this, Pi.zero_apply, map_zero])

end Eigen

section Fixed

open CFSG.LieType.BorelTits

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] {H : Type*} [Group H]

@[expose] def fixSub (ρ : H →* Module.End K V) (T : Subgroup H) : Submodule K V where
  carrier := {v | ∀ t ∈ T, ρ t v = v}
  add_mem' {u v} hu hv t ht := by rw [map_add, hu t ht, hv t ht]
  zero_mem' t _ := map_zero _
  smul_mem' c v hv t ht := by rw [map_smul, hv t ht]

theorem mem_fixSub {ρ : H →* Module.End K V} {T : Subgroup H} {v : V} :
    v ∈ fixSub ρ T ↔ ∀ t ∈ T, ρ t v = v := Iff.rfl

theorem apply_mem_fixSub {ρ : H →* Module.End K V} {T : Subgroup H} {e : H}
    (he : e ∈ Subgroup.normalizer (T : Set H)) {v : V} (hv : v ∈ fixSub ρ T) :
    ρ e v ∈ fixSub ρ T := by
  refine mem_fixSub.mpr fun t ht => ?_
  have ht' : e⁻¹ * t * e⁻¹⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (inv_mem he) t).mp ht
  rw [inv_inv] at ht'
  have h := mem_fixSub.mp hv _ ht'
  have hmul : ρ t * ρ e = ρ e * ρ (e⁻¹ * t * e) := by
    rw [← map_mul, ← map_mul]
    congr 1
    group
  calc ρ t (ρ e v) = (ρ t * ρ e) v := rfl
    _ = ρ e (ρ (e⁻¹ * t * e) v) := by rw [hmul]; rfl
    _ = ρ e v := by rw [h]

theorem false_of_fixSub_inf_perp [Finite V] [FiniteDimensional K V] (p : ℕ) [Fact p.Prime]
    [CharP K p] (F : ReflForm K V) (ρ : H →* Module.End K V) (hρ : IsIsometric F ρ)
    (hinj : Function.Injective ρ) (T : Subgroup H) (hT : IsPGroup p T) (hT1 : T ≠ ⊥)
    (hW : fixSub ρ T ⊓ F.perp (fixSub ρ T) = ⊥) : False := by
  set W := fixSub ρ T with hWdef
  have hinv : ∀ g ∈ T, ∀ v ∈ F.perp W, ρ g v ∈ F.perp W := fun g hg v hv =>
    IsIsometric.apply_mem_perp_of_forall hρ
      (fun w hw => by rw [mem_fixSub.mp hw g⁻¹ (inv_mem hg)]; exact hw) hv
  let ρ' : T →* Module.End K (F.perp W) :=
    { toFun := fun g => (ρ g).restrict fun v hv => hinv g g.2 v hv
      map_one' := by
        ext v
        simp [LinearMap.restrict_apply]
      map_mul' := fun g h => by
        ext v
        simp only [Subgroup.coe_mul, map_mul]
        rfl }
  have hperp : F.perp W = ⊥ := by
    by_contra hne
    have : Nontrivial (F.perp W) := Submodule.nontrivial_iff_ne_bot.mpr hne
    obtain ⟨v, hv0, hv⟩ := exists_fixed_ne_zero ρ' p ⊤ (hT.of_equiv Subgroup.topEquiv.symm)
    have hvW : (v : V) ∈ W := mem_fixSub.mpr fun t ht => by
      have := hv ⟨t, ht⟩ (Subgroup.mem_top _)
      exact congrArg Subtype.val this
    have hmem : (v : V) ∈ W ⊓ F.perp W := ⟨hvW, v.2⟩
    rw [hW, Submodule.mem_bot] at hmem
    exact hv0 (Subtype.ext hmem)
  have hWtop : W = ⊤ := by
    rw [← F.perp_perp W, hperp, ReflForm.perp_bot]
  apply hT1
  rw [eq_bot_iff]
  intro t ht
  rw [Subgroup.mem_bot]
  apply hinj
  ext v
  have hv : v ∈ W := hWtop ▸ Submodule.mem_top
  rw [mem_fixSub.mp hv t ht, map_one, Module.End.one_apply]

end Fixed

end PRankBounds

end CFSG.StandardType
