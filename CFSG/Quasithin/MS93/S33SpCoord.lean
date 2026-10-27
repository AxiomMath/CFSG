module

public import CFSG.Quasithin.MS93.MSPNorm
public import CFSG.Quasithin.MS93.S34Ext

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {G : Type} [Group G]

section Generic

variable {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (GL ι F)} {α : ↥A →* ↥Γ} {β : ↥V →* Multiplicative (Fin 1 → ι → F)}

theorem coordMap_conj' (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hβ : Function.Surjective β)
    (hβα : ∀ a : ↥A, IsCoordAct β a ((α a : GL ι F) : Matrix ι ι F).mulVec)
    {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G)) {f : (ι → F) → (ι → F)}
    (hf : IsCoordAct β t f) (a : ↥A) (x : ι → F) :
    f (((α a : GL ι F) : Matrix ι ι F) *ᵥ x) =
      ((α ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.1 htA a).1 a.2⟩ : GL ι F) :
        Matrix ι ι F) *ᵥ f x := by
  set a' : ↥A := ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.1 htA a).1 a.2⟩
  have h1 := hf.mul (hAV a.2) (hβα a)
  have h2 := (hβα a').mul htV hf
  have heq : (t : G) * a = (a' : G) * t := by simp [a']
  rw [heq] at h1
  have := IsCoordAct.unique hβ (mul_mem (hAV a'.2) htV) h1 h2
  exact congrFun this x

omit [Fintype ι] [DecidableEq ι] in
theorem coordMap_inv_comp' (hβ : Function.Surjective β) {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) {f f' : (ι → F) → (ι → F)}
    (hf : IsCoordAct β t f) (hf' : IsCoordAct β t⁻¹ f') (x : ι → F) :
    f (f' x) = x ∧ f' (f x) = x := by
  have h1 := hf.mul (inv_mem htV) hf'
  have h2 := hf'.mul htV hf
  rw [mul_inv_cancel] at h1
  rw [inv_mul_cancel] at h2
  exact ⟨congrFun (IsCoordAct.unique hβ (one_mem _) h1 isCoordAct_one) x,
    congrFun (IsCoordAct.unique hβ (one_mem _) h2 isCoordAct_one) x⟩

omit [Fintype ι] [DecidableEq ι] in
theorem isCoordAct_iterate' {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {f : (ι → F) → (ι → F)} (hf : IsCoordAct β g f) (m : ℕ) :
    IsCoordAct β (g ^ m) (f^[m]) := by
  induction m with
  | zero => simpa using (isCoordAct_one (β := β))
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ]
    exact ih.mul hg hf

omit [Fintype ι] [DecidableEq ι] in
theorem crd_commutator_kernel {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    {f : (ι → F) → (ι → F)} (hf : IsCoordAct β g f) (u : ↥V) (hc : ⁅g, (u : G)⁆ ∈ V) :
    Multiplicative.toAdd (β ⟨⁅g, (u : G)⁆, hc⟩) 0 =
      f (Multiplicative.toAdd (β u) 0) - Multiplicative.toAdd (β u) 0 := by
  set w : ↥V := ⟨g * u * g⁻¹, conj_mem_of_mem_normalizer hg u⟩
  have he : (⟨⁅g, (u : G)⁆, hc⟩ : ↥V) = w * u⁻¹ := by
    apply Subtype.ext
    simp only [w, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he, map_mul, map_inv, toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
  congr 1
  exact hf u w rfl

omit [Fintype ι] [DecidableEq ι] in
theorem fix_of_mem_centralizer' {R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.centralizer (R : Set G)) {f : (ι → F) → (ι → F)}
    (hf : IsCoordAct β y f) {u : ↥V} (hu : (u : G) ∈ R) :
    f (Multiplicative.toAdd (β u) 0) = Multiplicative.toAdd (β u) 0 := by
  have hc : (u : G) = y * u * y⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hy u hu
    rw [← this, mul_inv_cancel_right]
  exact (hf u u hc).symm

end Generic

theorem eq_id_of_quadratic' {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    {f g : W →+ W} {σ : F →+* F} (hσ : ∀ (c : F) (x : W), f (c • x) = σ c • f x)
    (hne : ∃ c : F, σ c ≠ c) (hg : ∀ (c : F) (x : W), g (c • x) = c • g x)
    (hfg : ∀ x : W, f (g x - x) = g x - x) (x : W) : g x = x := by
  by_contra hx
  obtain ⟨c, hc⟩ := hne
  apply hc
  have hx' : g x - x ≠ 0 := sub_ne_zero.2 hx
  have h1 := hσ c (g x - x)
  have h2 : f (c • (g x - x)) = c • (g x - x) := by
    have : c • (g x - x) = g (c • x) - c • x := by rw [hg, smul_sub]
    rw [this, hfg]
  rw [h2, hfg] at h1
  have h3 := sub_eq_zero.2 h1
  rw [← sub_smul] at h3
  exact (sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hx')).symm

section Sp4

variable {A V Z : Subgroup G} {F : Type} [Field F] {α : ↥A →* ↥(StatedSp 2 F)}
  {β : ↥V →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}

theorem isCoordAct_of_natSp
    (hβα : ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (α a : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i))
    (a : ↥A) : IsCoordAct β a (MSP.mat (α a)).mulVec := by
  intro u v huv
  simpa [moduleAct] using hβα a u v huv 0

variable (hα : Function.Surjective α) (hAV : A ≤ Subgroup.normalizer (V : Set G))
  (hβ : Function.Surjective β) (hβα : ∀ a : ↥A, IsCoordAct β a (MSP.mat (α a)).mulVec)
include hα hAV hβ hβα

theorem normalizes_coordMap {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G)) {f : MSP.V4 F →+ MSP.V4 F}
    (hf : IsCoordAct β t f) : MSP.Normalizes f := by
  intro g
  obtain ⟨a, rfl⟩ := hα g
  exact ⟨α ⟨t * a * t⁻¹, (Subgroup.mem_normalizer_iff.1 htA a).1 a.2⟩,
    fun v => coordMap_conj' (Γ := StatedSp 2 F) hAV hβ hβα htV htA hf a v⟩

omit hα hAV hβα in
theorem bijective_coordMap {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    {f f' : MSP.V4 F → MSP.V4 F} (hf : IsCoordAct β t f) (hf' : IsCoordAct β t⁻¹ f') :
    Function.Bijective f := by
  have hinv := coordMap_inv_comp' hβ htV hf hf'
  exact ⟨fun x y hxy => by rw [← (hinv x).2, ← (hinv y).2, hxy],
    fun x => ⟨f' x, (hinv x).1⟩⟩

theorem exists_semilinear_sp [Finite F] {t : G} (htV : t ∈ Subgroup.normalizer (V : Set G))
    (htA : t ∈ Subgroup.normalizer (A : Set G)) {f : MSP.V4 F →+ MSP.V4 F}
    (hf : IsCoordAct β t f) {f' : MSP.V4 F → MSP.V4 F} (hf' : IsCoordAct β t⁻¹ f') :
    ∃ σ : F →+* F, ∀ (c : F) (v : MSP.V4 F), f (c • v) = σ c • f v :=
  MSP.exists_semilinear (bijective_coordMap hβ htV hf hf')
    (normalizes_coordMap hα hAV hβ hβα htV htA hf)

theorem exists_sp4_of_linear [Finite F] [CharP F 2] {t : G}
    (htV : t ∈ Subgroup.normalizer (V : Set G)) (htA : t ∈ Subgroup.normalizer (A : Set G))
    {f : MSP.V4 F →+ MSP.V4 F} (hf : IsCoordAct β t f) {f' : MSP.V4 F → MSP.V4 F}
    (hf' : IsCoordAct β t⁻¹ f') (hlin : ∀ (c : F) (v : MSP.V4 F), f (c • v) = c • f v)
    {e : ℕ} (he : t ^ 2 ^ e = 1) : ∃ g : MSP.Sp4 F, IsCoordAct β t (MSP.mat g).mulVec := by
  have hpow : ∀ v, f^[2 ^ e] v = v := by
    intro v
    have h := isCoordAct_iterate' htV hf (2 ^ e)
    rw [he] at h
    exact congrFun (IsCoordAct.unique hβ (one_mem _) h isCoordAct_one) v
  obtain ⟨g, hg⟩ := MSP.exists_eq_mat_of_two_power (bijective_coordMap hβ htV hf hf')
    (normalizes_coordMap hα hAV hβ hβα htV htA hf) hlin hpow
  exact ⟨g, hf.congr hg⟩

end Sp4

end CFSG.Quasithin.MS93.S33
