module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
import CFSG.LocalAnalysis.StandardType.GGLangSixRoot

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.RootAut

private abbrev ggNbrLSideRSExcU4_toRat {τ : Tag} (γ : Fin τ.rank → ℤ) : Fin τ.rank → ℚ :=
  fun i => (γ i : ℚ)

private noncomputable def ggNbrLSideRSExcU4_formQ (τ : Tag) :
    LinearMap.BilinForm ℚ (Fin τ.rank → ℚ) :=
  Matrix.toBilin' (τ.symmetrizedCartan.map (Int.cast : ℤ → ℚ))

private theorem ggNbrLSideRSExcU4_formQ_toRat (τ : Tag) (x y : Fin τ.rank → ℤ) :
    ggNbrLSideRSExcU4_formQ τ (ggNbrLSideRSExcU4_toRat x) (ggNbrLSideRSExcU4_toRat y) =
      (iform x y : ℚ) := by
  rw [ggNbrLSideRSExcU4_formQ, Matrix.toBilin'_apply']
  simp only [ggNbrLSideRSExcU4_toRat, iform, Matrix.mulVec, Matrix.map_apply, dotProduct,
    Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem ggNbrLSideRSExcU4_posDef_symmetrizedCartan_int (τ : Tag) :
    τ.symmetrizedCartan.PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact (symmetrizedCartan_symm τ i j).symm
  · have hpos := iform_self_pos hx
    have e : dotProduct (star x) (Matrix.mulVec τ.symmetrizedCartan x) = iform x x := by
      simp only [dotProduct, Matrix.mulVec, star_trivial, iform, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rwa [e]

private theorem ggNbrLSideRSExcU4_formQ_pos (τ : Tag)
    {x : Fin τ.rank → ℚ} (hx : x ≠ 0) :
    0 < ggNbrLSideRSExcU4_formQ τ x x := by
  have hPD := TauCeti.Matrix.posDef_map_intCast
    (ggNbrLSideRSExcU4_posDef_symmetrizedCartan_int τ)
  have h := hPD.dotProduct_mulVec_pos hx
  simpa [ggNbrLSideRSExcU4_formQ, Matrix.toBilin'_apply', star_trivial] using h

private theorem ggNbrLSideRSExcU4_formQ_span_orthogonal (τ : Tag)
    {Ψ Φ : Set (Fin τ.rank → ℤ)} (h : ∀ α ∈ Ψ, ∀ β ∈ Φ, iform α β = 0) :
    ∀ u ∈ Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Ψ),
      ∀ v ∈ Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Φ),
        ggNbrLSideRSExcU4_formQ τ u v = 0 := by
  classical
  have hbase : ∀ α ∈ Ψ, ∀ β ∈ Φ,
      ggNbrLSideRSExcU4_formQ τ (ggNbrLSideRSExcU4_toRat α)
        (ggNbrLSideRSExcU4_toRat β) = 0 := by
    intro α hα β hβ
    rw [ggNbrLSideRSExcU4_formQ_toRat, h α hα β hβ]
    norm_num
  have hright : ∀ α ∈ Ψ,
      ∀ v ∈ Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Φ),
        ggNbrLSideRSExcU4_formQ τ (ggNbrLSideRSExcU4_toRat α) v = 0 := by
    intro α hα v hv
    refine Submodule.span_induction (p := fun v _ =>
      ggNbrLSideRSExcU4_formQ τ (ggNbrLSideRSExcU4_toRat α) v = 0) ?_ ?_ ?_ ?_ hv
    · rintro v ⟨β, hβ, rfl⟩
      exact hbase α hα β hβ
    · exact LinearMap.BilinForm.zero_right _
    · intro x y _ _ hx0 hy0
      rw [LinearMap.BilinForm.add_right, hx0, hy0, add_zero]
    · intro c x _ hx0
      rw [LinearMap.BilinForm.smul_right, hx0, mul_zero]
  intro u hu
  refine Submodule.span_induction (p := fun u _ =>
    ∀ v ∈ Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Φ),
      ggNbrLSideRSExcU4_formQ τ u v = 0) ?_ ?_ ?_ ?_ hu
  · rintro x ⟨α, hα, rfl⟩ v hv
    exact hright α hα v hv
  · intro v hv
    exact LinearMap.BilinForm.zero_left v
  · intro x y _ _ hx0 hy0 v hv
    rw [LinearMap.BilinForm.add_left, hx0 v hv, hy0 v hv, add_zero]
  · intro c x _ hx0 v hv
    rw [LinearMap.BilinForm.smul_left, hx0 v hv, mul_zero]

private theorem ggNbrLSideRSExcU4_sum_finrank_le_of_orthogonal
    {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (B : LinearMap.BilinForm ℚ V) (hB : ∀ x : V, x ≠ 0 → 0 < B x x)
    {W : ι → Submodule ℚ V} [∀ i, Module.Free ℚ (W i)] [∀ i, Module.Finite ℚ (W i)]
    (horth : ∀ i j, i ≠ j → ∀ x ∈ W i, ∀ y ∈ W j, B x y = 0) :
    ∑ i, Module.finrank ℚ (W i) ≤ Module.finrank ℚ V := by
  classical
  let f : (Π i, W i) →ₗ[ℚ] V :=
    { toFun := fun x => ∑ i, (x i : V)
      map_add' := by
        intro x y
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        simp [Finset.smul_sum] }
  have hinj : Function.Injective f := by
    intro x y hxy
    have hdiff : f (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hzero : x - y = 0 := by
      funext j
      apply Subtype.ext
      by_contra hne
      have hvne : (((x - y) j : W j) : V) ≠ 0 := hne
      have hpos : 0 < B (((x - y) j : W j) : V) (((x - y) j : W j) : V) := hB _ hvne
      have hterm : B (((x - y) j : W j) : V) (((x - y) j : W j) : V) = 0 := by
        have h1 : B (f (x - y)) (((x - y) j : W j) : V) = 0 := by
          rw [hdiff, LinearMap.BilinForm.zero_left]
        have h2 : B (f (x - y)) (((x - y) j : W j) : V) =
            ∑ i, B (((x - y) i : W i) : V) (((x - y) j : W j) : V) := by
          rw [show f (x - y) = ∑ i, (((x - y) i : W i) : V) from rfl]
          exact LinearMap.BilinForm.sum_left B Finset.univ _ _
        rw [h2, Finset.sum_eq_single j] at h1
        · exact h1
        · intro i _ hij
          exact horth i j hij ((x - y) i) ((x - y) i).2 ((x - y) j) ((x - y) j).2
        · intro h; exact absurd (Finset.mem_univ j) h
      exact hpos.ne' hterm
    exact sub_eq_zero.1 hzero
  have hfr : Module.finrank ℚ (Π i, W i) = ∑ i, Module.finrank ℚ (W i) :=
    Module.finrank_pi_fintype ℚ
  calc ∑ i, Module.finrank ℚ (W i)
      = Module.finrank ℚ (Π i, W i) := hfr.symm
    _ ≤ Module.finrank ℚ V := LinearMap.finrank_le_finrank_of_injective hinj

private theorem ggNbrLSideRSExcU4_orbit_image_ne
    {τ : Tag} {L : Type} [Field L]
    [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p) {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {s : ℕ}
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {k l : ℕ} (hkl : k < l) (hl : l < s) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
      (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i := by
  intro h
  have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i =
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] ''
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[l - k] '' componentRoots (rootCharHom a) i) := by
    rw [Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  rw [h2] at h
  have h3 := (Set.image_injective.2 (S.ρ.injective.iterate k)) h
  exact hmin (l - k) (by omega) (by omega) h3.symm

private theorem ggNbrLSideRSExcU4_iform_eq_zero_of_mem_iterate_ne
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ}
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    {k l : ℕ} (hkl : k < l) (hl : l < s) {α β : Fin τ.rank → ℤ}
    (hα : α ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots (rootCharHom a) i)
    (hβ : β ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots (rootCharHom a) i) :
    iform α β = 0 := by
  by_contra hne
  obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k
  obtain ⟨j', hj'⟩ := outer_iterate_image_component S hT i l
  have hαj : α ∈ componentRoots (rootCharHom a) j := by rw [hj]; exact hα
  have hβj : β ∈ componentRoots (rootCharHom a) j' := by rw [hj']; exact hβ
  obtain ⟨hαk, hαeq⟩ := hαj
  obtain ⟨hβk, hβeq⟩ := hβj
  have hmk : (⟦(⟨α, hαk⟩ : kernelRoots (rootCharHom a))⟧ :
      KernelComponent (rootCharHom a)) = ⟦(⟨β, hβk⟩ : kernelRoots (rootCharHom a))⟧ :=
    mk_eq_of_iform_ne_zero hne
  have hjeq : j = j' := by
    rw [← hαeq, ← hβeq]
    exact hmk
  apply ggNbrLSideRSExcU4_orbit_image_ne S i hmin hkl hl
  rw [← hj, ← hj', hjeq]

theorem ggNbrLSideRSExc_u4 :
    GGNbrLSideRSExcU4 := by
  intro τ L _ _ p₀ S a i hT hrank hcard
  classical
  let Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i
  let s : ℕ := componentOrbitLength S.ρ Ψ
  let Ψk : Fin s → Set (Fin τ.rank → ℤ) :=
    fun k => (S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' Ψ
  let W : Fin s → Submodule ℚ (Fin τ.rank → ℚ) :=
    fun k => Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Ψk k)
  obtain ⟨-, -, hmin⟩ := outer_componentOrbitLength_spec S hT i
  have hmin' : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' Ψ ≠ Ψ := hmin
  have hroot : ∀ k : Fin s, IsRootComponent (Ψk k) := by
    intro k
    obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k.val
    change IsRootComponent ((S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' Ψ)
    rw [← hj]
    exact isRootComponent_componentRoots j
  have hcardk : ∀ k : Fin s, (Ψk k).ncard = 6 := by
    intro k
    change ((S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' Ψ).ncard = 6
    rw [Set.ncard_image_of_injective _ (S.ρ.injective.iterate k.val)]
    exact hcard
  have hrankk : ∀ k : Fin s, compRank (Ψk k) = 2 := fun k =>
    LangRat.compRank_eq_two_of_ncard_eq_six (hroot k) (hcardk k)
  have hWrank : ∀ k : Fin s, Module.finrank ℚ (W k) = 2 := by
    intro k
    change Module.finrank ℚ (Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Ψk k)) = 2
    rw [show Module.finrank ℚ
        (Submodule.span ℚ (ggNbrLSideRSExcU4_toRat '' Ψk k)) = compRank (Ψk k) from rfl]
    exact hrankk k
  have hrootorth : ∀ k l : Fin s, k ≠ l → ∀ α ∈ Ψk k, ∀ β ∈ Ψk l, iform α β = 0 := by
    intro k l hkl α hα β hβ
    have hvalne : k.val ≠ l.val := fun h => hkl (Fin.ext h)
    rcases lt_or_gt_of_ne hvalne with hlt | hgt
    · exact ggNbrLSideRSExcU4_iform_eq_zero_of_mem_iterate_ne S hT i hmin' hlt (by omega)
        hα hβ
    · rw [iform_comm]
      exact ggNbrLSideRSExcU4_iform_eq_zero_of_mem_iterate_ne S hT i hmin' hgt (by omega)
        hβ hα
  have horthW : ∀ k l : Fin s, k ≠ l → ∀ x ∈ W k, ∀ y ∈ W l,
      ggNbrLSideRSExcU4_formQ τ x y = 0 := by
    intro k l hkl
    exact ggNbrLSideRSExcU4_formQ_span_orthogonal τ (hrootorth k l hkl)
  haveI : ∀ k : Fin s, Module.Finite ℚ (W k) := fun k =>
    FiniteDimensional.finiteDimensional_submodule (W k)
  haveI : ∀ k : Fin s, Module.Free ℚ (W k) := fun k => Module.Free.of_divisionRing ℚ (W k)
  have hbound : ∑ k : Fin s, Module.finrank ℚ (W k) ≤ τ.rank := by
    calc ∑ k : Fin s, Module.finrank ℚ (W k)
        ≤ Module.finrank ℚ (Fin τ.rank → ℚ) :=
          ggNbrLSideRSExcU4_sum_finrank_le_of_orthogonal (B :=
            ggNbrLSideRSExcU4_formQ τ) (hB := fun x hx => ggNbrLSideRSExcU4_formQ_pos τ hx)
            (W := W) horthW
      _ = τ.rank := Module.finrank_fin_fun ℚ
  have hsum : ∑ k : Fin s, Module.finrank ℚ (W k) = 2 * s := by
    calc ∑ k : Fin s, Module.finrank ℚ (W k) = ∑ _k : Fin s, 2 :=
          Finset.sum_congr rfl fun k _ => hWrank k
      _ = s * 2 := by simp [Finset.sum_const, Finset.card_univ]
      _ = 2 * s := by rw [Nat.mul_comm]
  change 2 * s ≤ τ.rank
  calc 2 * s = ∑ k : Fin s, Module.finrank ℚ (W k) := hsum.symm
    _ ≤ τ.rank := hbound

end CFSG.StandardType

end
