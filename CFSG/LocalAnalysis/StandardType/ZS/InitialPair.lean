module

public import CFSG.LocalAnalysis.StandardType.ZS.Support
public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflPair
import CFSG.LocalAnalysis.StandardType.ZS.Conjugate

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

section DetNeZero

variable {k : ℕ} {u : Fin k → U} {φ : Fin k → Module.Dual (ZMod p) U}

private def reflectionClosure (u : Fin k → U) (φ : Fin k → Module.Dual (ZMod p) U)
    (hφ : ∀ i, φ i (u i) = 2) : Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure (Set.range fun i => Module.reflection (hφ i))

private theorem exists_apply_ne_zero {φ : Module.Dual (ZMod p) U} (h : φ ≠ 0) :
    ∃ v, φ v ≠ 0 := by
  by_contra h'
  push Not at h'
  exact h (by ext v; exact h' v)

private theorem movedSpace_reflection_eq_span {a : U} {φ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hφ0 : φ ≠ 0) :
    HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) =
      Submodule.span (ZMod p) {a} := by
  apply le_antisymm
  · rintro w ⟨v, rfl⟩
    change Module.reflection hφ v - v ∈ Submodule.span (ZMod p) {a}
    rw [Module.reflection_apply]
    rw [show v - φ v • a - v = -(φ v • a) by abel]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ (φ v)
      (Submodule.subset_span (Set.mem_singleton a)))
  · rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨v, hv⟩ := exists_apply_ne_zero hφ0
    have hmem : -a ∈ HardMathSupport.Kantor79.movedSpace (Module.reflection hφ) := by
      refine ⟨(φ v)⁻¹ • v, ?_⟩
      have hφv : φ ((φ v)⁻¹ • v) = 1 := by
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
      change Module.reflection hφ ((φ v)⁻¹ • v) - ((φ v)⁻¹ • v) = -a
      rw [Module.reflection_apply, hφv, one_smul]
      abel
    simpa using Submodule.neg_mem _ hmem

private theorem functional_ne_zero_of_det_ne_zero
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) (i : Fin k) : φ i ≠ 0 := by
  intro h
  exact hdet (Matrix.det_eq_zero_of_row_eq_zero i (by intro j; simp [h]))

private theorem root_ne_zero_of_det_ne_zero
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) (i : Fin k) : u i ≠ 0 := by
  intro h
  exact hdet (Matrix.det_eq_zero_of_column_eq_zero i (by intro j; simp [h]))

private theorem linearIndependent_of_det_ne_zero
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    LinearIndependent (ZMod p) u := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmv : (Matrix.of fun i j => φ i (u j)).mulVec c = 0 := by
    funext i
    have h := congrArg (φ i) hc
    simp only [map_sum, map_smul, smul_eq_mul] at h
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h
  intro i
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hmv) i

private theorem pi_apply_sum (c : Fin k → ZMod p) :
    LinearMap.pi φ (∑ j, c j • u j) =
      (Matrix.of fun i j => φ i (u j)).mulVec c := by
  funext i
  simp [LinearMap.pi_apply, Matrix.mulVec, dotProduct, map_sum, mul_comm, smul_eq_mul]

private theorem reflectionClosure_commutatorSpace_eq_span [Module.Finite (ZMod p) U]
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    HardMathSupport.Kantor79.commutatorSpace (reflectionClosure u φ hφ) =
      Submodule.span (ZMod p) (Set.range u) := by
  have hφi := functional_ne_zero_of_det_ne_zero (u := u) hdet
  have hmoved : ∀ i, HardMathSupport.Kantor79.movedSpace
      (Module.reflection (hφ i)) = Submodule.span (ZMod p) {u i} :=
    fun i => movedSpace_reflection_eq_span (hφ i) (hφi i)
  rw [reflectionClosure]
  apply le_antisymm
  · rw [HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace]
    refine iSup_le fun i => ?_
    rw [hmoved i]
    refine Submodule.span_mono ?_
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    exact ⟨i, hx.symm⟩
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    have hx : u i ∈ HardMathSupport.Kantor79.movedSpace (Module.reflection (hφ i)) := by
      rw [hmoved i]
      exact Submodule.subset_span (Set.mem_singleton (u i))
    exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (Subgroup.subset_closure (Set.mem_range_self i)) hx

private theorem reflectionClosure_centralizerSpace_eq_ker
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    centralizerSpace (reflectionClosure u φ hφ) = LinearMap.ker (LinearMap.pi φ) := by
  have hu := root_ne_zero_of_det_ne_zero (φ := φ) hdet
  rw [reflectionClosure, LinearMap.ker_pi]
  ext v
  rw [mem_centralizerSpace, Submodule.mem_iInf]
  constructor
  · intro hv i
    rw [LinearMap.mem_ker]
    have h1 : Module.reflection (hφ i) v = v := hv _ (Subgroup.subset_closure ⟨i, rfl⟩)
    have h2 : (φ i v) • u i = 0 := by
      have h3 : Module.reflection (hφ i) v - v = 0 := sub_eq_zero.mpr h1
      rw [Module.reflection_apply] at h3
      have h4 : -((φ i v) • u i) = 0 := by rw [← h3]; abel
      simpa using h4
    exact (smul_eq_zero.mp h2).resolve_right (hu i)
  · intro hv
    have hgen : ∀ i, Module.reflection (hφ i) v = v := by
      intro i
      rw [Module.reflection_apply, LinearMap.mem_ker.mp (hv i), zero_smul, sub_zero]
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hgen i
    | one => rfl
    | mul a b ha hb iha ihb => rw [LinearEquiv.mul_apply, ihb, iha]
    | inv a ha iha =>
        calc a⁻¹ v = a⁻¹ (a v) := by rw [iha]
          _ = v := by
            change a.symm (a v) = v
            exact LinearEquiv.symm_apply_apply a v

private theorem reflectionClosure_inf_eq_bot [Module.Finite (ZMod p) U]
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    HardMathSupport.Kantor79.commutatorSpace (reflectionClosure u φ hφ) ⊓
      centralizerSpace (reflectionClosure u φ hφ) = ⊥ := by
  rw [reflectionClosure_commutatorSpace_eq_span hφ hdet,
    reflectionClosure_centralizerSpace_eq_ker hφ hdet]
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p)).mp hx.1
  have hxker : LinearMap.pi φ x = 0 := LinearMap.mem_ker.mp hx.2
  have hmv : (Matrix.of fun i j => φ i (u j)).mulVec c = 0 := by
    rw [← pi_apply_sum c, hc, hxker]
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  rw [← hc, hc0]
  simp

private theorem reflectionClosure_isCompl [Module.Finite (ZMod p) U]
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    IsCompl (HardMathSupport.Kantor79.commutatorSpace (reflectionClosure u φ hφ))
      (centralizerSpace (reflectionClosure u φ hφ)) := by
  refine IsCompl.of_le (le_of_eq (reflectionClosure_inf_eq_bot hφ hdet)) ?_
  rw [reflectionClosure_commutatorSpace_eq_span hφ hdet,
    reflectionClosure_centralizerSpace_eq_ker hφ hdet]
  intro x _
  have hsurj : Function.Surjective (Matrix.of fun i j => φ i (u j)).mulVec := by
    rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hdet
  obtain ⟨c, hc⟩ := hsurj (LinearMap.pi φ x)
  refine Submodule.mem_sup.mpr ⟨∑ j, c j • u j, ?_, x - ∑ j, c j • u j, ?_, by abel⟩
  · exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ (c j) (Submodule.subset_span ⟨j, rfl⟩)
  · rw [LinearMap.mem_ker, map_sub, pi_apply_sum c, ← hc]
    abel

private theorem reflectionClosure_finrank [Module.Finite (ZMod p) U]
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) :
    Module.finrank (ZMod p)
      (HardMathSupport.Kantor79.commutatorSpace (reflectionClosure u φ hφ)) = k := by
  rw [reflectionClosure_commutatorSpace_eq_span hφ hdet,
    finrank_span_eq_card (linearIndependent_of_det_ne_zero (φ := φ) hdet)]
  simp

private theorem reflectionClosure_exists_root_mem [Module.Finite (ZMod p) U]
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0)
    {X : Submodule (ZMod p) U}
    (hXV : X ≤ HardMathSupport.Kantor79.commutatorSpace (reflectionClosure u φ hφ))
    (hXinv : ∀ h ∈ reflectionClosure u φ hφ, ∀ x ∈ X, h x ∈ X) (hX0 : X ≠ ⊥) :
    ∃ i0, u i0 ∈ X := by
  have hVH := reflectionClosure_commutatorSpace_eq_span hφ hdet
  by_contra hnone
  push Not at hnone
  obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  have hxV : x ∈ Submodule.span (ZMod p) (Set.range u) := by
    rw [← hVH]; exact hXV hxX
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p)).mp hxV
  obtain ⟨i, hi⟩ : ∃ i, φ i x ≠ 0 := by
    by_contra h
    push Not at h
    have hmv : (Matrix.of fun i j => φ i (u j)).mulVec c = 0 := by
      funext i
      have hi' := h i
      rw [← hc] at hi'
      simp only [map_sum, map_smul, smul_eq_mul] at hi'
      simpa [Matrix.mulVec, dotProduct, mul_comm] using hi'
    have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
    exact hx0 (by rw [← hc, hc0]; simp)
  refine hnone i ?_
  have hrin : Module.reflection (hφ i) x ∈ X :=
    hXinv _ (Subgroup.subset_closure ⟨i, rfl⟩) x hxX
  have hsub : Module.reflection (hφ i) x - x ∈ X := X.sub_mem hrin hxX
  have heq : Module.reflection (hφ i) x - x = -((φ i x) • u i) := by
    rw [Module.reflection_apply]; abel
  have hmem : (φ i x) • u i ∈ X := by
    have h := X.neg_mem hsub
    rw [heq, neg_neg] at h
    exact h
  have hu : u i = (φ i x)⁻¹ • ((φ i x) • u i) :=
    (inv_smul_smul₀ hi (u i)).symm
  rw [hu]
  exact X.smul_mem _ hmem

private theorem reflectionClosure_forall_mem (hφ : ∀ i, φ i (u i) = 2)
    (hconn : ∀ I : Finset (Fin k), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0)
    {X : Submodule (ZMod p) U}
    (hXinv : ∀ h ∈ reflectionClosure u φ hφ, ∀ x ∈ X, h x ∈ X) {i0 : Fin k}
    (hi0 : u i0 ∈ X) :
    ∀ i, u i ∈ X := by
  classical
  by_contra hne
  push Not at hne
  let I : Finset (Fin k) := Finset.univ.filter fun i => u i ∈ X
  have hIne : I.Nonempty := ⟨i0, by simp [I, hi0]⟩
  have hIproper : I ≠ Finset.univ := by
    intro hI
    obtain ⟨i, hi⟩ := hne
    have : i ∈ I := by rw [hI]; exact Finset.mem_univ i
    exact hi (Finset.mem_filter.mp this).2
  obtain ⟨i, hiI, j, hjI, hφji⟩ := hconn I hIne hIproper
  have hiX : u i ∈ X := (Finset.mem_filter.mp hiI).2
  have hjX : u j ∈ X := by
    have hrj : Module.reflection (hφ j) (u i) ∈ X :=
      hXinv _ (Subgroup.subset_closure ⟨j, rfl⟩) _ hiX
    have hsub : Module.reflection (hφ j) (u i) - u i ∈ X := X.sub_mem hrj hiX
    have heq : Module.reflection (hφ j) (u i) - u i = -((φ j (u i)) • u j) := by
      rw [Module.reflection_apply]; abel
    have hmem : (φ j (u i)) • u j ∈ X := by
      have h := X.neg_mem hsub
      rw [heq, neg_neg] at h
      exact h
    have hu : u j = (φ j (u i))⁻¹ • ((φ j (u i)) • u j) :=
      (inv_smul_smul₀ hφji (u j)).symm
    rw [hu]
    exact X.smul_mem _ hmem
  exact hjI (by simp [I, hjX])

private theorem reflectionClosure_irredOnSection [Module.Finite (ZMod p) U]
    (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0)
    (hconn : ∀ I : Finset (Fin k), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0) :
    IrredOnSection (reflectionClosure u φ hφ) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflectionClosure u φ hφ)) := by
  classical
  have hVH := reflectionClosure_commutatorSpace_eq_span hφ hdet
  intro X _ hXV hXinv
  by_cases hX0 : X = ⊥
  · exact Or.inl hX0
  · right
    apply le_antisymm hXV
    rw [hVH, Submodule.span_le]
    rintro x ⟨i, rfl⟩
    obtain ⟨i0, hi0⟩ := reflectionClosure_exists_root_mem hφ hdet hXV hXinv hX0
    exact reflectionClosure_forall_mem hφ hconn hXinv hi0 i

end DetNeZero

private theorem reflection_congr {a : U} {φ : Module.Dual (ZMod p) U} {h₁ h₂ : φ a = 2} :
    Module.reflection h₁ = Module.reflection h₂ := by
  ext v
  rw [Module.reflection_apply]

private theorem cartan_det_identity {R : Type*} [CommRing R] (a b c d e f : R) (hab : a * b = 4) :
    2 * (2 * 2 * 2 - 2 * d * f - a * b * 2 + a * d * e + c * b * f - c * 2 * e)
      = -((a * e - 2 * f) * (b * c - 2 * d)) := by
  linear_combination (norm := ring) (e * c - 4) * hab

theorem splitSupport_of_det_ne_zero [Module.Finite (ZMod p) U] {k : ℕ}
    {u : Fin k → U} {φ : Fin k → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0)
    (hconn : ∀ I : Finset (Fin k), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0) :
    SplitSupport (Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) k := by
  change SplitSupport (reflectionClosure u φ hφ) k
  exact ⟨reflectionClosure_isCompl hφ hdet, reflectionClosure_finrank hφ hdet,
    reflectionClosure_irredOnSection hφ hdet hconn⟩

private theorem connected_fin_two {u : Fin 2 → U} {φ : Fin 2 → Module.Dual (ZMod p) U}
    (ha : φ 0 (u 1) ≠ 0) (hb : φ 1 (u 0) ≠ 0) :
    ∀ I : Finset (Fin 2), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0 := by
  intro I hIne hI
  by_cases h0 : (0 : Fin 2) ∈ I
  · have h1 : (1 : Fin 2) ∉ I := by
      intro h1
      apply hI
      apply Finset.eq_univ_of_forall
      intro i; fin_cases i
      · exact h0
      · exact h1
    exact ⟨0, h0, 1, h1, hb⟩
  · have h1 : (1 : Fin 2) ∈ I := by
      obtain ⟨i, hi⟩ := hIne
      fin_cases i
      · exact absurd hi h0
      · exact hi
    exact ⟨1, h1, 0, h0, ha⟩

private theorem reflection_range_fin_two {r₁ r₂ : U ≃ₗ[ZMod p] U} {u : Fin 2 → U}
    {φ : Fin 2 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hr₁ : r₁ = Module.reflection (hφ 0)) (hr₂ : r₂ = Module.reflection (hφ 1)) :
    Set.range (fun i : Fin 2 => Module.reflection (hφ i)) = {r₁, r₂} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (reflection_congr.trans hr₁.symm)
    · exact Or.inr (reflection_congr.trans hr₂.symm)
  · rintro (rfl | rfl)
    · exact ⟨0, reflection_congr.trans hr₁.symm⟩
    · exact ⟨1, reflection_congr.trans hr₂.symm⟩

private theorem splitSupport_two_of_cartan [Module.Finite (ZMod p) U]
    {r₁ r₂ : U ≃ₗ[ZMod p] U} {u₁ u₂ : U} {φ₁ φ₂ : Module.Dual (ZMod p) U}
    (hφ₁ : φ₁ u₁ = 2) (hφ₂ : φ₂ u₂ = 2)
    (hr₁ : r₁ = Module.reflection hφ₁) (hr₂ : r₂ = Module.reflection hφ₂)
    (ha : φ₁ u₂ ≠ 0) (hb : φ₂ u₁ ≠ 0)
    (hdet : (4 : ZMod p) - φ₁ u₂ * φ₂ u₁ ≠ 0) :
    SplitSupport (Subgroup.closure ({r₁, r₂} : Set (U ≃ₗ[ZMod p] U))) 2 := by
  let u : Fin 2 → U := ![u₁, u₂]
  let φ : Fin 2 → Module.Dual (ZMod p) U := ![φ₁, φ₂]
  have hφ : ∀ i, φ i (u i) = 2 := by
    intro i; fin_cases i <;> simp [u, φ, hφ₁, hφ₂]
  have hdet' : (Matrix.of fun i j => φ i (u j)).det ≠ 0 := by
    have h2 : (Matrix.of fun i j => φ i (u j)).det = (4 : ZMod p) - φ₁ u₂ * φ₂ u₁ := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply]
      have e0 : φ 0 = φ₁ := rfl
      have e1 : φ 1 = φ₂ := rfl
      have g0 : u 0 = u₁ := rfl
      have g1 : u 1 = u₂ := rfl
      rw [e0, e1, g0, g1, hφ₁, hφ₂]
      norm_num
    rw [h2]; exact hdet
  have hss := splitSupport_of_det_ne_zero hφ hdet' (connected_fin_two ha hb)
  have hr₁' : r₁ = Module.reflection (hφ 0) := hr₁.trans reflection_congr.symm
  have hr₂' : r₂ = Module.reflection (hφ 1) := hr₂.trans reflection_congr.symm
  rw [reflection_range_fin_two hφ hr₁' hr₂'] at hss
  exact hss

private theorem connected_fin_three {u : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    (ha : φ 0 (u 1) ≠ 0) (hb : φ 1 (u 0) ≠ 0)
    (hcd : φ 0 (u 2) ≠ 0 ∨ φ 1 (u 2) ≠ 0)
    (hef : φ 2 (u 0) ≠ 0 ∨ φ 2 (u 1) ≠ 0) :
    ∀ I : Finset (Fin 3), I.Nonempty → I ≠ Finset.univ →
      ∃ i ∈ I, ∃ j ∉ I, φ j (u i) ≠ 0 := by
  intro I hIne hIproper
  by_cases h0 : (0 : Fin 3) ∈ I
  · by_cases h1 : (1 : Fin 3) ∈ I
    · have h2 : (2 : Fin 3) ∉ I := by
        intro h2
        apply hIproper
        apply Finset.eq_univ_of_forall
        intro i; fin_cases i
        · exact h0
        · exact h1
        · exact h2
      rcases hef with he | hf
      · exact ⟨0, h0, 2, h2, he⟩
      · exact ⟨1, h1, 2, h2, hf⟩
    · exact ⟨0, h0, 1, h1, hb⟩
  · by_cases h1 : (1 : Fin 3) ∈ I
    · exact ⟨1, h1, 0, h0, ha⟩
    · have h2 : (2 : Fin 3) ∈ I := by
        obtain ⟨i, hi⟩ := hIne
        fin_cases i
        · exact absurd hi h0
        · exact absurd hi h1
        · exact hi
      rcases hcd with hc | hd
      · exact ⟨2, h2, 0, h0, hc⟩
      · exact ⟨2, h2, 1, h1, hd⟩

private theorem reflection_range_fin_three {r₁ r₂ t : U ≃ₗ[ZMod p] U} {u : Fin 3 → U}
    {φ : Fin 3 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hr₁ : r₁ = Module.reflection (hφ 0)) (hr₂ : r₂ = Module.reflection (hφ 1))
    (ht : t = Module.reflection (hφ 2)) :
    Set.range (fun i : Fin 3 => Module.reflection (hφ i)) = {r₁, r₂, t} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (reflection_congr.trans hr₁.symm)
    · exact Or.inr (Or.inl (reflection_congr.trans hr₂.symm))
    · exact Or.inr (Or.inr (reflection_congr.trans ht.symm))
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, reflection_congr.trans hr₁.symm⟩
    · exact ⟨1, reflection_congr.trans hr₂.symm⟩
    · exact ⟨2, reflection_congr.trans ht.symm⟩

private theorem cartan_det_three {u : Fin 3 → U} {φ : Fin 3 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2) (hab : φ 0 (u 1) * φ 1 (u 0) = 4) :
    2 * (Matrix.of fun i j => φ i (u j)).det =
      -((φ 0 (u 1) * φ 2 (u 0) - 2 * φ 2 (u 1)) *
        (φ 1 (u 0) * φ 0 (u 2) - 2 * φ 1 (u 2))) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [hφ 0, hφ 1, hφ 2]
  exact cartan_det_identity (φ 0 (u 1)) (φ 1 (u 0)) (φ 0 (u 2)) (φ 1 (u 2))
    (φ 2 (u 0)) (φ 2 (u 1)) hab

private theorem splitSupport_three_of_cartan [Module.Finite (ZMod p) U]
    {r₁ r₂ t : U ≃ₗ[ZMod p] U} {u₁ u₂ u₃ : U} {φ₁ φ₂ φ₃ : Module.Dual (ZMod p) U}
    (hφ₁ : φ₁ u₁ = 2) (hφ₂ : φ₂ u₂ = 2) (hφ₃ : φ₃ u₃ = 2)
    (hr₁ : r₁ = Module.reflection hφ₁) (hr₂ : r₂ = Module.reflection hφ₂)
    (ht : t = Module.reflection hφ₃)
    (ha : φ₁ u₂ ≠ 0) (hb : φ₂ u₁ ≠ 0)
    (hcd : φ₁ u₃ ≠ 0 ∨ φ₂ u₃ ≠ 0) (hef : φ₃ u₁ ≠ 0 ∨ φ₃ u₂ ≠ 0)
    (hab : φ₁ u₂ * φ₂ u₁ = 4)
    (hae : φ₁ u₂ * φ₃ u₁ - 2 * φ₃ u₂ ≠ 0)
    (hbc : φ₂ u₁ * φ₁ u₃ - 2 * φ₂ u₃ ≠ 0) :
    SplitSupport (Subgroup.closure ({r₁, r₂, t} : Set (U ≃ₗ[ZMod p] U))) 3 := by
  let u : Fin 3 → U := ![u₁, u₂, u₃]
  let φ : Fin 3 → Module.Dual (ZMod p) U := ![φ₁, φ₂, φ₃]
  have hφ : ∀ i, φ i (u i) = 2 := by
    intro i; fin_cases i <;> simp [u, φ, hφ₁, hφ₂, hφ₃]
  have hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0 := by
    intro hzero
    have h : 2 * (Matrix.of fun i j => φ i (u j)).det = 0 := by rw [hzero, mul_zero]
    rw [cartan_det_three hφ hab] at h
    have hne : (φ 0 (u 1) * φ 2 (u 0) - 2 * φ 2 (u 1)) *
        (φ 1 (u 0) * φ 0 (u 2) - 2 * φ 1 (u 2)) ≠ 0 := mul_ne_zero hae hbc
    exact (neg_ne_zero.mpr hne) h
  have hss := splitSupport_of_det_ne_zero hφ hdet (connected_fin_three ha hb hcd hef)
  have hr₁' : r₁ = Module.reflection (hφ 0) := hr₁.trans reflection_congr.symm
  have hr₂' : r₂ = Module.reflection (hφ 1) := hr₂.trans reflection_congr.symm
  have ht' : t = Module.reflection (hφ 2) := ht.trans reflection_congr.symm
  rw [reflection_range_fin_three hφ hr₁' hr₂' ht'] at hss
  exact hss

private theorem reflGen_closure_of_forall_isRefl {S : Set (U ≃ₗ[ZMod p] U)}
    (hS : ∀ g ∈ S, IsRefl p g) : ReflGen p (Subgroup.closure S) := by
  rw [ReflGen]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g hg
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hg, hS g hg⟩
  · rw [Subgroup.closure_le]
    rintro t ht
    exact ht.1

private def cartanW0 (φ₁ : Module.Dual (ZMod p) U) (u₁ : U) (u₂ : U) : U :=
  φ₁ u₂ • u₁ - (2 : ZMod p) • u₂

private def cartanPsi (φ₁ : Module.Dual (ZMod p) U) (u₁ : U)
    (φ₂ : Module.Dual (ZMod p) U) : Module.Dual (ZMod p) U where
  toFun v := (φ₂ u₁) * (φ₁ v) - 2 * (φ₂ v)
  map_add' v w := by
    simp only [map_add]
    rw [mul_add, mul_add]
    abel
  map_smul' c v := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    ring

private theorem cartan_w0_ne_zero {u₁ u₂ : U} {φ₁ : Module.Dual (ZMod p) U}
    (h2ne : (2 : ZMod p) ≠ 0) (hindep : u₂ ∉ Submodule.span (ZMod p) ({u₁} : Set U)) :
    cartanW0 φ₁ u₁ u₂ ≠ 0 := by
  intro h
  rw [cartanW0] at h
  have h2 : (2 : ZMod p) • u₂ = (φ₁ u₂) • u₁ := (sub_eq_zero.mp h).symm
  have hu₂span : u₂ ∈ Submodule.span (ZMod p) ({u₁} : Set U) := by
    rw [Submodule.mem_span_singleton]
    refine ⟨(2 : ZMod p)⁻¹ * (φ₁ u₂), ?_⟩
    calc ((2 : ZMod p)⁻¹ * (φ₁ u₂)) • u₁ = (2 : ZMod p)⁻¹ • ((φ₁ u₂) • u₁) := by
          rw [smul_smul]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • u₂) := by rw [← h2]
      _ = u₂ := inv_smul_smul₀ h2ne u₂
  exact hindep hu₂span

private theorem cartan_W_ne_bot {u₁ u₂ : U} {φ₁ : Module.Dual (ZMod p) U}
    (hw0 : cartanW0 φ₁ u₁ u₂ ≠ 0) :
    Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} ≠ ⊥ := by
  intro hbot
  have hmem : cartanW0 φ₁ u₁ u₂ ∈ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} :=
    Submodule.subset_span (Set.mem_singleton _)
  rw [hbot] at hmem
  exact hw0 (by simpa using hmem)

private theorem cartan_W_ne_top {u₁ u₂ : U} {φ₁ : Module.Dual (ZMod p) U}
    (hu₁0 : u₁ ≠ 0) (hindep : u₂ ∉ Submodule.span (ZMod p) ({u₁} : Set U)) :
    Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} ≠ ⊤ := by
  intro htop
  have h1 : u₁ ∈ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} := by
    rw [htop]; exact Submodule.mem_top
  have h2 : u₂ ∈ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} := by
    rw [htop]; exact Submodule.mem_top
  rw [Submodule.mem_span_singleton] at h1 h2
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hu₁0 hc.symm
  have hw0' : cartanW0 φ₁ u₁ u₂ = c⁻¹ • u₁ := by
    conv_rhs => rw [← hc]
    rw [inv_smul_smul₀ hc0]
  have : u₂ = (d * c⁻¹) • u₁ := by rw [← hd, hw0', smul_smul]
  exact hindep (Submodule.mem_span_singleton.mpr ⟨d * c⁻¹, this.symm⟩)

private theorem cartan_V0_ne_bot {u₁ u₂ : U} {φ₁ φ₂ : Module.Dual (ZMod p) U}
    (hφ₂ : φ₂ u₂ = 2) (hu₂0 : u₂ ≠ 0) (hab : φ₁ u₂ * φ₂ u₁ = 4) :
    LinearMap.ker (cartanPsi φ₁ u₁ φ₂) ≠ ⊥ := by
  intro hbot
  have hu₂V : u₂ ∈ LinearMap.ker (cartanPsi φ₁ u₁ φ₂) := by
    rw [LinearMap.mem_ker]
    change (φ₂ u₁) * (φ₁ u₂) - 2 * (φ₂ u₂) = 0
    rw [hφ₂, mul_comm (φ₂ u₁) (φ₁ u₂), hab]
    norm_num
  rw [hbot] at hu₂V
  exact hu₂0 (by simpa using hu₂V)

private theorem cartan_V0_ne_top {u₁ u₂ : U} {φ₁ φ₂ : Module.Dual (ZMod p) U}
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hp : p ≠ 2) (hA : QTwoLin.TransvectionFree G)
    (hφ₁ : φ₁ u₁ = 2) (hφ₂ : φ₂ u₂ = 2)
    (hr₁' : Module.reflection hφ₁ ∈ G) (hr₂' : Module.reflection hφ₂ ∈ G)
    (hne' : Module.reflection hφ₁ ≠ Module.reflection hφ₂)
    (h2ne : (2 : ZMod p) ≠ 0) (hb : φ₂ u₁ ≠ 0) :
    LinearMap.ker (cartanPsi φ₁ u₁ φ₂) ≠ ⊤ := by
  intro htop
  have hzero : cartanPsi φ₁ u₁ φ₂ = 0 := by
    ext v
    have hv : v ∈ LinearMap.ker (cartanPsi φ₁ u₁ φ₂) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    simpa using hv
  have hphi : φ₂ = ((2 : ZMod p)⁻¹ * φ₂ u₁) • φ₁ := by
    ext v
    have hv := congrArg (fun g => g v) hzero
    change (φ₂ u₁) * (φ₁ v) - 2 * (φ₂ v) = 0 at hv
    have h2v : (2 : ZMod p) * φ₂ v = (φ₂ u₁) * φ₁ v := (sub_eq_zero.mp hv).symm
    calc φ₂ v = (2 : ZMod p)⁻¹ * (2 * φ₂ v) := by
          rw [← mul_assoc, inv_mul_cancel₀ h2ne, one_mul]
      _ = (2 : ZMod p)⁻¹ * ((φ₂ u₁) * φ₁ v) := by rw [h2v]
      _ = ((2 : ZMod p)⁻¹ * φ₂ u₁) * φ₁ v := by rw [mul_assoc]
  have hc0 : (2 : ZMod p)⁻¹ * φ₂ u₁ ≠ 0 := mul_ne_zero (inv_ne_zero h2ne) hb
  have hker : LinearMap.ker φ₂ = LinearMap.ker φ₁ := by
    rw [hphi]
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero]
    exact ⟨fun h => h.resolve_left hc0, Or.inr⟩
  exact hne' (reflection_eq_of_ker_eq hp hA hφ₁ hφ₂ hr₁' hr₂' hker.symm)

private theorem cartan_hae {u₁ u₂ u₃ : U} {φ₁ φ₃ : Module.Dual (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} (hφ₃ : φ₃ u₃ = 2) (ht_eq : t = Module.reflection hφ₃)
    (htW : ∃ w ∈ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂},
      t w ∉ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂}) :
    φ₁ u₂ * φ₃ u₁ - 2 * φ₃ u₂ ≠ 0 := by
  intro hae0
  have hw0φ : φ₃ (cartanW0 φ₁ u₁ u₂) = φ₁ u₂ * φ₃ u₁ - 2 * φ₃ u₂ := by
    rw [cartanW0, map_sub, map_smul, map_smul]
    abel
  obtain ⟨w, hwW, htw⟩ := htW
  apply htw
  rw [Submodule.mem_span_singleton] at hwW
  obtain ⟨c, hc⟩ := hwW
  have hφw : φ₃ (cartanW0 φ₁ u₁ u₂) = 0 := by rw [hw0φ]; exact hae0
  have hfix : t (cartanW0 φ₁ u₁ u₂) = cartanW0 φ₁ u₁ u₂ := by
    rw [ht_eq, Module.reflection_apply, hφw, zero_smul, sub_zero]
  rw [← hc, map_smul, hfix]
  exact (Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂}).smul_mem c
    (Submodule.subset_span (Set.mem_singleton _))

private theorem cartan_hbc {u₁ u₃ : U} {φ₁ φ₂ φ₃ : Module.Dual (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} (hφ₃ : φ₃ u₃ = 2) (ht_eq : t = Module.reflection hφ₃)
    (htV : ∃ v ∈ LinearMap.ker (cartanPsi φ₁ u₁ φ₂),
      t v ∉ LinearMap.ker (cartanPsi φ₁ u₁ φ₂)) :
    φ₂ u₁ * φ₁ u₃ - 2 * φ₂ u₃ ≠ 0 := by
  intro hbc0
  have hu₃V : u₃ ∈ LinearMap.ker (cartanPsi φ₁ u₁ φ₂) := by
    rw [LinearMap.mem_ker]
    change (φ₂ u₁) * (φ₁ u₃) - 2 * (φ₂ u₃) = 0
    exact hbc0
  obtain ⟨v, hvV, htv⟩ := htV
  apply htv
  rw [ht_eq, Module.reflection_apply]
  exact (LinearMap.ker (cartanPsi φ₁ u₁ φ₂)).sub_mem hvV
    ((LinearMap.ker (cartanPsi φ₁ u₁ φ₂)).smul_mem _ hu₃V)

private theorem cartan_hcd {u₁ u₃ : U} {φ₁ φ₂ : Module.Dual (ZMod p) U}
    (hbc : φ₂ u₁ * φ₁ u₃ - 2 * φ₂ u₃ ≠ 0) : φ₁ u₃ ≠ 0 ∨ φ₂ u₃ ≠ 0 := by
  by_contra h
  push Not at h
  apply hbc
  rw [h.1, h.2]; simp

private theorem cartan_hef {u₁ u₂ u₃ : U} {φ₁ φ₃ : Module.Dual (ZMod p) U}
    {t : U ≃ₗ[ZMod p] U} (hφ₃ : φ₃ u₃ = 2) (ht_eq : t = Module.reflection hφ₃)
    (htW : ∃ w ∈ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂},
      t w ∉ Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂}) :
    φ₃ u₁ ≠ 0 ∨ φ₃ u₂ ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨w, hwW, htw⟩ := htW
  apply htw
  rw [Submodule.mem_span_singleton] at hwW
  obtain ⟨c, hc⟩ := hwW
  have hfix1 : t u₁ = u₁ := by
    rw [ht_eq, Module.reflection_apply, h.1, zero_smul, sub_zero]
  have hfix2 : t u₂ = u₂ := by
    rw [ht_eq, Module.reflection_apply, h.2, zero_smul, sub_zero]
  have hfixw : t (cartanW0 φ₁ u₁ u₂) = cartanW0 φ₁ u₁ u₂ := by
    rw [cartanW0, map_sub, map_smul, hfix1, map_smul, hfix2]
  rw [← hc, map_smul, hfixw]
  exact (Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂}).smul_mem c
    (Submodule.subset_span (Set.mem_singleton _))

private theorem cartan_three_assembly [Module.Finite (ZMod p) U] {r₁ r₂ t : U ≃ₗ[ZMod p] U}
    {u₁ u₂ u₃ : U} {φ₁ φ₂ φ₃ : Module.Dual (ZMod p) U}
    {G : Subgroup (U ≃ₗ[ZMod p] U)}
    (hφ₁ : φ₁ u₁ = 2) (hφ₂ : φ₂ u₂ = 2) (hφ₃ : φ₃ u₃ = 2)
    (h₁ : r₁ ∈ G) (h₂ : r₂ ∈ G) (hr₁ : IsRefl p r₁) (hr₂ : IsRefl p r₂)
    (hr₁eq : r₁ = Module.reflection hφ₁) (hr₂eq : r₂ = Module.reflection hφ₂)
    (htG : t ∈ G) (htRefl : IsRefl p t) (ht_eq : t = Module.reflection hφ₃)
    (ha : φ₁ u₂ ≠ 0) (hb : φ₂ u₁ ≠ 0) (hab : φ₁ u₂ * φ₂ u₁ = 4)
    (hcd : φ₁ u₃ ≠ 0 ∨ φ₂ u₃ ≠ 0) (hef : φ₃ u₁ ≠ 0 ∨ φ₃ u₂ ≠ 0)
    (hae : φ₁ u₂ * φ₃ u₁ - 2 * φ₃ u₂ ≠ 0) (hbc : φ₂ u₁ * φ₁ u₃ - 2 * φ₂ u₃ ≠ 0) :
    ∃ K : Subgroup (U ≃ₗ[ZMod p] U), r₁ ∈ K ∧ r₂ ∈ K ∧ K ≤ G ∧ ReflGen p K ∧
      SplitSupport K 3 := by
  refine ⟨Subgroup.closure ({r₁, r₂, t} : Set (U ≃ₗ[ZMod p] U)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr₁eq]; exact Subgroup.subset_closure (Or.inl rfl)
  · rw [hr₂eq]; exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  · exact (Subgroup.closure_le G).mpr (by
      rintro g (rfl | rfl | rfl)
      · exact h₁
      · exact h₂
      · exact htG)
  · exact reflGen_closure_of_forall_isRefl (by
      rintro g (rfl | rfl | rfl)
      · exact hr₁
      · exact hr₂
      · exact htRefl)
  · exact splitSupport_three_of_cartan hφ₁ hφ₂ hφ₃ hr₁eq hr₂eq ht_eq ha hb hcd hef
      hab hae hbc

private theorem exists_splitSupport_three_of_cartan_data (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G)
    {r₁ r₂ : U ≃ₗ[ZMod p] U} (h₁ : r₁ ∈ G) (h₂ : r₂ ∈ G)
    (hr₁ : IsRefl p r₁) (hr₂ : IsRefl p r₂)
    {u₁ u₂ : U} {φ₁ φ₂ : Module.Dual (ZMod p) U}
    (hφ₁ : φ₁ u₁ = 2) (hφ₂ : φ₂ u₂ = 2)
    (hr₁eq : r₁ = Module.reflection hφ₁) (hr₂eq : r₂ = Module.reflection hφ₂)
    (h2ne : (2 : ZMod p) ≠ 0) (hu₁0 : u₁ ≠ 0) (hu₂0 : u₂ ≠ 0)
    (hindep : u₂ ∉ Submodule.span (ZMod p) ({u₁} : Set U))
    (ha : φ₁ u₂ ≠ 0) (hb : φ₂ u₁ ≠ 0) (hab : φ₁ u₂ * φ₂ u₁ = 4) (hne : r₁ ≠ r₂) :
    ∃ K : Subgroup (U ≃ₗ[ZMod p] U), r₁ ∈ K ∧ r₂ ∈ K ∧ K ≤ G ∧ ReflGen p K ∧
      SplitSupport K 3 := by
  have hA : QTwoLin.TransvectionFree G := hG.2
  have hr₁' : Module.reflection hφ₁ ∈ G := by rw [← hr₁eq]; exact h₁
  have hr₂' : Module.reflection hφ₂ ∈ G := by rw [← hr₂eq]; exact h₂
  have hne' : Module.reflection hφ₁ ≠ Module.reflection hφ₂ := by
    rw [← hr₁eq, ← hr₂eq]; exact hne
  have hw0 : cartanW0 φ₁ u₁ u₂ ≠ 0 := cartan_w0_ne_zero h2ne hindep
  have hWne : Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} ≠ ⊥ := cartan_W_ne_bot hw0
  have hWtop : Submodule.span (ZMod p) {cartanW0 φ₁ u₁ u₂} ≠ ⊤ :=
    cartan_W_ne_top hu₁0 hindep
  have hV0ne : LinearMap.ker (cartanPsi φ₁ u₁ φ₂) ≠ ⊥ := cartan_V0_ne_bot hφ₂ hu₂0 hab
  have hV0top : LinearMap.ker (cartanPsi φ₁ u₁ φ₂) ≠ ⊤ :=
    cartan_V0_ne_top hp hA hφ₁ hφ₂ hr₁' hr₂' hne' h2ne hb
  obtain ⟨t, htG, htRefl, htW, htV⟩ :=
    exists_isRefl_moves_two hG.1 hirr hprim hWne hWtop hV0ne hV0top
  obtain ⟨u₃, φ₃, hφ₃, ht_eq⟩ := (isRefl_iff hp t).mp htRefl
  have hae : φ₁ u₂ * φ₃ u₁ - 2 * φ₃ u₂ ≠ 0 := cartan_hae hφ₃ ht_eq htW
  have hbc : φ₂ u₁ * φ₁ u₃ - 2 * φ₂ u₃ ≠ 0 := cartan_hbc hφ₃ ht_eq htV
  have hcd : φ₁ u₃ ≠ 0 ∨ φ₂ u₃ ≠ 0 := cartan_hcd hbc
  have hef : φ₃ u₁ ≠ 0 ∨ φ₃ u₂ ≠ 0 := cartan_hef hφ₃ ht_eq htW
  exact cartan_three_assembly hφ₁ hφ₂ hφ₃ h₁ h₂ hr₁ hr₂ hr₁eq hr₂eq htG htRefl ht_eq
    ha hb hab hcd hef hae hbc

private theorem cartan_pair_ha {r₁ r₂ : U ≃ₗ[ZMod p] U} {G : Subgroup (U ≃ₗ[ZMod p] U)}
    {φ₁ φ₂ : Module.Dual (ZMod p) U} {u₁ u₂ : U} (hp : p ≠ 2)
    (hA : QTwoLin.TransvectionFree G) (hφ₁ : φ₁ u₁ = 2) (hφ₂ : φ₂ u₂ = 2)
    (hr₁' : Module.reflection hφ₁ ∈ G) (hr₂' : Module.reflection hφ₂ ∈ G)
    (hne' : Module.reflection hφ₁ ≠ Module.reflection hφ₂)
    (hr₁eq : r₁ = Module.reflection hφ₁) (hr₂eq : r₂ = Module.reflection hφ₂)
    (hr₁sq : Module.reflection hφ₁ * Module.reflection hφ₁ = 1)
    (hr₂sq : Module.reflection hφ₂ * Module.reflection hφ₂ = 1)
    (hd : 3 < orderOf (r₁ * r₂)) :
    φ₁ u₂ ≠ 0 := by
  intro ha0
  have hcomm : Commute (Module.reflection hφ₁) (Module.reflection hφ₂) :=
    (commute_reflection_iff hp hA hφ₁ hφ₂ hr₁' hr₂' hne').mpr ha0
  have hsq : (r₁ * r₂) ^ 2 = 1 := by
    rw [hr₁eq, hr₂eq, hcomm.mul_pow 2, pow_two, pow_two, hr₁sq, hr₂sq, mul_one]
  have hdvd : orderOf (r₁ * r₂) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
  have hle : orderOf (r₁ * r₂) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem cartan_pair_setup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    {r₁ r₂ : U ≃ₗ[ZMod p] U} (h₁ : r₁ ∈ G) (h₂ : r₂ ∈ G)
    (hr₁ : IsRefl p r₁) (hr₂ : IsRefl p r₂) (hd : 3 < orderOf (r₁ * r₂)) :
    ∃ (u₁ : U) (φ₁ : Module.Dual (ZMod p) U) (hφ₁ : φ₁ u₁ = 2), r₁ = Module.reflection hφ₁ ∧
      ∃ (u₂ : U) (φ₂ : Module.Dual (ZMod p) U) (hφ₂ : φ₂ u₂ = 2),
      r₂ = Module.reflection hφ₂ ∧ r₁ ≠ r₂ ∧ (2 : ZMod p) ≠ 0 ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧
      u₂ ∉ Submodule.span (ZMod p) ({u₁} : Set U) ∧ φ₁ u₂ ≠ 0 ∧ φ₂ u₁ ≠ 0 := by
  obtain ⟨u₁, φ₁, hφ₁, hr₁eq⟩ := (isRefl_iff hp r₁).mp hr₁
  obtain ⟨u₂, φ₂, hφ₂, hr₂eq⟩ := (isRefl_iff hp r₂).mp hr₂
  have hA : QTwoLin.TransvectionFree G := hG.2
  have hr₁' : Module.reflection hφ₁ ∈ G := by rw [← hr₁eq]; exact h₁
  have hr₂' : Module.reflection hφ₂ ∈ G := by rw [← hr₂eq]; exact h₂
  have hne : r₁ ≠ r₂ := by
    intro h
    have h1 : orderOf (r₁ * r₂) = 1 := by rw [h, hr₂.1]; exact orderOf_one
    omega
  have hne' : Module.reflection hφ₁ ≠ Module.reflection hφ₂ := by
    rw [← hr₁eq, ← hr₂eq]; exact hne
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hu₁0 : u₁ ≠ 0 := by
    intro h0
    exact h2ne (by rw [h0, map_zero] at hφ₁; exact hφ₁.symm)
  have hu₂0 : u₂ ≠ 0 := by
    intro h0
    exact h2ne (by rw [h0, map_zero] at hφ₂; exact hφ₂.symm)
  have hindep : u₂ ∉ Submodule.span (ZMod p) ({u₁} : Set U) := by
    intro h
    exact hne' (reflection_eq_of_mem_span hp hA hφ₁ hφ₂ hr₁' hr₂' h)
  have hr₁sq : Module.reflection hφ₁ * Module.reflection hφ₁ = 1 := by
    rw [← hr₁eq]; exact hr₁.1
  have hr₂sq : Module.reflection hφ₂ * Module.reflection hφ₂ = 1 := by
    rw [← hr₂eq]; exact hr₂.1
  have ha : φ₁ u₂ ≠ 0 :=
    cartan_pair_ha hp hA hφ₁ hφ₂ hr₁' hr₂' hne' hr₁eq hr₂eq hr₁sq hr₂sq hd
  have hb : φ₂ u₁ ≠ 0 := by
    intro hb0
    exact ha ((apply_eq_zero_comm hp hA hφ₁ hφ₂ hr₁' hr₂').mpr hb0)
  exact ⟨u₁, φ₁, hφ₁, hr₁eq, u₂, φ₂, hφ₂, hr₂eq, hne, h2ne, hu₁0, hu₂0, hindep, ha, hb⟩

theorem exists_splitSupport_two_or_three (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {r₁ r₂ : U ≃ₗ[ZMod p] U} (h₁ : r₁ ∈ G)
    (h₂ : r₂ ∈ G) (hr₁ : IsRefl p r₁) (hr₂ : IsRefl p r₂) (hd : 3 < orderOf (r₁ * r₂)) :
    ∃ K : Subgroup (U ≃ₗ[ZMod p] U), r₁ ∈ K ∧ r₂ ∈ K ∧ K ≤ G ∧ ReflGen p K ∧
      (SplitSupport K 2 ∨ SplitSupport K 3) := by
  obtain ⟨u₁, φ₁, hφ₁, hr₁eq, u₂, φ₂, hφ₂, hr₂eq, hne, h2ne, hu₁0, hu₂0, hindep,
    ha, hb⟩ := cartan_pair_setup hp hG h₁ h₂ hr₁ hr₂ hd
  by_cases hab : φ₁ u₂ * φ₂ u₁ = 4
  · obtain ⟨K, hK₁, hK₂, hKG, hKr, hKs⟩ :=
      exists_splitSupport_three_of_cartan_data hp hG hirr hprim h₁ h₂ hr₁ hr₂ hφ₁ hφ₂ hr₁eq
        hr₂eq h2ne hu₁0 hu₂0 hindep ha hb hab hne
    exact ⟨K, hK₁, hK₂, hKG, hKr, Or.inr hKs⟩
  · have hdet2 : (4 : ZMod p) - φ₁ u₂ * φ₂ u₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    refine ⟨Subgroup.closure ({r₁, r₂} : Set (U ≃ₗ[ZMod p] U)), ?_, ?_, ?_, ?_, Or.inl ?_⟩
    · rw [hr₁eq]; exact Subgroup.subset_closure (Or.inl rfl)
    · rw [hr₂eq]; exact Subgroup.subset_closure (Or.inr rfl)
    · exact (Subgroup.closure_le G).mpr (by
        rintro g (rfl | rfl)
        · exact h₁
        · exact h₂)
    · exact reflGen_closure_of_forall_isRefl (by
        rintro g (rfl | rfl)
        · exact hr₁
        · exact hr₂)
    · exact splitSupport_two_of_cartan hφ₁ hφ₂ hr₁eq hr₂eq ha hb hdet2

end CFSG.StandardType.ZS
