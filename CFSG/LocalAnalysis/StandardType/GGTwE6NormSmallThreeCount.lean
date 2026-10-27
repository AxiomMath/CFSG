module

public import CFSG.LocalAnalysis.StandardType.GGTwE6NormSmallThreeStarSound
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex

public section

namespace CFSG.StandardType.TwE6NormThree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem smul_eq_sum_single (w : WeylGroup TwistTag.E6.tag) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    w • v = ∑ k, v k • (w • (Pi.single k 1 : Fin TwistTag.E6.tag.rank → ℤ)) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : (fun j => if k = j then (1 : ℤ) else 0) = Pi.single k 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm]

@[expose] noncomputable def weylDual (w : WeylGroup TwistTag.E6.tag)
    (y : Fin TwistTag.E6.tag.rank → ZMod 3) : Fin TwistTag.E6.tag.rank → ZMod 3 :=
  fun j => dot3 (w • (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ)) y

theorem dot3_smul (w : WeylGroup TwistTag.E6.tag) (γ : Fin TwistTag.E6.tag.rank → ℤ)
    (y : Fin TwistTag.E6.tag.rank → ZMod 3) : dot3 (w • γ) y = dot3 γ (weylDual w y) := by
  simp only [dot3, weylDual]
  rw [smul_eq_sum_single w γ]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

@[expose] noncomputable def weylMod3 (w : WeylGroup TwistTag.E6.tag) :
    (Fin TwistTag.E6.tag.rank → ZMod 3) →ₗ[ZMod 3] Fin TwistTag.E6.tag.rank → ZMod 3 :=
  Matrix.mulVecLin (Matrix.of fun k j =>
    (((w • Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) k : ℤ) : ZMod 3))

theorem mod3_smul (w : WeylGroup TwistTag.E6.tag) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    mod3 (w • γ) = weylMod3 w (mod3 γ) := by
  funext k
  simp only [mod3, weylMod3, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [smul_eq_sum_single w γ]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

@[expose] noncomputable def weylCart3 (w : WeylGroup TwistTag.E6.tag) :
    (Fin TwistTag.E6.tag.rank → ZMod 3) →ₗ[ZMod 3] Fin TwistTag.E6.tag.rank → ZMod 3 :=
  Matrix.mulVecLin (Matrix.of fun i a =>
    (((w⁻¹ • Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) a : ℤ) : ZMod 3))

theorem iform_eq_sum_cartan (u v : Fin TwistTag.E6.tag.rank → ℤ) :
    iform u v = ∑ a, u a * ∑ b, TwistTag.E6.tag.cartan a b * v b := by
  simp only [iform, Tag.symmetrizedCartan, show TwistTag.E6.tag.symmetrizer = 1 from rfl,
    Matrix.one_mul, Finset.mul_sum, mul_assoc]

theorem exists_smul_single_zero {g : Fin TwistTag.E6.tag.rank → ℤ}
    (hg : IsRoot TwistTag.E6.tag g) : ∃ w : WeylGroup TwistTag.E6.tag,
      w • (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) = g := by
  have step : ∀ {i k : Fin TwistTag.E6.tag.rank},
      reflect TwistTag.E6.tag i (reflect TwistTag.E6.tag k (Pi.single i 1)) = Pi.single k 1 →
      (∃ u : WeylGroup TwistTag.E6.tag,
        u • (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single i 1) →
      ∃ u : WeylGroup TwistTag.E6.tag,
        u • (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single k 1 :=
    fun {i k} hik ⟨u, hu⟩ => ⟨simple _ i * simple _ k * u, by
      rw [mul_smul, hu, mul_smul, simple_smul, simple_smul, hik]⟩
  have h0 : ∃ u : WeylGroup TwistTag.E6.tag,
      u • (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) = Pi.single (0 : Fin 6) 1 :=
    ⟨1, one_smul _ _⟩
  have h2 := step (i := (0 : Fin 6)) (k := (2 : Fin 6)) (by decide +kernel) h0
  have h3 := step (i := (2 : Fin 6)) (k := (3 : Fin 6)) (by decide +kernel) h2
  have h1 := step (i := (3 : Fin 6)) (k := (1 : Fin 6)) (by decide +kernel) h3
  have h4 := step (i := (3 : Fin 6)) (k := (4 : Fin 6)) (by decide +kernel) h3
  have h5 := step (i := (4 : Fin 6)) (k := (5 : Fin 6)) (by decide +kernel) h4
  have key : ∀ j : Fin 6, ∃ u : WeylGroup TwistTag.E6.tag,
      u • (Pi.single (0 : Fin 6) 1 : Fin TwistTag.E6.tag.rank → ℤ) =
        (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) := fun j => by
    fin_cases j
    exacts [h0, h1, h2, h3, h4, h5]
  obtain ⟨w, j, rfl⟩ := isRoot_iff_exists_smul_single.1 hg
  obtain ⟨u, hu⟩ := key j
  exact ⟨w * u, by rw [mul_smul, hu]⟩

theorem mem_dotOrth_mod3 {α : Fin TwistTag.E6.tag.rank → ℤ}
    {v : Fin TwistTag.E6.tag.rank → ZMod 3} :
    v ∈ LinearFlag.dotOrth (Submodule.span (ZMod 3) {mod3 α}) ↔ dot3 α v = 0 := by
  rw [LinearFlag.mem_dotOrth]
  refine ⟨fun h => h _ (Submodule.mem_span_singleton_self _), fun h w hw => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [dotProduct_smul, show v ⬝ᵥ mod3 α = dot3 α v from rfl, h, smul_zero]


theorem cartan3_smul (w : WeylGroup TwistTag.E6.tag) (γ : Fin TwistTag.E6.tag.rank → ℤ) :
    cartan3 (w • γ) = weylCart3 w (cartan3 γ) := by
  funext i
  have h := iform_smul w⁻¹ (Pi.single i 1) (w • γ)
  rw [inv_smul_smul, iform_eq_sum_cartan, iform_eq_sum_cartan] at h
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  simp only [cartan3, weylCart3, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.of_apply]
  rw [← h, Int.cast_sum]
  exact Finset.sum_congr rfl fun a _ => Int.cast_mul _ _

theorem smul_mem_starSet_iff (w : WeylGroup TwistTag.E6.tag)
    {y : Fin TwistTag.E6.tag.rank → ZMod 3} {g δ : Fin TwistTag.E6.tag.rank → ℤ} :
    w • δ ∈ starSet y (w • g) ↔ δ ∈ starSet (weylDual w y) g := by
  simp only [starSet, Set.mem_setOf_eq, isRoot_smul_iff, dot3_smul, iform_smul]

theorem starGood_smul (w : WeylGroup TwistTag.E6.tag) {y : Fin TwistTag.E6.tag.rank → ZMod 3}
    {g : Fin TwistTag.E6.tag.rank → ℤ} (h : StarGood (weylDual w y) g) : StarGood y (w • g) := by
  rcases h with ⟨s, hs, hli⟩ | ⟨hcl, d, hd, hsp⟩
  · refine Or.inl ⟨fun i => w • s i, fun i => (smul_mem_starSet_iff w).2 (hs i), ?_⟩
    refine LinearIndependent.of_comp (weylCart3 w⁻¹) ?_
    convert hli using 1
    funext i
    simp only [Function.comp_apply, ← cartan3_smul, inv_smul_smul]
  · refine Or.inr ⟨fun δ' hδ' ε' hε' hεy hδε => ?_, w • d, (smul_mem_starSet_iff w).2 hd,
      fun s' hs' => ?_⟩
    · rw [← smul_inv_smul w δ'] at hδ' hδε
      rw [← smul_inv_smul w ε'] at hε' hεy hδε ⊢
      rw [iform_smul] at hδε
      rw [isRoot_smul_iff] at hε'
      rw [dot3_smul] at hεy
      exact (smul_mem_starSet_iff w).2 (hcl _ ((smul_mem_starSet_iff w).1 hδ') _ hε' hεy hδε)
    · rw [← smul_inv_smul w s'] at hs' ⊢
      have hm := Submodule.mem_map_of_mem (f := weylMod3 w)
        (hsp _ ((smul_mem_starSet_iff w).1 hs'))
      rwa [Submodule.map_span, Set.image_pair, ← mod3_smul, ← mod3_smul, ← mod3_smul] at hm

theorem starGood_of_isRoot {y : Fin TwistTag.E6.tag.rank → ZMod 3}
    {g : Fin TwistTag.E6.tag.rank → ℤ} (hg : IsRoot TwistTag.E6.tag g) (hgy : dot3 g y = 0) :
    StarGood y g := by
  obtain ⟨w, rfl⟩ := exists_smul_single_zero hg
  exact starGood_smul w (starGood_single_zero hgy)

theorem three_le_finrank_cartan3_inf {α : Fin TwistTag.E6.tag.rank → ℤ}
    (_hα : IsRoot TwistTag.E6.tag α) {y : Fin TwistTag.E6.tag.rank → ZMod 3}
    {Ψ : Set (Fin TwistTag.E6.tag.rank → ℤ)} (hΨ : IsRootComponent Ψ)
    {γ₀ : Fin TwistTag.E6.tag.rank → ℤ} (hγ₀ : γ₀ ∈ Ψ) (hΨy : ∀ γ ∈ Ψ, dot3 γ y = 0)
    (hcl : ∀ γ ∈ Ψ, ∀ δ, IsRoot TwistTag.E6.tag δ → dot3 δ y = 0 → iform γ δ ≠ 0 → δ ∈ Ψ)
    {V : Submodule (ZMod 3) (Fin TwistTag.E6.tag.rank → ZMod 3)}
    (hV : 4 ≤ Module.finrank (ZMod 3) V) (hαV : ∀ v ∈ V, dot3 α v = 0)
    (hend : ∀ v ∈ V, (∀ γ ∈ Ψ, dot3 γ v = 0) → v ∈ Submodule.span (ZMod 3) {y}) :
    3 ≤ Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) (cartan3 '' Ψ) ⊓
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.dotOrth
        (Submodule.span (ZMod 3) {mod3 α})) := by
  have hrank : TwistTag.E6.tag.rank = 6 := rfl
  have hle : ∀ W : Submodule (ZMod 3) (Fin TwistTag.E6.tag.rank → ZMod 3), finrank (ZMod 3) W ≤ 6 :=
    fun W => (Submodule.finrank_le W).trans_eq (Module.finrank_fin_fun (R := ZMod 3))
  have hr : finrank (ZMod 3) (Submodule.span (ZMod 3) {mod3 α}) ≤ 1 :=
    (finrank_span_le_card (R := ZMod 3) ({mod3 α} : Set _)).trans (by simp)
  have hH := LinearFlag.finrank_dotOrth (Submodule.span (ZMod 3) {mod3 α})
  have hγ₀r := hΨ.isRoot γ₀ hγ₀
  rcases starGood_of_isRoot hγ₀r (hΨy γ₀ hγ₀) with ⟨s, hs, hli⟩ | ⟨hB, d, -, hsp⟩
  ·
    have hU : 4 ≤ finrank (ZMod 3) (Submodule.span (ZMod 3) (cartan3 '' Ψ)) := by
      rw [← Fintype.card_fin 4, ← finrank_span_eq_card hli]
      refine Submodule.finrank_mono (Submodule.span_mono ?_)
      rintro _ ⟨i, rfl⟩
      exact ⟨s i, hcl γ₀ hγ₀ (s i) (hs i).1 (hs i).2.1 (hs i).2.2, rfl⟩
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 3) (cartan3 '' Ψ))
      (LinearFlag.dotOrth (Submodule.span (ZMod 3) {mod3 α}))
    have := hle (Submodule.span (ZMod 3) (cartan3 '' Ψ) ⊔
      LinearFlag.dotOrth (Submodule.span (ZMod 3) {mod3 α}))
    omega
  ·
    exfalso
    have hγ₀S : γ₀ ∈ starSet y γ₀ := ⟨hγ₀r, hΨy γ₀ hγ₀, (iform_self_pos_of_isRoot hγ₀r).ne'⟩
    have horth : ∀ a ∈ {γ | γ ∈ Ψ ∧ γ ∈ starSet y γ₀}, ∀ b ∈ Ψ,
        b ∉ {γ | γ ∈ Ψ ∧ γ ∈ starSet y γ₀} → iform a b = 0 := fun a ha b hb hbS => by
      by_contra hab
      exact hbS ⟨hb, hB a ha.2 b (hΨ.isRoot b hb) (hΨy b hb) hab⟩
    have hΨS : Ψ ⊆ starSet y γ₀ := by
      rcases hΨ.irreducible {γ | γ ∈ Ψ ∧ γ ∈ starSet y γ₀} (fun _ h => h.1) horth with h | h
      · exact absurd (h ▸ ⟨hγ₀, hγ₀S⟩ : γ₀ ∈ (∅ : Set _)) (Set.notMem_empty γ₀)
      · exact fun γ hγ => (h.ge hγ).2
    set P := Submodule.span (ZMod 3) {mod3 γ₀, mod3 d} with hPdef
    set A := Submodule.span (ZMod 3) {mod3 α}
    have hP : finrank (ZMod 3) P ≤ 2 := by
      have h := finrank_span_finset_le_card (R := ZMod 3) ({mod3 γ₀, mod3 d} : Finset _)
      rw [Finset.coe_pair] at h
      rw [hPdef]
      exact h.trans Finset.card_le_two
    have hW := Submodule.finrank_add_le_finrank_add_finrank P A
    have hWo := LinearFlag.finrank_dotOrth (P ⊔ A)
    have hinf : V ⊓ LinearFlag.dotOrth (P ⊔ A) ≤ Submodule.span (ZMod 3) {y} := fun v hv => by
      obtain ⟨hvV, hvW⟩ := Submodule.mem_inf.1 hv
      exact hend v hvV fun γ hγ =>
        LinearFlag.mem_dotOrth.1 hvW (mod3 γ) (Submodule.mem_sup_left (hsp γ (hΨS hγ)))
    have hsup : V ⊔ LinearFlag.dotOrth (P ⊔ A) ≤ LinearFlag.dotOrth A := by
      refine sup_le (fun v hv => mem_dotOrth_mod3.2 (hαV v hv)) fun v hv => ?_
      exact LinearFlag.mem_dotOrth.2 fun x hx =>
        LinearFlag.mem_dotOrth.1 hv x (Submodule.mem_sup_right hx)
    have h1 : finrank (ZMod 3) ↥(V ⊓ LinearFlag.dotOrth (P ⊔ A)) ≤ 1 :=
      (Submodule.finrank_mono hinf).trans
        ((finrank_span_le_card (R := ZMod 3) ({y} : Set _)).trans (by simp))
    have h2 := Submodule.finrank_mono hsup
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq V (LinearFlag.dotOrth (P ⊔ A))
    omega

end CFSG.StandardType.TwE6NormThree

end
