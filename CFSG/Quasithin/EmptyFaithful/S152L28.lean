module

public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G]

theorem lambdaOf_mono {X Y : Subgroup G} (h : X ≤ Y) : lambdaOf X ≤ lambdaOf Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem conj_mem_lambdaOf {X : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (X : Set G))
    {y : G} (hy : y ∈ lambdaOf X) : g * y * g⁻¹ ∈ lambdaOf X := by
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hx.1, ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hx.2
  | one => simp
  | mul x y _ _ ihx ihy =>
    simpa [mul_assoc] using (lambdaOf X).mul_mem ihx ihy
  | inv x _ ih =>
    simpa [mul_assoc] using (lambdaOf X).inv_mem ih

theorem le_normalizer_lambdaOf {X H : Subgroup G} (hH : H ≤ Subgroup.normalizer (X : Set G)) :
    H ≤ Subgroup.normalizer (lambdaOf X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_lambdaOf (hH hg) hx, fun hx => ?_⟩
  have := conj_mem_lambdaOf (hH (Subgroup.inv_mem _ hg)) hx
  simpa [mul_assoc] using this

theorem commutator_conjClosure_le {V H Λ Z : Subgroup G} (hVH : V ≤ H)
    (hΛ : H ≤ Subgroup.normalizer (Λ : Set G)) (hZ : H ≤ Subgroup.normalizer (Z : Set G))
    (hVΛ : ⁅V, Λ⁆ ≤ Z) : ⁅conjClosure V H, Λ⁆ ≤ Z := by
  rw [Subgroup.commutator_le]
  intro u hu l hl
  have hP : ∀ u ∈ conjClosure V H, u ∈ H ∧ ∀ l ∈ Λ, ⁅u, l⁆ ∈ Z := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      refine ⟨H.mul_mem (H.mul_mem hh (hVH hz)) (H.inv_mem hh), fun l hl => ?_⟩
      have hl' : h⁻¹ * l * h ∈ Λ := by
        have := (Subgroup.mem_normalizer_iff.mp (hΛ (H.inv_mem hh)) l).mp hl
        simpa [mul_assoc] using this
      have hc : ⁅z, h⁻¹ * l * h⁆ ∈ Z := hVΛ (Subgroup.commutator_mem_commutator hz hl')
      have e : ⁅h * z * h⁻¹, l⁆ = h * ⁅z, h⁻¹ * l * h⁆ * h⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hZ hh) _).mp hc
    | one =>
      exact ⟨H.one_mem, fun l _ => by simp⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨H.mul_mem ihx.1 ihy.1, fun l hl => ?_⟩
      have e : ⁅x * y, l⁆ = x * ⁅y, l⁆ * x⁻¹ * ⁅x, l⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hZ ihx.1) _).mp (ihy.2 l hl)) (ihx.2 l hl)
    | inv x hx ih =>
      refine ⟨H.inv_mem ih.1, fun l hl => ?_⟩
      have e : ⁅x⁻¹, l⁆ = x⁻¹ * ⁅x, l⁆⁻¹ * x := by
        simp only [commutatorElement_def]; group
      rw [e]
      have h1 : ⁅x, l⁆⁻¹ ∈ Z := Z.inv_mem (ih.2 l hl)
      have := (Subgroup.mem_normalizer_iff.mp (hZ (H.inv_mem ih.1)) _).mp h1
      simpa [mul_assoc] using this
  exact (hP u hu).2 l hl

variable [Finite G]

theorem lemma_15_2_28 {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))}
    (h : quasithinQTFE14Cat G T Mc) (hH : IsHStar T M H) (hB₀ : IsB0 T Mc M B₀)
    (h25 : Lemma15225Concl T Mc M)
    (hV : V154 T Mc M ≤ pCoreOf 2 H)
    (hZS : H ≤ Subgroup.normalizer (zSOf T Mc M B₀ : Set G)) :
    ⁅conjClosure (V154 T Mc M) H, lambdaOf (pCoreOf 2 H)⁆ ≤ zSOf T Mc M B₀ := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hTH : T ≤ H := hH.1.1
  have hQT : pCoreOf 2 H ≤ T := by
    have := pCoreOf_two_le_sylow H S (hS ▸ hTH)
    rwa [hS] at this
  have hΛS : lambdaOf (pCoreOf 2 H) ≤ sOf152 T Mc M B₀ :=
    (lambdaOf_mono hQT).trans (h25.lambda_le B₀ hB₀)
  refine commutator_conjClosure_le ((hV.trans (pCoreOf_le 2 H))) (le_normalizer_lambdaOf
    (le_normalizer_pCoreOf 2 H)) hZS ?_
  exact (Subgroup.commutator_mono le_rfl hΛS).trans (h25.comm_le B₀ hB₀)

end CFSG.Quasithin
