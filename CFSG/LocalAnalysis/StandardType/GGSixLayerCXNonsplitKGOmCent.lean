module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix

public section

namespace CFSG.StandardType

namespace OmNonsplit

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal
  LayerCores LayerCores.OrthSplit LayerFacts
open scoped MatrixGroups

@[expose] def OmModel (K : Type) [Field K] {G : Type} [Group G] (L : Subgroup G) : Prop :=
  (∃ (W : Type) (_ : AddCommGroup W) (_ : Module K W) (_ : FiniteDimensional K W)
    (R : QuadraticForm K W), (polarBilin R).Nondegenerate ∧ 4 ≤ finrank K W ∧ ¬ SplitFour R ∧
      Nonempty (↥L ≃* ↥⁅TauCeti.QuadraticMap.orthogonalGroup R,
        TauCeti.QuadraticMap.orthogonalGroup R⁆)) ∨
    (4 ≤ Nat.card K ∧ Nonempty (↥L ≃* SL(2, K)))

theorem OmModel.of_mulEquiv {K : Type} [Field K] {G G' : Type} [Group G] [Group G']
    {L : Subgroup G} {L' : Subgroup G'} (e : ↥L' ≃* ↥L) (h : OmModel K L) : OmModel K L' := by
  rcases h with ⟨W, _, _, _, R, hR, h4, hns, ⟨e'⟩⟩ | ⟨h4, ⟨e'⟩⟩
  · exact Or.inl ⟨W, inferInstance, inferInstance, inferInstance, R, hR, h4, hns, ⟨e.trans e'⟩⟩
  · exact Or.inr ⟨h4, ⟨e.trans e'⟩⟩

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

section Ext

variable {A : Subgroup (V ≃ₗ[K] V)} [Fintype A] (hA : (Fintype.card A : K) ≠ 0)

@[expose] noncomputable def extFix : (fixSp A ≃ₗ[K] fixSp A) →* (V ≃ₗ[K] V) :=
  (split hA).comp (MonoidHom.inl _ _)

theorem extFix_injective : Function.Injective (extFix hA) :=
  (split_injective hA).comp fun _ _ h => congrArg Prod.fst h

theorem extFix_apply_free (g : fixSp A ≃ₗ[K] fixSp A) (y : freeSp A) : extFix hA g y = y := by
  show split hA (g, 1) y = y
  rw [split_apply_free]
  rfl

variable (Q : QuadraticForm K V) in
@[expose] noncomputable def fixPart : Subgroup (V ≃ₗ[K] V) :=
  (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp A))).map (extFix hA)

variable {Q : QuadraticForm K V}

theorem fixPart_le (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) :
    fixPart hA Q ≤
      Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [centralizer_eq_map_split hA hAO]
  rintro _ ⟨g₀, hg₀, rfl⟩
  exact ⟨(g₀, 1), Subgroup.mem_prod.mpr ⟨hg₀, one_mem _⟩, rfl⟩

theorem conj_mem_map_extFix (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    {N : Subgroup (fixSp A ≃ₗ[K] fixSp A)}
    (hN : ∀ u ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (fixSp A)), ∀ s ∈ N,
      u * s * u⁻¹ ∈ N) {c : V ≃ₗ[K] V}
    (hc : c ∈ Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓
      TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[K] V} (hg : g ∈ N.map (extFix hA)) :
    c * g * c⁻¹ ∈ N.map (extFix hA) := by
  rw [centralizer_eq_map_split hA hAO] at hc
  obtain ⟨⟨c₀, c₁⟩, hc01, rfl⟩ := hc
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  obtain ⟨hc₀, -⟩ := Subgroup.mem_prod.mp hc01
  refine ⟨c₀ * g₀ * c₀⁻¹, hN c₀ hc₀ g₀ hg₀, ?_⟩
  show split hA (c₀ * g₀ * c₀⁻¹, 1) = split hA (c₀, c₁) * split hA (g₀, 1) * (split hA (c₀, c₁))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Prod.ext rfl (by simp)

theorem conj_mem_fixPart (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {c : V ≃ₗ[K] V}
    (hc : c ∈ Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓
      TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[K] V} (hg : g ∈ fixPart hA Q) :
    c * g * c⁻¹ ∈ fixPart hA Q :=
  conj_mem_map_extFix hA hAO (fun _ hu _ hs => mul_mem (mul_mem hu hs) (inv_mem hu)) hc hg

theorem mem_fixPart_of_fixes [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ y ∈ freeSp A, g y = y) :
    g ∈ fixPart hA Q := by
  have hpres : ∀ v ∈ fixSp A, g v ∈ fixSp A := by
    intro v hv
    have hu : ∀ y ∈ freeSp A, polar Q (g v) y = 0 := by
      intro y hy
      calc polar Q (g v) y = polar Q (g v) (g y) := by rw [hfix y hy]
        _ = polar Q v y := polar_map_of_mem hg v y
        _ = 0 := polar_fixSp_freeSp hAO hv hy
    have h2 : g v - avg A (g v) = 0 :=
      polarNondegOn_freeSp hQ hA hAO _ (sub_avg_mem_freeSp hA (g v)) fun y hy => by
        rw [polar_sub_left, hu y hy, polar_fixSp_freeSp hAO (avg_mem_fixSp (g v)) hy, sub_zero]
    rw [sub_eq_zero] at h2
    rw [h2]
    exact avg_mem_fixSp (g v)
  have hgs : g ∈ stab A := by
    intro v
    have e1 : g v = g (avg A v) + (v - avg A v) := by
      rw [← hfix _ (sub_avg_mem_freeSp hA v), ← map_add, add_sub_cancel]
    rw [e1, map_add, LinearMap.mem_ker.mp (sub_avg_mem_freeSp hA v), add_zero]
    obtain ⟨w, hw⟩ := hpres _ (avg_mem_fixSp v)
    rw [← hw, avg_avg hA]
  refine ⟨restrFix A ⟨g, hgs⟩,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => map_of_mem hg (x : V), ?_⟩
  refine LinearEquiv.ext fun v => ?_
  show split hA (restrFix A ⟨g, hgs⟩, 1) v = g v
  rw [split_apply]
  show g (avg A v) + (v - avg A v) = g v
  rw [← hfix _ (sub_avg_mem_freeSp hA v), ← map_add, add_sub_cancel]

theorem fixPart_le_fixPart [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q) {B : Subgroup (V ≃ₗ[K] V)} [Fintype B]
    (hB : (Fintype.card B : K) ≠ 0) (hBO : B ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hle : freeSp B ≤ freeSp A) : fixPart hA Q ≤ fixPart hB Q := by
  rintro _ ⟨g₀, hg₀, rfl⟩
  refine mem_fixPart_of_fixes hB hQ hBO (fixPart_le hA hAO ⟨g₀, hg₀, rfl⟩).2 fun y hy => ?_
  exact extFix_apply_free hA g₀ ⟨y, hle hy⟩

end Ext

end OmNonsplit

end CFSG.StandardType
