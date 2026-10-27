module

public import CFSG.Monster.B.TwoA.Base.GeomLin
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagExtension
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData

public noncomputable section

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem isTotallyIsotropic_span {B : BilinForm K V} {S : Set V}
    (h : ∀ s ∈ S, ∀ t ∈ S, B s t = 0) : IsTotallyIsotropic B (span K S) := by
  have h1 : ∀ s ∈ S, ∀ y ∈ span K S, B s y = 0 := fun s hs y hy => by
    have : span K S ≤ LinearMap.ker (B s) :=
      span_le.2 fun t ht => LinearMap.mem_ker.2 (h s hs t ht)
    exact LinearMap.mem_ker.1 (this hy)
  intro x hx y hy
  have : span K S ≤ LinearMap.ker (B.flip y) :=
    span_le.2 fun s hs => LinearMap.mem_ker.2 (h1 s hs y hy)
  exact LinearMap.mem_ker.1 (this hx)

theorem isTotallyIsotropic_map_isometry {B : BilinForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup B) {W : Submodule K V}
    (hW : IsTotallyIsotropic B W) : IsTotallyIsotropic B (W.map (g : V →ₗ[K] V)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y).trans (hW x hx y hy)

theorem exists_symplecticBasis_of_chain [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) (T : Finset ℕ)
    (F : ℕ → Submodule K V) (hF : ∀ s ∈ T, ∀ t ∈ T, s ≤ t → F s ≤ F t)
    (hd : ∀ t ∈ T, finrank K (F t) = t) (hi : ∀ t ∈ T, IsTotallyIsotropic B (F t)) :
    ∃ b : Basis (Fin r ⊕ Fin r) K V, IsSymplecticBasis B b ∧
      ∀ t ∈ T, F t = span K (b '' (Sum.inl '' {j : Fin r | (j : ℕ) < t})) := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · obtain ⟨b, hb, -⟩ := exists_symplecticBasis_of_flag hB hnd hV (k := 0) (Nat.zero_le r)
      (fun _ => ⊥) (fun i hi => by rw [Nat.le_zero.1 hi, finrank_bot])
      (fun i hi => absurd hi (Nat.not_lt_zero _))
      (fun x hx y hy => by rw [(mem_bot K).1 hx, map_zero, LinearMap.zero_apply])
    exact ⟨b, hb, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  set m := T.max' hT
  have hm : m ∈ T := T.max'_mem hT
  have hmr : m ≤ r := by
    have := finrank_le_of_isTotallyIsotropic hB hnd hV (hi m hm)
    rwa [hd m hm] at this
  set n := finrank K V
  set bV := Module.finBasis K V
  set U : ℕ → Submodule K V := fun i => span K (bV '' {j : Fin n | (j : ℕ) < i}) with hU
  have hUd : ∀ i ≤ n, finrank K (U i) = i := fun i hi =>
    finrank_span_image_lt bV.linearIndependent hi
  have hUm : ∀ i j, i ≤ j → U i ≤ U j := fun i j hij =>
    span_mono (Set.image_mono fun k (hk : (k : ℕ) < i) => lt_of_lt_of_le hk hij)
  obtain ⟨e, he⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_flag T U F
    (fun i _ j _ hij => hUm i j hij) hF (fun i hi => by
      rw [hUd i (by have := T.le_max' i hi; omega), hd i hi])
  set W : ℕ → Submodule K V := fun i => (U i).map (e : V →ₗ[K] V) with hW
  have hWd : ∀ i ≤ m, finrank K (W i) = i := fun i hi => by
    rw [hW, LinearEquiv.finrank_map_eq, hUd i (by omega)]
  have hWm : ∀ i < m, W i ≤ W (i + 1) := fun i _ => map_mono (hUm i (i + 1) (Nat.le_succ i))
  have hWi : IsTotallyIsotropic B (W m) := by
    rw [hW]
    simp only
    rw [he m hm]
    exact hi m hm
  obtain ⟨b, hb, hbW⟩ := exists_symplecticBasis_of_flag hB hnd hV hmr W hWd hWm hWi
  refine ⟨b, hb, fun t ht => ?_⟩
  rw [← hbW t (T.le_max' t ht), hW]
  exact (he t ht).symm

theorem exists_isometry_map_span {ι : Type*} [Fintype ι] [DecidableEq ι] {B : BilinForm K V}
    {b b' : Basis ι K V} (h : BilinForm.toMatrix b B = BilinForm.toMatrix b' B) :
    ∃ g ∈ TauCeti.BilinForm.isometryGroup B, ∀ s : Set ι,
      (span K (b '' s)).map (g : V →ₗ[K] V) = span K (b' '' s) := by
  set φ := b.isometryEquivOfToMatrixEq b' h
  refine ⟨φ.toLinearEquiv, TauCeti.BilinForm.mem_isometryGroup_iff.mpr fun x y => φ.map_app y x,
    fun s => ?_⟩
  rw [map_span, ← Set.image_comp]
  congr 1
  exact Set.image_congr fun x _ => b.isometryEquivOfToMatrixEq_apply_basis b' h x

theorem exists_isometry_map_chain [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) (T : Finset ℕ)
    {F F' : ℕ → Submodule K V}
    (hF : ∀ s ∈ T, ∀ t ∈ T, s ≤ t → F s ≤ F t) (hF' : ∀ s ∈ T, ∀ t ∈ T, s ≤ t → F' s ≤ F' t)
    (hd : ∀ t ∈ T, finrank K (F t) = t) (hd' : ∀ t ∈ T, finrank K (F' t) = t)
    (hi : ∀ t ∈ T, IsTotallyIsotropic B (F t)) (hi' : ∀ t ∈ T, IsTotallyIsotropic B (F' t)) :
    ∃ g ∈ TauCeti.BilinForm.isometryGroup B, ∀ t ∈ T, (F t).map (g : V →ₗ[K] V) = F' t := by
  obtain ⟨b, hb, hbF⟩ := exists_symplecticBasis_of_chain hB hnd hV T F hF hd hi
  obtain ⟨b', hb', hbF'⟩ := exists_symplecticBasis_of_chain hB hnd hV T F' hF' hd' hi'
  obtain ⟨g, hg, hgs⟩ := exists_isometry_map_span (hb.trans hb'.symm)
  refine ⟨g, hg, fun t ht => ?_⟩
  rw [hbF t ht, hbF' t ht, ← Set.image_comp, ← Set.image_comp, Set.image_comp, Set.image_comp b']
  exact hgs _

theorem exists_isometry_map_eq [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (hV : finrank K V = 2 * r) {W W' : Submodule K V}
    (hW : IsTotallyIsotropic B W) (hW' : IsTotallyIsotropic B W')
    (h : finrank K W = finrank K W') :
    ∃ g ∈ TauCeti.BilinForm.isometryGroup B, W.map (g : V →ₗ[K] V) = W' := by
  obtain ⟨g, hg, hgW⟩ := exists_isometry_map_chain hB hnd hV {finrank K W} (F := fun _ => W)
    (F' := fun _ => W') (fun _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl)
    (fun t ht => (Finset.mem_singleton.1 ht).symm)
    (fun t ht => by rw [Finset.mem_singleton.1 ht]; exact h.symm) (fun _ _ => hW) (fun _ _ => hW')
  exact ⟨g, hg, hgW _ (Finset.mem_singleton_self _)⟩

end CFSG.Monster.B.TwoA.Sp8
