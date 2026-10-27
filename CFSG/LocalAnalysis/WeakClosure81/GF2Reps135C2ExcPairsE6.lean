module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCoverE6
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEClasses
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.TypeBound
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open CFSG.SeitzReduction (innerRepsE6 oddDerivE6YFrame oddDerivE6ZFrame highRoot)
open CFSG.LieType.Steinberg.Adjoint (iform)

@[expose] def e6Weight : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
    ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]

@[expose] def e6InnerWords : Fin 6 → Fin 4 → List (Fin 6) :=
  ![![[], [0], [0, 2], [0, 2, 3]],
    ![[], [1], [1, 3], [1, 3, 2]],
    ![[], [2], [2, 0], [2, 3]],
    ![[], [3], [3, 1], [3, 2]],
    ![[], [4], [4, 3], [4, 5]],
    ![[], [5], [5, 4], [5, 4, 3]]]

@[expose] def e6OuterWords : Fin 6 → Fin 7 → List (Fin 6) :=
  ![![[], [0, 2, 3, 4], [0, 2, 3, 1, 4], [0, 2, 3, 1, 4, 3], [0, 2, 3, 1, 4, 3, 2],
      [0, 2, 3, 1, 4, 3, 2, 0], [0, 2, 3, 1, 4, 3, 2, 5, 4]],
    ![[1, 3, 2], [1, 3, 4], [1, 3, 2, 4], [1, 3, 2, 0, 4], [1, 3, 2, 4, 3], [1, 3, 2, 0, 4, 3],
      [1, 3, 2, 4, 3, 1]],
    ![[2], [2, 3], [2, 3, 1], [2, 3, 4], [2, 0, 3, 4], [2, 3, 1, 4], [2, 0, 3, 1, 4]],
    ![[3, 2], [3, 4], [3, 1, 2], [3, 1, 4], [3, 2, 4], [3, 1, 2, 3], [3, 1, 2, 4]],
    ![[4], [4, 3], [4, 3, 1], [4, 3, 2], [4, 3, 1, 2], [4, 3, 2, 0], [4, 3, 1, 2, 0]],
    ![[], [5, 4, 3, 2], [5, 4, 3, 1, 2], [5, 4, 3, 1, 2, 3], [5, 4, 3, 1, 2, 3, 4],
      [5, 4, 3, 1, 2, 0, 3, 4], [5, 4, 3, 1, 2, 0, 3, 2, 4]]]

@[expose] def e6InnerFrames : List (List (Fin Tag.E6.rank → ℤ)) :=
  [[highRoot .E6], oddDerivE6YFrame, oddDerivE6ZFrame]

theorem reflect_e6Weight {s j : Fin Tag.E6.rank} (h : j ≠ s) :
    reflect .E6 j (e6Weight s) = e6Weight s := by
  revert s j
  decide +kernel

theorem e6InnerFrames_isRoot
    {F : List (Fin Tag.E6.rank → ℤ)} (hF : F ∈ e6InnerFrames) :
    ∀ β ∈ F, IsRoot .E6 β := by
  simp only [e6InnerFrames, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  all_goals
    simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
    decide +kernel

theorem e6InnerFrames_orth
    {F : List (Fin Tag.E6.rank → ℤ)} (hF : F ∈ e6InnerFrames) :
    F.Pairwise fun β γ => iform β γ = 0 ∧ ¬ IsRoot .E6 (β + γ) ∧ ¬ IsRoot .E6 (β - γ) := by
  simp only [e6InnerFrames, List.mem_cons, List.not_mem_nil, or_false] at hF
  rcases hF with rfl | rfl | rfl
  all_goals
    simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
    decide +kernel

private theorem e6_pair_weights_distinct_inner (F : List (Fin Tag.E6.rank → ℤ))
    (hF : F ∈ e6InnerFrames) (s : Fin Tag.E6.rank) :
    Function.Injective (Sum.elim (fun i : Fin 4 =>
        (e6InnerWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s))
      (fun i => F.foldr (fun β u => u - corootPair β u • β)
        ((e6InnerWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s)))) := by
  revert F s
  decide +kernel

theorem e6_pairs_inner
    {F : List (Fin Tag.E6.rank → ℤ)} (hF : F ∈ e6InnerFrames)
    (s : Fin Tag.E6.rank) :
    ∃ w : Fin 4 → WeylGroup .E6, Function.Injective (Sum.elim (fun i => w i • e6Weight s)
      (fun i => (reflectionWordProd F * w i) • e6Weight s)) := by
  let w : Fin 4 → WeylGroup .E6 :=
    fun i => (coxeterSystem .E6).wordProd (e6InnerWords s i).reverse
  have hstep : ∀ i : Fin 4, w i • e6Weight s =
      (e6InnerWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s) :=
    fun i => wordProd_reverse_smul (τ := .E6) (e6InnerWords s i) (e6Weight s)
  have hσ : ∀ i : Fin 4, (reflectionWordProd F * w i) • e6Weight s =
      F.foldr (fun β u => u - corootPair β u • β)
        ((e6InnerWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s)) := by
    intro i
    rw [mul_smul, hstep i]
    exact CFSG.StandardType.TableBExcTwoFusion.list_map_rootReflection_prod_smul
      F (e6InnerFrames_isRoot hF) _
  refine ⟨w, ?_⟩
  have hfun : Sum.elim (fun i => w i • e6Weight s)
      (fun i => (reflectionWordProd F * w i) • e6Weight s) =
      Sum.elim (fun i : Fin 4 => (e6InnerWords s i).foldl
          (fun v j => reflect .E6 j v) (e6Weight s))
        (fun i => F.foldr (fun β u => u - corootPair β u • β)
          ((e6InnerWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s))) := by
    funext x
    rcases x with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr, hstep i, hσ i]
  rw [hfun]
  exact e6_pair_weights_distinct_inner F hF s

private theorem e6_pair_weights_distinct_outer (s : Fin Tag.E6.rank) :
    Function.Injective (Sum.elim (fun i : Fin 7 =>
        (e6OuterWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s))
      (fun i => ([Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] :
          List (Fin Tag.E6.rank → ℤ)).foldr (fun β u => u - corootPair β u • β)
        ((e6OuterWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s)))) := by
  revert s
  decide +kernel

private theorem e6_pairwise_pair {a b : Fin Tag.E6.rank → ℤ}
    (h0 : iform a b = 0) (h1 : ¬ IsRoot .E6 (a + b)) (h2 : ¬ IsRoot .E6 (a - b)) :
    [a, b].Pairwise fun β γ =>
      iform β γ = 0 ∧ ¬ IsRoot .E6 (β + γ) ∧ ¬ IsRoot .E6 (β - γ) := by
  refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
  intro γ hγ
  rw [List.mem_singleton] at hγ
  subst hγ
  exact ⟨h0, h1, h2⟩

theorem e6_pairs_outer
    (s : Fin Tag.E6.rank) :
    ∃ w : Fin 7 → WeylGroup .E6, Function.Injective (Sum.elim (fun i => w i • e6Weight s)
      (fun i => (reflectionWordProd (τ := .E6) [Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] *
        w i) • e6Weight s)) := by
  let w : Fin 7 → WeylGroup .E6 :=
    fun i => (coxeterSystem .E6).wordProd (e6OuterWords s i).reverse
  have hstep : ∀ i : Fin 7, w i • e6Weight s =
      (e6OuterWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s) :=
    fun i => wordProd_reverse_smul (τ := .E6) (e6OuterWords s i) (e6Weight s)
  have hF : ∀ β ∈ ([Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] :
      List (Fin Tag.E6.rank → ℤ)), IsRoot .E6 β := by
    intro β hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl
    · rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
      decide +kernel
    · rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
      decide +kernel
  have hσ : ∀ i : Fin 7,
      (reflectionWordProd (τ := .E6) [Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] *
        w i) • e6Weight s =
      ([Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] :
        List (Fin Tag.E6.rank → ℤ)).foldr (fun β u => u - corootPair β u • β)
        ((e6OuterWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s)) := by
    intro i
    rw [mul_smul, hstep i]
    exact CFSG.StandardType.TableBExcTwoFusion.list_map_rootReflection_prod_smul
      (τ := .E6) [Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] hF _
  refine ⟨w, ?_⟩
  have hfun : Sum.elim (fun i => w i • e6Weight s)
      (fun i => (reflectionWordProd (τ := .E6)
        [Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] * w i) • e6Weight s) =
      Sum.elim (fun i : Fin 7 => (e6OuterWords s i).foldl (fun v j => reflect .E6 j v)
          (e6Weight s))
        (fun i => ([Pi.single (0 : Fin 6) 1, Pi.single (5 : Fin 6) 1] :
          List (Fin Tag.E6.rank → ℤ)).foldr (fun β u => u - corootPair β u • β)
          ((e6OuterWords s i).foldl (fun v j => reflect .E6 j v) (e6Weight s))) := by
    funext x
    rcases x with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr, hstep i, hσ i]
  rw [hfun]
  exact e6_pair_weights_distinct_outer s


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem e6_four_le_finrank_inner [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    (hnt : ∃ (g : ↥(e6Data_valid.minGroup K)) (v : V), ρ g v ≠ v)
    (z : ↥(e6Data_valid.minGroup K))
    (hz : (Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) ∈ innerRepsE6 K) :
    4 ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  classical
  obtain ⟨y, χ, J, ht⟩ := e6_exists_isCoverType hρ
  have hJ : J ≠ Finset.univ := fun h => by
    obtain ⟨g, v, hv⟩ := hnt
    exact hv (CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.no_J_univ hρ ht h g v)
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.E6.rank, s ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.2 fun s => by
      by_contra h'; exact h ⟨s, h'⟩)
  have hv : ∀ j ∈ J, reflect .E6 j (e6Weight s) = e6Weight s := fun i hi =>
    reflect_e6Weight fun h => hs (h ▸ hi)
  simp only [innerRepsE6, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz
  ·
    have hzval : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        pinnedX .E6 K (highRoot .E6) 1 := by
      simpa using congrArg Subtype.val hz
    have hz' : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        (([highRoot .E6].map fun β =>
          pinnedX .E6 K β ((fun _ => (1 : Kˣ)) β)).prod) := by
      rw [hzval]
      simp
    have hFmem : [highRoot .E6] ∈ e6InnerFrames := by simp [e6InnerFrames]
    obtain ⟨w, hw⟩ := e6_pairs_inner (F := [highRoot .E6]) hFmem s
    exact e6_le_finrank_range_frame_sub_one_cover hρ ht hv
      (e6InnerFrames_isRoot hFmem) (e6InnerFrames_orth hFmem) (fun _ => 1) z hz' w hw
  ·
    have hzval : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        (oddDerivE6YFrame.map fun σ => pinnedX .E6 K σ 1).prod := by
      simpa using congrArg Subtype.val hz
    have hz' : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        (oddDerivE6YFrame.map fun β =>
          pinnedX .E6 K β ((fun _ => (1 : Kˣ)) β)).prod := by
      simpa using hzval
    have hFmem : oddDerivE6YFrame ∈ e6InnerFrames := by simp [e6InnerFrames]
    obtain ⟨w, hw⟩ := e6_pairs_inner (F := oddDerivE6YFrame) hFmem s
    exact e6_le_finrank_range_frame_sub_one_cover hρ ht hv
      (e6InnerFrames_isRoot hFmem) (e6InnerFrames_orth hFmem) (fun _ => 1) z hz' w hw
  ·
    have hzval : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        (oddDerivE6ZFrame.map fun σ => pinnedX .E6 K σ 1).prod := by
      simpa using congrArg Subtype.val hz
    have hz' : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
        (oddDerivE6ZFrame.map fun β =>
          pinnedX .E6 K β ((fun _ => (1 : Kˣ)) β)).prod := by
      simpa using hzval
    have hFmem : oddDerivE6ZFrame ∈ e6InnerFrames := by simp [e6InnerFrames]
    obtain ⟨w, hw⟩ := e6_pairs_inner (F := oddDerivE6ZFrame) hFmem s
    exact e6_le_finrank_range_frame_sub_one_cover hρ ht hv
      (e6InnerFrames_isRoot hFmem) (e6InnerFrames_orth hFmem) (fun _ => 1) z hz' w hw

theorem e6_seven_le_finrank_outer_frame [Module.Finite k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    (hnt : ∃ (g : ↥(e6Data_valid.minGroup K)) (v : V), ρ g v ≠ v) (d₁ d₆ : Kˣ)
    (z : ↥(e6Data_valid.minGroup K))
    (hz : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
      pinnedX .E6 K (Pi.single (0 : Fin 6) 1) (d₁ : K) *
        pinnedX .E6 K (Pi.single (5 : Fin 6) 1) (d₆ : K)) :
    7 ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  classical
  obtain ⟨y, χ, J, ht⟩ := e6_exists_isCoverType hρ
  have hJ : J ≠ Finset.univ := fun h => by
    obtain ⟨g, v, hv⟩ := hnt
    exact hv (CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.no_J_univ hρ ht h g v)
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.E6.rank, s ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.2 fun s => by
      by_contra h'; exact h ⟨s, h'⟩)
  have hv : ∀ j ∈ J, reflect .E6 j (e6Weight s) = e6Weight s := fun i hi =>
    reflect_e6Weight fun h => hs (h ▸ hi)
  have hF : ∀ β ∈ ([Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1,
      Pi.single (⟨5, by decide⟩ : Fin Tag.E6.rank) 1] :
      List (Fin Tag.E6.rank → ℤ)), IsRoot .E6 β := by
    intro β hβ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl
    · rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
      decide +kernel
    · rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
      decide +kernel
  have horth : ([Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1,
      Pi.single (⟨5, by decide⟩ : Fin Tag.E6.rank) 1] :
      List (Fin Tag.E6.rank → ℤ)).Pairwise fun β γ =>
      iform β γ = 0 ∧ ¬ IsRoot .E6 (β + γ) ∧ ¬ IsRoot .E6 (β - γ) := by
    refine e6_pairwise_pair (a := Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1)
      (b := Pi.single (⟨5, by decide⟩ : Fin Tag.E6.rank) 1) ?_ ?_ ?_
    · decide
    · rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
      decide +kernel
    · rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6)]
      decide +kernel
  let c : (Fin Tag.E6.rank → ℤ) → Kˣ :=
    fun β => if β = Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 then d₁ else d₆
  have hne : (Pi.single (⟨5, by decide⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) ≠
      (Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1 : Fin Tag.E6.rank → ℤ) := by
    decide
  have hz' : ((Isogeny.e6Isogeny K z : ↥(adjointGroup .E6 K)) : ModGL .E6 K) =
      (([Pi.single (⟨0, by decide⟩ : Fin Tag.E6.rank) 1,
        Pi.single (⟨5, by decide⟩ : Fin Tag.E6.rank) 1] :
        List (Fin Tag.E6.rank → ℤ)).map fun β => pinnedX .E6 K β (c β)).prod := by
    simp only [c, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hz]
    simp only [if_true, if_neg hne]
    rfl
  obtain ⟨w, hw⟩ := e6_pairs_outer s
  exact e6_le_finrank_range_frame_sub_one_cover hρ ht hv hF horth c z hz' w hw

end CFSG.LocalAnalysis.WeakClosure81
