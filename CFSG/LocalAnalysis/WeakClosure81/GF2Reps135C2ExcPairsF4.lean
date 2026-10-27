module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcFrame
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneF4ClassDescentPhi
import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2FieldPieceModel
import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.TypeBound
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Chevalley.RootOps (orbitCertRoot)
open CFSG.LieType.Steinberg.Adjoint (iform)

@[expose] def f4Weight : Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ :=
  ![![2, 3, 4, 2], ![3, 6, 8, 4], ![2, 4, 6, 3], ![1, 2, 3, 2]]

@[expose] def f4PairWords : Fin 4 → Fin 7 → List (Fin 4) :=
  ![![[0], [0, 1, 2, 1, 0, 3, 2, 1, 0], [0, 1, 2, 3], [0, 1, 2, 1],
      [0, 1, 2, 1, 0, 3, 2, 1, 0, 2], [0, 1, 2, 1, 0, 3, 2], [0, 1, 2, 1, 0]],
    ![[1, 2, 1, 3, 2], [1, 2, 1, 3], [1, 2], [1, 2, 1, 0, 3], [1], [1, 0, 2, 1, 0], [1, 2, 3]],
    ![[2, 1, 3], [2], [2, 1, 3, 2], [2, 1, 0, 2, 1, 2, 3], [2, 1], [2, 1, 3, 2, 1], [2, 1, 2]],
    ![[3, 2, 1], [3, 2, 1, 2], [3, 2, 1, 2, 3], [3], [3, 2, 1, 0, 2, 1, 2],
      [3, 2, 1, 0, 2, 1, 2, 3, 2], [3, 2, 1, 0, 2, 1, 3]]]

theorem reflect_f4Weight {s j : Fin Tag.F4.rank} (h : j ≠ s) :
    reflect .F4 j (f4Weight s) = f4Weight s := by
  revert s j
  decide +kernel

private theorem f4DescCandidates_bounds (L : List ℕ) (hL : L ∈ f4DescCandidates) :
    ∀ p ∈ L, 24 ≤ p ∧ p ≤ 47 := by
  revert L
  decide +kernel

theorem f4DescCandidates_isRoot
    {L : List ℕ} (hL : L ∈ f4DescCandidates) :
    ∀ β ∈ L.map (orbitCertRoot .F4), IsRoot .F4 β := by
  intro β hβ
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hβ
  exact (f4_isRoot_pos (f4DescCandidates_bounds L hL p hp)).1

theorem f4DescCandidates_pairwise {L : List ℕ} (hL : L ∈ f4DescCandidates) :
    (L.map (orbitCertRoot .F4)).Pairwise fun β γ => iform β γ = 0 := by
  revert L
  decide +kernel

private def f4PairWordsInner (s : Fin Tag.F4.rank) (i : Fin 4) : List (Fin 4) :=
  f4PairWords s (Fin.castLE (by decide) i)

private theorem f4_pair_weights_distinct_inner (s : Fin Tag.F4.rank) (L : List ℕ)
    (hL : L ∈ f4DescCandidates) :
    Function.Injective (Sum.elim (fun i : Fin 4 =>
        (f4PairWordsInner s i).foldl (fun v j => reflect .F4 j v) (f4Weight s))
      (fun i => (L.map (orbitCertRoot .F4)).foldr (fun β u => u - corootPair β u • β)
        ((f4PairWordsInner s i).foldl (fun v j => reflect .F4 j v) (f4Weight s)))) := by
  revert L s
  decide +kernel

theorem f4_pairs_inner
    {L : List ℕ} (hL : L ∈ f4DescCandidates)
    (s : Fin Tag.F4.rank) :
    ∃ w : Fin 4 → WeylGroup .F4, Function.Injective (Sum.elim (fun i => w i • f4Weight s)
      (fun i => (reflectionWordProd (L.map (orbitCertRoot .F4)) * w i) • f4Weight s)) := by
  let w : Fin 4 → WeylGroup .F4 :=
    fun i => (coxeterSystem .F4).wordProd (f4PairWordsInner s i).reverse
  have hstep : ∀ i : Fin 4, w i • f4Weight s =
      (f4PairWordsInner s i).foldl (fun v j => reflect .F4 j v) (f4Weight s) :=
    fun i => wordProd_reverse_smul (τ := .F4) (f4PairWordsInner s i) (f4Weight s)
  have hσ : ∀ i : Fin 4, (reflectionWordProd (L.map (orbitCertRoot .F4)) * w i) •
      f4Weight s =
      (L.map (orbitCertRoot .F4)).foldr (fun β u => u - corootPair β u • β)
        ((f4PairWordsInner s i).foldl (fun v j => reflect .F4 j v) (f4Weight s)) := by
    intro i
    rw [mul_smul, hstep i]
    exact CFSG.StandardType.TableBExcTwoFusion.list_map_rootReflection_prod_smul
      (L.map (orbitCertRoot .F4)) (fun β hβ => f4DescCandidates_isRoot hL β hβ) _
  refine ⟨w, ?_⟩
  have hfun : Sum.elim (fun i => w i • f4Weight s)
      (fun i => (reflectionWordProd (L.map (orbitCertRoot .F4)) * w i) • f4Weight s) =
      Sum.elim (fun i : Fin 4 => (f4PairWordsInner s i).foldl
          (fun v j => reflect .F4 j v) (f4Weight s))
        (fun i => (L.map (orbitCertRoot .F4)).foldr (fun β u => u - corootPair β u • β)
          ((f4PairWordsInner s i).foldl (fun v j => reflect .F4 j v) (f4Weight s))) := by
    funext x
    rcases x with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr, hstep i, hσ i]
  rw [hfun]
  exact f4_pair_weights_distinct_inner s L hL

private theorem f4_pair_weights_distinct_outer (s : Fin Tag.F4.rank) :
    Function.Injective (Sum.elim (fun i : Fin 7 =>
        (f4PairWords s i).foldl (fun v j => reflect .F4 j v) (f4Weight s))
      (fun i => ([Pi.single (0 : Fin 4) 1, Pi.single (3 : Fin 4) 1] :
          List (Fin Tag.F4.rank → ℤ)).foldr (fun β u => u - corootPair β u • β)
        ((f4PairWords s i).foldl (fun v j => reflect .F4 j v) (f4Weight s)))) := by
  revert s
  decide +kernel

theorem f4_pairs_outer
    (s : Fin Tag.F4.rank) :
    ∃ w : Fin 7 → WeylGroup .F4, Function.Injective (Sum.elim (fun i => w i • f4Weight s)
      (fun i => (reflectionWordProd (τ := .F4) [Pi.single (0 : Fin 4) 1, Pi.single (3 : Fin 4) 1] *
        w i) • f4Weight s)) := by
  let F : List (Fin Tag.F4.rank → ℤ) :=
    [Pi.single (0 : Fin Tag.F4.rank) 1, Pi.single (3 : Fin Tag.F4.rank) 1]
  let w : Fin 7 → WeylGroup .F4 :=
    fun i => (coxeterSystem .F4).wordProd (f4PairWords s i).reverse
  have hstep : ∀ i : Fin 7, w i • f4Weight s =
      (f4PairWords s i).foldl (fun v j => reflect .F4 j v) (f4Weight s) :=
    fun i => wordProd_reverse_smul (τ := .F4) (f4PairWords s i) (f4Weight s)
  have hF : ∀ β ∈ F, IsRoot .F4 β := by
    intro β hβ
    simp only [F, List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl
    · exact IsRoot.basis 0
    · exact IsRoot.basis 3
  have hσ : ∀ i : Fin 7, (reflectionWordProd F * w i) • f4Weight s =
      F.foldr (fun β u => u - corootPair β u • β)
        ((f4PairWords s i).foldl (fun v j => reflect .F4 j v) (f4Weight s)) := by
    intro i
    rw [mul_smul, hstep i]
    exact CFSG.StandardType.TableBExcTwoFusion.list_map_rootReflection_prod_smul F hF _
  refine ⟨w, ?_⟩
  change Function.Injective (Sum.elim (fun i => w i • f4Weight s)
    (fun i => (reflectionWordProd F * w i) • f4Weight s))
  have hfun : Sum.elim (fun i => w i • f4Weight s)
      (fun i => (reflectionWordProd F * w i) • f4Weight s) =
      Sum.elim (fun i : Fin 7 => (f4PairWords s i).foldl (fun v j => reflect .F4 j v)
          (f4Weight s))
        (fun i => F.foldr (fun β u => u - corootPair β u • β)
          ((f4PairWords s i).foldl (fun v j => reflect .F4 j v) (f4Weight s))) := by
    funext x
    rcases x with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr, hstep i, hσ i]
  rw [hfun]
  exact f4_pair_weights_distinct_outer s


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem f4_rootRankOneGroup_commute {β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot .F4 β)
    (hγ : IsRoot .F4 γ) (h0 : iform β γ = 0) :
    ∀ x ∈ rootRankOneGroup .F4 K β, ∀ y ∈ rootRankOneGroup .F4 K γ, x * y = y * x := by
  have hβL : rootRankOneGroup .F4 K β =
      rootSubgroup .F4 K β ⊔ rootSubgroup .F4 K (-β) :=
    (exceptional_Lang_root_rank_one_torus_transport .F4 K hβ).1
  have hγL : rootRankOneGroup .F4 K γ =
      rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ) :=
    (exceptional_Lang_root_rank_one_torus_transport .F4 K hγ).1
  have hle := CFSG.SeitzReduction.F4Pilot.rootPair_le_centralizer_rootPair_q2p (K := K) hβ hγ h0
  rw [← hβL, ← hγL] at hle
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

variable {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem f4_four_le_finrank_frame [Module.Finite k V] {n : ℕ}
    (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup .F4 K) V} (hρ : IsSimpleRep ρ)
    (hinj : Function.Injective ρ) {L : List ℕ} (hL : L ∈ f4DescCandidates)
    (z : adjointGroup .F4 K) (hz : (z : ModGL .F4 K) = (L.map fun p => f4x K p 1).prod) :
    4 ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType
    (hw := CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.exists_weyl_neg_F4') (p := 2) hρ
  have hJ : J ≠ Finset.univ := fun h =>
    CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.no_J_univ4 hn hK hρ hinj ht h
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.F4.rank, s ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.2 fun s => by
      by_contra h'; exact h ⟨s, h'⟩)
  have hv : ∀ j ∈ J, reflect .F4 j (f4Weight s) = f4Weight s := fun i hi =>
    reflect_f4Weight fun h => hs (h ▸ hi)
  have hF : ∀ β ∈ L.map (orbitCertRoot .F4), IsRoot .F4 β := f4DescCandidates_isRoot hL
  have hcomm : (L.map (orbitCertRoot .F4)).Pairwise fun β γ =>
      ∀ x ∈ rootRankOneGroup .F4 K β, ∀ y ∈ rootRankOneGroup .F4 K γ, x * y = y * x :=
    (f4DescCandidates_pairwise hL).imp_of_mem fun {β γ} hβ hγ h0 =>
      f4_rootRankOneGroup_commute (hF β hβ) (hF γ hγ) h0
  have hz' : (z : ModGL .F4 K) =
      ((L.map (orbitCertRoot .F4)).map fun β =>
        pinnedX .F4 K β ((fun _ => (1 : Kˣ)) β)).prod := by
    rw [hz, List.map_map]
    rfl
  obtain ⟨w, hw⟩ := f4_pairs_inner hL s
  exact le_finrank_range_frame_sub_one_of_commute hρ ht hv hF hcomm (fun _ => 1) z hz' w hw

theorem f4_seven_le_finrank_outer_frame [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup .F4 K) V} (hρ : IsSimpleRep ρ)
    (hinj : Function.Injective ρ) (d₁ d₄ : Kˣ) (z : adjointGroup .F4 K)
    (hz : (z : ModGL .F4 K) =
      pinnedX .F4 K (Pi.single (0 : Fin 4) 1) (d₁ : K) *
        pinnedX .F4 K (Pi.single (3 : Fin 4) 1) (d₄ : K)) :
    7 ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType
    (hw := CFSG.HardMathSupport.Cooperstein.Coordinator.FFExc.exists_weyl_neg_F4') (p := 2) hρ
  have hJ : J ≠ Finset.univ := fun h =>
    CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.no_J_univ4 hn hK hρ hinj ht h
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.F4.rank, s ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.2 fun s => by
      by_contra h'; exact h ⟨s, h'⟩)
  have hv : ∀ j ∈ J, reflect .F4 j (f4Weight s) = f4Weight s := fun i hi =>
    reflect_f4Weight fun h => hs (h ▸ hi)
  let F : List (Fin Tag.F4.rank → ℤ) :=
    [Pi.single (0 : Fin Tag.F4.rank) 1, Pi.single (3 : Fin Tag.F4.rank) 1]
  have hF : ∀ β ∈ F, IsRoot .F4 β := by
    intro β hβ
    simp only [F, List.mem_cons, List.not_mem_nil, or_false] at hβ
    rcases hβ with rfl | rfl
    · exact IsRoot.basis 0
    · exact IsRoot.basis 3
  have h0 : iform (Pi.single (0 : Fin Tag.F4.rank) 1)
      (Pi.single (3 : Fin Tag.F4.rank) 1) = 0 := by decide
  have hcomm : F.Pairwise fun β γ =>
      ∀ x ∈ rootRankOneGroup .F4 K β, ∀ y ∈ rootRankOneGroup .F4 K γ, x * y = y * x := by
    refine List.Pairwise.cons ?_ (List.pairwise_singleton _ _)
    intro γ hγ
    rw [List.mem_singleton] at hγ
    subst hγ
    exact f4_rootRankOneGroup_commute (IsRoot.basis 0) (IsRoot.basis 3) h0
  let c : (Fin Tag.F4.rank → ℤ) → Kˣ :=
    fun β => if β = Pi.single (0 : Fin Tag.F4.rank) 1 then d₁ else d₄
  have hne : (Pi.single (3 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) ≠
      (Pi.single (0 : Fin Tag.F4.rank) 1 : Fin Tag.F4.rank → ℤ) := by
    decide
  have hz' : (z : ModGL .F4 K) = (F.map fun β => pinnedX .F4 K β (c β)).prod := by
    simp only [F, c, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hz]
    simp only [if_true, if_neg hne]
    rfl
  obtain ⟨w, hw⟩ := f4_pairs_outer s
  exact le_finrank_range_frame_sub_one_of_commute hρ ht hv hF hcomm c z hz' w hw

end CFSG.LocalAnalysis.WeakClosure81
