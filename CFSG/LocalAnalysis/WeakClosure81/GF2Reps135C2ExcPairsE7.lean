module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcFrame
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotClasses
import CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.E7NoJUniv
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionE7
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCoverRoots

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.SeitzReduction.E7Pilot (e7ASFrame e7ASFrame_pairwise e7ASFrame_isRoot)
open CFSG.LieType.Steinberg.Adjoint (iform)
open CFSG.LieType.Chevalley.SimplyLacedCover (not_isRoot_add)

@[expose] def e7Weight : Fin Tag.E7.rank → Fin Tag.E7.rank → ℤ :=
  ![![4, 4, 6, 8, 6, 4, 2], ![4, 7, 8, 12, 9, 6, 3], ![6, 8, 12, 16, 12, 8, 4],
    ![8, 12, 16, 24, 18, 12, 6], ![6, 9, 12, 18, 15, 10, 5], ![4, 6, 8, 12, 10, 8, 4],
    ![2, 3, 4, 6, 5, 4, 3]]

@[expose] def e7PairWords : Fin 7 → Fin 7 → List (Fin 7) :=
  ![![[], [0], [0, 2], [0, 2, 3], [0, 2, 3, 1], [0, 2, 3, 4], [0, 2, 3, 1, 4]],
    ![[], [1], [1, 3], [1, 3, 2], [1, 3, 4], [1, 3, 2, 0], [1, 3, 2, 4]],
    ![[], [2], [2, 0], [2, 3], [2, 0, 3], [2, 3, 1], [2, 3, 4]],
    ![[], [3], [3, 1], [3, 2], [3, 4], [3, 1, 2], [3, 1, 4]],
    ![[], [4], [4, 3], [4, 5], [4, 3, 1], [4, 3, 2], [4, 3, 5]],
    ![[], [5], [5, 4], [5, 6], [5, 4, 3], [5, 4, 6], [5, 4, 3, 1]],
    ![[], [6], [6, 5], [6, 5, 4], [6, 5, 4, 3], [6, 5, 4, 3, 1], [6, 5, 4, 3, 2]]]

theorem reflect_e7Weight {s j : Fin Tag.E7.rank} (h : j ≠ s) :
    reflect .E7 j (e7Weight s) = e7Weight s := by
  revert s j
  decide +kernel

theorem e7ASFrame_strongOrth
    (k : Fin 5) :
    (e7ASFrame k).Pairwise fun β γ =>
      iform β γ = 0 ∧ ¬ IsRoot .E7 (β + γ) ∧ ¬ IsRoot .E7 (β - γ) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hβ : IsRoot .E7 (e7ASFrame k)[i] := e7ASFrame_isRoot k _ (List.getElem_mem hi)
  have hγ : IsRoot .E7 (e7ASFrame k)[j] := e7ASFrame_isRoot k _ (List.getElem_mem hj)
  have horth : iform (e7ASFrame k)[i] (e7ASFrame k)[j] = 0 :=
    List.pairwise_iff_getElem.1 (e7ASFrame_pairwise k) i j hi hj hij
  have hτ : ∀ i, Tag.E7.symmetrizer i i = 1 := by decide
  refine ⟨horth, not_isRoot_add hτ hβ hγ horth.ge, ?_⟩
  rw [sub_eq_add_neg]
  exact not_isRoot_add hτ hβ (IsRoot.neg hγ)
    (by rw [SimplyLacedCover.iform_neg_right, horth, neg_zero])

private theorem e7_pair_weights_distinct (k : Fin 5) (s : Fin Tag.E7.rank) :
    Function.Injective (Sum.elim (fun i : Fin 7 =>
        (e7PairWords s i).foldl (fun v j => reflect .E7 j v) (e7Weight s))
      (fun i => (e7ASFrame k).foldr (fun β u => u - corootPair β u • β)
        ((e7PairWords s i).foldl (fun v j => reflect .E7 j v) (e7Weight s)))) := by
  revert k s
  decide +kernel

theorem e7_pairs
    (k : Fin 5) (s : Fin Tag.E7.rank) :
    ∃ w : Fin 7 → WeylGroup .E7, Function.Injective (Sum.elim (fun i => w i • e7Weight s)
      (fun i => (reflectionWordProd (e7ASFrame k) * w i) • e7Weight s)) := by
  let w : Fin 7 → WeylGroup .E7 :=
    fun i => (coxeterSystem .E7).wordProd (e7PairWords s i).reverse
  have hstep : ∀ i : Fin 7, w i • e7Weight s =
      (e7PairWords s i).foldl (fun v j => reflect .E7 j v) (e7Weight s) :=
    fun i => wordProd_reverse_smul (τ := .E7) (e7PairWords s i) (e7Weight s)
  have hσ : ∀ i : Fin 7, (reflectionWordProd (e7ASFrame k) * w i) • e7Weight s =
      (e7ASFrame k).foldr (fun β u => u - corootPair β u • β)
        ((e7PairWords s i).foldl (fun v j => reflect .E7 j v) (e7Weight s)) := by
    intro i
    rw [mul_smul, hstep i]
    exact CFSG.StandardType.TableBExcTwoFusion.list_map_rootReflection_prod_smul
      (e7ASFrame k) (e7ASFrame_isRoot k) _
  refine ⟨w, ?_⟩
  have hfun : Sum.elim (fun i => w i • e7Weight s)
      (fun i => (reflectionWordProd (e7ASFrame k) * w i) • e7Weight s) =
      Sum.elim (fun i : Fin 7 => (e7PairWords s i).foldl (fun v j => reflect .E7 j v)
          (e7Weight s))
        (fun i => (e7ASFrame k).foldr (fun β u => u - corootPair β u • β)
          ((e7PairWords s i).foldl (fun v j => reflect .E7 j v) (e7Weight s))) := by
    funext x
    rcases x with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr, hstep i, hσ i]
  rw [hfun]
  exact e7_pair_weights_distinct k s


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem e7_seven_le_finrank_frame [Module.Finite k V] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {ρ : Representation k (adjointGroup .E7 K) V} (hρ : IsSimpleRep ρ)
    (hinj : Function.Injective ρ) (j : Fin 5) (c : (Fin Tag.E7.rank → ℤ) → Kˣ)
    (z : adjointGroup .E7 K)
    (hz : (z : ModGL .E7 K) = ((e7ASFrame j).map fun β => pinnedX .E7 K β (c β)).prod) :
    7 ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType
    (hw := CFSG.HardMathSupport.Timmesfeld.LangTorus.exists_weyl_neg_E7) (p := 2) hρ
  have hJ : J ≠ Finset.univ := fun h =>
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.no_J_univ_e7 hn hK hρ hinj ht h
  obtain ⟨s, hs⟩ : ∃ s : Fin Tag.E7.rank, s ∉ J := by
    by_contra h
    exact hJ (Finset.eq_univ_iff_forall.2 fun s => by
      by_contra h'; exact h ⟨s, h'⟩)
  have hv : ∀ i ∈ J, reflect .E7 i (e7Weight s) = e7Weight s := fun i hi =>
    reflect_e7Weight fun h => hs (h ▸ hi)
  obtain ⟨w, hw⟩ := e7_pairs (k := j) (s := s)
  exact le_finrank_range_frame_sub_one hρ ht hv (e7ASFrame_isRoot j)
    (e7ASFrame_strongOrth j) c z hz w hw

end CFSG.LocalAnalysis.WeakClosure81
