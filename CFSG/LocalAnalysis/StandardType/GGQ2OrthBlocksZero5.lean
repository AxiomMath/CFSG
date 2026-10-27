module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero6

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.ClassicalInvolution.Models.SymplecticPairs Matrix
open CFSG.Open (StatedSp)
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K]
variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)

abbrev embSum (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → Fin (t + δ.val) ⊕ Fin (t + δ.val) :=
  Sum.map (emb t δ S) (emb t δ S)

theorem embSum_injective (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    Function.Injective (embSum t δ S) :=
  Sum.map_injective.2 ⟨emb_injective t δ S, emb_injective t δ S⟩

theorem mem_range_embSum_iff {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)}
    (z : Fin (t + δ.val) ⊕ Fin (t + δ.val)) :
    z ∈ Set.range (embSum t δ S) ↔
      (WitSpNs.plane z : Fin (t + δ.val)) ∈ liftSupport t δ S := by
  constructor
  · rintro ⟨w, rfl⟩
    rcases w with i | i <;> simp [embSum, mem_liftSupport_iff]
  · intro hz
    obtain ⟨k, hk⟩ := (mem_liftSupport_iff (S := S) (WitSpNs.plane z)).mp hz
    rcases z with i | i
    · refine ⟨Sum.inl k, ?_⟩
      simp only [embSum, Sum.map_inl, Sum.inl.injEq]
      simpa using hk
    · refine ⟨Sum.inr k, ?_⟩
      simp only [embSum, Sum.map_inr, Sum.inr.injEq]
      simpa using hk

@[expose] def orthExt (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K →*
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K :=
  spEmbedGL (emb t δ S) (emb_injective t δ S)

theorem orthExt_apply_image (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (A : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K)
    (x y : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) :
    ((orthExt t δ S A : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) (embSum t δ S x) (embSum t δ S y) =
      (A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
        (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) x y :=
  spEmbedMat_apply_image (emb_injective t δ S)
    (A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
      (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) x y

theorem orthExt_apply_not_mem (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (A : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K)
    {a b : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (h : ¬ (a ∈ Set.range (embSum t δ S) ∧ b ∈ Set.range (embSum t δ S))) :
    ((orthExt t δ S A : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b =
      (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b :=
  spEmbedMat_apply_of_not_mem
    (A : Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
      (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) h

theorem orthExt_injective (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    Function.Injective (orthExt (K := K) t δ S) := by
  intro A B h
  apply Units.ext
  apply spEmbedMat_injective (emb_injective t δ S)
  exact congrArg (fun u : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K =>
    (u : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
      (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) h

section CharTwo

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem one_sub_planeIdem_eq_diagonal (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) :
    (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      Matrix.diagonal (fun z => if (WitSpNs.plane z : Fin (t + δ.val)) ∈
        liftSupport t δ S then (0 : K) else 1) := by
  rw [SpBlocks.planeIdem, ← Matrix.diagonal_one, Matrix.diagonal_sub]
  congr 1
  funext z
  change (1 - (if (Sum.elim id id z : Fin (t + δ.val)) ∈ liftSupport t δ S then (1 : K)
    else 0)) = (if (Sum.elim id id z : Fin (t + δ.val)) ∈ liftSupport t δ S then 0 else 1)
  split_ifs <;> simp

omit [Finite K] in
theorem mem_oBlockGroup_zero_iff (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : ↥(omegaQ (K := K) t δ)} :
    g ∈ oBlockGroup ζ t δ (.zero S) ↔
      ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
          (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) =
        1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) := by
  rw [oBlockGroup, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hval⟩
    have hs' : s = ⟨(g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K),
        omegaQ_le_statedSp t δ g.2⟩ := Subtype.ext hval
    subst hs'
    exact hs
  · intro h
    exact ⟨⟨(g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K),
      omegaQ_le_statedSp t δ g.2⟩, h, rfl⟩

omit [Finite K] in
theorem one_sub_mul_of_mem_oBlockGroup (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : ↥(omegaQ (K := K) t δ)} (hg : g ∈ oBlockGroup ζ t δ (.zero S)) :
    (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) *
        ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
          Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
            (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) := by
  have hfix := (mem_oBlockGroup_zero_iff ζ t δ S).1 hg
  exact SpBlocks.one_sub_planeIdem_mul_of_mem (omegaQ_le_statedSp t δ g.2) hfix

omit [Finite K] in
theorem apply_of_not_mem_plane_right (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : ↥(omegaQ (K := K) t δ)} (hg : g ∈ oBlockGroup ζ t δ (.zero S))
    {a b : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (hb : (WitSpNs.plane b : Fin (t + δ.val)) ∉ liftSupport t δ S) :
    ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b =
      (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b := by
  have hfix := (mem_oBlockGroup_zero_iff ζ t δ S).1 hg
  let d : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    fun z => if WitSpNs.plane z ∈ liftSupport t δ S then 0 else 1
  have hd : (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) = Matrix.diagonal d :=
    one_sub_planeIdem_eq_diagonal t δ S
  have hdb : d b = 1 := by simp [d, hb]
  have h := congrFun (congrFun hfix a) b
  rw [hd, Matrix.mul_diagonal, Matrix.diagonal_apply] at h
  rw [hdb, mul_one] at h
  rw [h, Matrix.one_apply]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos hab, hab]
    exact hdb
  · rw [if_neg hab, if_neg hab]

omit [Finite K] in
theorem apply_of_not_mem_plane_left (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {g : ↥(omegaQ (K := K) t δ)} (hg : g ∈ oBlockGroup ζ t δ (.zero S))
    {a b : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (ha : (WitSpNs.plane a : Fin (t + δ.val)) ∉ liftSupport t δ S) :
    ((g : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b =
      (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) a b := by
  have hfix := one_sub_mul_of_mem_oBlockGroup ζ t δ S hg
  let d : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    fun z => if WitSpNs.plane z ∈ liftSupport t δ S then 0 else 1
  have hd : (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) = Matrix.diagonal d :=
    one_sub_planeIdem_eq_diagonal t δ S
  have hda : d a = 1 := by simp [d, ha]
  have h := congrFun (congrFun hfix a) b
  rw [hd, Matrix.diagonal_mul, Matrix.diagonal_apply] at h
  rw [hda, one_mul] at h
  rw [h, Matrix.one_apply]


omit [Finite K] [CharP K 2] in
theorem planeQ_add_of_support (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {x y : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K}
    (hx : ∀ z : Fin (t + δ.val) ⊕ Fin (t + δ.val),
      (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S → x z = 0)
    (hy : ∀ z : Fin (t + δ.val) ⊕ Fin (t + δ.val),
      (WitSpNs.plane z : Fin (t + δ.val)) ∈ liftSupport t δ S → y z = 0) :
    planeQ (K := K) t δ (x + y) = planeQ (K := K) t δ x + planeQ (K := K) t δ y := by
  rw [planeQ, planeQ, planeQ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ∈ liftSupport t δ S
  · have hy1 : y (Sum.inl j) = 0 := hy _ (by simpa using hj)
    have hy2 : y (Sum.inr j) = 0 := hy _ (by simpa using hj)
    simp [Pi.add_apply, hy1, hy2]
  · have hx1 : x (Sum.inl j) = 0 := hx _ (by simpa using hj)
    have hx2 : x (Sum.inr j) = 0 := hx _ (by simpa using hj)
    simp [Pi.add_apply, hx1, hx2]

omit [Finite K] [CharP K 2] in
theorem sum_comp_embSum {t : ℕ} {δ : Fin 2} {S : Finset (Fin t)}
    {f : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K}
    (hf : ∀ q : Fin (t + δ.val) ⊕ Fin (t + δ.val),
      q ∉ Set.range (embSum t δ S) → f q = 0) :
    (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val), f q) =
      ∑ x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val), f (embSum t δ S x) := by
  classical
  have hsub : ∀ q ∈ (Finset.univ : Finset (Fin (t + δ.val) ⊕ Fin (t + δ.val))),
      q ∉ Finset.univ.image (embSum t δ S) → f q = 0 := by
    intro q _ hq
    exact hf q (by simpa using hq)
  calc (∑ q : Fin (t + δ.val) ⊕ Fin (t + δ.val), f q)
      = ∑ q ∈ (Finset.univ : Finset (Fin (t + δ.val) ⊕ Fin (t + δ.val))), f q := rfl
    _ = ∑ q ∈ Finset.univ.image (embSum t δ S), f q :=
        (Finset.sum_subset (Finset.subset_univ _) hsub).symm
    _ = ∑ x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val), f (embSum t δ S x) :=
        Finset.sum_image fun a _ b _ h => embSum_injective t δ S h

@[expose] def liftVec (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (v : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K) :
    Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
  Function.extend (embSum t δ S) v 0

omit [Finite K] [CharP K 2] in
theorem liftVec_apply_embSum (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (v : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K)
    (x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) :
    liftVec t δ S v (embSum t δ S x) = v x :=
  (embSum_injective t δ S).extend_apply v 0 x

omit [Finite K] [CharP K 2] in
theorem liftVec_apply_of_not_mem (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (v : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K)
    {z : Fin (t + δ.val) ⊕ Fin (t + δ.val)} (hz : z ∉ Set.range (embSum t δ S)) :
    liftVec t δ S v z = 0 :=
  Function.extend_apply' _ _ _ hz

omit [Finite K] [CharP K 2] in
theorem liftVec_apply_of_plane_not_mem (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (v : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val) → K)
    {z : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (hz : (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S) :
    liftVec t δ S v z = 0 :=
  liftVec_apply_of_not_mem t δ S v fun h => hz ((mem_range_embSum_iff z).1 h)

omit [Finite K] [CharP K 2] in
theorem orthExt_mul_one_sub (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (A : GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) :
    ((orthExt t δ S A : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
        (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) =
      1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S) := by
  let d : Fin (t + δ.val) ⊕ Fin (t + δ.val) → K :=
    fun z => if WitSpNs.plane z ∈ liftSupport t δ S then 0 else 1
  have hd : (1 - SpBlocks.planeIdem (t + δ.val) (liftSupport t δ S)) = Matrix.diagonal d :=
    one_sub_planeIdem_eq_diagonal t δ S
  rw [hd]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases hb : (WitSpNs.plane b : Fin (t + δ.val)) ∈ liftSupport t δ S
  · have hdb : d b = 0 := by simp [d, hb]
    rw [hdb, mul_zero]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, show d a = 0 from hdb]
    · rw [if_neg hab]
  · have hdb : d b = 1 := by simp [d, hb]
    rw [hdb, mul_one]
    have hnot : b ∉ Set.range (embSum t δ S) := fun h => hb ((mem_range_embSum_iff b).1 h)
    rw [orthExt_apply_not_mem t δ S A (fun hh => hnot hh.2)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, show d a = 1 from hdb, Matrix.one_apply_eq]
    · rw [if_neg hab, Matrix.one_apply_ne hab]

end CharTwo

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
