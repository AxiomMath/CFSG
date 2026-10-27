module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksZero2

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.ClassicalInvolution.Models.SymplecticPairs Matrix
open CFSG.Open (StatedSp)
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)

omit [Finite K] [CharP K 2] in
theorem coe_otau (t : ℕ) (δ : Fin 2) (u : PlaneRaw.V t) :
    ((otau ζ t δ u : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      WitSpNs.planeMat fun j =>
        ((ζ (Multiplicative.ofAdd ((liftV t δ u) j)) : SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) :=
  SpBlocks.coe_tau ζ (t + δ.val) (liftV t δ u)

@[expose] def restrV (t : ℕ) (S : Finset (Fin t)) (u : PlaneRaw.V t) :
    PlaneRaw.V S.card :=
  fun k => if h : (k : ℕ) < S.card then u (S.orderEmbOfFin rfl ⟨k, h⟩) else 0

theorem liftV_restrV_eq (t : ℕ) (δ : Fin 2) (S : Finset (Fin t)) (u : PlaneRaw.V t)
    (k : Fin (S.card + δ.val)) :
    liftV t δ u (emb t δ S k) = liftV S.card δ (restrV t S u) k := by
  induction k using Fin.addCases with
  | left i =>
    rw [emb_castAdd, liftV_apply_castAdd, liftV_apply_castAdd, restrV]
    have hi : (i : ℕ) < S.card := i.isLt
    rw [dif_pos hi]
  | right j =>
    rw [emb_natAdd, liftV_apply_natAdd, liftV_apply_natAdd]

theorem liftV_apply_of_plane_not_mem (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {u : PlaneRaw.V t} (hu : PlaneRaw.vSupport u ⊆ S)
    {z : Fin (t + δ.val) ⊕ Fin (t + δ.val)}
    (hz : (WitSpNs.plane z : Fin (t + δ.val)) ∉ liftSupport t δ S) :
    Sum.elim (liftV t δ u) (liftV t δ u) z = 0 := by
  rcases z with j | j
  · change liftV t δ u j = 0
    induction j using Fin.addCases with
    | left i =>
      rw [liftV_apply_castAdd]
      have hz' : Fin.castAdd δ.val i ∉ liftSupport t δ S := hz
      have hi : i ∉ S := by
        intro hi
        exact hz' (Finset.mem_union_left _ (Finset.mem_map_of_mem (Fin.castAddEmb δ.val) hi))
      have hnot : i ∉ PlaneRaw.vSupport u := fun h => hi (hu h)
      simpa [PlaneRaw.vSupport] using hnot
    | right k =>
      exact liftV_apply_natAdd t δ u k
  · change liftV t δ u j = 0
    induction j using Fin.addCases with
    | left i =>
      rw [liftV_apply_castAdd]
      have hz' : Fin.castAdd δ.val i ∉ liftSupport t δ S := hz
      have hi : i ∉ S := by
        intro hi
        exact hz' (Finset.mem_union_left _ (Finset.mem_map_of_mem (Fin.castAddEmb δ.val) hi))
      have hnot : i ∉ PlaneRaw.vSupport u := fun h => hi (hu h)
      simpa [PlaneRaw.vSupport] using hnot
    | right k =>
      exact liftV_apply_natAdd t δ u k

theorem plane_embSum (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) :
    WitSpNs.plane (embSum t δ S x) = emb t δ S (WitSpNs.plane x) := by
  rcases x with i | i <;> rfl

theorem side_embSum (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    (x : Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) :
    WitSpNs.side (embSum t δ S x) = WitSpNs.side x := by
  rcases x with i | i <;> rfl

theorem liftV_apply_of_not_mem (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {u : PlaneRaw.V t} (hu : PlaneRaw.vSupport u ⊆ S)
    {j : Fin (t + δ.val)} (hj : j ∉ liftSupport t δ S) :
    liftV t δ u j = 0 :=
  liftV_apply_of_plane_not_mem t δ S hu (z := Sum.inl j) (by simpa using hj)

omit [Finite K] [CharP K 2] in
theorem otau_eq_orthExt_otau (t : ℕ) (δ : Fin 2) (S : Finset (Fin t))
    {u : PlaneRaw.V t} (hu : PlaneRaw.vSupport u ⊆ S) :
    otau ζ t δ u = orthExt t δ S (otau ζ S.card δ (restrV t S u)) := by
  apply Units.ext
  rw [coe_otau]
  rw [show ((orthExt t δ S (otau ζ S.card δ (restrV t S u)) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :
        Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
          (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      spEmbedMat (emb t δ S) (((otau ζ S.card δ (restrV t S u) :
        GL (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K) :
          Matrix (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val))
            (Fin (S.card + δ.val) ⊕ Fin (S.card + δ.val)) K)) from rfl]
  rw [coe_otau]
  change WitSpNs.planeMat (fun j =>
      ((ζ (Multiplicative.ofAdd (liftV t δ u j)) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) =
    spEmbedMat (emb t δ S) (WitSpNs.planeMat fun k =>
      ((ζ (Multiplicative.ofAdd (liftV S.card δ (restrV t S u) k)) :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
  have hkey : ∀ k : Fin (S.card + δ.val),
      ((ζ (Multiplicative.ofAdd (liftV t δ u (emb t δ S k))) : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) =
      ((ζ (Multiplicative.ofAdd (liftV S.card δ (restrV t S u) k)) :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    intro k
    rw [liftV_restrV_eq t δ S u k]
  ext a b
  by_cases ha : a ∈ Set.range (embSum t δ S)
  · by_cases hb : b ∈ Set.range (embSum t δ S)
    · obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      rw [spEmbedMat_apply_image (emb_injective t δ S), WitSpNs.planeMat_apply,
        WitSpNs.planeMat_apply, plane_embSum, plane_embSum, side_embSum, side_embSum]
      by_cases hxy : WitSpNs.plane x = WitSpNs.plane y
      · rw [if_pos (congrArg (emb t δ S) hxy), if_pos hxy]
        exact congrFun (congrFun (hkey (WitSpNs.plane y)) (WitSpNs.side x)) (WitSpNs.side y)
      · rw [if_neg (fun h => hxy (emb_injective t δ S h)), if_neg hxy]
    · obtain ⟨x, rfl⟩ := ha
      rw [spEmbedMat_apply_of_not_mem _ (fun h => hb h.2), WitSpNs.planeMat_apply,
        plane_embSum]
      have hzb : (WitSpNs.plane b : Fin (t + δ.val)) ∉ liftSupport t δ S :=
        fun h => hb ((mem_range_embSum_iff b).2 h)
      have hA : ((ζ (Multiplicative.ofAdd (liftV t δ u (WitSpNs.plane b))) :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
        rw [show liftV t δ u (WitSpNs.plane b) = 0 from
          liftV_apply_of_not_mem t δ S hu hzb, ofAdd_zero, map_one,
          Matrix.SpecialLinearGroup.coe_one]
      have hmemL : emb t δ S (WitSpNs.plane x) ∈ liftSupport t δ S := by
        rw [← plane_embSum t δ S x]
        exact (mem_range_embSum_iff (embSum t δ S x)).1 (Set.mem_range_self x)
      have hne_plane : emb t δ S (WitSpNs.plane x) ≠ WitSpNs.plane b := by
        intro h
        exact hzb (h ▸ hmemL)
      rw [if_neg hne_plane]
      change (0 : K) = (1 : Matrix (Fin (t + δ.val) ⊕ Fin (t + δ.val))
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) (embSum t δ S x) b
      rw [Matrix.one_apply_ne (by rintro rfl; exact hb (Set.mem_range_self x))]
  · rw [spEmbedMat_apply_of_not_mem _ (fun h => ha h.1), WitSpNs.planeMat_apply]
    have hza : (WitSpNs.plane a : Fin (t + δ.val)) ∉ liftSupport t δ S :=
      fun h => ha ((mem_range_embSum_iff a).2 h)
    have hA : ((ζ (Multiplicative.ofAdd (liftV t δ u (WitSpNs.plane a))) :
        SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [show liftV t δ u (WitSpNs.plane a) = 0 from
        liftV_apply_of_not_mem t δ S hu hza, ofAdd_zero, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    by_cases hpp : WitSpNs.plane a = WitSpNs.plane b
    · rw [if_pos hpp]
      have hAb : ((ζ (Multiplicative.ofAdd (liftV t δ u (WitSpNs.plane b))) :
          SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
        rw [show liftV t δ u (WitSpNs.plane b) = 0 from
          liftV_apply_of_not_mem t δ S hu (hpp ▸ hza), ofAdd_zero, map_one,
          Matrix.SpecialLinearGroup.coe_one]
      rw [hAb, Matrix.one_apply, Matrix.one_apply]
      by_cases hside : WitSpNs.side a = WitSpNs.side b
      · rw [if_pos hside, if_pos (WitSpNs.eq_of_plane_side hpp hside)]
      · rw [if_neg hside, if_neg (fun hab => hside (congrArg WitSpNs.side hab))]
    · rw [if_neg hpp, Matrix.one_apply_ne (fun hab => hpp (congrArg WitSpNs.plane hab))]

end

end CFSG.StandardType.GGQ2Frame.OrthBlocks
