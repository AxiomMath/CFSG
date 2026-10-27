module

public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {K : Type} [Field K]

@[expose] def e6Vec (c : Fin 6 → ℤ) : Fin TwistTag.E6.tag.rank → ℤ := c

theorem e6_fold_roots :
    [⟨1, by decide⟩].foldl (fun v a => TwistTag.E6.orbitReflection a • v)
        (e6Vec ![0, 0, 0, 1, 0, 0]) = e6Vec ![0, 0, 1, 1, 1, 0] ∧
    [⟨1, by decide⟩, ⟨0, by decide⟩].foldl (fun v a => TwistTag.E6.orbitReflection a • v)
        (e6Vec ![0, 0, 0, 1, 0, 0]) = e6Vec ![1, 0, 1, 1, 1, 1] ∧
    [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩,
        ⟨2, by decide⟩, ⟨3, by decide⟩].foldl (fun v a => TwistTag.E6.orbitReflection a • v)
        (e6Vec ![0, 0, 0, 1, 0, 0]) = e6Vec ![1, 2, 2, 3, 2, 1] := by
  simp only [TwistTag.orbitReflection, wordProd_smul]
  decide +kernel

theorem map_conj_orbitN_rootPair (t : TwistTag) (σ : K →+* K) (a : Fin t.foldedTag.rank)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    (rootSubgroup t.tag K β ⊔ rootSubgroup t.tag K (-β)).map
        (MulAut.conj (orbitN t K σ a 1 : ModGL t.tag K)).toMonoidHom =
      rootSubgroup t.tag K (t.orbitReflection a • β) ⊔
        rootSubgroup t.tag K (-(t.orbitReflection a • β)) := by
  obtain ⟨-, -, -, -, -, hN, -⟩ := exceptional_fixed_rank_one_central_image t K σ a
  rw [hN, Subgroup.map_sup, (canonical_weyl_root_transport t.tag K).2.1 _ β hβ,
    (canonical_weyl_root_transport t.tag K).2.1 _ (-β) (IsRoot.neg hβ), smul_neg]

theorem map_conj_orbitN_list_rootPair (t : TwistTag) (σ : K →+* K)
    (ω : List (Fin t.foldedTag.rank)) {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) :
    (rootSubgroup t.tag K β ⊔ rootSubgroup t.tag K (-β)).map (MulAut.conj
        ((ω.map fun a => (orbitN t K σ a 1 : ModGL t.tag K)).reverse.prod)).toMonoidHom =
      rootSubgroup t.tag K (ω.foldl (fun v a => t.orbitReflection a • v) β) ⊔
        rootSubgroup t.tag K (-(ω.foldl (fun v a => t.orbitReflection a • v) β)) := by
  induction ω generalizing β with
  | nil =>
    ext x
    simp
  | cons a ω ih =>
    rw [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton, map_conj_mul,
      map_conj_orbitN_rootPair t σ a hβ, ih (IsRoot.smul hβ _), List.foldl_cons]

theorem commute_of_mem_rootPair_of_check {τ : Tag} {α β : Fin τ.rank → ℤ}
    (hα : RootOps.isRootB τ α = true) (hβ : RootOps.isRootB τ β = true) (h0 : iform α β = 0)
    (hp : RootOps.isRootB τ (α + β) = false) (hm : RootOps.isRootB τ (α - β) = false)
    {x y : ModGL τ K} (hx : x ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α))
    (hy : y ∈ rootSubgroup τ K β ⊔ rootSubgroup τ K (-β)) : x * y = y * x := by
  have hnot : ∀ {v : Fin τ.rank → ℤ}, RootOps.isRootB τ v = false → ¬ IsRoot τ v :=
    fun hv hr => by
      rw [← RootOps.isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  have hα' := RootOps.isRootB_iff.1 hα
  have hβ' := RootOps.isRootB_iff.1 hβ
  rw [← (exceptional_Lang_root_rank_one_torus_transport τ K hα').1] at hx
  rw [← (exceptional_Lang_root_rank_one_torus_transport τ K hβ').1] at hy
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation τ K hα' hβ' h0
    (hnot hp) (hnot hm) x hx y hy

theorem e6_four_roots_check :
    let α : Fin 4 → Fin TwistTag.E6.tag.rank → ℤ := ![e6Vec ![0, 0, 0, 1, 0, 0],
      e6Vec ![0, 0, 1, 1, 1, 0], e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]]
    (∀ i, RootOps.isRootB TwistTag.E6.tag (α i) = true) ∧
      ∀ i j, i ≠ j → iform (α i) (α j) = 0 ∧ RootOps.isRootB TwistTag.E6.tag (α i + α j) = false ∧
        RootOps.isRootB TwistTag.E6.tag (α i - α j) = false := by
  decide +kernel

theorem even_twisted_E6_four_commuting_faithful_fixed_SL2 (K : Type) [Field K] [CharP K 2]
    (σ : K →+* K) :
    ∃ ι : Fin 4 → (SL2 (RingHom.eqLocusField σ (RingHom.id K)) →* graphFixedRootGroup .E6 K σ),
      (∀ i, Function.Injective (ι i)) ∧
      ∀ i j, i ≠ j → ∀ A B, ι i A * ι j B = ι j B * ι i A := by
  obtain ⟨R, -, -, -, -, -, hRrange, hRC, hRker, -⟩ :=
    exceptional_fixed_rank_one_central_image .E6 K σ ⟨2, by decide⟩
  have hle : RingHom.eqLocusField σ (RingHom.id K) ≤ orbitField .E6 K σ ⟨2, by decide⟩ :=
    fun c hc => by
      rw [mem_orbitField]
      exact (pow_one σ).symm ▸ hc
  let incl : SL2 (RingHom.eqLocusField σ (RingHom.id K)) →*
      SL2 (orbitField .E6 K σ ⟨2, by decide⟩) :=
    Matrix.SpecialLinearGroup.map (Subfield.inclusion hle)
  have hincl : Function.Injective incl := fun A B h => by
    ext p q
    have := congrArg (fun C : SL2 (orbitField .E6 K σ ⟨2, by decide⟩) =>
      (C : Matrix (Fin 2) (Fin 2) (orbitField .E6 K σ ⟨2, by decide⟩)) p q) h
    simp only [incl, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at this
    exact congrArg Subtype.val ((Subfield.inclusion hle).injective this)
  have hRinj : Function.Injective R := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨l, hl, hgl⟩ := hRker g (MonoidHom.mem_ker.2 hg)
    have hl1 : (l : orbitField .E6 K σ ⟨2, by decide⟩) = 1 := by
      apply Subtype.ext
      have h2 : ((l : orbitField .E6 K σ ⟨2, by decide⟩) : K) ^ 2 = 1 := by
        have := congrArg Subtype.val hl
        simpa using this
      exact CharTwo.sq_injective (show ((l : orbitField .E6 K σ ⟨2, by decide⟩) : K) ^ 2 =
        (1 : K) ^ 2 by rw [h2, one_pow])
    refine Subtype.ext ?_
    rw [hgl, hl1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  have hj : ∀ k, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin ⟨2, by decide⟩) =
      ⟨3, by decide⟩ := fun k => by
    have h := TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem ⟨2, by decide⟩) k
    have h3 : TwistTag.E6.orbit ⟨2, by decide⟩ = {⟨3, by decide⟩} := by decide
    rwa [h3, Finset.mem_singleton] at h
  have hRQ : R.range ≤ rootSubgroup TwistTag.E6.tag K (Pi.single ⟨3, by decide⟩ 1) ⊔
      rootSubgroup TwistTag.E6.tag K (-Pi.single ⟨3, by decide⟩ 1) := by
    rw [hRrange, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  have hNC : ∀ a, (orbitN .E6 K σ a 1 : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup .E6 K σ := fun a => by
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a _)) (graphFixedNegUnipotent_le_graphFixedRootGroup
        _ K σ (orbitY_mem_graphFixedNegUnipotent _ σ a _)))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (orbitX_mem_graphFixedPosUnipotent _ σ a _))
  let seq : Fin 4 → List (Fin TwistTag.E6.foldedTag.rank) := ![[], [⟨1, by decide⟩],
    [⟨1, by decide⟩, ⟨0, by decide⟩], [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨3, by decide⟩,
      ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]]
  let h : Fin 4 → ModGL TwistTag.E6.tag K := fun i =>
    ((seq i).map fun a => (orbitN .E6 K σ a 1 : ModGL TwistTag.E6.tag K)).reverse.prod
  have hhC : ∀ i, h i ∈ graphFixedRootGroup .E6 K σ := fun i =>
    Subgroup.list_prod_mem _ fun x hx => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
      exact hNC a
  have hRC' : R.range ≤ graphFixedRootGroup .E6 K σ := hRrange ▸ hRC
  have hmem : ∀ i A, (MulAut.conj (h i)).toMonoidHom.comp (R.comp incl) A ∈
      graphFixedRootGroup .E6 K σ := fun i A =>
    mul_mem (mul_mem (hhC i) (hRC' ⟨_, rfl⟩)) (inv_mem (hhC i))
  obtain ⟨hroot, hcheck⟩ := e6_four_roots_check
  have he3 : (Pi.single ⟨3, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      e6Vec ![0, 0, 0, 1, 0, 0] := by decide +kernel
  have hfold : ∀ i, (seq i).foldl (fun v a => TwistTag.E6.orbitReflection a • v)
      (Pi.single ⟨3, by decide⟩ 1) = (![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i := by
    obtain ⟨h1, h2, h3⟩ := e6_fold_roots
    intro i
    fin_cases i
    · exact he3
    · rw [he3]; exact h1
    · rw [he3]; exact h2
    · rw [he3]; exact h3
  have hQ : ∀ i A, (MulAut.conj (h i)).toMonoidHom.comp (R.comp incl) A ∈
      rootSubgroup TwistTag.E6.tag K ((![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i) ⊔
      rootSubgroup TwistTag.E6.tag K (-(![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i) := fun i A => by
    rw [← hfold i, ← map_conj_orbitN_list_rootPair .E6 σ (seq i) (isRoot_single _ _)]
    exact ⟨_, hRQ ⟨_, rfl⟩, rfl⟩
  refine ⟨fun i => ((MulAut.conj (h i)).toMonoidHom.comp (R.comp incl)).codRestrict _ (hmem i),
    fun i A B hAB => ?_, fun i j hij A B => ?_⟩
  · exact (hRinj.comp hincl) ((MulAut.conj (h i)).injective (congrArg Subtype.val hAB))
  · obtain ⟨h0, hp, hm⟩ := hcheck i j hij
    exact Subtype.ext (commute_of_mem_rootPair_of_check (hroot i) (hroot j) h0 hp hm
      (hQ i A) (hQ j B))

end CFSG.RankThree.Chevalley
