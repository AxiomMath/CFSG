module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.UnipotentNo117Part2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.PositiveNo117

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg

open CFSG.StandardType.F4ExplicitPos.UnipotentNo117

theorem f4_ringCommContained_simpleRoot
    (R : Type) [CommRing R] (i : Fin Tag.F4.rank)
    (β : Root Tag.F4) (hβ : 0 < height β.1) (hne : β ≠ simpleRoot Tag.F4 i) :
    (rootOperatorFamily Tag.F4).RingCommContained R (simpleRoot Tag.F4 i) β :=
  RootOps.ringCommContained_of_checks R dataChecks_F4.valid dataChecks_F4.tab
    CFSG.StandardType.F4ExplicitPos.Check68.f4_repsCheck_without68
    CFSG.StandardType.F4ExplicitPos.Check68.f4_coverCheck_without68 i β hβ hne

theorem exists_cartan_pos_w
    {τ : Tag} {α : Fin τ.rank → ℤ} (hα : α ≠ 0) (hnn : ∀ j, 0 ≤ α j) :
    ∃ i, 0 < α i ∧ 0 < ∑ j, τ.cartan i j * α j := by
  by_contra hcon
  push Not at hcon
  have hd : ∀ i : Fin τ.rank, 0 < τ.symmetrizer i i := by
    cases τ <;> intro i <;> fin_cases i <;> decide
  have hsym : ∀ i j : Fin τ.rank, τ.symmetrizedCartan i j = τ.symmetrizer i i * τ.cartan i j := by
    intro i j
    cases τ <;> fin_cases i <;> fin_cases j <;> decide
  set x : Fin τ.rank →₀ ℝ := Finsupp.equivFunOnFinite.symm fun j => (α j : ℝ)
  have hx : x ≠ 0 := by
    intro h
    apply hα
    funext j
    have := congrArg (fun y : Fin τ.rank →₀ ℝ => y j) h
    simpa [x] using this
  have hxv : ∀ j, x j = (α j : ℝ) := fun j => by simp [x]
  have hpos := (posDef_symmetrizedCartan τ).2 hx
  rw [Finsupp.sum_fintype _ _ (fun i => by simp)] at hpos
  simp only [hxv, star_trivial, Matrix.map_apply, hsym, Int.cast_mul] at hpos
  have hin : ∀ i, (x.sum fun j xj => (α i : ℝ) * ((τ.symmetrizer i i : ℝ) *
      (τ.cartan i j : ℝ)) * xj) =
      ∑ j, (α i : ℝ) * ((τ.symmetrizer i i : ℝ) * (τ.cartan i j : ℝ)) * (α j : ℝ) := fun i => by
    rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
    simp [hxv]
  simp only [hin] at hpos
  have hle : ∑ i, ∑ j, (α i : ℝ) * ((τ.symmetrizer i i : ℝ) * (τ.cartan i j : ℝ)) * (α j : ℝ) ≤
      0 := by
    refine Finset.sum_nonpos fun i _ => ?_
    have : ∑ j, (α i : ℝ) * ((τ.symmetrizer i i : ℝ) * (τ.cartan i j : ℝ)) * (α j : ℝ) =
        (α i : ℝ) * (τ.symmetrizer i i : ℝ) * ∑ j, (τ.cartan i j : ℝ) * (α j : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    rcases (hnn i).lt_or_eq with h | h
    · have h1 : (0 : ℝ) < α i := by exact_mod_cast h
      have h2 : (0 : ℝ) < τ.symmetrizer i i := by exact_mod_cast hd i
      have h3 : ∑ j, (τ.cartan i j : ℝ) * (α j : ℝ) ≤ 0 := by
        exact_mod_cast hcon i h
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h3
    · rw [← h]
      simp
  linarith

theorem exists_reflect_height_lt_w
    {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (hpos : 0 < height α) (hns : ∀ i, α ≠ Pi.single i 1) :
    ∃ i, IsRoot τ (reflect τ i α) ∧ 0 < height (reflect τ i α) ∧
      height (reflect τ i α) < height α := by
  have hnn := (IsRoot.height_pos_iff hα).1 hpos
  obtain ⟨i, -, hi⟩ := exists_cartan_pos_w hα.ne_zero hnn
  refine ⟨i, .reflect i hα, height_reflect_pos hα hpos (hns i), ?_⟩
  have : height (reflect τ i α) = height α - ∑ j, τ.cartan i j * α j := by
    simp only [height, reflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
    simp [Pi.single_apply]
  omega

theorem f4_ringCommContained_pos
    (R : Type) [CommRing R] (α β : Root Tag.F4)
    (hα : 0 < height α.1) (hβ : 0 < height β.1) (hne : α ≠ β) :
    (rootOperatorFamily Tag.F4).RingCommContained R α β := by
  induction h : (height α.1).toNat using Nat.strong_induction_on generalizing α β with
  | _ n ih =>
    by_cases hs : ∃ i, α = simpleRoot Tag.F4 i
    · obtain ⟨i, rfl⟩ := hs
      exact f4_ringCommContained_simpleRoot R i β hβ (Ne.symm hne)
    push Not at hs
    have hns : ∀ i, α.1 ≠ Pi.single i 1 := fun i h => hs i (Subtype.ext h)
    obtain ⟨i, hr, hrpos, hrlt⟩ := exists_reflect_height_lt_w α.2 hα hns
    by_cases hb : β = simpleRoot Tag.F4 i
    · subst hb
      exact (f4_ringCommContained_simpleRoot R i α hα hne).symm
    have hβ' : 0 < height (reflect Tag.F4 i β.1) :=
      height_reflect_pos β.2 hβ fun h => hb (Subtype.ext h)
    have hne' : simple Tag.F4 i • α ≠ simple Tag.F4 i • β := fun h => hne (smul_left_cancel _ h)
    have hrec := ih (height (reflect Tag.F4 i α.1)).toNat (by omega) (simple Tag.F4 i • α)
      (simple Tag.F4 i • β) (by rw [coe_smul_root, simple_smul]; exact hrpos)
      (by rw [coe_smul_root, simple_smul]; exact hβ') hne' (by rw [coe_smul_root, simple_smul])
    have := (rootOperatorFamily Tag.F4).ring_comm_transport i hrec
    rwa [smul_smul, (coxeterSystem Tag.F4).simple_mul_simple_self, one_smul, smul_smul,
      (coxeterSystem Tag.F4).simple_mul_simple_self, one_smul] at this

theorem f4_commutator_rootSubgroup_le
    (R : Type) [CommRing R] {α β : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot Tag.F4 α) (hβ : IsRoot Tag.F4 β) (hαp : 0 < height α) (hβp : 0 < height β)
    (hne : α ≠ β) :
    ⁅rootSubgroup Tag.F4 R α, rootSubgroup Tag.F4 R β⁆ ≤
      ⨆ (γ : Fin Tag.F4.rank → ℤ)
        (_ : IsRoot Tag.F4 γ ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β),
        rootSubgroup Tag.F4 R γ := by
  have hc := f4_ringCommContained_pos R ⟨α, hα⟩ ⟨β, hβ⟩ hαp hβp
    (fun h => hne (congrArg Subtype.val h))
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [rootSubgroup_eq_ringRootSubgroup R hα] at hx
  rw [rootSubgroup_eq_ringRootSubgroup R hβ] at hy
  rw [commutatorElement_def]
  have hle : (⨆ (γ : Root Tag.F4) (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α + b • β),
      (rootOperatorFamily Tag.F4).ringRootSubgroup R γ) ≤
      ⨆ (γ : Fin Tag.F4.rank → ℤ)
        (_ : IsRoot Tag.F4 γ ∧ ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ = a • α + b • β),
        rootSubgroup Tag.F4 R γ := by
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, ha, hb, hγe⟩ := hγ
    rw [← rootSubgroup_eq_ringRootSubgroup R γ.2]
    exact le_iSup₂_of_le γ.1 ⟨γ.2, a, b, ha, hb, hγe⟩ le_rfl
  exact hle (hc x hx y hy)

theorem f4_height_nsmul_add_nsmul (a b : ℕ) (α β : Fin Tag.F4.rank → ℤ) :
    height (a • α + b • β) = a * height α + b * height β := by
  simp [height, Finset.sum_add_distrib, Finset.mul_sum]

theorem f4_bijOn_prod_pinnedX
    (R : Type) [CommRing R] {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot Tag.F4 (a • α + b • β) → a • α + b • β ∈ S)
    {m : ℕ} (α : Fin m → Fin Tag.F4.rank → ℤ) (hα : Function.Injective α)
    (hrange : Set.range α = S) :
    Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX Tag.F4 R (α i) (c i)).prod)
      Set.univ (rootSpan Tag.F4 R S) := by
  classical
  have hαS : ∀ i, α i ∈ S := fun i => hrange ▸ Set.mem_range_self i
  have hUX : ∀ β ∈ S, rootSubgroup Tag.F4 R β ≤ rootSpan Tag.F4 R S := fun β hβ =>
    le_iSup₂_of_le β hβ le_rfl
  refine ⟨fun c _ => ?_, fun c _ c' _ h =>
    (positive_root_product_injectivity_w (τ := Tag.F4) R α hα fun i => hS _ (hαS i)).2 h,
    fun g hg => ?_⟩
  · refine list_prod_mem fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact hUX _ (hαS i) (Subgroup.subset_closure ⟨c i, rfl⟩)
  set X := rootSpan Tag.F4 R S
  have : Fintype S :=
    ((finite_setOf_isRoot Tag.F4).subset fun a ha => (hS a ha).1).fintype
  let A : S → Subgroup X := fun β => (rootSubgroup Tag.F4 R β.1).subgroupOf X
  have hmapA : ∀ β : S, (A β).map X.subtype = rootSubgroup Tag.F4 R β.1 := fun β => by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (hUX β.1 β.2)]
  have hab : ∀ β, IsMulCommutative (A β) := fun β =>
    ⟨⟨fun x y => Subtype.ext (Subtype.ext (rootSubgroup_mul_comm R
      (Subgroup.mem_subgroupOf.1 x.2) (Subgroup.mem_subgroupOf.1 y.2)))⟩⟩
  have hgen : ⨆ β, A β = ⊤ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [hmapA]
    exact (iSup_subtype' (p := (· ∈ S)) (f := fun β _ => rootSubgroup Tag.F4 R β)).symm
  have hc : ∀ i j : S, i ≠ j →
      ⁅A i, A j⁆ ≤ ⨆ (k : S) (_ : max (height i.1) (height j.1) < height k.1), A k := by
    intro i j hij
    rw [← Subgroup.map_le_map_iff_of_injective X.subtype_injective, Subgroup.map_commutator,
      hmapA, hmapA]
    simp only [Subgroup.map_iSup, hmapA]
    obtain ⟨hir, hip⟩ := hS _ i.2
    obtain ⟨hjr, hjp⟩ := hS _ j.2
    refine (f4_commutator_rootSubgroup_le R hir hjr hip hjp
      (fun h => hij (Subtype.ext h))).trans (iSup₂_le fun γ hγ => ?_)
    obtain ⟨hγr, a, b, ha, hb, rfl⟩ := hγ
    have hγS : a • i.1 + b • j.1 ∈ S := hclosed _ i.2 _ j.2 a b ha hb hγr
    refine le_iSup₂_of_le (⟨a • i.1 + b • j.1, hγS⟩ : S) ?_ le_rfl
    rw [f4_height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    refine max_lt ?_ ?_ <;> nlinarith
  let L : List S := List.ofFn fun i => (⟨α i, hαS i⟩ : S)
  have hnd : L.Nodup := List.nodup_ofFn.2 fun i j h => hα (congrArg Subtype.val h)
  have hall : ∀ β : S, β ∈ L := fun β => by
    obtain ⟨i, hi⟩ : β.1 ∈ Set.range α := hrange ▸ β.2
    exact List.mem_ofFn.2 ⟨i, Subtype.ext hi⟩
  obtain ⟨f, hf, hgf⟩ := height_commutator_collection
    (fun β : S => height β.1) A hab hgen hc L hnd hall ⟨g, hg⟩
  have hc' : ∀ β : S,
      ∃ c : R, pinnedX Tag.F4 R β.1 c =
        ((f β : X) : (Module.End R (RootModule Tag.F4 R))ˣ) :=
    fun β => mem_rootSubgroup.1 (Subgroup.mem_subgroupOf.1 (hf β))
  choose c hc using hc'
  refine ⟨fun i => c ⟨α i, hαS i⟩, Set.mem_univ _, ?_⟩
  have hg' : g = (L.map fun β => ((f β : X) : (Module.End R (RootModule Tag.F4 R))ˣ)).prod := by
    have h1 := congrArg Subtype.val hgf
    rwa [Subgroup.val_list_prod, List.map_map] at h1
  rw [hg', List.map_ofFn]
  show (List.ofFn fun i => pinnedX Tag.F4 R (α i) (c ⟨α i, hαS i⟩)).prod = _
  congr 1
  exact List.ofFn_inj.2 (funext fun i => hc ⟨α i, hαS i⟩)

theorem f4_positive_root_collection
    (R : Type) [CommRing R] :
    (∀ S : Set (Fin Tag.F4.rank → ℤ), (∀ α ∈ S, IsRoot Tag.F4 α ∧ 0 < height α) →
      (∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot Tag.F4 (a • α + b • β) → a • α + b • β ∈ S) →
      ∀ {m : ℕ} (α : Fin m → Fin Tag.F4.rank → ℤ), Function.Injective α → Set.range α = S →
        Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX Tag.F4 R (α i) (c i)).prod)
          Set.univ (rootSpan Tag.F4 R S)) ∧
    ∀ {m : ℕ} (α : Fin m → Fin Tag.F4.rank → ℤ), Function.Injective α →
      Set.range α = {β | IsRoot Tag.F4 β ∧ 0 < height β} →
      Set.BijOn (fun c : Fin m → R => (List.ofFn fun i => pinnedX Tag.F4 R (α i) (c i)).prod)
        Set.univ (posUnipotent Tag.F4 R) := by
  refine ⟨fun S hS hclosed m α hα hrange => f4_bijOn_prod_pinnedX R hS hclosed α hα hrange,
    fun α hα hrange => f4_bijOn_prod_pinnedX R (fun β hβ => hβ)
      (fun β hβ γ hγ a b ha hb hr => ?_) α hα hrange⟩
  refine ⟨hr, ?_⟩
  rw [f4_height_nsmul_add_nsmul]
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith [hβ.2, hγ.2]

end CFSG.StandardType.F4ExplicitPos.PositiveNo117

end

end
