module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PositiveNo117

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.A2Actual

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KE CFSG.RankThree.E6

open CFSG.StandardType.F4ExplicitPos.PositiveNo117

open scoped Pointwise

variable {K : Type} [Field K]

theorem exists_mem_parabolicWeylGroup_smul
    {τ : Tag} {J : Set (Fin τ.rank)} :
    ∀ (n : ℕ) (α : Fin τ.rank → ℤ), (height α).toNat = n → α ∈ parabolicPosRoots τ J →
      ∃ w ∈ parabolicWeylGroup τ J, ∃ j ∈ J, w • (Pi.single j 1 : Fin τ.rank → ℤ) = α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α hn hα
    obtain ⟨⟨hroot, hzero⟩, -, hpos⟩ := hα
    have hnn := (IsRoot.height_pos_iff hroot).1 hpos
    obtain ⟨i, hαi, hci⟩ := exists_cartan_pos_w (IsRoot.ne_zero hroot) hnn
    have hiJ : i ∈ J := by
      by_contra hi
      rw [hzero i hi] at hαi
      exact lt_irrefl 0 hαi
    by_cases hsimple : α = Pi.single i 1
    · exact ⟨1, one_mem _, i, hiJ, by rw [one_smul, hsimple]⟩
    · have hβ : reflect τ i α ∈ {β | IsRoot τ β ∧ 0 < height β ∧ β ≠ Pi.single i 1} :=
        (bijOn_reflect i).mapsTo ⟨hroot, hpos, hsimple⟩
      have hht : height (reflect τ i α) = height α - ∑ j, τ.cartan i j * α j := by
        simp [reflect, height, Finset.sum_sub_distrib, Pi.single_apply]
      have hβJ : reflect τ i α ∈ parabolicPosRoots τ J := by
        refine ⟨⟨hβ.1, fun k hk => ?_⟩, hβ.1, hβ.2.1⟩
        rw [reflect, Pi.sub_apply, Pi.smul_apply,
          Pi.single_eq_of_ne (fun h => hk (by rw [h]; exact hiJ)), smul_zero, sub_zero,
          hzero k hk]
      have hlt : (height (reflect τ i α)).toNat < n := by
        rw [← hn, hht]
        have := hβ.2.1
        omega
      obtain ⟨w, hw, j, hj, hwj⟩ := ih _ hlt _ rfl hβJ
      refine ⟨simple τ i * w, mul_mem (Subgroup.subset_closure ⟨i, hiJ, rfl⟩) hw, j, hj, ?_⟩
      rw [mul_smul, hwj, simple_smul, reflect_reflect]

theorem parabolicLeviUnipotent_le_subsystemGroup
    {τ : Tag} {K : Type} [Field K]
    {A : Set (Fin τ.rank)} :
    parabolicLeviUnipotent τ K A ≤ subsystemGroup τ K A := by
  refine iSup₂_le fun α hα => ?_
  obtain ⟨w, hw, j, hj, rfl⟩ :=
    exists_mem_parabolicWeylGroup_smul (τ := τ) _ α rfl hα
  rw [← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ j)]
  rintro _ ⟨u, hu, rfl⟩
  have huS : u ∈ subsystemGroup τ K A := by
    refine (Subgroup.closure_le _).2 ?_ hu
    rintro _ ⟨c, rfl⟩
    rw [pinnedX_single]
    exact xUnit_mem_subsystemGroup hj c
  have hn := canonicalRep_mem_subsystemGroup (K := K) hw
  exact mul_mem (mul_mem hn huS) (inv_mem hn)

theorem subsystemBorel_le_subsystemGroup
    {τ : Tag} {K : Type} [Field K]
    {A : Set (Fin τ.rank)} : subsystemBorel τ K A ≤ subsystemGroup τ K A :=
  sup_le subsystemTorus_le_subsystemGroup parabolicLeviUnipotent_le_subsystemGroup

theorem rootSubgroup_le_subsystemGroup
    {τ : Tag} {K : Type} [Field K]
    {J : Set (Fin τ.rank)} {α : Fin τ.rank → ℤ} (hα : α ∈ parabolicRoots τ J) :
    rootSubgroup τ K α ≤ subsystemGroup τ K J := by
  rcases IsRoot.height_pos_or_neg hα.1 with hpos | hneg
  · exact (le_iSup₂_of_le α (mem_parabolicPosRoots_of hα hpos) le_rfl :
      rootSubgroup τ K α ≤ parabolicLeviUnipotent τ K J).trans
      parabolicLeviUnipotent_le_subsystemGroup
  · have hmem : -α ∈ parabolicPosRoots τ J :=
      mem_parabolicPosRoots_of (neg_mem_parabolicRoots hα) (by rw [height_neg]; omega)
    obtain ⟨w, hw, j, hj, hwj⟩ :=
      exists_mem_parabolicWeylGroup_smul (τ := τ) _ (-α) rfl hmem
    have hα' : α = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by
      rw [smul_neg, hwj, neg_neg]
    rw [hα', ← (canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ j)]
    rintro _ ⟨u, hu, rfl⟩
    have huQ : u ∈ subsystemGroup τ K J := by
      refine (Subgroup.closure_le _).2 ?_ hu
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_subsystemGroup hj c
    have hn := canonicalRep_mem_subsystemGroup (K := K) hw
    exact mul_mem (mul_mem hn huQ) (inv_mem hn)

theorem subsystemGroup_eq_rootSpan
    {τ : Tag} {K : Type} [Field K] (J : Set (Fin τ.rank)) :
    subsystemGroup τ K J = rootSpan τ K (parabolicRoots τ J) := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_)
    (iSup₂_le fun α hα => rootSubgroup_le_subsystemGroup hα)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [← pinnedX_single]
    exact pinnedX_mem_rootSpan (single_mem_parabolicRoots hj) c
  · rw [← pinnedX_neg_single]
    exact pinnedX_mem_rootSpan (neg_mem_parabolicRoots (single_mem_parabolicRoots hj)) c

theorem f4_exists_list_prod_pinnedX_eq
    (R : Type) [CommRing R]
    {S : Set (Fin Tag.F4.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.F4 (a • α + b • β) →
      a • α + b • β ∈ S)
    {l : List (Fin Tag.F4.rank → ℤ)} (hl : l.Nodup) (hmem : ∀ α, α ∈ l ↔ α ∈ S)
    {g : (Module.End R (RootModule Tag.F4 R))ˣ} (hg : g ∈ rootSpan Tag.F4 R S) :
    ∃ c : (Fin Tag.F4.rank → ℤ) → R, (l.map fun α => pinnedX Tag.F4 R α (c α)).prod = g := by
  have hget : Function.Injective l.get := List.nodup_iff_injective_get.1 hl
  have hrange : Set.range l.get = S := by
    ext α
    rw [Set.mem_range, ← hmem]
    exact List.mem_iff_get.symm
  obtain ⟨c, -, hc⟩ := (f4_bijOn_prod_pinnedX R hS hclosed l.get hget hrange).surjOn hg
  refine ⟨Function.extend l.get c 0, ?_⟩
  rw [← hc]
  have e : ∀ f : (Fin Tag.F4.rank → ℤ) → (Module.End R (RootModule Tag.F4 R))ˣ,
      l.map f = List.ofFn (f ∘ l.get) := fun f => by rw [← List.map_ofFn, List.ofFn_get]
  rw [e]
  congr 2
  funext i
  simp only [Function.comp_apply, hget.extend_apply]

theorem f4_exists_mul_rootSpan_eq
    (R : Type) [CommRing R] {S₁ S₂ : Set (Fin Tag.F4.rank → ℤ)}
    (hS₁ : ∀ α ∈ S₁, IsRoot Tag.F4 α ∧ 0 < height α)
    (hS₂ : ∀ α ∈ S₂, IsRoot Tag.F4 α ∧ 0 < height α)
    (hdisj : Disjoint S₁ S₂)
    (hclosed : ∀ α ∈ S₁ ∪ S₂, ∀ β ∈ S₁ ∪ S₂, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot Tag.F4 (a • α + b • β) → a • α + b • β ∈ S₁ ∪ S₂)
    {g : (Module.End R (RootModule Tag.F4 R))ˣ} (hg : g ∈ rootSpan Tag.F4 R (S₁ ∪ S₂)) :
    ∃ u₁ ∈ rootSpan Tag.F4 R S₁, ∃ u₂ ∈ rootSpan Tag.F4 R S₂, u₁ * u₂ = g := by
  obtain ⟨l₁, hl₁, hm₁⟩ := exists_list_of_finite
    ((finite_setOf_isRoot Tag.F4).subset fun α hα => (hS₁ α hα).1)
  obtain ⟨l₂, hl₂, hm₂⟩ := exists_list_of_finite
    ((finite_setOf_isRoot Tag.F4).subset fun α hα => (hS₂ α hα).1)
  have hnd : (l₁ ++ l₂).Nodup := List.nodup_append.2 ⟨hl₁, hl₂, fun α h₁ β h₂ h =>
    Set.disjoint_left.1 hdisj ((hm₁ α).1 h₁) (h ▸ (hm₂ β).1 h₂)⟩
  have hS : ∀ α ∈ S₁ ∪ S₂, IsRoot Tag.F4 α ∧ 0 < height α := fun α hα =>
    hα.elim (hS₁ α) (hS₂ α)
  obtain ⟨c, hc⟩ := f4_exists_list_prod_pinnedX_eq R hS hclosed hnd
    (fun α => by rw [List.mem_append, hm₁, hm₂, Set.mem_union]) hg
  rw [List.map_append, List.prod_append] at hc
  exact ⟨_, list_map_prod_pinnedX_mem_rootSpan R (fun α hα => (hm₁ α).1 hα) c, _,
    list_map_prod_pinnedX_mem_rootSpan R (fun α hα => (hm₂ α).1 hα) c, hc⟩

theorem f4_weylElt_mul_eq_of_mem_subsystemBorel
    {A : Set (Fin Tag.F4.rank)}
    {i : Fin Tag.F4.rank} (hi : i ∈ A) {b : ModGL Tag.F4 K}
    (hb : b ∈ subsystemBorel Tag.F4 K A) :
    ∃ b' ∈ subsystemBorel Tag.F4 K A, ∃ c : K,
      weylElt Tag.F4 K i 1 * b = b' * (weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i c) := by
  rw [← SetLike.mem_coe, coe_subsystemBorel] at hb
  obtain ⟨t, ht, v, hv, rfl⟩ := hb
  set S₁ := parabolicPosRoots Tag.F4 A \ {Pi.single i 1}
  have hsplit : parabolicPosRoots Tag.F4 A = S₁ ∪ {Pi.single i 1} := by
    rw [Set.sdiff_union_self, Set.union_eq_left.2
      (Set.singleton_subset_iff.2 (single_mem_parabolicPosRoots hi))]
  have hv' : v ∈ rootSpan Tag.F4 K (S₁ ∪ {Pi.single i 1}) := by
    rw [← hsplit]
    exact hv
  obtain ⟨u, hu, x, hx, rfl⟩ := f4_exists_mul_rootSpan_eq K (S₁ := S₁) (S₂ := {Pi.single i 1})
    (fun α hα => hα.1.2) (fun α hα => by
      rw [Set.mem_singleton_iff.1 hα]
      exact ⟨isRoot_single Tag.F4 i, by rw [height_single]; exact one_pos⟩)
    (Set.disjoint_singleton_right.2 fun h => h.2 rfl)
    (fun α hα β hβ a b ha hb hr => by
      rw [← hsplit] at hα hβ ⊢
      exact add_mem_parabolicPosRoots hα hβ ha hb hr) hv'
  rw [rootSpan, iSup_singleton] at hx
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  set n := weylElt Tag.F4 K i 1
  have hnt : n * t * n⁻¹ ∈ subsystemTorus Tag.F4 K A := weylElt_conj_mem_subsystemTorus hi ht
  have hnu : n * u * n⁻¹ ∈ parabolicLeviUnipotent Tag.F4 K A := by
    have h1 : n * u * n⁻¹ ∈ (rootSpan Tag.F4 K S₁).map (MulAut.conj n).toMonoidHom := ⟨u, hu, rfl⟩
    rw [map_conj_weylElt_rootSpan K i 1 fun α hα => hα.1.1.1,
      image_reflect_parabolicPosRoots_diff hi] at h1
    exact rootSpan_mono Set.sdiff_subset h1
  refine ⟨n * t * n⁻¹ * (n * u * n⁻¹), mul_mem (Subgroup.mem_sup_left hnt)
    (Subgroup.mem_sup_right hnu), c, ?_⟩
  rw [pinnedX_single]
  group

theorem f4_weylElt_mul_mem_subsystemCell
    {A : Set (Fin Tag.F4.rank)}
    {i : Fin Tag.F4.rank} (hi : i ∈ A) {w : WeylGroup Tag.F4}
    (hw : w ∈ parabolicWeylGroup Tag.F4 A) {x : ModGL Tag.F4 K}
    (hx : x ∈ subsystemCell Tag.F4 K A w) :
    weylElt Tag.F4 K i 1 * x ∈ subsystemCell Tag.F4 K A (simple Tag.F4 i * w) ∨
      weylElt Tag.F4 K i 1 * x ∈ subsystemCell Tag.F4 K A w := by
  obtain ⟨b, hb, b', hb', rfl⟩ := mem_subsystemCell.1 hx
  obtain ⟨b'', hb'', c, hc⟩ := f4_weylElt_mul_eq_of_mem_subsystemBorel hi hb
  have e : weylElt Tag.F4 K i 1 * (b * canonicalRep (coxeterSystem Tag.F4) K w * b') =
      b'' * (weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i c) *
        canonicalRep (coxeterSystem Tag.F4) K w * b' := by
    rw [← hc]
    group
  rw [e]
  rcases (coxeterSystem Tag.F4).length_simple_mul w i with h | h
  · left
    have hx' : xUnit Tag.F4 K i c ∈ rootSubgroup Tag.F4 K (Pi.single i 1) := by
      rw [← pinnedX_single]
      exact Subgroup.subset_closure ⟨c, rfl⟩
    obtain ⟨b₁, hb₁, h1⟩ := exists_mul_canonicalRep_eq_subsystem hw (single_mem_parabolicRoots hi)
      (height_inv_smul_single_pos h) hx'
    have hn := weylElt_mul_canonicalRep_of_length_eq (R := K) (cs := coxeterSystem Tag.F4) h
    refine mem_subsystemCell.2 ⟨b'', hb'', b₁ * b', mul_mem hb₁ hb', ?_⟩
    rw [← hn]
    calc b'' * (weylElt Tag.F4 K i 1 * canonicalRep (coxeterSystem Tag.F4) K w) * (b₁ * b') =
          b'' * weylElt Tag.F4 K i 1 *
            (canonicalRep (coxeterSystem Tag.F4) K w * b₁) * b' := by group
      _ = b'' * weylElt Tag.F4 K i 1 *
            (xUnit Tag.F4 K i c * canonicalRep (coxeterSystem Tag.F4) K w) * b' := by
          rw [h1]
      _ = b'' * (weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i c) *
            canonicalRep (coxeterSystem Tag.F4) K w * b' := by
          group
  · have h' : (coxeterSystem Tag.F4).length ((coxeterSystem Tag.F4).simple i * w) =
        (coxeterSystem Tag.F4).length w - 1 := by omega
    by_cases hc0 : c = 0
    · left
      have hn := weylElt_mul_canonicalRep_of_length_add_one_eq (R := K)
        (cs := coxeterSystem Tag.F4) h
      refine mem_subsystemCell.2 ⟨b'' * torusElt Tag.F4 K i (-1),
        mul_mem hb'' (torusElt_mem_subsystemBorel hi _), b', hb', ?_⟩
      rw [hc0, xUnit_zero, mul_one, mul_assoc b'' (weylElt Tag.F4 K i 1), hn, ← mul_assoc]
    · right
      have hr := weylElt_one_mul_xUnit (τ := Tag.F4) (R := K) i (Units.mk0 c hc0)
      rw [Units.val_mk0] at hr
      have hy : yUnit Tag.F4 K i (((Units.mk0 c hc0)⁻¹ : Kˣ) : K) ∈
          rootSubgroup Tag.F4 K (-Pi.single i 1) := by
        rw [← pinnedX_neg_single]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      obtain ⟨b₂, hb₂, h2⟩ := exists_mul_canonicalRep_eq_subsystem hw
        (neg_mem_parabolicRoots (single_mem_parabolicRoots hi))
        (height_inv_smul_neg_single_pos h') hy
      refine mem_subsystemCell.2 ⟨b'' * xUnit Tag.F4 K i (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) *
          torusElt Tag.F4 K i (-(Units.mk0 c hc0)⁻¹),
        mul_mem (mul_mem hb'' (xUnit_mem_subsystemBorel hi _)) (torusElt_mem_subsystemBorel hi _),
        b₂ * b', mul_mem hb₂ hb', ?_⟩
      rw [hr]
      calc _ = b'' * xUnit Tag.F4 K i (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) *
            torusElt Tag.F4 K i (-(Units.mk0 c hc0)⁻¹) *
              (canonicalRep (coxeterSystem Tag.F4) K w * b₂) * b' := by group
        _ = b'' * xUnit Tag.F4 K i (-(((Units.mk0 c hc0)⁻¹ : Kˣ) : K)) *
            torusElt Tag.F4 K i (-(Units.mk0 c hc0)⁻¹) *
              (yUnit Tag.F4 K i (((Units.mk0 c hc0)⁻¹ : Kˣ) : K) *
                canonicalRep (coxeterSystem Tag.F4) K w) * b' := by rw [h2]
        _ = _ := by group

theorem f4_weylElt_mul_mem_subsystemCells
    {A : Set (Fin Tag.F4.rank)}
    {i : Fin Tag.F4.rank} (hi : i ∈ A) {x : ModGL Tag.F4 K}
    (hx : x ∈ subsystemCells Tag.F4 K A) :
    weylElt Tag.F4 K i 1 * x ∈ subsystemCells Tag.F4 K A := by
  obtain ⟨w, hw, hx⟩ := mem_subsystemCells.1 hx
  have hsw : simple Tag.F4 i * w ∈ parabolicWeylGroup Tag.F4 A :=
    mul_mem (Subgroup.subset_closure ⟨i, hi, rfl⟩) hw
  rcases f4_weylElt_mul_mem_subsystemCell hi hw hx with h | h
  · exact mem_subsystemCells.2 ⟨_, hsw, h⟩
  · exact mem_subsystemCells.2 ⟨w, hw, h⟩

end CFSG.StandardType.F4ExplicitPos.A2Actual
end

end
