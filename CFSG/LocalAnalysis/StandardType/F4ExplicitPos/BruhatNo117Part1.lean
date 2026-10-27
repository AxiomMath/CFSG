module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PositiveNo117

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.BruhatNo117

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.LieType.Steinberg

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open CFSG.StandardType.F4ExplicitPos.PositiveNo117 CFSG.StandardType.F4ExplicitPos.UnipotentNo117

open scoped Pointwise

variable {K : Type} [Field K]

theorem f4_positive_root_ideal_normality
    (R : Type) [CommRing R]
    {J S : Set (Fin Tag.F4.rank → ℤ)} (hJS : J ⊆ S)
    (hS : ∀ α ∈ S, IsRoot Tag.F4 α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot Tag.F4 (a • α + b • β) → a • α + b • β ∈ J) :
    rootSpan Tag.F4 R J ≤ rootSpan Tag.F4 R S ∧
      ((rootSpan Tag.F4 R J).subgroupOf (rootSpan Tag.F4 R S)).Normal := by
  set F := rootOperatorFamily Tag.F4
  have hle : rootSpan Tag.F4 R J ≤ rootSpan Tag.F4 R S :=
    iSup₂_le fun β hβ => le_iSup₂_of_le β (hJS hβ) le_rfl
  have hroot_le : ∀ β ∈ J, rootSubgroup Tag.F4 R β ≤ rootSpan Tag.F4 R J := fun β hβ =>
    le_iSup₂_of_le β hβ le_rfl
  have key : ∀ α ∈ S, ∀ (c : R), ∀ β ∈ J, ∀ d : R,
      pinnedX Tag.F4 R α c * pinnedX Tag.F4 R β d * (pinnedX Tag.F4 R α c)⁻¹ ∈
        rootSpan Tag.F4 R J := by
    intro α hα c β hβ d
    by_cases hab : α = β
    · subst hab
      have h : pinnedX Tag.F4 R α c * pinnedX Tag.F4 R α d * (pinnedX Tag.F4 R α c)⁻¹ =
          pinnedX Tag.F4 R α d := by
        rw [mul_inv_eq_iff_eq_mul, ← pinnedX_add, ← pinnedX_add, add_comm]
      rw [h]
      exact hroot_le α hβ (Subgroup.subset_closure ⟨_, rfl⟩)
    obtain ⟨hαr, hαp⟩ := hS α hα
    obtain ⟨hβr, hβp⟩ := hS β (hJS hβ)
    have hne : (⟨α, hαr⟩ : Root Tag.F4) ≠ ⟨β, hβr⟩ := fun h => hab (congrArg Subtype.val h)
    have hcomm := f4_ringCommContained_pos R ⟨α, hαr⟩ ⟨β, hβr⟩ hαp hβp hne
    have hx : pinnedX Tag.F4 R α c ∈ F.ringRootSubgroup R ⟨α, hαr⟩ := by
      rw [← rootSubgroup_eq_ringRootSubgroup R hαr]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    have hy : pinnedX Tag.F4 R β d ∈ F.ringRootSubgroup R ⟨β, hβr⟩ := by
      rw [← rootSubgroup_eq_ringRootSubgroup R hβr]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    have hmem := hcomm _ hx _ hy
    have hcone : (⨆ (γ : Root Tag.F4)
        (_ : ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ γ.1 = a • α + b • β),
        F.ringRootSubgroup R γ) ≤ rootSpan Tag.F4 R J := by
      refine iSup₂_le fun γ ⟨a, b, ha, hb, hγ⟩ => ?_
      rw [← rootSubgroup_eq_ringRootSubgroup R γ.2]
      refine hroot_le γ.1 ?_
      rw [hγ]
      exact hclosed α hα β hβ a b ha hb (hγ ▸ γ.2)
    have h1 := hcone hmem
    have h2 := mul_mem h1 (hroot_le β hβ (Subgroup.subset_closure ⟨d, rfl⟩))
    rwa [inv_mul_cancel_right] at h2
  refine ⟨hle, (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2 ?_⟩
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  have hmap : ∀ c : R, rootSpan Tag.F4 R J ≤
      (rootSpan Tag.F4 R J).comap (MulAut.conj (pinnedX Tag.F4 R α c)).toMonoidHom := fun c =>
    iSup₂_le fun β hβ => (Subgroup.closure_le _).2 (by
      rintro _ ⟨d, rfl⟩
      exact key α hα c β hβ d)
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => hmap c hy, fun hy => ?_⟩
  have h := hmap (-c) hy
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
  convert h using 1
  rw [← pinnedX_neg]
  group

theorem f4_simple_positive_root_complement
    (R : Type) [CommRing R] (i : Fin Tag.F4.rank) :
    rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} ≤
        posUnipotent Tag.F4 R ∧
    ((rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1}).subgroupOf
      (posUnipotent Tag.F4 R)).Normal ∧
    (posUnipotent Tag.F4 R : Set (Module.End R (RootModule Tag.F4 R))ˣ) =
      (rootSubgroup Tag.F4 R (Pi.single i 1) : Set (Module.End R (RootModule Tag.F4 R))ˣ) *
        (rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} :
          Set (Module.End R (RootModule Tag.F4 R))ˣ) ∧
    (posUnipotent Tag.F4 R : Set (Module.End R (RootModule Tag.F4 R))ˣ) =
      (rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} :
          Set (Module.End R (RootModule Tag.F4 R))ˣ) *
        (rootSubgroup Tag.F4 R (Pi.single i 1) : Set (Module.End R (RootModule Tag.F4 R))ˣ) ∧
    rootSubgroup Tag.F4 R (Pi.single i 1) ⊓
        rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} = ⊥ ∧
    (∀ a ∈ rootSubgroup Tag.F4 R (Pi.single i 1),
      ∀ a' ∈ rootSubgroup Tag.F4 R (Pi.single i 1),
      ∀ b ∈ rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
      ∀ b' ∈ rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
        a * b = a' * b' → a = a' ∧ b = b') ∧
    ∀ a ∈ rootSubgroup Tag.F4 R (Pi.single i 1),
      ∀ a' ∈ rootSubgroup Tag.F4 R (Pi.single i 1),
      ∀ b ∈ rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
      ∀ b' ∈ rootSpan Tag.F4 R {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1},
        b * a = b' * a' → a = a' ∧ b = b' := by
  set Si : Set (Fin Tag.F4.rank → ℤ) :=
    {γ | IsRoot Tag.F4 γ ∧ 0 < height γ ∧ γ ≠ Pi.single i 1} with hSi
  set U := rootSubgroup Tag.F4 R (Pi.single i 1)
  set N := rootSpan Tag.F4 R Si
  have hpos1 : 0 < height (Pi.single i 1 : Fin Tag.F4.rank → ℤ) := by
    rw [height_single]; exact one_pos
  obtain ⟨hle, hnorm⟩ := f4_positive_root_ideal_normality R (J := Si)
    (S := {γ | IsRoot Tag.F4 γ ∧ 0 < height γ}) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩) (fun γ hγ => hγ)
    (fun α hα β hβ a b ha hb hr => nsmul_add_nsmul_mem_complement hα.2 hβ.2.1 ha hb hr)
  have hnormal :
      posUnipotent Tag.F4 R ≤ Subgroup.normalizer (N : Set (Module.End R (RootModule Tag.F4 R))ˣ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnorm
  have hU : U ≤ posUnipotent Tag.F4 R :=
    le_iSup₂_of_le (Pi.single i 1) ⟨isRoot_single Tag.F4 i, hpos1⟩ le_rfl
  have hsup := rootSubgroup_single_sup_rootSpan_complement R i
  have hinf : U ⊓ N = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨hxU, hxN⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hxU
    have hfin : Si.Finite := (finite_setOf_isRoot Tag.F4).subset fun γ hγ => hγ.1
    set s := hfin.toFinset
    let β : Fin s.card → Fin Tag.F4.rank → ℤ := fun k => (s.equivFin.symm k : Fin Tag.F4.rank → ℤ)
    have hβinj : Function.Injective β := fun k l h =>
      s.equivFin.symm.injective (Subtype.ext h)
    have hβS : ∀ k, β k ∈ Si := fun k => hfin.mem_toFinset.1 (s.equivFin.symm k).2
    have hβrange : Set.range β = Si := by
      ext γ
      refine ⟨fun ⟨k, hk⟩ => hk ▸ hβS k, fun hγ => ⟨s.equivFin ⟨γ, hfin.mem_toFinset.2 hγ⟩, ?_⟩⟩
      simp [β]
    obtain ⟨d, -, hd⟩ := (f4_bijOn_prod_pinnedX R (S := Si) (fun γ hγ => ⟨hγ.1, hγ.2.1⟩)
      (fun α hα β' hβ' a b ha hb hr => nsmul_add_nsmul_mem_complement hα.2.1 hβ'.2.1 ha hb hr)
      β hβinj hβrange).2.2 hxN
    let γ : Fin (s.card + 1) → Fin Tag.F4.rank → ℤ := Fin.cons (Pi.single i 1) β
    have hγinj : Function.Injective γ :=
      Fin.cons_injective_iff.2 ⟨fun ⟨k, hk⟩ => (hβS k).2.2 hk, hβinj⟩
    have hγpos : ∀ k, IsRoot Tag.F4 (γ k) ∧ 0 < height (γ k) := fun k => by
      refine Fin.cases ⟨isRoot_single Tag.F4 i, hpos1⟩ (fun k => ?_) k
      exact ⟨(hβS k).1, (hβS k).2.1⟩
    have hprod := (positive_root_product_injectivity_w R γ hγinj hγpos).2
      (a₁ := Fin.cons c 0) (a₂ := Fin.cons 0 d)
    have heq :
        (List.ofFn fun k => pinnedX Tag.F4 R (γ k) ((Fin.cons c 0 : Fin (s.card + 1) → R) k)).prod =
          (List.ofFn fun k =>
            pinnedX Tag.F4 R (γ k) ((Fin.cons 0 d : Fin (s.card + 1) → R) k)).prod := by
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons, γ, Pi.zero_apply,
        pinnedX_zero, List.ofFn_const, List.prod_replicate, one_pow, mul_one, one_mul]
      exact hd.symm
    have hc := congrFun (hprod heq) 0
    simp only [Fin.cons_zero] at hc
    rw [hc, pinnedX_zero]
    exact Subgroup.one_mem _
  have hprod1 : (posUnipotent Tag.F4 R : Set (Module.End R (RootModule Tag.F4 R))ˣ) =
      (U : Set (Module.End R (RootModule Tag.F4 R))ˣ) *
        (N : Set (Module.End R (RootModule Tag.F4 R))ˣ) := by
    rw [← hsup, Subgroup.coe_mul_of_left_le_normalizer_right U N (hU.trans hnormal)]
  have hprod2 : (posUnipotent Tag.F4 R : Set (Module.End R (RootModule Tag.F4 R))ˣ) =
      (N : Set (Module.End R (RootModule Tag.F4 R))ˣ) *
        (U : Set (Module.End R (RootModule Tag.F4 R))ˣ) := by
    rw [← hsup, sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left N U (hU.trans hnormal)]
  refine ⟨hle, hnorm, hprod1, hprod2, hinf, fun a ha a' ha' b hb b' hb' h => ?_,
    fun a ha a' ha' b hb b' hb' h => ?_⟩
  · have hm : a'⁻¹ * a = b' * b⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have h1 : a'⁻¹ * a ∈ U ⊓ N :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, hm ▸ mul_mem hb' (inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_left_cancel h⟩
  · have hm : a * a'⁻¹ = b⁻¹ * b' := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, inv_mul_cancel_left]
    have h1 : a * a'⁻¹ ∈ U ⊓ N :=
      Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem ha'), hm ▸ mul_mem (inv_mem hb) hb'⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_right_cancel h⟩

theorem f4_simple_Weyl_positive_complement
    (R : Type) [CommRing R] (i : Fin Tag.F4.rank)
    (t : Rˣ) :
    (posComplement Tag.F4 R i).map (MulAut.conj (weylElt Tag.F4 R i t)).toMonoidHom =
        posComplement Tag.F4 R i ∧
    (rootSubgroup Tag.F4 R (Pi.single i 1)).map (MulAut.conj (weylElt Tag.F4 R i t)).toMonoidHom =
      rootSubgroup Tag.F4 R (-Pi.single i 1) ∧
    ((posUnipotent Tag.F4 R).map (MulAut.conj (weylElt Tag.F4 R i t)).toMonoidHom :
        Set (Module.End R (RootModule Tag.F4 R))ˣ) =
      SetLike.coe (rootSubgroup Tag.F4 R (-Pi.single i 1)) * SetLike.coe (posComplement Tag.F4 R i)
          ∧
    ((posUnipotent Tag.F4 R).map (MulAut.conj (weylElt Tag.F4 R i t)).toMonoidHom :
        Set (Module.End R (RootModule Tag.F4 R))ˣ) =
      SetLike.coe (posComplement Tag.F4 R i) * SetLike.coe (rootSubgroup Tag.F4 R (-Pi.single i 1))
          ∧
    ((posComplement Tag.F4 R i).subgroupOf
      ((posUnipotent Tag.F4 R).map (MulAut.conj (weylElt Tag.F4 R i t)).toMonoidHom)).Normal ∧
    rootSubgroup Tag.F4 R (-Pi.single i 1) ⊓ posComplement Tag.F4 R i = ⊥ ∧
    (∀ a ∈ rootSubgroup Tag.F4 R (-Pi.single i 1), ∀ a' ∈ rootSubgroup Tag.F4 R (-Pi.single i 1),
      ∀ b ∈ posComplement Tag.F4 R i, ∀ b' ∈ posComplement Tag.F4 R i,
        a * b = a' * b' → a = a' ∧ b = b') ∧
    ∀ a ∈ rootSubgroup Tag.F4 R (-Pi.single i 1), ∀ a' ∈ rootSubgroup Tag.F4 R (-Pi.single i 1),
      ∀ b ∈ posComplement Tag.F4 R i, ∀ b' ∈ posComplement Tag.F4 R i,
        b * a = b' * a' → a = a' ∧ b = b' := by
  obtain ⟨-, hnorm, -, -, -, -, -⟩ := f4_simple_positive_root_complement R i
  have hS : (posComplement Tag.F4 R i).map (MulAut.conj (weylElt Tag.F4 R i t)).toMonoidHom =
      posComplement Tag.F4 R i := by
    simp only [posComplement]
    rw [map_conj_weylElt_rootSpan R i t fun γ hγ => hγ.1]
    congr 1
    exact (bijOn_reflect i).image_eq
  set n := weylElt Tag.F4 R i t
  set Ustar := posComplement Tag.F4 R i
  set U := rootSubgroup Tag.F4 R (Pi.single i 1)
  set V := rootSubgroup Tag.F4 R (-Pi.single i 1)
  have hU : U.map (MulAut.conj n).toMonoidHom = V := by
    rw [map_conj_weylElt_rootSubgroup' R i t (isRoot_single Tag.F4 i), reflect_single_self]
  have hplus : (posUnipotent Tag.F4 R).map (MulAut.conj n).toMonoidHom = V ⊔ Ustar := by
    rw [← rootSubgroup_single_sup_rootSpan_complement R i, Subgroup.map_sup, hU]
    exact congrArg (V ⊔ ·) hS
  have hUplus : posUnipotent Tag.F4 R ≤ Subgroup.normalizer (Ustar : Set (Module.End R
      (RootModule Tag.F4 R))ˣ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (iSup₂_le fun γ hγ =>
      le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl)).1 hnorm
  have hn : n ∈ Subgroup.normalizer (Ustar : Set (Module.End R (RootModule Tag.F4 R))ˣ) := by
    rw [Subgroup.mem_normalizer_iff_conj_image_eq]
    have h := congrArg SetLike.coe hS
    rw [Subgroup.coe_map] at h
    exact h
  have hVN : V ≤ Subgroup.normalizer (Ustar : Set (Module.End R (RootModule Tag.F4 R))ˣ) := by
    rw [← hU]
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hUplus ((le_iSup₂_of_le (Pi.single i 1)
      ⟨isRoot_single Tag.F4 i, by rw [height_single]; exact one_pos⟩ le_rfl :
        U ≤ posUnipotent Tag.F4 R) hx)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn hx') (inv_mem hn)
  have hsupN : V ⊔ Ustar ≤
      Subgroup.normalizer (Ustar : Set (Module.End R (RootModule Tag.F4 R))ˣ) :=
    sup_le hVN Subgroup.le_normalizer
  have hinf : V ⊓ Ustar = ⊥ := by
    refine eq_bot_iff.2 fun g hg => ?_
    obtain ⟨hgV, hgU⟩ := Subgroup.mem_inf.1 hg
    have h1 : g ∈ posUnipotent Tag.F4 R ⊓ negUnipotent Tag.F4 R := Subgroup.mem_inf.2
      ⟨(iSup₂_le fun γ hγ => le_iSup₂_of_le γ ⟨hγ.1, hγ.2.1⟩ le_rfl : Ustar ≤ _) hgU,
        (le_iSup₂_of_le (-Pi.single i 1)
          ⟨isRoot_neg_single Tag.F4 i, by rw [height_neg, height_single]; omega⟩ le_rfl :
            V ≤ negUnipotent Tag.F4 R) hgV⟩
    rwa [posUnipotent_inf_negUnipotent] at h1
  refine ⟨hS, hU, ?_, ?_, ?_, hinf, fun a ha a' ha' b hb b' hb' h => ?_,
    fun a ha a' ha' b hb b' hb' h => ?_⟩
  · rw [hplus, Subgroup.coe_mul_of_left_le_normalizer_right V Ustar hVN]
  · rw [hplus, sup_comm, Subgroup.coe_mul_of_right_le_normalizer_left Ustar V hVN]
  · rw [hplus]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hsupN
  · have hm : a'⁻¹ * a = b' * b⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
    have h1 : a'⁻¹ * a ∈ V ⊓ Ustar :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, hm ▸ mul_mem hb' (inv_mem hb)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_left_cancel h⟩
  · have hm : a * a'⁻¹ = b⁻¹ * b' := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← h, inv_mul_cancel_left]
    have h1 : a * a'⁻¹ ∈ V ⊓ Ustar :=
      Subgroup.mem_inf.2 ⟨mul_mem ha (inv_mem ha'), hm ▸ mul_mem (inv_mem hb) hb'⟩
    rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h1
    subst h1
    exact ⟨rfl, mul_right_cancel h⟩

theorem f4_weylElt_mul_eq_of_mem_borelGroup
    (i : Fin Tag.F4.rank) {b : ModGL Tag.F4 K}
    (hb : b ∈ borelGroup Tag.F4 K) :
    ∃ b' ∈ borelGroup Tag.F4 K, ∃ c : K,
      weylElt Tag.F4 K i 1 * b = b' * (weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i c) := by
  obtain ⟨-, -, -, -, hHU, -⟩ := triangular_borel_structure.{0, 0} Tag.F4 K
  obtain ⟨hle, -, -, hUN, -⟩ := f4_simple_positive_root_complement K i
  have hb' : b ∈ (torusGroup Tag.F4 K : Set (ModGL Tag.F4 K)) *
      (posUnipotent Tag.F4 K : Set (ModGL Tag.F4 K)) := by
    rw [← hHU]
    exact hb
  obtain ⟨h, hh, v, hv, rfl⟩ := hb'
  rw [SetLike.mem_coe, ← SetLike.mem_coe, hUN] at hv
  obtain ⟨u, hu, x, hx, rfl⟩ := hv
  obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hx
  set n := weylElt Tag.F4 K i 1
  have hnh : n * h * n⁻¹ ∈ torusGroup Tag.F4 K :=
    (Subgroup.mem_normalizer_iff.1 (weylElt_mem_normalizer_torus Tag.F4 K i 1) h).1 hh
  have hnu : n * u * n⁻¹ ∈ posComplement Tag.F4 K i := by
    rw [← (f4_simple_Weyl_positive_complement K i 1).1]
    exact ⟨u, hu, rfl⟩
  refine ⟨n * h * n⁻¹ * (n * u * n⁻¹),
    mul_mem ((le_sup_left : torusGroup Tag.F4 K ≤ borelGroup Tag.F4 K) hnh)
      ((le_sup_right : posUnipotent Tag.F4 K ≤ borelGroup Tag.F4 K) (hle hnu)), c, ?_⟩
  rw [pinnedX_single]
  group

theorem f4_exists_of_mem_bruhatCell_simple_mul
    {i : Fin Tag.F4.rank} {w : WeylGroup Tag.F4}
    {x : ModGL Tag.F4 K}
    (hx : x ∈ bruhatCell Tag.F4 K (simple Tag.F4 i) * bruhatCell Tag.F4 K w) :
    ∃ b ∈ borelGroup Tag.F4 K, ∃ b' ∈ borelGroup Tag.F4 K, ∃ c : K,
      x = b * (weylElt Tag.F4 K i 1 * xUnit Tag.F4 K i c) *
        canonicalRep (coxeterSystem Tag.F4) K w * b' := by
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.1 hx
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := mem_bruhatCell.1 hy
  obtain ⟨b₃, hb₃, b₄, hb₄, rfl⟩ := mem_bruhatCell.1 hz
  obtain ⟨b', hb', c, hc⟩ := f4_weylElt_mul_eq_of_mem_borelGroup i (mul_mem hb₂ hb₃)
  refine ⟨b₁ * b', mul_mem hb₁ hb', b₄, hb₄, c, ?_⟩
  rw [canonicalRep_simple]
  calc b₁ * weylElt Tag.F4 K i 1 * b₂ * (b₃ * canonicalRep (coxeterSystem Tag.F4) K w * b₄) =
        b₁ * (weylElt Tag.F4 K i 1 * (b₂ * b₃)) *
          canonicalRep (coxeterSystem Tag.F4) K w * b₄ := by
        group
    _ = _ := by rw [hc]; group

theorem f4_bruhatCell_simple_mul_of_length_eq_add_one
    {i : Fin Tag.F4.rank}
    {w : WeylGroup Tag.F4}
    (h : (coxeterSystem Tag.F4).length (simple Tag.F4 i * w) =
      (coxeterSystem Tag.F4).length w + 1) :
    bruhatCell Tag.F4 K (simple Tag.F4 i) * bruhatCell Tag.F4 K w =
      bruhatCell Tag.F4 K (simple Tag.F4 i * w) := by
  have hn : weylElt Tag.F4 K i 1 * canonicalRep (coxeterSystem Tag.F4) K w =
      canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) :=
    weylElt_mul_canonicalRep_of_length_eq h
  refine Set.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨b, hb, b', hb', c, rfl⟩ := f4_exists_of_mem_bruhatCell_simple_mul hx
    obtain ⟨b'', hb'', hc⟩ := exists_mul_canonicalRep_eq (w := w) (isRoot_single Tag.F4 i)
      (height_inv_smul_single_pos h) (Subgroup.subset_closure ⟨c, pinnedX_single Tag.F4 K i c⟩)
    refine mem_bruhatCell.2 ⟨b, hb, b'' * b', mul_mem hb'' hb', ?_⟩
    calc b * canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) * (b'' * b') =
          b * (weylElt Tag.F4 K i 1 * canonicalRep (coxeterSystem Tag.F4) K w) *
            (b'' * b') := by
          rw [hn]
      _ = b * weylElt Tag.F4 K i 1 * (canonicalRep (coxeterSystem Tag.F4) K w * b'') * b' := by
          group
      _ = b * weylElt Tag.F4 K i 1 *
            (xUnit Tag.F4 K i c * canonicalRep (coxeterSystem Tag.F4) K w) * b' := by
          rw [hc]
      _ = _ := by group
  · obtain ⟨b, hb, b', hb', rfl⟩ := mem_bruhatCell.1 hx
    have e : b * weylElt Tag.F4 K i 1 * 1 * (1 * canonicalRep (coxeterSystem Tag.F4) K w * b') =
        b * canonicalRep (coxeterSystem Tag.F4) K (simple Tag.F4 i * w) * b' := by
      rw [← hn]
      group
    rw [← e]
    exact mem_bruhatCell_simple_mul hb (one_mem _) (one_mem _) hb'

end CFSG.StandardType.F4ExplicitPos.BruhatNo117
end

end
