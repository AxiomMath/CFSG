module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9ShapeA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3C9ShapeC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def S1611e3ShapeL3 {G : Type} [Group G] [Finite G] (H : Subgroup G) : Prop :=
  ∀ (Y : Subgroup G), Y ≤ H → ∀ hY : (Y.subgroupOf H).Normal,
    haveI := hY
    ∀ X : Subgroup (↥H ⧸ Y.subgroupOf H), X.Normal → X ≠ ⊥ →
      (∀ N : Subgroup (↥H ⧸ Y.subgroupOf H), N.Normal → N ≤ X → N = ⊥ ∨ N = X) →
      ¬ IsMulCommutative X →
      ∀ L : Subgroup (↥H ⧸ Y.subgroupOf H), CFSG.Open.IsComponentOf L X → IsL3 ↥L 1

theorem s1611e3_compFactorAutInF_of_shapeL3 {G : Type} [Group G] [Finite G] {H S : Subgroup G}
    (hSH : S ≤ H) (hS2 : IsPGroup 2 S) (hshape : S1611e3ShapeL3 H) :
    CompFactorAutInF 2 H S := by
  intro Y hY hYn
  haveI := hYn
  let S' : Subgroup (↥H ⧸ Y.subgroupOf H) :=
    (S.subgroupOf H).map (QuotientGroup.mk' (Y.subgroupOf H))
  have hS'2 : IsPGroup 2 S' := by
    have h1 : IsPGroup 2 (S.subgroupOf H) :=
      hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    exact IsPGroup.map h1 (QuotientGroup.mk' (Y.subgroupOf H))
  exact s1611e3_cFAutInFGroup_of_shapeL3 S' hS'2 (fun X hX hXne hmin hnc L hL =>
    hshape Y hY hYn X hX hXne hmin hnc L hL)

theorem s1611e3_shapeL3_of_layer {G : Type} [Group G] [Finite G] {H : Subgroup G}
    {Q : Type} [Group Q] [Finite Q] (π : ↥H →* Q) (hπ : Function.Surjective π)
    (hker : Group.IsSolvable ↥π.ker) {E : Subgroup Q} [E.Normal]
    (hEQ : Group.IsSolvable (Q ⧸ E)) {L : Type} [Group L] (hL : IsL3 L 1)
    (eE : ↥E ≃* L × L) : S1611e3ShapeL3 H := by
  classical
  haveI : Finite L := by
    haveI : Finite ↥E := inferInstance
    haveI : Finite (L × L) := Finite.of_equiv ↥E eE
    exact Finite.of_injective (fun x : L => (x, (1 : L))) (fun a b h => (Prod.ext_iff.mp h).1)
  intro Y hY hYn
  haveI := hYn
  intro X hXn hXne hXmin hXnc L0 hL0
  let Y' : Subgroup ↥H := Y.subgroupOf H
  let q : ↥H →* (↥H ⧸ Y') := QuotientGroup.mk' Y'
  let E0 : Subgroup ↥H := E.comap π
  have hE0n : E0.Normal := (inferInstance : E.Normal).comap π
  haveI : E0.Normal := hE0n
  let Ehat : Subgroup (↥H ⧸ Y') := E0.map q
  have hEhatn : Ehat.Normal := hE0n.map q (QuotientGroup.mk'_surjective Y')
  haveI : Ehat.Normal := hEhatn
  let R : Subgroup (↥H ⧸ Y') := (π.ker).map q
  have hRn : R.Normal :=
    (inferInstance : (π.ker).Normal).map q (QuotientGroup.mk'_surjective Y')
  haveI : R.Normal := hRn
  have hRE : R ≤ Ehat := Subgroup.map_mono (f := q) (by
    intro x hx
    exact Subgroup.mem_comap.mpr (by rw [MonoidHom.mem_ker.mp hx]; exact E.one_mem))
  have hRsol : Group.IsSolvable ↥R := by
    haveI : Group.IsSolvable ↥(π.ker) := hker
    let κ : ↥(π.ker) →* ↥R :=
      (q.comp (π.ker).subtype).codRestrict R
        (fun x => Subgroup.mem_map.mpr ⟨(x : ↥H), x.2, rfl⟩)
    have hκsurj : Function.Surjective κ := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    exact Group.isSolvable_of_surjective (f := κ) hκsurj
  have hH_E0_sol : Group.IsSolvable (↥H ⧸ E0) := by
    let φQE : ↥H →* Q ⧸ E := (QuotientGroup.mk' E).comp π
    have hφQE : Function.Surjective φQE :=
      (QuotientGroup.mk'_surjective E).comp hπ
    have hφQEker : φQE.ker = E0 := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      change (QuotientGroup.mk' E) (π x) = 1 ↔ π x ∈ E
      exact QuotientGroup.eq_one_iff (π x)
    have e : ↥H ⧸ E0 ≃* Q ⧸ E :=
      (QuotientGroup.quotientMulEquivOfEq hφQEker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective φQE hφQE)
    haveI : Group.IsSolvable (Q ⧸ E) := hEQ
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Group.IsSolvable (↥H ⧸ E0) := hH_E0_sol
  have hPE : Group.IsSolvable ((↥H ⧸ Y') ⧸ Ehat) := by
    let ψ : ↥H →* ((↥H ⧸ Y') ⧸ Ehat) := (QuotientGroup.mk' Ehat).comp q
    have hψsurj : Function.Surjective ψ :=
      (QuotientGroup.mk'_surjective Ehat).comp (QuotientGroup.mk'_surjective Y')
    have hE0le : E0 ≤ ψ.ker := by
      intro e he
      rw [MonoidHom.mem_ker]
      have hmem : q e ∈ Ehat := Subgroup.mem_map.mpr ⟨e, he, rfl⟩
      exact (QuotientGroup.eq_one_iff (q e)).mpr hmem
    let ψbar : (↥H ⧸ E0) →* ((↥H ⧸ Y') ⧸ Ehat) :=
      QuotientGroup.lift (N := E0) ψ hE0le
    have hψbarsurj : Function.Surjective ψbar :=
      QuotientGroup.lift_surjective_of_surjective (N := E0) ψ hψsurj hE0le
    exact Group.isSolvable_of_surjective (f := ψbar) hψbarsurj
  let πE : ↥E0 →* ↥E :=
    (π.comp E0.subtype).codRestrict E (fun x => Subgroup.mem_comap.mp x.2)
  have hπE : Function.Surjective πE := by
    intro e
    obtain ⟨h, hh⟩ := hπ (e : Q)
    refine ⟨⟨h, Subgroup.mem_comap.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [hh]; exact e.2
    · exact hh
  let g0 : ↥E0 →* ↥Ehat :=
    (q.comp E0.subtype).codRestrict Ehat
      (fun x => Subgroup.mem_map.mpr ⟨(x : ↥H), x.2, rfl⟩)
  have hg0surj : Function.Surjective g0 := by
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let F : ↥E0 →* (↥Ehat ⧸ R.subgroupOf Ehat) :=
    (QuotientGroup.mk' (R.subgroupOf Ehat)).comp g0
  have hFsurj : Function.Surjective F :=
    (QuotientGroup.mk'_surjective (R.subgroupOf Ehat)).comp hg0surj
  have hker_le : πE.ker ≤ F.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have hxval : π (x : ↥H) = 1 := congrArg Subtype.val hx
    have hxker : (x : ↥H) ∈ π.ker := MonoidHom.mem_ker.mpr hxval
    have hmem : g0 x ∈ R.subgroupOf Ehat :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨(x : ↥H), hxker, rfl⟩)
    exact (QuotientGroup.eq_one_iff (g0 x)).mpr hmem
  let Fbar : (↥E0 ⧸ πE.ker) →* (↥Ehat ⧸ R.subgroupOf Ehat) :=
    QuotientGroup.lift (N := πE.ker) F hker_le
  have hFbarsurj : Function.Surjective Fbar :=
    QuotientGroup.lift_surjective_of_surjective (N := πE.ker) F hFsurj hker_le
  let e0 : (↥E0 ⧸ πE.ker) ≃* ↥E :=
    QuotientGroup.quotientKerEquivOfSurjective πE hπE
  let φ : ↥E →* (↥Ehat ⧸ R.subgroupOf Ehat) := Fbar.comp e0.symm.toMonoidHom
  have hφsurj : Function.Surjective φ := hFbarsurj.comp e0.symm.surjective
  let f : L × L →* (↥Ehat ⧸ R.subgroupOf Ehat) := φ.comp eE.symm.toMonoidHom
  have hf : Function.Surjective f := hφsurj.comp eE.symm.surjective
  exact s1611e3_shape_of_normal_solvable_quotient hRE hRsol hPE hL f hf X hXn hXne hXmin hXnc
    L0 hL0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
