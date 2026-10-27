module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] {H R T : Subgroup G}

private theorem le_map_subtype_comap {Y : Type} [Group Y] {π : ↥H →* Y} (hTH : T ≤ H)
    {Xb : Subgroup Y} (hTX : (T.subgroupOf H).map π ≤ Xb) : T ≤ (Xb.comap π).map H.subtype :=
  fun t ht => ⟨⟨t, hTH ht⟩, hTX (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ht)), rfl⟩

private theorem map_subtype_comap_lt {Y : Type} [Group Y] {π : ↥H →* Y}
    (hπ : Function.Surjective π) {Xb : Subgroup Y} (hXt : Xb < ⊤) :
    (Xb.comap π).map H.subtype < H := by
  refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun hXeq => hXt.ne ?_
  have h1 : Xb.comap π = ⊤ := by
    rw [← Subgroup.comap_map_eq_self_of_injective H.subtype_injective (Xb.comap π), hXeq]
    exact Subgroup.subgroupOf_self H
  rw [← Subgroup.map_comap_eq_self_of_surjective hπ Xb, h1, Subgroup.map_top_of_surjective π hπ]

theorem isCompositionFactor_map_of_le [Finite G] (hRs : Group.IsSolvable ↥R) {X : Subgroup G}
    (hXH : X ≤ H) {L : Type} [Group L] (h : E1.IsCompositionFactor ↥X L)
    (hnab : ∃ a b : L, a * b ≠ b * a) :
    E1.IsCompositionFactor
      ↥((X.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H).normalCore)) L := by
  let φ : ↥X →* ↥H ⧸ (R.subgroupOf H).normalCore :=
    (QuotientGroup.mk' (R.subgroupOf H).normalCore).comp (Subgroup.inclusion hXH)
  have hrange :
      φ.range = (X.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H).normalCore) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  rcases isCompositionFactor_of_normal φ.ker h with h1 | h2
  · exfalso
    have hmem : ∀ k : ↥φ.ker, ((k : ↥X) : G) ∈ R := by
      intro k
      have hk : φ (k : ↥X) = 1 := k.2
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk
      exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le (R.subgroupOf H) hk)
    let f : ↥φ.ker →* ↥R :=
      { toFun := fun k => ⟨((k : ↥X) : G), hmem k⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥R => (z : G)) hab
    have : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_isSolvable_injective hf
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_abelian_of_compositionFactor
      inferInstance h1 a b)
  · exact (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))).1 h2

theorem isCompositionFactor_of_quot {L : Type} [Group L]
    (h : E1.IsCompositionFactor (↥H ⧸ (R.subgroupOf H).normalCore) L) :
    E1.IsCompositionFactor ↥H L :=
  CFSG.Quasithin.H13.L829N.isCompositionFactor_of_surjective _
    (QuotientGroup.mk'_surjective _) h

theorem lGen_eq_of_quot [Finite G] (hRs : Group.IsSolvable ↥R) (hHR : ¬ H ≤ R) (hTH : T ≤ H)
    (h : lGen IsCalL1 (⊤ : Subgroup (↥H ⧸ (R.subgroupOf H).normalCore))
      ((T.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H).normalCore)) = ⊤) :
    lGen IsCalL1 H T = H := by
  set Nc : Subgroup ↥H := (R.subgroupOf H).normalCore
  set π : ↥H →* ↥H ⧸ Nc := QuotientGroup.mk' Nc
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Nc
  have hker : π.ker = Nc := QuotientGroup.ker_mk' Nc
  have key : ∀ Xb ∈ calLT IsCalL1 (⊤ : Subgroup (↥H ⧸ Nc)) ((T.subgroupOf H).map π),
      Xb.comap π ≤ (lGen IsCalL1 H T).subgroupOf H := by
    intro Xb hXb
    obtain ⟨hTX, hXt, hXcf⟩ := hXb
    have hXH : (Xb.comap π).map H.subtype ≤ H := Subgroup.map_subtype_le _
    have hXsub : ((Xb.comap π).map H.subtype).subgroupOf H = Xb.comap π :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    have hXmap : (((Xb.comap π).map H.subtype).subgroupOf H).map π = Xb := by
      rw [hXsub, Subgroup.map_comap_eq_self_of_surjective hπ]
    have hmem : (Xb.comap π).map H.subtype ∈ calLT IsCalL1 H T := by
      refine ⟨le_map_subtype_comap hTH hTX, map_subtype_comap_lt hπ hXt, ?_⟩
      rintro ⟨L, _, hcf, hL⟩
      have : Finite L := isCompositionFactor_finite hcf
      have hcf' : E1.IsCompositionFactor
          ↥((((Xb.comap π).map H.subtype).subgroupOf H).map π) L :=
        isCompositionFactor_map_of_le hRs hXH hcf (exists_mul_ne_of_isCalL1 hL)
      rw [hXmap] at hcf'
      exact hXcf ⟨L, inferInstance, hcf', hL⟩
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact (le_iSup₂_of_le _ hmem le_rfl : (Xb.comap π).map H.subtype ≤ lGen IsCalL1 H T)
      (Subgroup.mem_map_of_mem H.subtype hy)
  have hNct : Nc ≠ ⊤ := by
    intro h'
    apply hHR
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥H) ∈ Nc := by
      rw [h']
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hx')
  have : Nontrivial (↥H ⧸ Nc) := QuotientGroup.nontrivial_iff.mpr hNct
  obtain ⟨Xb, hXb⟩ :
      (calLT IsCalL1 (⊤ : Subgroup (↥H ⧸ Nc)) ((T.subgroupOf H).map π)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hbot : lGen IsCalL1 (⊤ : Subgroup (↥H ⧸ Nc)) ((T.subgroupOf H).map π) = ⊥ := by
      simp [lGen, hempty]
    exact bot_ne_top (hbot.symm.trans h)
  have hkerle : Nc ≤ (lGen IsCalL1 H T).subgroupOf H :=
    hker ▸ (MonoidHom.ker_le_comap π Xb).trans (key Xb hXb)
  have htop : ((lGen IsCalL1 H T).subgroupOf H).map π = ⊤ := by
    rw [eq_top_iff, ← h]
    refine iSup₂_le fun Yb hYb => ?_
    calc Yb = (Yb.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ Yb).symm
      _ ≤ _ := Subgroup.map_mono (key Yb hYb)
  have hsub : (lGen IsCalL1 H T).subgroupOf H = ⊤ := by
    have h1 := Subgroup.comap_map_eq π ((lGen IsCalL1 H T).subgroupOf H)
    rw [htop, Subgroup.comap_top, hker, sup_of_le_left hkerle] at h1
    exact h1.symm
  exact le_antisymm lGen_le (Subgroup.subgroupOf_eq_top.mp hsub)

theorem hasUniqueMaxOver_quot [Finite G] (hTH : T ≤ H) {M : Subgroup G} (hN : calNIn H T = {M})
    (hRM : R ≤ M) :
    HasUniqueMaxOver ((T.subgroupOf H).map (QuotientGroup.mk' (R.subgroupOf H).normalCore)) := by
  set Nc : Subgroup ↥H := (R.subgroupOf H).normalCore
  set π : ↥H →* ↥H ⧸ Nc := QuotientGroup.mk' Nc
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Nc
  have hker : π.ker = Nc := QuotientGroup.ker_mk' Nc
  have hM : M ∈ calNIn H T := hN ▸ Set.mem_singleton M
  have hkerM : Nc ≤ M.subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRM (Subgroup.mem_subgroupOf.mp (Subgroup.normalCore_le _ hx)))
  refine ⟨(M.subgroupOf H).map π, lt_top_iff_ne_top.mpr fun htop => ?_, fun Xb hTX hXt => ?_⟩
  ·
    have h1 := Subgroup.comap_map_eq π (M.subgroupOf H)
    rw [htop, Subgroup.comap_top, hker, sup_of_le_left hkerM] at h1
    exact hM.2.1.not_ge (Subgroup.subgroupOf_eq_top.mp h1.symm)
  · obtain ⟨Z, hZ, hXZ⟩ :=
      exists_mem_calNIn_of_lt (le_map_subtype_comap hTH hTX) (map_subtype_comap_lt hπ hXt)
    rw [hN, Set.mem_singleton_iff] at hZ
    subst hZ
    calc Xb = (Xb.comap π).map π := (Subgroup.map_comap_eq_self_of_surjective hπ Xb).symm
      _ ≤ (Z.subgroupOf H).map π := Subgroup.map_mono fun y hy =>
          Subgroup.mem_subgroupOf.mpr (hXZ (Subgroup.mem_map_of_mem H.subtype hy))

theorem hasQuotShape_fStarMod_of_mulEquiv {N : Subgroup G} (hN : (N.subgroupOf H).Normal)
    {P : ∀ (X : Type) [Group X], Prop} {X : Type} [Group X]
    (e : ↥(CFSG.Open.genFittingFStar (↥H ⧸ (N.subgroupOf H).normalCore)) ≃* X) (hP : P X) :
    HasQuotShape (fStarMod N H) (N : Set G) P := by
  set Nc : Subgroup ↥H := (N.subgroupOf H).normalCore
  have hcore : Nc = N.subgroupOf H := Subgroup.normalCore_eq_self _
  set F : Subgroup (↥H ⧸ Nc) := CFSG.Open.genFittingFStar (↥H ⧸ Nc)
  set π : ↥H →* ↥H ⧸ Nc := QuotientGroup.mk' Nc
  set Fp : Subgroup ↥H := F.comap π
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Nc
  let ψ : ↥Fp →* ↥F := π.subgroupComap F
  have hψ : Function.Surjective ψ := MonoidHom.subgroupComap_surjective π F hπ
  let α : ↥Fp ≃* ↥(Fp.map H.subtype) :=
    Subgroup.equivMapOfInjective Fp H.subtype H.subtype_injective
  have hcoe : ∀ k : ↥Fp, ((α k : ↥(Fp.map H.subtype)) : G) = ((k : ↥H) : G) := fun k =>
    Subgroup.coe_equivMapOfInjective_apply Fp H.subtype H.subtype_injective k
  let φ : ↥(Fp.map H.subtype) →* X := e.toMonoidHom.comp (ψ.comp α.symm.toMonoidHom)
  refine ⟨X, inferInstance, φ, e.surjective.comp (hψ.comp α.symm.surjective), fun k => ?_, hP⟩
  obtain ⟨k', rfl⟩ := α.surjective k
  change e (ψ (α.symm (α k'))) = 1 ↔ ((α k' : ↥(Fp.map H.subtype)) : G) ∈ (N : Set G)
  have h1 : ψ k' = 1 ↔ (k' : ↥H) ∈ Nc := by
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k' : ↥H)
  rw [MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff, hcoe k', SetLike.mem_coe, h1, hcore,
    Subgroup.mem_subgroupOf]

theorem hasQuotShape_of_quot (hRn : (R.subgroupOf H).Normal)
    {P : ∀ (X : Type) [Group X], Prop} (hP : P (↥H ⧸ (R.subgroupOf H).normalCore)) :
    HasQuotShape H (R : Set G) P := by
  refine ⟨_, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, fun k => ?_, hP⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.normalCore_eq_self,
    Subgroup.mem_subgroupOf, SetLike.mem_coe]

end CFSG.LocalAnalysis.WeakClosure81

end
