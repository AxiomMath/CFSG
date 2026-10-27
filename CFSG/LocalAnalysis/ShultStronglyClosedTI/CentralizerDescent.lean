module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerQuotient

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable {G : Type*} [Group G]

theorem localInvolutions_image (U : Subgroup G) (u : G) :
    (localCentralizer u).subtype '' localInvolutions U u =
      conjugateInvolutions U ∩ (localCentralizer u : Set G) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hxD, hxX⟩
    exact ⟨⟨x, hxX⟩, hxD, rfl⟩

theorem localHull_image (u z : G) :
    (localHull u z).map (localCentralizer u).subtype =
      Subgroup.closure (conjugatesOf z ∩ (localCentralizer u : Set G)) := by
  rw [localHull, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, a.property⟩
  · rintro ⟨hxz, hxX⟩
    exact ⟨⟨x, hxX⟩, hxz, rfl⟩

variable [Finite G]

theorem centralizer_hull_descent (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G))
    (Q : Sylow 2 (localCentralizer u)) (hWQ : localSubgroup U u ≤ (Q : Subgroup _)) :
    let X := localCentralizer u
    let W := localSubgroup U u
    let H := (Subgroup.normalizer (U : Set G)).subgroupOf X
    let Z := localCentralKernel u
    let π := QuotientGroup.mk' Z
    let V := W.map π
    let L := localHull u z
    W ≠ ⊥ ∧ IsElemAbelian 2 W ∧ fusionStronglyClosed (W : Set X) (Q : Subgroup X) ∧
      fusionIsTI W ∧ ¬ W.Normal ∧ Subgroup.normalizer (W : Set X) = H ∧ H ≠ ⊤ ∧
      u ∉ conjugateInvolutions U ∧ W ⊓ Z = ⊥ ∧
      localInvolutions U u = X.subtype ⁻¹' conjugatesOf z ∧
      (∃ hzX : z ∈ X, localInvolutions U u = conjugatesOf (⟨z, hzX⟩ : X)) ∧
      localInvolutions U u = conjugateInvolutions W ∧
      L = Subgroup.normalClosure (W : Set X) ∧ L.Normal ∧
      (∀ w ∈ W, w ≠ 1 → ∃ P : Sylow 2 X, ∃ hwP : w ∈ (P : Subgroup X),
        (⟨w, hwP⟩ : (P : Subgroup X)) ∈ Subgroup.center (P : Subgroup X)) ∧
      (localQuotientSylow u Q : Subgroup (X ⧸ Z)) = (Q : Subgroup X).map π ∧
      Nonempty (W ≃* V) ∧ V ≠ ⊥ ∧ IsElemAbelian 2 V ∧
      fusionStronglyClosed (V : Set (X ⧸ Z)) (localQuotientSylow u Q : Subgroup (X ⧸ Z)) ∧
      ¬ V.Normal ∧ fusionIsTI V ∧
      (Subgroup.normalizer (V : Set (X ⧸ Z))).comap π = H ∧
      (∀ w ∈ W, w ≠ 1 → (Subgroup.centralizer ({π w} : Set (X ⧸ Z))).comap π =
        Subgroup.centralizer ({w} : Set X)) ∧
      Nonempty (L ⧸ Z.subgroupOf L ≃* Subgroup.normalClosure (V : Set (X ⧸ Z))) := by
  dsimp only
  refine ⟨localSubgroup_ne_bot U hzU hzne hcomm, localSubgroup_elementary U hUel u,
    localSubgroup_stronglyClosed T U hclosed hTI hzU hzne hcomm Q hWQ,
    localSubgroup_TI U hTI u, localSubgroup_not_normal U hTI hzU hzne hcomm hX,
    local_normalizer_eq U hTI hzU hzne hcomm, ?_,
    local_central_involution_not_mem T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    localSubgroup_inf_kernel_eq_bot T U hUT hUel hclosed hTI hu hzU hzne hcomm hX,
    localInvolutions_eq_ambient_class_preimage T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    localInvolutions_eq_conjugacy_class T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    localInvolutions_eq_local_conjugateInvolutions T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    localHull_eq_normalClosure T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    localHull_normal T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    fun w hw hwne => localSubgroup_exists_central_sylow T U hUT hUel hclosed hTI
      hzU hzne hcomm hX hw hwne, localQuotientSylow_coe u Q,
    ⟨localQuotientSubgroupEquiv T U hUT hUel hclosed hTI hu hzU hzne hcomm hX⟩,
    localQuotient_subgroup_ne_bot T U hUT hUel hclosed hTI hu hzU hzne hcomm hX,
    localQuotient_elementary U hUel u,
    localQuotient_stronglyClosed T U hclosed hTI hu hzU hzne hcomm Q hWQ,
    localQuotient_subgroup_not_normal T U hUT hUel hclosed hTI hu hzU hzne hcomm hX,
    localQuotient_TI T U hUT hUel hclosed hTI hzU hzne hcomm hX,
    localQuotient_normalizer_preimage T U hUT hUel hclosed hTI hu hzU hzne hcomm hX,
    fun w hw hwne => localQuotient_centralizer_preimage T U hUT hUel hclosed hTI
      hzU hzne hcomm hX hw hwne,
    ⟨localQuotientHullEquiv T U hUT hUel hclosed hTI hzU hzne hcomm hX⟩⟩
  rw [← local_normalizer_eq U hTI hzU hzne hcomm]
  exact local_normalizer_ne_top U hTI hzU hzne hcomm hX

end CFSG.ShultStronglyClosedTI
