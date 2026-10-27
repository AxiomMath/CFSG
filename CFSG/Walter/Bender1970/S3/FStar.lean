module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17i
public import CFSG.Walter.Bender1970.S2.Subnormal

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

universe u

variable {G : Type u} [Group G]

theorem isSubnormal_subgroupOf_of_le {K Y A : Subgroup G} (hKY : K ≤ Y) (hYA : Y ≤ A)
    (hK : (K.subgroupOf A).IsSubnormal) : (K.subgroupOf Y).IsSubnormal := by
  have h1 := isSubnormal_subgroupOf_of_subnormal_of_le (Subgroup.subgroupOf_mono A hKY) hK
  let ψ : Y →* (Y.subgroupOf A) :=
    { toFun := fun y => ⟨⟨y, hYA y.2⟩, y.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
  convert h1.comap ψ using 1
  ext y
  exact Iff.rfl

theorem isSubnormal_subgroupOf_of_isNormalIn {A B : Subgroup G} (h : IsNormalIn A B) :
    (A.subgroupOf B).IsSubnormal :=
  isSubnormal_subgroupOf_of_le_normalizer h.1 (le_normalizer_of_isNormalIn h)

theorem isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting {S A : Subgroup G}
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hS : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal) :
    (S.subgroupOf A).IsSubnormal :=
  fstar_isSubnormal_subgroupOf_of_subnormal_subgroupOf_normal hSF hS
    (generalizedFittingSubgroupOf_le A) (generalizedFittingSubgroupOf_isNormalIn A)

variable [Finite G]

theorem fittingSubgroupOf_le_of_isSubnormal {A S : Subgroup G} (hSA : S ≤ A)
    (hS : (S.subgroupOf A).IsSubnormal) :
    CFSG.fittingSubgroupOf S ≤ CFSG.fittingSubgroupOf A := by
  classical
  rcases (Subgroup.IsSubnormal.isSubnormal_iff (G := ↥A) (H := S.subgroupOf A)).1 hS with
    ⟨n, f, hmono, hnorm, hf0, hfn⟩
  have hmain : ∀ i : ℕ, i ≤ n →
      CFSG.fittingSubgroupOf S ≤ CFSG.fittingSubgroupOf ((f i).map A.subtype) := by
    intro i hi
    induction i with
    | zero =>
      have hK0 : (f 0).map A.subtype = S := by
        rw [hf0]
        exact Subgroup.map_subgroupOf_eq_of_le hSA
      rw [hK0]
    | succ i ih =>
      set Ni : Subgroup G := (f i).map A.subtype
      set Nip : Subgroup G := (f (i + 1)).map A.subtype
      have hNiNip : IsNormalIn Ni Nip := by
        refine ⟨Subgroup.map_mono (f := A.subtype) (hmono (Nat.le_succ i)), ?_⟩
        intro a ha x hx
        rcases (Subgroup.mem_map).1 hx with ⟨x0, hx0, rfl⟩
        rcases (Subgroup.mem_map).1 ha with ⟨a0, ha0, rfl⟩
        have hconj : a0 * x0 * a0⁻¹ ∈ f i :=
          (Subgroup.normal_subgroupOf_iff (hmono (Nat.le_succ i))).mp (hnorm i)
            x0 a0 hx0 ha0
        exact Subgroup.mem_map.mpr ⟨a0 * x0 * a0⁻¹, hconj, by simp [mul_assoc]⟩
      have hFnorm : IsNormalIn (CFSG.fittingSubgroupOf Ni) Nip :=
        fstar_characteristic_subgroupOf_map_normal_in (F := Ni)
          (K := CFSG.fittingSubgroup ↥Ni) inferInstance hNiNip
      have hFleF' : CFSG.fittingSubgroupOf Ni ≤ CFSG.fittingSubgroupOf Nip :=
        le_fittingSubgroupOf_of_isNormalIn_nilpotent
          (fun x hx => hNiNip.1 (Subgroup.map_subtype_le _ hx)) hFnorm
          (CFSG.fittingSubgroupOf_isNilpotent Ni)
      exact (ih (Nat.le_of_succ_le hi)).trans hFleF'
  have htop : (f n).map A.subtype = A := by
    rw [hfn]
    ext x
    simp
  exact (hmain n le_rfl).trans (le_of_eq (by rw [htop]))

omit [Finite G] in
theorem fittingSubgroupOf_eq_self_of_isNilpotent {S : Subgroup G} (hS : Group.IsNilpotent S) :
    CFSG.fittingSubgroupOf S = S := by
  have h : CFSG.fittingSubgroup S = ⊤ := CFSG.fitting_eq_top_of_nilpotent S
  rw [CFSG.fittingSubgroupOf, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem le_fittingSubgroupOf_of_isSubnormal {A S : Subgroup G} (hSA : S ≤ A)
    (hS : (S.subgroupOf A).IsSubnormal) (hSn : Group.IsNilpotent S) :
    S ≤ CFSG.fittingSubgroupOf A := by
  calc S = CFSG.fittingSubgroupOf S := (fittingSubgroupOf_eq_self_of_isNilpotent hSn).symm
    _ ≤ CFSG.fittingSubgroupOf A := fittingSubgroupOf_le_of_isSubnormal hSA hS

omit [Finite G] in
theorem isComponentOf_of_isSubnormal {A S K : Subgroup G} (hSA : S ≤ A)
    (hS : (S.subgroupOf A).IsSubnormal) (hK : IsComponentOf K S) : IsComponentOf K A :=
  ⟨hK.1.trans hSA, isSubnormal_subgroupOf_trans hK.1 hK.2.1 hS, hK.2.2⟩

omit [Finite G] in
theorem componentLayerOf_le_of_isSubnormal {A S : Subgroup G} (hSA : S ≤ A)
    (hS : (S.subgroupOf A).IsSubnormal) : componentLayerOf S ≤ componentLayerOf A :=
  sSup_le fun _ hK => le_sSup (isComponentOf_of_isSubnormal hSA hS hK)

theorem generalizedFittingSubgroupOf_le_of_isSubnormal {A S : Subgroup G} (hSA : S ≤ A)
    (hS : (S.subgroupOf A).IsSubnormal) :
    generalizedFittingSubgroupOf S ≤ generalizedFittingSubgroupOf A :=
  sup_le_sup (fittingSubgroupOf_le_of_isSubnormal hSA hS)
    (componentLayerOf_le_of_isSubnormal hSA hS)

omit [Finite G] in
theorem isNilpotent_of_le {K F : Subgroup G} (hF : Group.IsNilpotent F) (hKF : K ≤ F) :
    Group.IsNilpotent K :=
  Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hKF).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hKF).surjective

theorem componentLayerOf_le_sup_centralizer {A V : Subgroup G} (hVA : V ≤ A)
    (hV : (V.subgroupOf A).IsSubnormal) :
    componentLayerOf A ≤ V ⊔ Subgroup.centralizer (V : Set G) := by
  refine sSup_le fun K hK => ?_
  rcases fstar_component_le_or_commutator_eq_bot_of_subnormal_subgroupOf hVA hV hK with h | h
  · exact h.trans le_sup_left
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans le_sup_right

omit [Finite G] in
theorem componentLayerOf_isNormalIn_generalizedFitting (A : Subgroup G) :
    IsNormalIn (componentLayerOf A) (generalizedFittingSubgroupOf A) :=
  ⟨le_sup_right, fun h hh k hk =>
    (componentLayerOf_isNormalIn A).2 h (generalizedFittingSubgroupOf_le A hh) k hk⟩

omit [Finite G] in
theorem fittingSubgroupOf_isNormalIn_generalizedFitting (A : Subgroup G) :
    IsNormalIn (CFSG.fittingSubgroupOf A) (generalizedFittingSubgroupOf A) :=
  ⟨le_sup_left, fun h hh k hk =>
    (fittingSubgroupOf_isNormalIn A).2 h (generalizedFittingSubgroupOf_le A hh) k hk⟩

theorem componentLayerOf_le_centralizer_fitting (A : Subgroup G) :
    componentLayerOf A ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf A : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (layer_centralizes_fitting A)

theorem fittingSubgroupOf_le_centralizer_layer (A : Subgroup G) :
    CFSG.fittingSubgroupOf A ≤ Subgroup.centralizer (componentLayerOf A : Set G) :=
  Subgroup.le_centralizer_iff.mp (componentLayerOf_le_centralizer_fitting A)

theorem center_componentLayerOf_le_fitting (A : Subgroup G) :
    (Subgroup.center (componentLayerOf A)).map (componentLayerOf A).subtype ≤
      CFSG.fittingSubgroupOf A := by
  have hZ : IsNormalIn ((Subgroup.center (componentLayerOf A)).map (componentLayerOf A).subtype)
      A :=
    map_characteristic_isNormalIn_of_isNormalIn _ inferInstance (componentLayerOf_isNormalIn A)
  refine le_fittingSubgroupOf_of_isNormalIn_nilpotent hZ.1 hZ ?_
  have : IsMulCommutative ((Subgroup.center (componentLayerOf A)).map
      (componentLayerOf A).subtype) :=
    Subgroup.map_isMulCommutative _ _
  exact CommGroup.isNilpotent

theorem generalizedFittingSubgroupOf_inf_centralizer_le (A : Subgroup G) :
    generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (componentLayerOf A : Set G) ≤
      CFSG.fittingSubgroupOf A := by
  rintro x ⟨hxF, hxC⟩
  obtain ⟨f, hf, e, he, rfl⟩ :=
    mem_sup_decompose_of_centralizes hxF (componentLayerOf_le_centralizer_fitting A)
  have hfC : f ∈ Subgroup.centralizer (componentLayerOf A : Set G) :=
    fittingSubgroupOf_le_centralizer_layer A hf
  have heC : e ∈ Subgroup.centralizer (componentLayerOf A : Set G) := by
    have : e = f⁻¹ * (f * e) := by group
    rw [this]
    exact mul_mem (inv_mem hfC) hxC
  have heZ : e ∈ (Subgroup.center (componentLayerOf A)).map (componentLayerOf A).subtype := by
    refine ⟨⟨e, he⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp heC) y y.2)
  exact mul_mem hf (center_componentLayerOf_le_fitting A heZ)

theorem eq_inf_fitting_sup_layer {A Y : Subgroup G} (hEY : componentLayerOf A ≤ Y)
    (hYF : Y ≤ generalizedFittingSubgroupOf A) :
    Y = (Y ⊓ CFSG.fittingSubgroupOf A) ⊔ componentLayerOf A := by
  refine le_antisymm (fun y hy => ?_) (sup_le inf_le_left hEY)
  obtain ⟨f, hf, e, he, rfl⟩ :=
    mem_sup_decompose_of_centralizes (hYF hy) (componentLayerOf_le_centralizer_fitting A)
  have hfY : f ∈ Y := by
    have : f = f * e * e⁻¹ := by group
    rw [this]
    exact mul_mem hy (inv_mem (hEY he))
  exact Subgroup.mul_mem_sup ⟨hfY, hf⟩ he

theorem isSubnormal_of_componentLayerOf_le {A Y : Subgroup G} (hEY : componentLayerOf A ≤ Y)
    (hYF : Y ≤ generalizedFittingSubgroupOf A) :
    (Y.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal := by
  set F := generalizedFittingSubgroupOf A
  have hXF : Y ⊓ CFSG.fittingSubgroupOf A ≤ F := inf_le_left.trans hYF
  have hEF : componentLayerOf A ≤ F := le_sup_right
  have hX : ((Y ⊓ CFSG.fittingSubgroupOf A).subgroupOf F).IsSubnormal :=
    isSubnormal_subgroupOf_trans inf_le_right
      (isSubnormal_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent A) _ inf_le_right)
      (isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn_generalizedFitting A))
  have hE : ((componentLayerOf A).subgroupOf F).IsSubnormal :=
    isSubnormal_subgroupOf_of_isNormalIn (componentLayerOf_isNormalIn_generalizedFitting A)
  rw [eq_inf_fitting_sup_layer hEY hYF, Subgroup.subgroupOf_sup hXF hEF]
  exact CFSG.GroupTheory.isSubnormal_sup hX hE

theorem generalizedFittingSubgroupOf_eq_self_of_componentLayerOf_le {A Y : Subgroup G}
    (hEY : componentLayerOf A ≤ Y) (hYF : Y ≤ generalizedFittingSubgroupOf A) :
    generalizedFittingSubgroupOf Y = Y := by
  refine le_antisymm (generalizedFittingSubgroupOf_le Y) ?_
  have hYA : Y ≤ A := hYF.trans (generalizedFittingSubgroupOf_le A)
  refine (eq_inf_fitting_sup_layer hEY hYF).le.trans (sup_le ?_ ?_)
  ·
    have hN : IsNormalIn (Y ⊓ CFSG.fittingSubgroupOf A) Y := by
      refine ⟨inf_le_left, fun h hh k hk => ?_⟩
      rw [Subgroup.mem_inf] at hk ⊢
      exact ⟨Y.mul_mem (Y.mul_mem hh hk.1) (Y.inv_mem hh),
        (fittingSubgroupOf_isNormalIn A).2 h (hYA hh) k hk.2⟩
    have hnil : Group.IsNilpotent (Y ⊓ CFSG.fittingSubgroupOf A : Subgroup G) :=
      isNilpotent_of_le (CFSG.fittingSubgroupOf_isNilpotent A) inf_le_right
    exact (le_fittingSubgroupOf_of_isNormalIn_nilpotent hN.1 hN hnil).trans le_sup_left
  ·
    refine (sSup_le fun K hK => le_sSup (s := {E : Subgroup G | IsComponentOf E Y}) ?_).trans
      le_sup_right
    have hKY : K ≤ Y := (le_sSup hK).trans hEY
    exact ⟨hKY, isSubnormal_subgroupOf_of_le hKY hYA hK.2.1, hK.2.2⟩

@[expose] def subnormalHull (A W : Subgroup G) : Subgroup G :=
  W ⊔ componentLayerOf A ⊔ (CFSG.fittingSubgroupOf A ⊓ Subgroup.centralizer (W : Set G))

omit [Finite G] in
theorem le_subnormalHull (A W : Subgroup G) : W ≤ subnormalHull A W :=
  le_sup_left.trans le_sup_left

omit [Finite G] in
theorem componentLayerOf_le_subnormalHull (A W : Subgroup G) :
    componentLayerOf A ≤ subnormalHull A W :=
  le_sup_right.trans le_sup_left

omit [Finite G] in
theorem subnormalHull_le_generalizedFitting {A W : Subgroup G}
    (hWF : W ≤ generalizedFittingSubgroupOf A) :
    subnormalHull A W ≤ generalizedFittingSubgroupOf A :=
  sup_le (sup_le hWF le_sup_right) (inf_le_left.trans le_sup_left)

theorem isSubnormal_subnormalHull {A W : Subgroup G} (hWF : W ≤ generalizedFittingSubgroupOf A)
    (hW : (W.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal) :
    ((subnormalHull A W).subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal := by
  set F := generalizedFittingSubgroupOf A
  have hEF : componentLayerOf A ≤ F := le_sup_right
  have hCF : CFSG.fittingSubgroupOf A ⊓ Subgroup.centralizer (W : Set G) ≤ F :=
    inf_le_left.trans le_sup_left
  have hE : ((componentLayerOf A).subgroupOf F).IsSubnormal :=
    isSubnormal_subgroupOf_of_isNormalIn (componentLayerOf_isNormalIn_generalizedFitting A)
  have hC :
      ((CFSG.fittingSubgroupOf A ⊓ Subgroup.centralizer (W : Set G)).subgroupOf F).IsSubnormal :=
    isSubnormal_subgroupOf_trans inf_le_left
      (isSubnormal_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent A) _ inf_le_left)
      (isSubnormal_subgroupOf_of_isNormalIn (fittingSubgroupOf_isNormalIn_generalizedFitting A))
  rw [subnormalHull, Subgroup.subgroupOf_sup (sup_le hWF hEF) hCF,
    Subgroup.subgroupOf_sup hWF hEF]
  exact CFSG.GroupTheory.isSubnormal_sup (CFSG.GroupTheory.isSubnormal_sup hW hE) hC

theorem generalizedFitting_inf_centralizer_subnormalHull_le (A W : Subgroup G) :
    generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (subnormalHull A W : Set G) ≤
      subnormalHull A W := by
  rintro x ⟨hxF, hxC⟩
  have hxE : x ∈ Subgroup.centralizer (componentLayerOf A : Set G) :=
    Subgroup.centralizer_le (componentLayerOf_le_subnormalHull A W) hxC
  have hxW : x ∈ Subgroup.centralizer (W : Set G) :=
    Subgroup.centralizer_le (le_subnormalHull A W) hxC
  exact (le_sup_right : _ ≤ subnormalHull A W)
    ⟨generalizedFittingSubgroupOf_inf_centralizer_le A ⟨hxF, hxE⟩, hxW⟩

theorem subnormalHull_le_sup_centralizer {A W : Subgroup G}
    (hWF : W ≤ generalizedFittingSubgroupOf A)
    (hW : (W.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal) :
    subnormalHull A W ≤ W ⊔ Subgroup.centralizer (W : Set G) :=
  sup_le (sup_le le_sup_left (componentLayerOf_le_sup_centralizer
    (hWF.trans (generalizedFittingSubgroupOf_le A))
    (isSubnormal_subgroupOf_of_isSubnormal_generalizedFitting hWF hW)))
    (inf_le_right.trans le_sup_right)

omit [Finite G] in
theorem sup_centralizer_le_normalizer (W : Subgroup G) :
    W ⊔ Subgroup.centralizer (W : Set G) ≤ Subgroup.normalizer (W : Set G) :=
  sup_le Subgroup.le_normalizer (Subgroup.centralizer_le_normalizer _)

theorem qCoreOf_inf_eq_bot_of_sup_centralizer_le (hsimple : IsSimpleGroup G) {A : Subgroup G}
    (hA : IsCoatom A) {V B : Subgroup G} (hVF : V ≤ generalizedFittingSubgroupOf A)
    (hV : (V.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hVB : V ⊔ Subgroup.centralizer (V : Set G) ≤ B) {q : ℕ} (hq : q.Prime)
    (hqA : q ∉ primesOfOrder (CFSG.fittingSubgroupOf A)) : qCoreOf B q ⊓ A = ⊥ :=
  bender1970_1_7_i_oddCoreDisjoint hsimple A hA (subnormalHull A V)
    (subnormalHull_le_generalizedFitting hVF) (isSubnormal_subnormalHull hVF hV)
    (generalizedFitting_inf_centralizer_subnormalHull_le A V)
    ((subnormalHull_le_sup_centralizer hVF hV).trans hVB) q hq hqA

end CFSG.Walter
