module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ConjugateGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.OrderReductions.InvolutionGraph

variable {G : Type*} [Group G]

abbrev localCentralizer (u : G) : Subgroup G := Subgroup.centralizer ({u} : Set G)

@[expose] def localSubgroup (U : Subgroup G) (u : G) : Subgroup (localCentralizer u) :=
  U.subgroupOf (localCentralizer u)

@[expose] def localInvolutions (U : Subgroup G) (u : G) : Set (localCentralizer u) :=
  (localCentralizer u).subtype ⁻¹' conjugateInvolutions U

theorem localSubgroup_image (U : Subgroup G) (u : G) :
    (localSubgroup U u).map (localCentralizer u).subtype = U ⊓ localCentralizer u :=
  Subgroup.subgroupOf_map_subtype U (localCentralizer u)

theorem localSubgroup_elementary (U : Subgroup G) (hUel : IsElemAbelian 2 U) (u : G) :
    IsElemAbelian 2 (localSubgroup U u) := by
  refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
  · intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : U => (c : G))
      (isMulCommutative_iff.mp hUel.1 (⟨a, a.property⟩ : U) (⟨b, b.property⟩ : U))
  · intro a ha
    apply Subtype.ext
    exact hUel.2 a ha

theorem localSubgroup_ne_bot (U : Subgroup G) {u z : G}
    (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u) : localSubgroup U u ≠ ⊥ := by
  intro hbot
  have hzX : z ∈ localCentralizer u := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have hzW : (⟨z, hzX⟩ : localCentralizer u) ∈ localSubgroup U u := hzU
  have hone := Subgroup.mem_bot.mp (hbot ▸ hzW)
  exact hzne (congrArg Subtype.val hone)

theorem local_normalizer_contains (U : Subgroup G) (u : G) :
    (Subgroup.normalizer (U : Set G)).subgroupOf (localCentralizer u) ≤
      Subgroup.normalizer (localSubgroup U u : Set (localCentralizer u)) := by
  intro x hx
  apply Subgroup.mem_normalizer_iff.mpr
  intro w
  change ((w : G) ∈ U ↔ (x : G) * (w : G) * (x : G)⁻¹ ∈ U)
  exact Subgroup.mem_normalizer_iff.mp hx w

theorem local_normalizer_eq (U : Subgroup G) (hTI : fusionIsTI U) {u z : G}
    (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u) :
    Subgroup.normalizer (localSubgroup U u : Set (localCentralizer u)) =
      (Subgroup.normalizer (U : Set G)).subgroupOf (localCentralizer u) := by
  apply le_antisymm ?_ (local_normalizer_contains U u)
  intro x hx
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hzX : z ∈ localCentralizer u := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  let zX : localCentralizer u := ⟨z, hzX⟩
  have hzW : zX ∈ localSubgroup U u := hzU
  have hxzW : (MulAut.conj x) zX ∈ localSubgroup U u :=
    (Subgroup.mem_normalizer_iff.mp hx zX).mp hzW
  have hxzU : (MulAut.conj (x : G)) z ∈ U := hxzW
  have hxzmap : (MulAut.conj (x : G)) z ∈ U.map (MulAut.conj (x : G)).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj (x : G)).toMonoidHom hzU
  have hone := Subgroup.mem_bot.mp ((hTI x hne) ▸
    (show (MulAut.conj (x : G)) z ∈ U ⊓ U.map (MulAut.conj (x : G)).toMonoidHom from
      ⟨hxzU, hxzmap⟩))
  exact hzne ((MulAut.conj (x : G)).injective (hone.trans (map_one _).symm))

theorem local_normalizer_ne_top (U : Subgroup G) (hTI : fusionIsTI U) {u z : G}
    (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    Subgroup.normalizer (localSubgroup U u : Set (localCentralizer u)) ≠ ⊤ := by
  rw [local_normalizer_eq U hTI hzU hzne hcomm]
  intro htop
  apply hX
  intro x hx
  exact (show (⟨x, hx⟩ : localCentralizer u) ∈
    (Subgroup.normalizer (U : Set G)).subgroupOf (localCentralizer u) from
      htop.symm ▸ Subgroup.mem_top _)

theorem localSubgroup_not_normal (U : Subgroup G) (hTI : fusionIsTI U) {u z : G}
    (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    ¬ (localSubgroup U u).Normal := by
  intro hn
  exact local_normalizer_ne_top U hTI hzU hzne hcomm hX
    (Subgroup.normalizer_eq_top_iff.mpr hn)

theorem localSubgroup_TI (U : Subgroup G) (hTI : fusionIsTI U) (u : G) :
    fusionIsTI (localSubgroup U u) := by
  intro x hne
  apply le_antisymm ?_ bot_le
  rintro w ⟨hwW, hwmap⟩
  apply Subgroup.mem_bot.mpr
  by_contra hwne
  have hwneG : (w : G) ≠ 1 := fun h => hwne (Subtype.ext h)
  obtain ⟨v, hvW, hvw⟩ := Subgroup.mem_map.mp hwmap
  have hwmapU : (w : G) ∈ U.map (MulAut.conj (x : G)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨v, hvW, ?_⟩
    exact congrArg Subtype.val hvw
  have hxU : (x : G) ∈ Subgroup.normalizer (U : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    by_contra hxne
    exact hwneG (Subgroup.mem_bot.mp ((hTI x hxne) ▸
      (show (w : G) ∈ U ⊓ U.map (MulAut.conj (x : G)).toMonoidHom from ⟨hwW, hwmapU⟩)))
  exact hne (Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (local_normalizer_contains U u hxU))

variable [Finite G]

theorem localSubgroup_stronglyClosed (T : Sylow 2 G) (U : Subgroup G)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (Q : Sylow 2 (localCentralizer u)) (hWQ : localSubgroup U u ≤ (Q : Subgroup _)) :
    fusionStronglyClosed (localSubgroup U u : Set (localCentralizer u)) (Q : Subgroup _) := by
  let X := localCentralizer u
  let P := (Q : Subgroup X).map X.subtype
  have hPtwo : IsPGroup 2 P := Q.isPGroup'.map X.subtype
  obtain ⟨R, hPR⟩ := hPtwo.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G R T
  have hRmap : (R : Subgroup G).map (MulAut.conj a).toMonoidHom = T := by
    change (a • R : Sylow 2 G).toSubgroup = T.toSubgroup
    rw [ha]
  have hPmapT : P.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) := by
    rw [← hRmap]
    exact Subgroup.map_mono hPR
  have hzX : z ∈ X := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have hzP : z ∈ P := Subgroup.mem_map_of_mem X.subtype
    (hWQ (show (⟨z, hzX⟩ : X) ∈ localSubgroup U u from hzU))
  have hazT : (MulAut.conj a) z ∈ (T : Subgroup G) :=
    hPmapT (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hzP)
  have hazU : (MulAut.conj a) z ∈ U := by
    change a * z * a⁻¹ ∈ (U : Set G)
    simpa only [inv_inv] using hclosed z hzU a⁻¹
      (by simpa only [inv_inv, MulAut.conj_apply] using hazT)
  have haU : a ∈ Subgroup.normalizer (U : Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    by_contra hne
    have hazmap := Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hzU
    have hone := Subgroup.mem_bot.mp ((hTI a hne) ▸
      (show (MulAut.conj a) z ∈ U ⊓ U.map (MulAut.conj a).toMonoidHom from ⟨hazU, hazmap⟩))
    exact hzne ((MulAut.conj a).injective (hone.trans (map_one _).symm))
  intro w hw x hwx
  let v : X := x⁻¹ * w * x
  have hvP : (v : G) ∈ P := Subgroup.mem_map_of_mem X.subtype hwx
  have havT : (MulAut.conj a) (v : G) ∈ (T : Subgroup G) :=
    hPmapT (Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom hvP)
  change a * ((x : G)⁻¹ * (w : G) * (x : G)) * a⁻¹ ∈ (T : Subgroup G) at havT
  have havU : (MulAut.conj a) (v : G) ∈ U := by
    have hmem : ((x : G) * a⁻¹)⁻¹ * (w : G) * ((x : G) * a⁻¹) ∈ (T : Subgroup G) := by
      simpa only [MulAut.conj_apply, mul_inv_rev, inv_inv, mul_assoc] using havT
    have h := hclosed w hw ((x : G) * a⁻¹) hmem
    change a * ((x : G)⁻¹ * (w : G) * (x : G)) * a⁻¹ ∈ (U : Set G)
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using h
  change (v : G) ∈ U
  exact (Subgroup.mem_normalizer_iff.mp haU (v : G)).mpr havU

omit [Finite G] in
theorem localInvolutions_order_two (U : Subgroup G) (hUel : IsElemAbelian 2 U) (u : G)
    {x : localCentralizer u} (hx : x ∈ localInvolutions U u) : orderOf x = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact conjugateInvolutions_order_two U hUel hx

omit [Finite G] in
theorem localInvolutions_conj_mem (U : Subgroup G) (u : G) {x : localCentralizer u}
    (hx : x ∈ localInvolutions U u) (g : localCentralizer u) :
    (MulAut.conj g) x ∈ localInvolutions U u :=
  conjugateInvolutions_conj_mem U hx (g : G)

theorem localInvolutions_mul_mem (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    (u : G) {x y : localCentralizer u} (hx : x ∈ localInvolutions U u)
    (hy : y ∈ localInvolutions U u) (hne : x ≠ y) (hcomm : Commute x y) :
    x * y ∈ localInvolutions U u :=
  conjugateInvolutions_mul_mem T U hUT hUel hclosed hTI hx hy
    (fun h => hne (Subtype.ext h)) (hcomm.map (localCentralizer u).subtype)

omit [Finite G] in
@[expose] def localGraphHom (U : Subgroup G) (hUel : IsElemAbelian 2 U) (u : G) :
    NormalGraph.graph (localInvolutions U u) (fun _ hx => localInvolutions_order_two U hUel u hx) →g
      conjugateCommutingGraph U hUel where
  toFun x := ⟨(x : localCentralizer u), x.property⟩
  map_rel' := by
    intro x y hadj
    refine ⟨?_, hadj.2.map (localCentralizer u).subtype⟩
    intro h
    apply hadj.1
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun v : Involution G => (v : G)) h

theorem localInvolutions_not_preconnected (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    ¬ (NormalGraph.graph (localInvolutions U u)
      (fun _ hx => localInvolutions_order_two U hUel u hx)).Preconnected := by
  intro hconnected
  obtain ⟨x, hxX, hxH⟩ := IsConcreteLE.not_le_iff_exists.mp hX
  have hzX : z ∈ localCentralizer u := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  let zX : localCentralizer u := ⟨z, hzX⟩
  have hzD : zX ∈ localInvolutions U u := by
    change z ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hzU, by simpa only [Set.mem_singleton_iff] using hzne⟩
  let xX : localCentralizer u := ⟨x, hxX⟩
  let zx := (MulAut.conj xX) zX
  have hzxD : zx ∈ localInvolutions U u := localInvolutions_conj_mem U u hzD xX
  have hreach := (hconnected (⟨zX, hzD⟩ : localInvolutions U u) ⟨zx, hzxD⟩).map
    (localGraphHom U hUel u)
  obtain ⟨a, hza, hzxa⟩ :=
    (conjugateCommutingGraph_reachable_iff T U hUT hUel hclosed hTI _ _).mp hreach
  have haU : U.map (MulAut.conj a).toMonoidHom = U := by
    have hz1 : z ∈ U.map (MulAut.conj (1 : G)).toMonoidHom := (map_conj_one U).symm ▸ hzU
    simpa only [map_conj_one] using
      conjugates_eq_of_common_nonidentity U hTI a 1 hzne hza hz1
  have hzxne : ((MulAut.conj x) z) ≠ 1 :=
    fun h => hzne ((MulAut.conj x).injective (h.trans (map_one _).symm))
  have hzxmap : (MulAut.conj x) z ∈ U.map (MulAut.conj x).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj x).toMonoidHom hzU
  have hxU : U.map (MulAut.conj x).toMonoidHom = U :=
    (conjugates_eq_of_common_nonidentity U hTI x a hzxne hzxmap hzxa).trans haU
  exact hxH (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hxU)

theorem localInvolutions_eq_conjugacy_class (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    ∃ hzX : z ∈ localCentralizer u,
      localInvolutions U u = conjugatesOf (⟨z, hzX⟩ : localCentralizer u) := by
  have hzX : z ∈ localCentralizer u := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have hzD : (⟨z, hzX⟩ : localCentralizer u) ∈ localInvolutions U u := by
    change z ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hzU, by simpa only [Set.mem_singleton_iff] using hzne⟩
  exact ⟨hzX, NormalGraph.eq_conjugacy_class (localInvolutions U u)
    (fun _ hx => localInvolutions_order_two U hUel u hx)
    (fun _ hx g => localInvolutions_conj_mem U u hx g)
    (fun _ hx _ hy hne hc => localInvolutions_mul_mem T U hUT hUel hclosed hTI u hx hy hne hc)
    (localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX) ⟨_, hzD⟩⟩

theorem localInvolutions_eq_local_conjugateInvolutions (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    localInvolutions U u = conjugateInvolutions (localSubgroup U u) := by
  obtain ⟨hzX, heq⟩ := localInvolutions_eq_conjugacy_class T U hUT hUel hclosed hTI
    hzU hzne hcomm hX
  ext x
  constructor
  · intro hx
    have hxconj := heq ▸ hx
    exact Group.mem_conjugatesOfSet_iff.mpr
      ⟨⟨z, hzX⟩, ⟨hzU, by
        intro hone
        exact hzne (congrArg Subtype.val (Set.mem_singleton_iff.mp hone))⟩, hxconj⟩
  · intro hx
    obtain ⟨w, ⟨hw, hwne⟩, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
    have hwD : w ∈ localInvolutions U u := Group.subset_conjugatesOfSet
      ⟨hw, by
        intro hone
        apply hwne
        apply Set.mem_singleton_iff.mpr
        exact Subtype.ext (Set.mem_singleton_iff.mp hone)⟩
    exact localInvolutions_conj_mem U u hwD g

theorem localInvolutions_eq_ambient_class_preimage (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    localInvolutions U u = (localCentralizer u).subtype ⁻¹' conjugatesOf z := by
  obtain ⟨hzX, heq⟩ := localInvolutions_eq_conjugacy_class T U hUT hUel hclosed hTI
    hzU hzne hcomm hX
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp (heq ▸ hx)
    exact isConj_iff.mpr ⟨(g : G), congrArg Subtype.val hg⟩
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    change g * z * g⁻¹ = (x : G) at hg
    have hzD : z ∈ conjugateInvolutions U := Group.subset_conjugatesOfSet
      ⟨hzU, by simpa only [Set.mem_singleton_iff] using hzne⟩
    change (x : G) ∈ conjugateInvolutions U
    rw [← hg]
    exact conjugateInvolutions_conj_mem U hzD g

theorem localSubgroup_exists_central_sylow (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G))
    {w : localCentralizer u} (hw : w ∈ localSubgroup U u) (hwne : w ≠ 1) :
    ∃ Q : Sylow 2 (localCentralizer u), ∃ hwQ : w ∈ (Q : Subgroup _),
      (⟨w, hwQ⟩ : (Q : Subgroup _)) ∈ Subgroup.center (Q : Subgroup _) := by
  have hwD : w ∈ localInvolutions U u := Group.subset_conjugatesOfSet
    ⟨hw, by
      intro hone
      exact hwne (Subtype.ext (Set.mem_singleton_iff.mp hone))⟩
  exact NormalGraph.exists_central_sylow (localInvolutions U u)
    (fun _ hx => localInvolutions_order_two U hUel u hx)
    (fun _ hx g => localInvolutions_conj_mem U u hx g)
    (fun _ hx _ hy hne hc => localInvolutions_mul_mem T U hUT hUel hclosed hTI u hx hy hne hc)
    (localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX) ⟨w, hwD⟩

omit [Finite G] in
theorem closure_conjugateInvolutions_eq_normalClosure (U : Subgroup G) :
    Subgroup.closure (conjugateInvolutions U) = Subgroup.normalClosure (U : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact (Group.conjugatesOfSet_mono (Set.sdiff_subset)).trans
      Subgroup.conjugatesOfSet_subset_normalClosure
  · rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨w, hw, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    by_cases hwone : w = 1
    · obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
      simp only [hwone, mul_one, mul_inv_cancel]
      exact (Subgroup.closure (conjugateInvolutions U)).one_mem
    · exact Subgroup.subset_closure (Group.mem_conjugatesOfSet_iff.mpr
        ⟨w, ⟨hw, by simpa only [Set.mem_singleton_iff] using hwone⟩, hconj⟩)

omit [Finite G] in
@[expose] def localHull (u z : G) : Subgroup (localCentralizer u) :=
  Subgroup.closure ((localCentralizer u).subtype ⁻¹' conjugatesOf z)

theorem localHull_eq_normalClosure (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    localHull u z = Subgroup.normalClosure (localSubgroup U u : Set (localCentralizer u)) := by
  rw [localHull, ← localInvolutions_eq_ambient_class_preimage T U hUT hUel hclosed hTI
    hzU hzne hcomm hX,
    localInvolutions_eq_local_conjugateInvolutions T U hUT hUel hclosed hTI hzU hzne hcomm hX]
  exact closure_conjugateInvolutions_eq_normalClosure _

theorem localHull_normal (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    (localHull u z).Normal := by
  rw [localHull_eq_normalClosure T U hUT hUel hclosed hTI hzU hzne hcomm hX]
  infer_instance

theorem local_componentSet_eq (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    (u : G) (z : localInvolutions U u) (hzW : (z : localCentralizer u) ∈ localSubgroup U u) :
    NormalGraph.componentSet (localInvolutions U u)
      (fun _ hx => localInvolutions_order_two U hUel u hx) z =
        (localSubgroup U u : Set (localCentralizer u)) \ {1} := by
  have hzGne : ((z : localCentralizer u) : G) ≠ 1 :=
    ((mem_conjugateInvolutions_iff U).mp z.property).choose_spec.2
  ext x
  constructor
  · rintro ⟨hxD, hzx⟩
    have hreach := hzx.map (localGraphHom U hUel u)
    obtain ⟨a, hza, hxa⟩ :=
      (conjugateCommutingGraph_reachable_iff T U hUT hUel hclosed hTI _ _).mp hreach
    have hz1 : ((z : localCentralizer u) : G) ∈ U.map (MulAut.conj (1 : G)).toMonoidHom :=
      (map_conj_one U).symm ▸ hzW
    have haU : U.map (MulAut.conj a).toMonoidHom = U := by
      simpa only [map_conj_one] using
        conjugates_eq_of_common_nonidentity U hTI a 1 hzGne hza hz1
    have hxW : x ∈ localSubgroup U u := haU ▸ hxa
    have hxneG := ((mem_conjugateInvolutions_iff U).mp hxD).choose_spec.2
    exact ⟨hxW, fun h => hxneG (congrArg Subtype.val (Set.mem_singleton_iff.mp h))⟩
  · rintro ⟨hxW, hxne⟩
    have hxD : x ∈ localInvolutions U u := Group.subset_conjugatesOfSet
      ⟨hxW, by
        intro hone
        apply hxne
        exact Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hone))⟩
    refine ⟨hxD, NormalGraph.reachable_of_commute _ _ z ⟨x, hxD⟩ ?_⟩
    exact congrArg (fun w : localSubgroup U u => (w : localCentralizer u))
      (isMulCommutative_iff.mp (localSubgroup_elementary U hUel u).1 ⟨z, hzW⟩ ⟨x, hxW⟩)

end CFSG.ShultStronglyClosedTI
