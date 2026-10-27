module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralizerGeometry
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.QuotientGraph

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open
open CFSG.OrderReductions.InvolutionGraph

variable {G : Type*} [Group G]

@[expose] def localCentralElement (u : G) : localCentralizer u :=
  ⟨u, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem localCentralElement_mem_center (u : G) :
    localCentralElement u ∈ Subgroup.center (localCentralizer u) := by
  apply Subgroup.mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp x.property

@[expose] def localCentralKernel (u : G) : Subgroup (localCentralizer u) :=
  Subgroup.zpowers (localCentralElement u)

theorem localCentralKernel_le_center (u : G) :
    localCentralKernel u ≤ Subgroup.center (localCentralizer u) :=
  Subgroup.zpowers_le.mpr (localCentralElement_mem_center u)

instance localCentralKernel_normal (u : G) : (localCentralKernel u).Normal :=
  Subgroup.normal_of_le_center (localCentralKernel_le_center u)

theorem normalizer_nonidentity (U : Subgroup G) :
    Subgroup.normalizer ((U : Set G) \ {1}) = Subgroup.normalizer (U : Set G) := by
  ext g
  rw [Subgroup.mem_set_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hxone : x = 1
    · simp only [hxone, mul_one, mul_inv_cancel]
    · have hconjne : g * x * g⁻¹ ≠ 1 :=
        fun heq => hxone ((MulAut.conj g).injective (heq.trans (map_one _).symm))
      change (x ∈ (U : Set G) ↔ g * x * g⁻¹ ∈ (U : Set G))
      simpa only [Set.mem_sdiff, Set.mem_singleton_iff, hxone, hconjne, not_false_eq_true,
        and_true] using h x
  · intro h x
    have hne : x ≠ 1 ↔ g * x * g⁻¹ ≠ 1 := by
      constructor
      · intro hx heq
        exact hx ((MulAut.conj g).injective (heq.trans (map_one _).symm))
      · intro hx heq
        exact hx (by simp only [heq, mul_one, mul_inv_cancel])
    exact and_congr (h x) hne

theorem quotient_injective_on_subgroup (U Z : Subgroup G) [Z.Normal]
    (hinj : Set.InjOn (QuotientGroup.mk' Z) ((U : Set G) \ {1}))
    (hdisjoint : U ⊓ Z = ⊥) : Set.InjOn (QuotientGroup.mk' Z) (U : Set G) := by
  intro x hx y hy heq
  by_cases hxone : x = 1
  · subst x
    have hyZ : y ∈ Z := (QuotientGroup.eq_one_iff y).mp
      ((map_one (QuotientGroup.mk' Z)).symm.trans heq).symm
    exact (Subgroup.mem_bot.mp (hdisjoint ▸ (show y ∈ U ⊓ Z from ⟨hy, hyZ⟩))).symm
  · by_cases hyone : y = 1
    · subst y
      have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp
        (heq.trans (map_one (QuotientGroup.mk' Z)))
      exact Subgroup.mem_bot.mp (hdisjoint ▸ (show x ∈ U ⊓ Z from ⟨hx, hxZ⟩))
    · exact hinj ⟨hx, by simpa only [Set.mem_singleton_iff] using hxone⟩
        ⟨hy, by simpa only [Set.mem_singleton_iff] using hyone⟩ heq

def quotientSubgroupEquiv (U Z : Subgroup G) [Z.Normal]
    (hinj : Set.InjOn (QuotientGroup.mk' Z) (U : Set G)) :
    U ≃* U.map (QuotientGroup.mk' Z) := by
  let f := (QuotientGroup.mk' Z).subgroupMap U
  apply MulEquiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val h))
  · rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨x, hx⟩, rfl⟩

theorem quotient_nonidentity_image (U Z : Subgroup G) [Z.Normal]
    (hdisjoint : U ⊓ Z = ⊥) :
    (QuotientGroup.mk' Z) '' ((U : Set G) \ {1}) =
      (U.map (QuotientGroup.mk' Z) : Set (G ⧸ Z)) \ {1} := by
  ext q
  constructor
  · rintro ⟨x, ⟨hx, hxne⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hx, ?_⟩
    intro hone
    have hxZ : x ∈ Z := (QuotientGroup.eq_one_iff x).mp (Set.mem_singleton_iff.mp hone)
    exact hxne (Set.mem_singleton_iff.mpr
      (Subgroup.mem_bot.mp (hdisjoint ▸ (show x ∈ U ⊓ Z from ⟨hx, hxZ⟩))))
  · rintro ⟨hq, hqne⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hq
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro hxone
    apply hqne
    apply Set.mem_singleton_iff.mpr
    have hone := Set.mem_singleton_iff.mp hxone
    simp only [hone, map_one]

variable [Finite G]

theorem local_central_involution_not_mem (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    u ∉ conjugateInvolutions U := by
  intro huD
  exact NormalGraph.no_central_vertex (localInvolutions U u)
    (fun _ hx => localInvolutions_order_two U hUel u hx)
    (localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX)
    (show localCentralElement u ∈ localInvolutions U u from huD)
    (localCentralElement_mem_center u)

theorem localSubgroup_inf_kernel_eq_bot (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    localSubgroup U u ⊓ localCentralKernel u = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxW, hxZ⟩
  by_contra hxne
  have hucard : Nat.card (localCentralKernel u) = 2 := by
    rw [localCentralKernel, Nat.card_zpowers, Subgroup.orderOf_mk]
    change orderOf u = 2
    exact hu
  have hune : localCentralElement u ≠ 1 := by
    intro hone
    have huone : u = 1 := congrArg Subtype.val hone
    rw [huone, orderOf_one] at hu
    omega
  have hxu : x = localCentralElement u := by
    obtain ⟨a, _, ha⟩ := (Nat.card_eq_two_iff' (1 : localCentralKernel u)).mp hucard
    have hx' : (⟨x, hxZ⟩ : localCentralKernel u) ≠ 1 :=
      fun h => hxne (congrArg Subtype.val h)
    have hu' : (⟨localCentralElement u, Subgroup.mem_zpowers _⟩ : localCentralKernel u) ≠ 1 :=
      fun h => hune (congrArg Subtype.val h)
    exact congrArg Subtype.val ((ha _ hx').trans (ha _ hu').symm)
  have huU : u ∈ U := by
    rw [hxu] at hxW
    exact hxW
  exact local_central_involution_not_mem T U hUT hUel hclosed hTI hzU hzne hcomm hX
    (Group.subset_conjugatesOfSet ⟨huU, by
      intro hone
      exact hune (Subtype.ext (Set.mem_singleton_iff.mp hone))⟩)

omit [Finite G] in
theorem localCentralKernel_le_sylow {u : G} (hu : orderOf u = 2)
    (Q : Sylow 2 (localCentralizer u)) : localCentralKernel u ≤ (Q : Subgroup _) := by
  have htwo : IsPGroup 2 (localCentralKernel u) := IsPGroup.of_card (n := 1) (by
    rw [localCentralKernel, Nat.card_zpowers, Subgroup.orderOf_mk]
    change orderOf u = 2 ^ 1
    rw [hu, pow_one])
  exact htwo.le_sylow_of_normal Q

omit [Finite G] in
theorem local_quotient_sylow_preimage {u : G} (hu : orderOf u = 2)
    (Q : Sylow 2 (localCentralizer u)) :
    ((Q : Subgroup _).map (QuotientGroup.mk' (localCentralKernel u))).comap
      (QuotientGroup.mk' (localCentralKernel u)) = (Q : Subgroup _) := by
  rw [QuotientGroup.comap_map_mk', sup_eq_right.mpr (localCentralKernel_le_sylow hu Q)]

@[expose] def localQuotientSylow (u : G) (Q : Sylow 2 (localCentralizer u)) :
    Sylow 2 ((localCentralizer u) ⧸ localCentralKernel u) :=
  Q.mapSurjective (QuotientGroup.mk'_surjective (localCentralKernel u))

theorem localQuotientSylow_coe (u : G) (Q : Sylow 2 (localCentralizer u)) :
    (localQuotientSylow u Q : Subgroup ((localCentralizer u) ⧸ localCentralKernel u)) =
      (Q : Subgroup (localCentralizer u)).map (QuotientGroup.mk' (localCentralKernel u)) := rfl

theorem localQuotient_stronglyClosed (T : Sylow 2 G) (U : Subgroup G)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (Q : Sylow 2 (localCentralizer u)) (hWQ : localSubgroup U u ≤ (Q : Subgroup _)) :
    fusionStronglyClosed
      ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u)) :
        Set ((localCentralizer u) ⧸ localCentralKernel u))
      (localQuotientSylow u Q : Subgroup ((localCentralizer u) ⧸ localCentralKernel u)) := by
  let π := QuotientGroup.mk' (localCentralKernel u)
  have hlocal := localSubgroup_stronglyClosed T U hclosed hTI hzU hzne hcomm Q hWQ
  intro w hw x hwx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (localCentralKernel u) x
  have hpre : a⁻¹ * v * a ∈ (Q : Subgroup _) := by
    have hq : π (a⁻¹ * v * a) ∈ (Q : Subgroup _).map π := by
      change (π a)⁻¹ * π v * π a ∈ (Q : Subgroup _).map π at hwx
      simpa only [map_mul, map_inv] using hwx
    have hmem : a⁻¹ * v * a ∈ ((Q : Subgroup _).map π).comap π := hq
    rwa [local_quotient_sylow_preimage hu Q] at hmem
  have hW : a⁻¹ * v * a ∈ localSubgroup U u := hlocal v hv a hpre
  have hmem := Subgroup.mem_map_of_mem π hW
  change (π a)⁻¹ * π v * π a ∈ (localSubgroup U u).map π
  simpa only [map_mul, map_inv] using hmem

theorem localQuotient_injective_on_subgroup (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    Set.InjOn (QuotientGroup.mk' (localCentralKernel u)) (localSubgroup U u : Set _) := by
  apply quotient_injective_on_subgroup _ _ ?_
    (localSubgroup_inf_kernel_eq_bot T U hUT hUel hclosed hTI hu hzU hzne hcomm hX)
  have hinj := NormalGraph.quotient_injective_on_vertices (localInvolutions U u)
    (fun _ hx => localInvolutions_order_two U hUel u hx)
    (fun _ hx _ hy hne hc => localInvolutions_mul_mem T U hUT hUel hclosed hTI u hx hy hne hc)
    (localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX)
    (localCentralKernel u) (localCentralKernel_le_center u)
  intro x hx y hy hxy
  have hxD : x ∈ localInvolutions U u := by
    change (x : G) ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hx.1, fun hone => hx.2
      (Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hone)))⟩
  have hyD : y ∈ localInvolutions U u := by
    change (y : G) ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hy.1, fun hone => hy.2
      (Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp hone)))⟩
  exact hinj hxD hyD hxy

def localQuotientSubgroupEquiv (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    localSubgroup U u ≃* (localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u)) :=
  quotientSubgroupEquiv _ _
    (localQuotient_injective_on_subgroup T U hUT hUel hclosed hTI hu hzU hzne hcomm hX)

theorem localQuotient_normalizer_preimage (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    (Subgroup.normalizer
      ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u)) : Set _)).comap
      (QuotientGroup.mk' (localCentralKernel u)) =
        (Subgroup.normalizer (U : Set G)).subgroupOf (localCentralizer u) := by
  let D := localInvolutions U u
  let horder : ∀ x ∈ D, orderOf x = 2 := fun _ hx => localInvolutions_order_two U hUel u hx
  let hconj : ∀ x ∈ D, ∀ g : localCentralizer u, (MulAut.conj g) x ∈ D :=
    fun _ hx g => localInvolutions_conj_mem U u hx g
  let hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D :=
    fun _ hx _ hy hne hc => localInvolutions_mul_mem T U hUT hUel hclosed hTI u hx hy hne hc
  have hdis := localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX
  have hzX : z ∈ localCentralizer u := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have hzD : (⟨z, hzX⟩ : localCentralizer u) ∈ D := by
    change z ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hzU, by simpa only [Set.mem_singleton_iff] using hzne⟩
  let zD : D := ⟨⟨z, hzX⟩, hzD⟩
  let Z := localCentralKernel u
  let π := QuotientGroup.mk' Z
  have hcomp := local_componentSet_eq T U hUT hUel hclosed hTI u zD hzU
  have himage := NormalGraph.quotient_component_image D horder hconj hproduct hdis Z
    (localCentralKernel_le_center u) zD
  have hWZ := localSubgroup_inf_kernel_eq_bot T U hUT hUel hclosed hTI hu hzU hzne hcomm hX
  have hqcomp := himage.symm
  rw [hcomp, quotient_nonidentity_image _ _ hWZ] at hqcomp
  have hpre := NormalGraph.quotient_component_normalizer_preimage D horder hconj hproduct
    hdis Z (localCentralKernel_le_center u) zD
  rw [hqcomp, hcomp, normalizer_nonidentity, normalizer_nonidentity,
    local_normalizer_eq U hTI hzU hzne hcomm] at hpre
  exact hpre

theorem localQuotient_subgroup_not_normal (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    ¬ ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u))).Normal := by
  intro hn
  have hpre := localQuotient_normalizer_preimage T U hUT hUel hclosed hTI
    hu hzU hzne hcomm hX
  rw [Subgroup.normalizer_eq_top_iff.mpr hn, Subgroup.comap_top] at hpre
  apply local_normalizer_ne_top U hTI hzU hzne hcomm hX
  rw [local_normalizer_eq U hTI hzU hzne hcomm]
  exact hpre.symm

theorem localQuotient_centralizer_preimage (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G))
    {w : localCentralizer u} (hw : w ∈ localSubgroup U u) (hwne : w ≠ 1) :
    (Subgroup.centralizer ({(QuotientGroup.mk' (localCentralKernel u)) w} : Set _)).comap
      (QuotientGroup.mk' (localCentralKernel u)) = Subgroup.centralizer ({w} : Set _) := by
  have hwD : w ∈ localInvolutions U u := by
    change (w : G) ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hw, fun hone => hwne
      (Subtype.ext (Set.mem_singleton_iff.mp hone))⟩
  exact NormalGraph.quotient_centralizer_preimage (localInvolutions U u)
    (fun _ hx => localInvolutions_order_two U hUel u hx)
    (fun _ hx g => localInvolutions_conj_mem U u hx g)
    (fun _ hx _ hy hne hc => localInvolutions_mul_mem T U hUT hUel hclosed hTI u hx hy hne hc)
    (localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX)
    (localCentralKernel u) (localCentralKernel_le_center u) hwD

omit [Finite G] in
theorem map_conj_natural {K : Type*} [Group K] (U : Subgroup G) (f : G →* K) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map f =
      (U.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

theorem localQuotient_TI (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    fusionIsTI ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u))) := by
  let W := localSubgroup U u
  let Z := localCentralKernel u
  let π := QuotientGroup.mk' Z
  have hinj := NormalGraph.quotient_injective_on_vertices (localInvolutions U u)
    (fun _ hx => localInvolutions_order_two U hUel u hx)
    (fun _ hx _ hy hne hc => localInvolutions_mul_mem T U hUT hUel hclosed hTI u hx hy hne hc)
    (localInvolutions_not_preconnected T U hUT hUel hclosed hTI hzU hzne hcomm hX)
    Z (localCentralKernel_le_center u)
  intro y hne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z y
  have hWconj : W.map (MulAut.conj a).toMonoidHom ≠ W := by
    intro heq
    apply hne
    rw [← map_conj_natural W π a, heq]
  apply le_antisymm ?_ bot_le
  rintro q ⟨hqW, hqconj⟩
  apply Subgroup.mem_bot.mpr
  by_contra hqne
  obtain ⟨w, hwW, hwq⟩ := Subgroup.mem_map.mp hqW
  obtain ⟨v, hvW, hvq⟩ := Subgroup.mem_map.mp hqconj
  obtain ⟨v0, hv0W, hv0v⟩ := Subgroup.mem_map.mp hvW
  change π v0 = v at hv0v
  have hwne : w ≠ 1 := by
    intro hone
    exact hqne (hwq.symm.trans (by simp only [hone, map_one]))
  have hv0ne : v0 ≠ 1 := by
    intro hone
    have hvone : v = 1 := hv0v.symm.trans (by simp only [hone, map_one])
    exact hqne (hvq.symm.trans (by simp only [hvone, map_one]))
  have hwD : w ∈ localInvolutions U u := by
    change (w : G) ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hwW, fun hone => hwne
      (Subtype.ext (Set.mem_singleton_iff.mp hone))⟩
  have hv0D : v0 ∈ localInvolutions U u := by
    change (v0 : G) ∈ conjugateInvolutions U
    exact Group.subset_conjugatesOfSet ⟨hv0W, fun hone => hv0ne
      (Subtype.ext (Set.mem_singleton_iff.mp hone))⟩
  have heq : π w = π ((MulAut.conj a) v0) := by
    calc
      π w = q := hwq
      _ = (MulAut.conj (π a)) v := hvq.symm
      _ = π ((MulAut.conj a) v0) := by
        rw [← hv0v]
        simp only [MulAut.conj_apply, map_mul, map_inv]
  have hactual : w = (MulAut.conj a) v0 :=
    hinj hwD (localInvolutions_conj_mem U u hv0D a) heq
  have hwconj : w ∈ W.map (MulAut.conj a).toMonoidHom := by
    rw [hactual]
    exact Subgroup.mem_map_of_mem _ hv0W
  exact hwne (Subgroup.mem_bot.mp ((localSubgroup_TI U hTI u a hWconj) ▸
    (show w ∈ W ⊓ W.map (MulAut.conj a).toMonoidHom from ⟨hwW, hwconj⟩)))

omit [Finite G] in
theorem localQuotient_elementary (U : Subgroup G) (hUel : IsElemAbelian 2 U) (u : G) :
    IsElemAbelian 2 ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u))) :=
  CFSG.TwoRankLowerBound.Helpers.isElemAbelian_map _ (localSubgroup_elementary U hUel u) _

theorem localQuotient_subgroup_ne_bot (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hu : orderOf u = 2) (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    (localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u)) ≠ ⊥ := by
  intro hbot
  have hinj := localQuotient_injective_on_subgroup T U hUT hUel hclosed hTI
    hu hzU hzne hcomm hX
  have hzX : z ∈ localCentralizer u := Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  let zX : localCentralizer u := ⟨z, hzX⟩
  have hzW : zX ∈ localSubgroup U u := hzU
  have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' (localCentralKernel u)) hzW
  have hone := Subgroup.mem_bot.mp (hbot ▸ hmem)
  have hz1 : zX = 1 := hinj hzW (localSubgroup U u).one_mem
    (hone.trans (map_one _).symm)
  exact hzne (congrArg Subtype.val hz1)

theorem localQuotient_hull_image (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    (localHull u z).map (QuotientGroup.mk' (localCentralKernel u)) =
      Subgroup.normalClosure
        ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u)) : Set _) := by
  rw [localHull_eq_normalClosure T U hUT hUel hclosed hTI hzU hzne hcomm hX]
  exact Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)

def localQuotientHullEquiv (T : Sylow 2 G) (U : Subgroup G)
    (hUT : U ≤ (T : Subgroup G)) (hUel : IsElemAbelian 2 U)
    (hclosed : fusionStronglyClosed (U : Set G) (T : Subgroup G)) (hTI : fusionIsTI U)
    {u z : G} (hzU : z ∈ U) (hzne : z ≠ 1) (hcomm : Commute z u)
    (hX : ¬ localCentralizer u ≤ Subgroup.normalizer (U : Set G)) :
    (localHull u z) ⧸ (localCentralKernel u).subgroupOf (localHull u z) ≃*
      Subgroup.normalClosure
        ((localSubgroup U u).map (QuotientGroup.mk' (localCentralKernel u)) :
          Set ((localCentralizer u) ⧸ localCentralKernel u)) :=
  (NormalGraph.subgroupQuotientEquiv _ _).trans
    (MulEquiv.subgroupCongr
      (localQuotient_hull_image T U hUT hUel hclosed hTI hzU hzne hcomm hX))

theorem localQuotient_card_lt {u : G} (hu : orderOf u = 2) :
    Nat.card ((localCentralizer u) ⧸ localCentralKernel u) < Nat.card (localCentralizer u) := by
  have hcard : Nat.card (localCentralKernel u) = 2 := by
    rw [localCentralKernel, Nat.card_zpowers, Subgroup.orderOf_mk]
    change orderOf u = 2
    exact hu
  have horder := Subgroup.card_eq_card_quotient_mul_card_subgroup (localCentralKernel u)
  rw [hcard] at horder
  have hpos : 0 < Nat.card ((localCentralizer u) ⧸ localCentralKernel u) := Nat.card_pos
  omega

omit [Finite G] in
theorem localCentralizer_ne_top_of_not_central {u : G} (hu : u ∉ Subgroup.center G) :
    localCentralizer u ≠ ⊤ := by
  intro htop
  apply hu
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hx : x ∈ localCentralizer u := htop.symm ▸ Subgroup.mem_top x
  exact Subgroup.mem_centralizer_singleton_iff.mp hx

theorem local_descent_card_lt [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u : G} (hu : orderOf u = 2) :
    localCentralizer u ≠ ⊤ ∧
      Nat.card ((localCentralizer u) ⧸ localCentralKernel u) < Nat.card (localCentralizer u) ∧
      Nat.card (localCentralizer u) < Nat.card G := by
  have hune : u ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at hu
    omega
  have hnotcentral : u ∉ Subgroup.center G := by
    intro hcentral
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hbot | htop
    · exact hune (Subgroup.mem_bot.mp (hbot ▸ hcentral))
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (Subgroup.mem_center_iff.mp (htop.symm ▸ Subgroup.mem_top b) a)
  have hproper := localCentralizer_ne_top_of_not_central hnotcentral
  refine ⟨hproper, localQuotient_card_lt hu, ?_⟩
  have hlt := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hproper)
  simpa only [Subgroup.card_top] using hlt

end CFSG.ShultStronglyClosedTI
