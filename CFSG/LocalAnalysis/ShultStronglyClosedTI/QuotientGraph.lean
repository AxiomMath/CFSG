module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowGeometry

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.NormalGraph

open CFSG.OrderReductions.InvolutionGraph
open CFSG.OrderReductions.InvolutionFusion

variable {G : Type*} [Group G]

theorem no_central_vertex (D : Set G) (horder : ∀ x ∈ D, orderOf x = 2)
    (hdisconnected : ¬ (graph D horder).Preconnected) {z : G} (hz : z ∈ D) :
    z ∉ Subgroup.center G := by
  intro hcentral
  apply hdisconnected
  intro x y
  have hxz : Commute (x : G) z := Subgroup.mem_center_iff.mp hcentral x
  have hyz : Commute (y : G) z := Subgroup.mem_center_iff.mp hcentral y
  exact (reachable_of_commute D horder x ⟨z, hz⟩ hxz).trans
    (reachable_of_commute D horder y ⟨z, hz⟩ hyz).symm

theorem commute_of_involution_product_central {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hcentral : x * y ∈ Subgroup.center G) : Commute x y := by
  let first : Involution G := ⟨x, hx⟩
  let second : Involution G := ⟨y, hy⟩
  have hfix : (MulAut.conj x) (x * y) = x * y := by
    apply (conj_eq_iff_centralizer x (x * y)).mpr
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hcentral x)
  have hflip := product_conjugate_inv first second
  change (MulAut.conj x) (x * y) = (x * y)⁻¹ at hflip
  have heq : x * y = (x * y)⁻¹ := hfix.symm.trans hflip
  change x * y = y * x
  simpa only [mul_inv_rev, inv_eq_self_of_orderOf_eq_two hx,
    inv_eq_self_of_orderOf_eq_two hy] using heq

theorem quotient_injective_on_vertices (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    Set.InjOn (QuotientGroup.mk' Z) D := by
  intro x hx y hy heq
  have hxinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two (horder x hx)
  have hxyZ : x * y ∈ Z := by
    have h := QuotientGroup.eq.mp heq
    rwa [hxinv] at h
  by_contra hne
  have hcomm := commute_of_involution_product_central (horder x hx) (horder y hy) (hZ hxyZ)
  exact no_central_vertex D horder hdisconnected (hproduct x hx y hy hne hcomm) (hZ hxyZ)

theorem quotient_vertices_order_two (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    ∀ q ∈ (QuotientGroup.mk' Z) '' D, orderOf q = 2 := by
  rintro _ ⟨x, hx, rfl⟩
  apply orderOf_eq_prime_iff.mpr
  refine ⟨?_, ?_⟩
  · have hxpow := pow_orderOf_eq_one x
    rw [horder x hx] at hxpow
    simpa only [map_pow, map_one] using congrArg (QuotientGroup.mk' Z) hxpow
  · intro hone
    exact no_central_vertex D horder hdisconnected hx
      (hZ ((QuotientGroup.eq_one_iff x).mp hone))

theorem quotient_commute_iff (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    {x y : G} (hx : x ∈ D) :
    Commute ((QuotientGroup.mk' Z) x) ((QuotientGroup.mk' Z) y) ↔ Commute x y := by
  constructor
  · intro hcomm
    have hsame : (QuotientGroup.mk' Z) ((MulAut.conj y) x) = (QuotientGroup.mk' Z) x := by
      change (QuotientGroup.mk' Z) (y * x * y⁻¹) = (QuotientGroup.mk' Z) x
      rw [map_mul, map_mul, map_inv, ← hcomm.eq]
      group
    have heq := quotient_injective_on_vertices D horder hproduct hdisconnected Z hZ
      (hconj x hx y) hx hsame
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      ((conj_eq_iff_centralizer y x).mp heq)).symm
  · intro hcomm
    exact hcomm.map (QuotientGroup.mk' Z)

@[expose] def quotientVertexEquiv (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    D ≃ (QuotientGroup.mk' Z) '' D :=
  Equiv.ofBijective (fun x => ⟨(QuotientGroup.mk' Z) x, ⟨x, x.property, rfl⟩⟩)
    ⟨fun x y h => Subtype.ext
      (quotient_injective_on_vertices D horder hproduct hdisconnected Z hZ x.property y.property
        (congrArg Subtype.val h)),
      fun ⟨_, x, hx, hq⟩ => ⟨⟨x, hx⟩, Subtype.ext hq⟩⟩

@[expose] def quotientGraphIso (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    graph D horder ≃g graph ((QuotientGroup.mk' Z) '' D)
      (quotient_vertices_order_two D horder hdisconnected Z hZ) where
  toEquiv := quotientVertexEquiv D horder hproduct hdisconnected Z hZ
  map_rel_iff' := by
    intro x y
    constructor
    · intro hadj
      refine ⟨?_, (quotient_commute_iff D horder hconj hproduct hdisconnected Z hZ
        x.property).mp hadj.2⟩
      intro heq
      apply hadj.1
      apply Subtype.ext
      exact congrArg (QuotientGroup.mk' Z)
        (congrArg (fun t : Involution G => (t : G)) heq)
    · intro hadj
      refine ⟨?_, hadj.2.map (QuotientGroup.mk' Z)⟩
      intro heq
      apply hadj.1
      apply Subtype.ext
      exact quotient_injective_on_vertices D horder hproduct hdisconnected Z hZ
        x.property y.property
        (congrArg (fun t : Involution (G ⧸ Z) => (t : G ⧸ Z)) heq)

theorem quotient_graph_not_preconnected (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) :
    ¬ (graph ((QuotientGroup.mk' Z) '' D)
      (quotient_vertices_order_two D horder hdisconnected Z hZ)).Preconnected :=
  fun h => hdisconnected
    ((quotientGraphIso D horder hconj hproduct hdisconnected Z hZ).preconnected_iff.mpr h)

theorem quotient_vertices_conj_mem (D : Set G)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (Z : Subgroup G) [Z.Normal] {q : G ⧸ Z}
    (hq : q ∈ (QuotientGroup.mk' Z) '' D) (g : G ⧸ Z) :
    (MulAut.conj g) q ∈ (QuotientGroup.mk' Z) '' D := by
  obtain ⟨x, hx, rfl⟩ := hq
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z g
  refine ⟨(MulAut.conj a) x, hconj x hx a, ?_⟩
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem quotient_vertices_mul_mem (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G)
    {q r : G ⧸ Z} (hq : q ∈ (QuotientGroup.mk' Z) '' D)
    (hr : r ∈ (QuotientGroup.mk' Z) '' D) (hne : q ≠ r) (hcomm : Commute q r) :
    q * r ∈ (QuotientGroup.mk' Z) '' D := by
  obtain ⟨x, hx, rfl⟩ := hq
  obtain ⟨y, hy, rfl⟩ := hr
  have hxy : x ≠ y := fun h => hne (congrArg (QuotientGroup.mk' Z) h)
  have hcomm' := (quotient_commute_iff D horder hconj hproduct hdisconnected Z hZ hx).mp hcomm
  exact ⟨x * y, hproduct x hx y hy hxy hcomm', map_mul _ _ _⟩

theorem quotient_centralizer_preimage (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) {z : G} (hz : z ∈ D) :
    (Subgroup.centralizer ({(QuotientGroup.mk' Z) z} : Set (G ⧸ Z))).comap
      (QuotientGroup.mk' Z) = Subgroup.centralizer ({z} : Set G) := by
  ext g
  constructor
  · intro hg
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hsame : (QuotientGroup.mk' Z) ((MulAut.conj g) z) = (QuotientGroup.mk' Z) z := by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hcomm]
      group
    exact (conj_eq_iff_centralizer g z).mp
      (quotient_injective_on_vertices D horder hproduct hdisconnected Z hZ
        (hconj z hz g) hz hsame)
  · intro hg
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact (show Commute g z from Subgroup.mem_centralizer_singleton_iff.mp hg).map
      (QuotientGroup.mk' Z)

theorem quotient_centralizer_image (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) {z : G} (hz : z ∈ D) :
    (Subgroup.centralizer ({z} : Set G)).map (QuotientGroup.mk' Z) =
      Subgroup.centralizer ({(QuotientGroup.mk' Z) z} : Set (G ⧸ Z)) := by
  rw [← quotient_centralizer_preimage D horder hconj hproduct hdisconnected Z hZ hz]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) _

def subgroupQuotientEquiv (H Z : Subgroup G) [Z.Normal] :
    H ⧸ Z.subgroupOf H ≃* H.map (QuotientGroup.mk' Z) := by
  let f := (QuotientGroup.mk' Z).domRestrict H
  have hker : f.ker = Z.subgroupOf H := by
    ext x
    change ((x : G) : G ⧸ Z) = 1 ↔ (x : G) ∈ Z
    exact QuotientGroup.eq_one_iff (x : G)
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range H (QuotientGroup.mk' Z))))

def centralizerQuotientEquiv (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) {z : G} (hz : z ∈ D) :
    (Subgroup.centralizer ({z} : Set G)) ⧸
      Z.subgroupOf (Subgroup.centralizer ({z} : Set G)) ≃*
        Subgroup.centralizer ({(QuotientGroup.mk' Z) z} : Set (G ⧸ Z)) :=
  (subgroupQuotientEquiv _ Z).trans
    (MulEquiv.subgroupCongr (quotient_centralizer_image D horder hconj hproduct
      hdisconnected Z hZ hz))

theorem quotient_hull_image (D : Set G) (Z : Subgroup G) [Z.Normal] :
    (Subgroup.closure D).map (QuotientGroup.mk' Z) =
      Subgroup.closure ((QuotientGroup.mk' Z) '' D) := MonoidHom.map_closure _ _

def hullQuotientEquiv (D : Set G) (Z : Subgroup G) [Z.Normal] :
    (Subgroup.closure D) ⧸ Z.subgroupOf (Subgroup.closure D) ≃*
      Subgroup.closure ((QuotientGroup.mk' Z) '' D) :=
  (subgroupQuotientEquiv _ Z).trans (MulEquiv.subgroupCongr (quotient_hull_image D Z))

theorem central_subgroup_le_component_normalizer (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) (z : D) :
    Z ≤ Subgroup.normalizer (componentSet D horder z) := by
  intro c hc
  apply centralizer_le_component_normalizer D horder hconj z
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hZ hc) z).symm

theorem quotientGraphIso_conj (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (x : D) (g : G) :
    (quotientGraphIso D horder hconj hproduct hdisconnected Z hZ
      (conjugationGraphHom D horder hconj g x) : G ⧸ Z) =
        (MulAut.conj ((QuotientGroup.mk' Z) g))
          (quotientGraphIso D horder hconj hproduct hdisconnected Z hZ x : G ⧸ Z) := by
  change (QuotientGroup.mk' Z) ((MulAut.conj g) (x : G)) =
    (MulAut.conj ((QuotientGroup.mk' Z) g)) ((QuotientGroup.mk' Z) (x : G))
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem quotient_component_image (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (z : D) :
    (QuotientGroup.mk' Z) '' componentSet D horder z =
      componentSet ((QuotientGroup.mk' Z) '' D)
        (quotient_vertices_order_two D horder hdisconnected Z hZ)
        (quotientGraphIso D horder hconj hproduct hdisconnected Z hZ z) := by
  let e := quotientGraphIso D horder hconj hproduct hdisconnected Z hZ
  ext q
  constructor
  · rintro ⟨x, ⟨hxD, hzx⟩, rfl⟩
    exact ⟨⟨x, hxD, rfl⟩, hzx.map e.toHom⟩
  · rintro ⟨hqD, hzq⟩
    obtain ⟨x, hxD, rfl⟩ := hqD
    have hzx : (graph D horder).Reachable z ⟨x, hxD⟩ :=
      (SimpleGraph.Iso.reachable_iff (φ := e)).mp hzq
    exact ⟨x, ⟨hxD, hzx⟩, rfl⟩

theorem quotient_component_normalizer_preimage (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (z : D) :
    (Subgroup.normalizer (componentSet ((QuotientGroup.mk' Z) '' D)
      (quotient_vertices_order_two D horder hdisconnected Z hZ)
      (quotientGraphIso D horder hconj hproduct hdisconnected Z hZ z))).comap
        (QuotientGroup.mk' Z) = Subgroup.normalizer (componentSet D horder z) := by
  let e := quotientGraphIso D horder hconj hproduct hdisconnected Z hZ
  let hqorder := quotient_vertices_order_two D horder hdisconnected Z hZ
  have hqconj : ∀ q ∈ (QuotientGroup.mk' Z) '' D, ∀ g : G ⧸ Z,
      (MulAut.conj g) q ∈ (QuotientGroup.mk' Z) '' D :=
    fun _ hq g => quotient_vertices_conj_mem D hconj Z hq g
  ext g
  change (QuotientGroup.mk' Z) g ∈ Subgroup.normalizer
    (componentSet ((QuotientGroup.mk' Z) '' D) hqorder (e z)) ↔
      g ∈ Subgroup.normalizer (componentSet D horder z)
  rw [mem_component_normalizer_iff _ hqorder hqconj,
    mem_component_normalizer_iff D horder hconj]
  have hconjeq : conjugationGraphHom ((QuotientGroup.mk' Z) '' D) hqorder hqconj
      ((QuotientGroup.mk' Z) g) (e z) = e (conjugationGraphHom D horder hconj g z) :=
    Subtype.ext (quotientGraphIso_conj D horder hconj hproduct hdisconnected Z hZ z g).symm
  rw [hconjeq]
  exact SimpleGraph.Iso.reachable_iff

theorem quotient_component_normalizer_image (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (z : D) :
    (Subgroup.normalizer (componentSet D horder z)).map (QuotientGroup.mk' Z) =
      Subgroup.normalizer (componentSet ((QuotientGroup.mk' Z) '' D)
        (quotient_vertices_order_two D horder hdisconnected Z hZ)
        (quotientGraphIso D horder hconj hproduct hdisconnected Z hZ z)) := by
  rw [← quotient_component_normalizer_preimage D horder hconj hproduct hdisconnected Z hZ z]
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Z) _

def componentNormalizerQuotientEquiv (D : Set G)
    (horder : ∀ x ∈ D, orderOf x = 2)
    (hconj : ∀ x ∈ D, ∀ g : G, (MulAut.conj g) x ∈ D)
    (hproduct : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → Commute x y → x * y ∈ D)
    (hdisconnected : ¬ (graph D horder).Preconnected)
    (Z : Subgroup G) [Z.Normal] (hZ : Z ≤ Subgroup.center G) (z : D) :
    (Subgroup.normalizer (componentSet D horder z)) ⧸
      Z.subgroupOf (Subgroup.normalizer (componentSet D horder z)) ≃*
        Subgroup.normalizer (componentSet ((QuotientGroup.mk' Z) '' D)
          (quotient_vertices_order_two D horder hdisconnected Z hZ)
          (quotientGraphIso D horder hconj hproduct hdisconnected Z hZ z)) :=
  (subgroupQuotientEquiv _ Z).trans
    (MulEquiv.subgroupCongr (quotient_component_normalizer_image D horder hconj hproduct
      hdisconnected Z hZ z))

end CFSG.ShultStronglyClosedTI.NormalGraph
