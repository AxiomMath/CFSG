module

public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem open_isQuasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

section Transl

variable {V X : Subgroup G} [IsMulCommutative ↥V] (hXV : X ≤ Subgroup.normalizer (V : Set G))
include hXV

theorem fixV_autOn_eq :
    fixV (autOn X V) = (Subgroup.centralizer (X : Set G)).subgroupOf V := by
  ext v
  rw [Ch10.SecA.mem_fixV_autOn hXV v, Subgroup.mem_subgroupOf]

omit [IsMulCommutative ↥V] in
theorem inv_autOn_iff {J : Subgroup G} (hJV : J ≤ V) :
    (∀ x ∈ autOn X V, ∀ w ∈ J.subgroupOf V, x w ∈ J.subgroupOf V) ↔
      X ≤ Subgroup.normalizer (J : Set G) := by
  constructor
  · intro h g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ X, ∀ j ∈ J, g * j * g⁻¹ ∈ J := by
      intro g hg j hj
      have h1 := h _ (Ch10.SecA.mem_autOn_iff'.mpr ⟨⟨g, hXV hg⟩, hg, rfl⟩) ⟨j, hJV hj⟩ hj
      rw [Subgroup.mem_subgroupOf, Ch10.SecA.coe_conjAct_apply'] at h1
      exact h1
    intro j
    refine ⟨fun hj => key g hg j hj, fun hj => ?_⟩
    have := key g⁻¹ (X.inv_mem hg) _ hj
    simpa [mul_assoc] using this
  · intro hJ x hx w hw
    obtain ⟨g, hgX, rfl⟩ := Ch10.SecA.mem_autOn_iff'.mp hx
    rw [Subgroup.mem_subgroupOf, Ch10.SecA.coe_conjAct_apply']
    exact (Subgroup.mem_normalizer_iff.mp (hJ hgX) _).mp hw

theorem commSub_autOn_eq {J : Subgroup G} (hJV : J ≤ V) :
    commSub (J.subgroupOf V) (autOn X V) = (⁅J, X⁆).subgroupOf V := by
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨φ, hφ, v, hv, rfl⟩
    obtain ⟨g, hgX, rfl⟩ := Ch10.SecA.mem_autOn_iff'.mp hφ
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Ch10.SecA.coe_conjAct_apply']
    have h : (g : G) * v * (g : G)⁻¹ * (v : G)⁻¹ = ⁅(v : G), (g : G)⁆⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hv hgX)
  · have hle : ⁅J, X⁆ ≤ (commSub (J.subgroupOf V) (autOn X V)).map V.subtype := by
      rw [Subgroup.commutator_le]
      intro x hx l hl
      have hmem : conjAct V ⟨l, hXV hl⟩ ⟨x, hJV hx⟩ * (⟨x, hJV hx⟩ : ↥V)⁻¹ ∈
          commSub (J.subgroupOf V) (autOn X V) :=
        Subgroup.subset_closure
          ⟨_, Ch10.SecA.mem_autOn_iff'.mpr ⟨⟨l, hXV hl⟩, hl, rfl⟩, ⟨x, hJV hx⟩, hx, rfl⟩
      refine ⟨(conjAct V ⟨l, hXV hl⟩ ⟨x, hJV hx⟩ * (⟨x, hJV hx⟩ : ↥V)⁻¹)⁻¹,
        Subgroup.inv_mem _ hmem, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul,
        Ch10.SecA.coe_conjAct_apply']
      rw [commutatorElement_def]
      group
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    obtain ⟨w, hw, hwv⟩ := hle hv
    rwa [← Subtype.ext hwv]

theorem mem_irrPlus_autOn {J : Subgroup G} (hJV : J ≤ V)
    (hXJ : X ≤ Subgroup.normalizer (J : Set G)) (hcomm : ⁅J, X⁆ = J)
    (hlt : J ⊓ Subgroup.centralizer (X : Set G) < J)
    (hirr : ∀ J' : Subgroup G, J ⊓ Subgroup.centralizer (X : Set G) ≤ J' → J' ≤ J →
      X ≤ Subgroup.normalizer (J' : Set G) →
        J' = J ⊓ Subgroup.centralizer (X : Set G) ∨ J' = J) :
    J.subgroupOf V ∈ IrrPlus (autOn X V) (⊤ : Subgroup ↥V) := by
  have hfix := fixV_autOn_eq hXV
  have hinf : J.subgroupOf V ⊓ fixV (autOn X V) =
      (J ⊓ Subgroup.centralizer (X : Set G)).subgroupOf V := by
    rw [hfix]
    ext v
    simp [Subgroup.mem_subgroupOf]
  have hmap : ∀ W : Subgroup ↥V, (W.map V.subtype).subgroupOf V = W := fun W =>
    Subgroup.comap_map_eq_self_of_injective V.subtype_injective W
  rw [mem_irrPlus_top_iff]
  refine ⟨(inv_autOn_iff hXV hJV).mpr hXJ, by rw [commSub_autOn_eq hXV hJV, hcomm], ?_, ?_⟩
  · rw [hinf]
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono _ inf_le_left) fun h => hlt.ne ?_
    have h1 := congrArg (Subgroup.map V.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hJV),
      Subgroup.map_subgroupOf_eq_of_le hJV] at h1
  · intro W hW hJW hWJ
    set W' := W.map V.subtype with hW'
    have hW'V : W' ≤ V := Subgroup.map_subtype_le W
    have hWW : W'.subgroupOf V = W := hmap W
    have h1 : J ⊓ Subgroup.centralizer (X : Set G) ≤ W' := by
      intro x hx
      rw [hinf] at hJW
      have hxV : x ∈ V := hJV hx.1
      exact ⟨⟨x, hxV⟩, hJW (show (⟨x, hxV⟩ : ↥V) ∈ _ from hx), rfl⟩
    have h2 : W' ≤ J := by
      rintro _ ⟨w, hw, rfl⟩
      exact hWJ hw
    have h3 : X ≤ Subgroup.normalizer (W' : Set G) := by
      rw [← inv_autOn_iff hXV hW'V, hWW]
      exact hW
    rcases hirr W' h1 h2 h3 with h4 | h4
    · left
      rw [hinf, ← hWW, h4]
    · right
      rw [← hWW, h4]

end Transl

theorem map_mem_irrPlus {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {g : MulAut V}
    (hg : g ∈ Subgroup.normalizer (H : Set (MulAut V))) {W : Subgroup V}
    (hW : W ∈ IrrPlus H (⊤ : Subgroup V)) : W.map g.toMonoidHom ∈ IrrPlus H (⊤ : Subgroup V) := by
  rw [mem_irrPlus_top_iff] at hW ⊢
  obtain ⟨hinv, hcomm, hlt, hirr⟩ := hW
  have hconj : ∀ x ∈ H, g⁻¹ * x * g ∈ H := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
    simpa using this
  have hconj' : ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hfix : (fixV H).map g.toMonoidHom = fixV H := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩ x hx
      have h1 := hv _ (hconj x hx)
      change x (g v) = g v
      have h2 : (g⁻¹ * x * g) v = v := h1
      simp only [MulAut.mul_apply] at h2
      have := congrArg g h2
      simpa using this
    · intro v hv
      refine ⟨g⁻¹ v, fun x hx => ?_, by simp⟩
      have h1 := hv _ (hconj' x hx)
      have h2 : g (x (g⁻¹ v)) = v := h1
      have h3 := congrArg (fun y => (g⁻¹ : MulAut V) y) h2
      simp only [MulAut.inv_apply_self] at h3
      exact h3
  have hinf : W.map g.toMonoidHom ⊓ fixV H = (W ⊓ fixV H).map g.toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ g.injective, hfix]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x hx _ ⟨w, hw, rfl⟩
    refine ⟨(g⁻¹ * x * g) w, hinv _ (hconj x hx) w hw, ?_⟩
    simp
  · apply le_antisymm
    · rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, _, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨(g⁻¹ * x * g) w * w⁻¹, ?_, ?_⟩
      · rw [← hcomm]
        exact Subgroup.subset_closure ⟨_, hconj x hx, w, hw, rfl⟩
      · simp
    · conv_lhs => rw [← hcomm]
      rw [commSub, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨x, hx, w, hw, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨g * x * g⁻¹, hconj' x hx, g w, ⟨w, hw, rfl⟩, ?_⟩
      simp
  · rw [hinf]
    refine lt_of_le_of_ne (Subgroup.map_mono hlt.le) fun h => hlt.ne ?_
    exact Subgroup.map_injective g.injective h
  · intro J hJ hJ1 hJ2
    have hJ' : ∀ x ∈ H, ∀ w ∈ J.map g⁻¹.toMonoidHom, x w ∈ J.map g⁻¹.toMonoidHom := by
      rintro x hx _ ⟨w, hw, rfl⟩
      refine ⟨(g * x * g⁻¹) w, hJ _ (hconj' x hx) w hw, ?_⟩
      simp
    have h1 : W ⊓ fixV H ≤ J.map g⁻¹.toMonoidHom := by
      intro v hv
      refine ⟨g v, ?_, by simp⟩
      rw [hinf] at hJ1
      exact hJ1 ⟨v, hv, rfl⟩
    have h2 : J.map g⁻¹.toMonoidHom ≤ W := by
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hJ2 hw
      simpa using hv
    have hback : (J.map g⁻¹.toMonoidHom).map g.toMonoidHom = J := by
      rw [Subgroup.map_map]
      convert Subgroup.map_id J
      ext v
      simp
    rcases hirr _ hJ' h1 h2 with h3 | h3
    · left
      rw [hinf, ← hback, h3]
    · right
      rw [← hback, h3]

end CFSG.Quasithin.Vol2.Ch11.OE3
