module

public import CFSG.Quasithin.EmptyFaithful.S152Y02
public import CFSG.Quasithin.EmptyFaithful.S14117Star

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S152Y

variable {G : Type} [Group G] [Finite G]

section Images

variable {M X Y : Subgroup G}

omit [Finite G] in
theorem commutator_subgroupOf_eq (hX : X ≤ M) (hY : Y ≤ M) :
    ⁅X, Y⁆.subgroupOf M = ⁅X.subgroupOf M, Y.subgroupOf M⁆ := by
  have h1 : ⁅X, Y⁆ ≤ M := (Subgroup.commutator_le).mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hX hx) (hY hy)) (M.inv_mem (hX hx)))
      (M.inv_mem (hY hy))
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h1, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]

omit [Finite G] in
theorem imageOTwoQuot_commutator (hX : X ≤ M) (hY : Y ≤ M) :
    imageOTwoQuot M ⁅X, Y⁆ = ⁅imageOTwoQuot M X, imageOTwoQuot M Y⁆ := by
  unfold imageOTwoQuot
  rw [commutator_subgroupOf_eq hX hY, Subgroup.map_commutator]

theorem imageOTwoQuot_oTwoUpper (hX : X ≤ M) :
    imageOTwoQuot M (oTwoUpper X) = oTwoUpper (imageOTwoQuot M X) := by
  unfold imageOTwoQuot
  rw [oTwoUpper_map, ← A4.oTwoUpper_subgroupOf hX]

theorem imageOTwoQuot_le_normalizer (hn : X ≤ Subgroup.normalizer (Y : Set G)) :
    imageOTwoQuot M X ≤ Subgroup.normalizer (imageOTwoQuot M Y : Set (OTwoQuot M)) := by
  intro u hu
  obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
  refine A4.mem_normalizer_of_conj_mem fun v hv => ?_
  obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hv
  refine mem_imageOTwoQuot_iff.mpr ⟨x * y * x⁻¹,
    M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM),
    (Subgroup.mem_normalizer_iff.mp (hn hxX) y).mp hyY, ?_⟩
  show (QuotientGroup.mk (⟨x, hxM⟩ * ⟨y, hyM⟩ * ⟨x, hxM⟩⁻¹ : ↥M) : OTwoQuot M) = _
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

omit [Finite G] in
theorem imageOTwoQuot_isPGroup (hX : X ≤ M) (h2 : IsPGroup 2 X) :
    IsPGroup 2 (imageOTwoQuot M X) :=
  (A4.isPGroup_subgroupOf_of_le hX h2).map _

end Images

section Pi

variable {T Mc M : Subgroup G}

@[expose] noncomputable def piStar (h : Data T Mc M) : OTwoQuot M →* MulAut (V154 T Mc M) :=
  QuotientGroup.lift (CFSG.Open.pCore 2 ↥M) (A4.actionOn (V154 T Mc M) M h.hMV) (by
    intro x hx
    rw [MonoidHom.mem_ker, A4.actionOn_eq_one_iff]
    exact h.hyp.pCoreOf_le_centralizer ⟨x, hx, rfl⟩)

theorem piStar_mk (h : Data T Mc M) (x : ↥M) :
    piStar h (QuotientGroup.mk x) = A4.actionOn (V154 T Mc M) M h.hMV x := rfl

theorem piStar_mk_eq_one_iff (h : Data T Mc M) {x : G} (hx : x ∈ M) :
    piStar h (QuotientGroup.mk ⟨x, hx⟩) = 1 ↔ x ∈ Subgroup.centralizer (V154 T Mc M : Set G) := by
  rw [piStar_mk]
  exact A4.actionOn_eq_one_iff h.hMV ⟨x, hx⟩

theorem map_piStar_imageOTwoQuot (h : Data T Mc M) {X : Subgroup G} (hX : X ≤ M) :
    (imageOTwoQuot M X).map (piStar h) = autOn X (V154 T Mc M) := by
  ext a
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact mem_autOn_iff_exists.mpr ⟨x, h.hMV hxM, hxX, rfl⟩
  · intro ha
    obtain ⟨x, hx, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
    exact ⟨QuotientGroup.mk ⟨x, hX hxX⟩, mem_imageOTwoQuot_iff.mpr ⟨x, hX hxX, hxX, rfl⟩, rfl⟩

theorem imageOTwoQuot_inf_centralizer (h : Data T Mc M) {X : Subgroup G} :
    imageOTwoQuot M (X ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) =
      imageOTwoQuot M X ⊓ (piStar h).ker := by
  ext u
  constructor
  · intro hu
    obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    refine ⟨mem_imageOTwoQuot_iff.mpr ⟨x, hxM, hxX.1, rfl⟩, ?_⟩
    exact (piStar_mk_eq_one_iff h hxM).mpr hxX.2
  · rintro ⟨hu, hk⟩
    obtain ⟨x, hxM, hxX, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact mem_imageOTwoQuot_iff.mpr ⟨x, hxM, ⟨hxX, (piStar_mk_eq_one_iff h hxM).mp hk⟩, rfl⟩

end Pi

end S152Y

end CFSG.Quasithin
