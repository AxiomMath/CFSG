module

public import CFSG.Quasithin.EmptyFaithful.SzN17Aut
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.C48Spor

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique

section Img

variable {G : Type} [Group G] {X : Subgroup G} (N : Subgroup ↥X) [N.Normal]

@[expose] def img (Y : Subgroup G) : Subgroup (↥X ⧸ N) :=
  (Y.subgroupOf X).map (QuotientGroup.mk' N)

variable {N}

theorem mem_img {Y : Subgroup G} {a : ↥X ⧸ N} :
    a ∈ img N Y ↔ ∃ x : ↥X, (x : G) ∈ Y ∧ (x : ↥X ⧸ N) = a := by
  unfold img
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h⟩⟩

theorem mk_mem_img {Y : Subgroup G} {x : ↥X} (hx : (x : G) ∈ Y) :
    (x : ↥X ⧸ N) ∈ img N Y :=
  mem_img.2 ⟨x, hx, rfl⟩

theorem img_mono {Y Y' : Subgroup G} (h : Y ≤ Y') : img N Y ≤ img N Y' :=
  Subgroup.map_mono fun _ hx => h hx

omit [N.Normal] in
theorem subgroupOf_sup_of_le {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X) :
    (Y ⊔ Y').subgroupOf X = Y.subgroupOf X ⊔ Y'.subgroupOf X :=
  Subgroup.subgroupOf_sup hY hY'

omit [N.Normal] in
theorem commutator_le_of_le {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X) : ⁅Y, Y'⁆ ≤ X :=
  Subgroup.commutator_le.2 fun g hg g' hg' => by
    rw [commutatorElement_def]
    exact X.mul_mem (X.mul_mem (X.mul_mem (hY hg) (hY' hg')) (X.inv_mem (hY hg)))
      (X.inv_mem (hY' hg'))

omit [N.Normal] in
theorem commutator_subgroupOf_of_le {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X) :
    (⁅Y, Y'⁆).subgroupOf X = ⁅Y.subgroupOf X, Y'.subgroupOf X⁆ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hY,
    Subgroup.map_subgroupOf_eq_of_le hY',
    Subgroup.map_subgroupOf_eq_of_le (commutator_le_of_le hY hY')]

theorem img_sup {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X) :
    img N (Y ⊔ Y') = img N Y ⊔ img N Y' := by
  unfold img
  rw [subgroupOf_sup_of_le hY hY', Subgroup.map_sup]

theorem img_commutator {Y Y' : Subgroup G} (hY : Y ≤ X) (hY' : Y' ≤ X) :
    img N ⁅Y, Y'⁆ = ⁅img N Y, img N Y'⁆ := by
  unfold img
  rw [commutator_subgroupOf_of_le hY hY', Subgroup.map_commutator]

@[expose] noncomputable def imgHom {Y : Subgroup G} (hY : Y ≤ X) : ↥Y →* ↥(img N Y) :=
  ((QuotientGroup.mk' N).comp (Subgroup.inclusion hY)).codRestrict (img N Y)
    (fun y => mk_mem_img (x := Subgroup.inclusion hY y) y.2)

theorem coe_imgHom {Y : Subgroup G} (hY : Y ≤ X) (y : ↥Y) :
    (imgHom (N := N) hY y : ↥X ⧸ N) = ((⟨y, hY y.2⟩ : ↥X) : ↥X ⧸ N) := rfl

theorem imgHom_surjective {Y : Subgroup G} (hY : Y ≤ X) :
    Function.Surjective (imgHom (N := N) hY) := by
  rintro ⟨a, ha⟩
  obtain ⟨x, hxY, rfl⟩ := mem_img.1 ha
  exact ⟨⟨x, hxY⟩, Subtype.ext rfl⟩

theorem mem_ker_imgHom {Y : Subgroup G} (hY : Y ≤ X) (y : ↥Y) :
    y ∈ (imgHom (N := N) hY).ker ↔ (⟨y, hY y.2⟩ : ↥X) ∈ N := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, coe_imgHom, OneMemClass.coe_one,
    QuotientGroup.eq_one_iff]

end Img

section Img2

variable {G : Type} [Group G] {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]

theorem img_map_subtype {Y : Subgroup G} (hY : Y ≤ X) (Z : Subgroup ↥Y) :
    img N (Z.map Y.subtype) = (Z.map (imgHom (N := N) hY)).map (img N Y).subtype := by
  ext a
  rw [mem_img]
  constructor
  · rintro ⟨x, ⟨z, hz, hzx⟩, rfl⟩
    refine ⟨imgHom (N := N) hY z, ⟨z, hz, rfl⟩, ?_⟩
    rw [Subgroup.coe_subtype, coe_imgHom]
    congr 1
    exact Subtype.ext hzx
  · rintro ⟨b, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨⟨z, hY z.2⟩, ⟨z, hz, rfl⟩, rfl⟩

theorem img_le_normalizer {Y Z : Subgroup G} (h : Y ≤ Subgroup.normalizer (Z : Set G)) :
    img N Y ≤ Subgroup.normalizer (img N Z : Set (↥X ⧸ N)) := by
  intro a ha
  obtain ⟨y, hyY, rfl⟩ := mem_img.1 ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨z, hzZ, rfl⟩ := mem_img.1 hb
    have hz' : (y : G) * z * (y : G)⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (h hyY) z).mp hzZ
    exact mem_img.2 ⟨y * z * y⁻¹, hz', by simp⟩
  · intro hb
    obtain ⟨w, hwZ, hw⟩ := mem_img.1 hb
    have hw' : (y : G)⁻¹ * w * y ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (h hyY)) w).mp hwZ
      simpa using this
    refine mem_img.2 ⟨y⁻¹ * w * y, hw', ?_⟩
    have hb' : (b : ↥X ⧸ N) = (y : ↥X ⧸ N)⁻¹ * ((y : ↥X ⧸ N) * b * (y : ↥X ⧸ N)⁻¹) *
        (y : ↥X ⧸ N) := by group
    rw [hb', ← hw]
    simp

theorem isPGroup_img {p : ℕ} {Y : Subgroup G} (h : IsPGroup p ↥Y) : IsPGroup p ↥(img N Y) :=
  (h.comap_of_injective X.subtype X.subtype_injective).map (QuotientGroup.mk' N)

theorem isElemAbelian_img {Y : Subgroup G} (h : IsElemAbelian 2 Y) :
    IsElemAbelian 2 (img N Y) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨x, hx, rfl⟩ := mem_img.1 ha
    obtain ⟨x', hx', rfl⟩ := mem_img.1 hb
    apply Subtype.ext
    have hc : (x : G) * x' = x' * x := by
      have := h.1.is_comm.comm ⟨x, hx⟩ ⟨x', hx'⟩
      exact congrArg Subtype.val this
    have hc' : x * x' = x' * x := Subtype.ext hc
    simp only [Subgroup.coe_mul]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc']
  · obtain ⟨x, hx, rfl⟩ := mem_img.1 ha
    have h2 : (x : G) ^ 2 = 1 := h.2 x hx
    have h2' : x ^ 2 = 1 := Subtype.ext (by simpa using h2)
    rw [← QuotientGroup.mk_pow, h2', QuotientGroup.mk_one]

theorem img_centerOf_le {P : Subgroup G} : img N (centerOf P) ≤ centerOf (img N P) := by
  intro a ha
  obtain ⟨x, hx, rfl⟩ := mem_img.1 ha
  refine ⟨mk_mem_img hx.1, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  obtain ⟨y, hy, rfl⟩ := mem_img.1 hb
  have hc : (y : G) * x = x * y := (Subgroup.mem_centralizer_iff.mp hx.2) y hy
  have hc' : y * x = x * y := Subtype.ext hc
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc']

end Img2

section Img3

variable {G : Type} [Group G] {X : Subgroup G} {N : Subgroup ↥X} [N.Normal]

theorem pCore_map_eq_of_surjective {p : ℕ} {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    (CFSG.pCore p A).map f = CFSG.pCore p B := by
  apply le_antisymm
  · exact le_sSup ⟨CFSG.pCore_normal.map f hf, CFSG.pCore_isPGroup.map f⟩
  · have hle : (CFSG.pCore p B).comap f ≤ CFSG.pCore p A :=
      le_sSup ⟨CFSG.pCore_normal.comap f, CFSG.pCore_isPGroup.comap_of_ker_isPGroup f hker⟩
    calc CFSG.pCore p B = ((CFSG.pCore p B).comap f).map f :=
          (Subgroup.map_comap_eq_self_of_surjective hf _).symm
      _ ≤ (CFSG.pCore p A).map f := Subgroup.map_mono hle

theorem img_pCoreOf {Y : Subgroup G} (hY : Y ≤ X) (hker : IsPGroup 2 ↥(imgHom (N := N) hY).ker) :
    img N (pCoreOf 2 Y) = pCoreOf 2 (img N Y) := by
  unfold pCoreOf
  rw [img_map_subtype hY,
    pCore_map_eq_of_surjective (imgHom_surjective hY) hker]

theorem ker_mk_comp_imgHom {Y : Subgroup G} (hY : Y ≤ X)
    (hker : IsPGroup 2 ↥(imgHom (N := N) hY).ker) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥(img N Y))).comp (imgHom (N := N) hY)).ker =
      CFSG.pCore 2 ↥Y := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
    ← pCore_map_eq_of_surjective (imgHom_surjective hY) hker, Subgroup.comap_map_eq]
  exact sup_eq_left.2 (le_sSup ⟨MonoidHom.normal_ker _, hker⟩)

@[expose] noncomputable def modO2Equiv {Y : Subgroup G} (hY : Y ≤ X)
    (hker : IsPGroup 2 ↥(imgHom (N := N) hY).ker) : ModO2 Y ≃* ModO2 (img N Y) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_mk_comp_imgHom hY hker).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp (imgHom_surjective hY)))

theorem map_conjClosure {A B : Type} [Group A] [Group B] (f : A →* B) (Z H : Subgroup A) :
    (conjClosure Z H).map f = conjClosure (Z.map f) (H.map f) := by
  unfold conjClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨h, hh, z, hz, rfl⟩, rfl⟩
    exact ⟨f h, ⟨h, hh, rfl⟩, f z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨h * z * h⁻¹, ⟨h, hh, z, hz, rfl⟩, by simp⟩

omit [N.Normal] in
theorem conjClosure_le_of_le {L M : Subgroup G} (hL : L ≤ X) (hM : M ≤ X) :
    conjClosure L M ≤ X :=
  Subgroup.closure_le _ |>.2 fun _ ⟨_, hh, _, hz, hx⟩ => hx ▸
    X.mul_mem (X.mul_mem (hM hh) (hL hz)) (X.inv_mem (hM hh))

theorem img_conjClosure {L M : Subgroup G} (hL : L ≤ X) (hM : M ≤ X) :
    img N (conjClosure L M) = conjClosure (img N L) (img N M) := by
  have hsub : (conjClosure L M).subgroupOf X = conjClosure (L.subgroupOf X) (M.subgroupOf X) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [map_conjClosure, Subgroup.map_subgroupOf_eq_of_le hL, Subgroup.map_subgroupOf_eq_of_le hM,
      Subgroup.map_subgroupOf_eq_of_le (conjClosure_le_of_le hL hM)]
  unfold img
  rw [hsub, map_conjClosure]

theorem map_subgroupOf_imgHom {R Y : Subgroup G} (hY : Y ≤ X) (hRY : R ≤ Y) :
    (R.subgroupOf Y).map (imgHom (N := N) hY) = (img N R).subgroupOf (img N Y) := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf, coe_imgHom]
    exact mk_mem_img hy
  · intro a ha
    rw [Subgroup.mem_subgroupOf] at ha
    obtain ⟨x, hxR, hx⟩ := mem_img.1 ha
    refine ⟨⟨(x : G), hRY hxR⟩, hxR, Subtype.ext ?_⟩
    rw [coe_imgHom, ← hx]

theorem isSylowTwoOf_img {R Y : Subgroup G} (hY : Y ≤ X) (h : IsSylowTwoOf R Y) :
    IsSylowTwoOf (img N R) (img N Y) := by
  obtain ⟨hRY, hR, hidx⟩ := h
  have hdiv := Subgroup.index_map_dvd (R.subgroupOf Y) (imgHom_surjective (N := N) hY)
  rw [map_subgroupOf_imgHom hY hRY] at hdiv
  exact ⟨img_mono hRY, isPGroup_img hR, fun hdvd => hidx (hdvd.trans hdiv)⟩

theorem img_mem_cComp [Finite G] {L M : Subgroup G} (hM : M ≤ X) (hL : L ∈ cComp M)
    (hne : img N L ≠ ⊥) : img N L ∈ cComp (img N M) :=
  SzN17.map_mem_cComp_of_ne_bot (QuotientGroup.mk' N) (A312.mem_cComp_subgroupOf hM hL) hne

end Img3

end CFSG.Quasithin.C48Spor
