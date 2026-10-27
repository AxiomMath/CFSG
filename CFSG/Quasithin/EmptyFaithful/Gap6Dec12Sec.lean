module

public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.EmptyFaithful.S145Two
public import CFSG.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

namespace Gap6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

def cSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 1], by decide⟩

def sSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], by decide⟩

def d3toSL : DihedralGroup 3 → Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
  | .r i => cSL ^ i.val
  | .sr i => sSL * cSL ^ i.val

theorem d3toSL_mul : ∀ a b : DihedralGroup 3, d3toSL (a * b) = d3toSL a * d3toSL b := by
  decide +kernel

noncomputable def d3hom : DihedralGroup 3 →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun := d3toSL
  map_one' := by decide +kernel
  map_mul' := d3toSL_mul

theorem d3hom_injective : Function.Injective d3hom := by
  have : ∀ a b : DihedralGroup 3, d3toSL a = d3toSL b → a = b := by decide +kernel
  exact fun a b h => this a b h

theorem d3hom_card :
    Nat.card (DihedralGroup 3) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  rw [DihedralGroup.nat_card, Nat.card_eq_fintype_card]
  decide +kernel

noncomputable def sl2EquivDihedral3 :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃* DihedralGroup 3 :=
  (MulEquiv.ofBijective d3hom ((Nat.bijective_iff_injective_and_card d3hom).2
    ⟨d3hom_injective, d3hom_card⟩)).symm

theorem secImg_commutator {G : Type} [Group G] {A B X Y : Subgroup G} [(B.subgroupOf A).Normal]
    (hX : X ≤ A) (hY : Y ≤ A) : secImg A B ⁅X, Y⁆ = ⁅secImg A B X, secImg A B Y⁆ := by
  have h1 : ⁅X, Y⁆ ≤ A := (Subgroup.commutator_le).mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem (hX hx) (hY hy)) (A.inv_mem (hX hx))) (A.inv_mem (hY hy))
  unfold secImg
  have e : ⁅X, Y⁆.subgroupOf A = ⁅X.subgroupOf A, Y.subgroupOf A⁆ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le h1, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]
  rw [e, Subgroup.map_commutator]

section Setting

variable {G : Type} [Group G]

abbrev Sec (Z : Subgroup G) : Type _ := SecQuot (Subgroup.normalizer (Z : Set G)) Z

structure Dec12Ctx (Z U H : Subgroup G) : Prop where
  hZ : H ≤ Subgroup.normalizer (Z : Set G)
  hUZ : U ≤ Subgroup.normalizer (Z : Set G)
  hHU : H ≤ Subgroup.normalizer (U : Set G)
  hUab : IsElemAbelian 2 U
  hker : centralizerMod Z H ⁅U, H⁆ ≤ centralizerMod Z H U

variable {Z U H : Subgroup G}

namespace Dec12Ctx

variable (hc : Dec12Ctx Z U H)

include hc

theorem comm_le : ⁅U, H⁆ ≤ U := S145.commutator_le_of_le_normalizer hc.hHU

theorem le_normalizer_K : H ≤ Subgroup.normalizer ((⁅U, H⁆ : Subgroup G) : Set G) :=
  F9.le_normalizer_commutator_of_le hc.hHU Subgroup.le_normalizer

theorem K_le_N : ⁅U, H⁆ ≤ Subgroup.normalizer (Z : Set G) := hc.comm_le.trans hc.hUZ

theorem helU : IsElemAbelian 2 (tildeOf Z U) := isElemAbelian_secImg hc.hUab

theorem helK : IsElemAbelian 2 (tildeOf Z ⁅U, H⁆) :=
  isElemAbelian_secImg (F7.isElemAbelian_mono hc.hUab hc.comm_le)

theorem tilde_le_normalizer_U :
    tildeOf Z H ≤ Subgroup.normalizer (tildeOf Z U : Set (Sec Z)) :=
  secImg_le_normalizer_secImg hc.hHU

theorem tilde_le_normalizer_K :
    tildeOf Z H ≤ Subgroup.normalizer (tildeOf Z ⁅U, H⁆ : Set (Sec Z)) :=
  secImg_le_normalizer_secImg hc.le_normalizer_K

@[expose] noncomputable def toH : ↥H →* ↥(tildeOf Z H) :=
  (toTilde hc.hZ).codRestrict (tildeOf Z H) fun x =>
    secMk_mem_secImg (x := Subgroup.inclusion hc.hZ x) x.2

theorem toH_coe (x : ↥H) : ((toH hc x : ↥(tildeOf Z H)) : Sec Z) = toTilde hc.hZ x := rfl

theorem toH_surjective : Function.Surjective (toH hc) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := mem_secImg.1 y.2
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  rw [toH_coe]
  exact hxy

@[expose] noncomputable def actU : ↥H →* MulAut ↥(tildeOf Z U) :=
  (A4.actionOn (tildeOf Z U) (tildeOf Z H) hc.tilde_le_normalizer_U).comp (toH hc)

@[expose] noncomputable def actW : ↥H →* MulAut ↥(tildeOf Z ⁅U, H⁆) :=
  (A4.actionOn (tildeOf Z ⁅U, H⁆) (tildeOf Z H) hc.tilde_le_normalizer_K).comp (toH hc)

theorem actU_coe (x : ↥H) (m : ↥(tildeOf Z U)) :
    ((actU hc x m : ↥(tildeOf Z U)) : Sec Z) =
      toTilde hc.hZ x * (m : Sec Z) * (toTilde hc.hZ x)⁻¹ := rfl

theorem actW_coe (x : ↥H) (w : ↥(tildeOf Z ⁅U, H⁆)) :
    ((actW hc x w : ↥(tildeOf Z ⁅U, H⁆)) : Sec Z) =
      toTilde hc.hZ x * (w : Sec Z) * (toTilde hc.hZ x)⁻¹ := rfl

@[expose] noncomputable def iota : ↥(tildeOf Z ⁅U, H⁆) →* ↥(tildeOf Z U) :=
  Subgroup.inclusion (secImg_mono hc.comm_le)

theorem iota_coe (w : ↥(tildeOf Z ⁅U, H⁆)) : ((iota hc w : ↥(tildeOf Z U)) : Sec Z) = w := rfl

theorem iota_injective : Function.Injective (iota hc) := Subgroup.inclusion_injective _

theorem iota_actW (x : ↥H) (w : ↥(tildeOf Z ⁅U, H⁆)) :
    iota hc (actW hc x w) = actU hc x (iota hc w) := rfl

theorem actU_mul_inv_mem_range (x : ↥H) (m : ↥(tildeOf Z U)) :
    actU hc x m * m⁻¹ ∈ (iota hc).range := by
  obtain ⟨u, hu, hum⟩ := mem_secImg.1 m.2
  set xN : ↥(Subgroup.normalizer (Z : Set G)) := Subgroup.inclusion hc.hZ x with hxN
  have hxu : ((xN * u * xN⁻¹ * u⁻¹ : ↥(Subgroup.normalizer (Z : Set G))) : G) ∈ ⁅U, H⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator x.2 hu
  refine ⟨⟨secMk _ _ (xN * u * xN⁻¹ * u⁻¹), secMk_mem_secImg hxu⟩, Subtype.ext ?_⟩
  rw [iota_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, actU_coe, map_mul, map_inv, hum]
  rfl

theorem toTilde_conj_eq_iff {V : Subgroup G} (hV : V ≤ Subgroup.normalizer (Z : Set G)) (x : ↥H) :
    (∀ w ∈ tildeOf Z V, toTilde hc.hZ x * w * (toTilde hc.hZ x)⁻¹ = w) ↔
      ∀ v ∈ V, (x : G) * v * (x : G)⁻¹ * v⁻¹ ∈ Z := by
  constructor
  · intro h v hv
    have hw : secMk (Subgroup.normalizer (Z : Set G)) Z ⟨v, hV hv⟩ ∈ tildeOf Z V :=
      secMk_mem_secImg (x := ⟨v, hV hv⟩) hv
    have h1 := h _ hw
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact commutator_mem_of_secMk_commute (x := Subgroup.inclusion hc.hZ x) (y := ⟨v, hV hv⟩) h1
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := mem_secImg.1 hw
    have h1 := secMk_comm_of_commutator_mem (A := Subgroup.normalizer (Z : Set G)) (K := Z)
      (x := Subgroup.inclusion hc.hZ x) (y := v) (h v hv)
    rw [mul_inv_eq_iff_eq_mul]
    exact h1

theorem actW_eq_one_iff (x : ↥H) : actW hc x = 1 ↔ (x : G) ∈ centralizerMod Z H ⁅U, H⁆ := by
  have h1 : actW hc x = 1 ↔ ∀ w ∈ tildeOf Z ⁅U, H⁆, toTilde hc.hZ x * w * (toTilde hc.hZ x)⁻¹ = w := by
    constructor
    · intro h w hw
      have := congrArg (fun φ : MulAut ↥(tildeOf Z ⁅U, H⁆) => ((φ ⟨w, hw⟩ : ↥(tildeOf Z ⁅U, H⁆)) : Sec Z)) h
      simpa [actW_coe] using this
    · intro h
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [actW_coe]
      exact h w w.2
  rw [h1, toTilde_conj_eq_iff hc hc.K_le_N, mem_centralizerMod]
  exact ⟨fun h => ⟨x.2, hc.hZ x.2, h⟩, fun h => h.2.2⟩

theorem actU_eq_one_iff (x : ↥H) : actU hc x = 1 ↔ (x : G) ∈ centralizerMod Z H U := by
  have h1 : actU hc x = 1 ↔ ∀ w ∈ tildeOf Z U, toTilde hc.hZ x * w * (toTilde hc.hZ x)⁻¹ = w := by
    constructor
    · intro h w hw
      have := congrArg (fun φ : MulAut ↥(tildeOf Z U) => ((φ ⟨w, hw⟩ : ↥(tildeOf Z U)) : Sec Z)) h
      simpa [actU_coe] using this
    · intro h
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [actU_coe]
      exact h w w.2
  rw [h1, toTilde_conj_eq_iff hc hc.hUZ, mem_centralizerMod]
  exact ⟨fun h => ⟨x.2, hc.hZ x.2, h⟩, fun h => h.2.2⟩

theorem actU_eq_one_of_actW_eq_one (x : ↥H) (hx : actW hc x = 1) : actU hc x = 1 :=
  (actU_eq_one_iff hc x).2 (hc.hker ((actW_eq_one_iff hc x).1 hx))

theorem actW_range :
    (actW hc).range = autOn (tildeOf Z H) (tildeOf Z ⁅U, H⁆) := by
  ext a
  rw [A4.mem_autOn_iff hc.tilde_le_normalizer_K, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨toH hc x, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := toH_surjective hc y
    exact ⟨x, rfl⟩

@[expose] noncomputable def HL (L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) : Subgroup G :=
  (L.comap (actW hc)).map H.subtype

variable {hc}

theorem mem_HL {L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} {g : G} :
    g ∈ HL hc L ↔ ∃ h : ↥H, actW hc h ∈ L ∧ (h : G) = g := by
  unfold HL
  simp only [Subgroup.mem_map, Subgroup.mem_comap, Subgroup.subtype_apply]

theorem HL_le (L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) : HL hc L ≤ H := by
  intro g hg
  obtain ⟨h, -, rfl⟩ := mem_HL.1 hg
  exact h.2

theorem mem_HL_iff {L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} {g : G} (hg : g ∈ H) :
    g ∈ HL hc L ↔ actW hc ⟨g, hg⟩ ∈ L := by
  constructor
  · intro h
    obtain ⟨h', hL, rfl⟩ := mem_HL.1 h
    exact hL
  · intro h
    exact mem_HL.2 ⟨⟨g, hg⟩, h, rfl⟩

theorem mem_HL_of_mem {L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} {h : ↥H} (hh : actW hc h ∈ L) :
    (h : G) ∈ HL hc L := mem_HL.2 ⟨h, hh, rfl⟩

theorem HL_mono {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} (h : L ≤ L') : HL hc L ≤ HL hc L' := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := mem_HL.1 hg
  exact mem_HL_of_mem (h hx)

theorem HL_inf (L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) :
    HL hc (L ⊓ L') = HL hc L ⊓ HL hc L' := by
  ext g
  constructor
  · intro hg
    exact ⟨HL_mono inf_le_left hg, HL_mono inf_le_right hg⟩
  · rintro ⟨h1, h2⟩
    have hgH : g ∈ H := HL_le L h1
    exact (mem_HL_iff hgH).2 ⟨(mem_HL_iff hgH).1 h1, (mem_HL_iff hgH).1 h2⟩

theorem HL_bot : HL hc (⊥ : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) = centralizerMod Z H ⁅U, H⁆ := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, hx, rfl⟩ := mem_HL.1 hg
    exact (actW_eq_one_iff hc x).1 (Subgroup.mem_bot.1 hx)
  · intro hg
    have hgH : g ∈ H := hg.1
    exact (mem_HL_iff hgH).2 (Subgroup.mem_bot.2 ((actW_eq_one_iff hc ⟨g, hgH⟩).2 hg))

theorem HL_sup {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} (hL : L ≤ (actW hc).range)
    (hL' : L' ≤ (actW hc).range) : HL hc (L ⊔ L') = HL hc L ⊔ HL hc L' := by
  unfold HL
  rw [← Subgroup.map_sup, Subgroup.comap_sup_eq_of_le_range _ hL hL']

theorem centralizerMod_le_HL {L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} :
    centralizerMod Z H ⁅U, H⁆ ≤ HL hc L := by
  rw [← HL_bot (hc := hc)]
  exact HL_mono bot_le

theorem relIndex_HL (B : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))) :
    (HL hc B).relIndex H = B.relIndex (actW hc).range := by
  have h1 : (HL hc B).subgroupOf H = B.comap (actW hc) := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact mem_HL_iff x.2
  rw [Subgroup.relIndex, h1, Subgroup.index_comap]

theorem HL_le_of_le {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} (hL : L ≤ (actW hc).range)
    (h : HL hc L ≤ HL hc L') : L ≤ L' := by
  intro l hl
  obtain ⟨x, rfl⟩ := hL hl
  exact (mem_HL_iff x.2).1 (h (mem_HL_of_mem hl))

theorem HL_injective {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} (hL : L ≤ (actW hc).range)
    (hL' : L' ≤ (actW hc).range) (h : HL hc L = HL hc L') : L = L' :=
  le_antisymm (HL_le_of_le hL h.le) (HL_le_of_le hL' h.ge)

theorem actW_conj (t g : ↥H) :
    (actW hc t)⁻¹ * actW hc g * actW hc t = actW hc (t⁻¹ * g * t) := by
  simp only [map_mul, map_inv]

theorem conjSub_HL {t : G} (ht : t ∈ H) {L L' : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))}
    (hLL' : ∀ x, x ∈ L' ↔ (actW hc ⟨t, ht⟩)⁻¹ * x * actW hc ⟨t, ht⟩ ∈ L) :
    conjSub t (HL hc L) = HL hc L' := by
  ext g
  rw [mem_conjSub]
  constructor
  · intro hg
    have hgH' : t⁻¹ * g * t ∈ H := HL_le L hg
    have hgH : g ∈ H := by
      have := H.mul_mem (H.mul_mem ht hgH') (H.inv_mem ht)
      simpa [mul_assoc] using this
    refine (mem_HL_iff hgH).2 ?_
    rw [hLL']
    have h1 := (mem_HL_iff hgH').1 hg
    have e := actW_conj (hc := hc) ⟨t, ht⟩ ⟨g, hgH⟩
    have e2 : (⟨t, ht⟩⁻¹ * ⟨g, hgH⟩ * ⟨t, ht⟩ : ↥H) = ⟨t⁻¹ * g * t, hgH'⟩ := Subtype.ext rfl
    rw [e2] at e
    rw [e]
    exact h1
  · intro hg
    have hgH : g ∈ H := HL_le _ hg
    have hgH' : t⁻¹ * g * t ∈ H := H.mul_mem (H.mul_mem (H.inv_mem ht) hgH) ht
    refine (mem_HL_iff hgH').2 ?_
    have h1 := (mem_HL_iff hgH).1 hg
    rw [hLL'] at h1
    have e := actW_conj (hc := hc) ⟨t, ht⟩ ⟨g, hgH⟩
    have e2 : (⟨t, ht⟩⁻¹ * ⟨g, hgH⟩ * ⟨t, ht⟩ : ↥H) = ⟨t⁻¹ * g * t, hgH'⟩ := Subtype.ext rfl
    rw [e2] at e
    rw [← e]
    exact h1

theorem secIso_HL {L : Subgroup (MulAut ↥(tildeOf Z ⁅U, H⁆))} (hL : L ≤ (actW hc).range)
    {D : Type*} [Group D] (e : ↥L ≃* D) :
    SecIso (HL hc L) (centralizerMod Z H ⁅U, H⁆) D := by
  let f : ↥(HL hc L) →* ↥L := ((actW hc).comp (Subgroup.inclusion (HL_le L))).codRestrict L
    (fun x => (mem_HL_iff (HL_le L x.2)).1 x.2)
  have hker : f.ker = (centralizerMod Z H ⁅U, H⁆).subgroupOf (HL hc L) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have : f x = 1 ↔ actW hc (Subgroup.inclusion (HL_le L) x) = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [this, actW_eq_one_iff hc]
    rfl
  have hsurj : Function.Surjective f := by
    intro l
    obtain ⟨h, hh⟩ := hL l.2
    have hmem : (h : G) ∈ HL hc L := mem_HL_of_mem (by rw [hh]; exact l.2)
    exact ⟨⟨h, hmem⟩, Subtype.ext hh⟩
  have hnorm : ((centralizerMod Z H ⁅U, H⁆).subgroupOf (HL hc L)).Normal := hker ▸ f.normal_ker
  refine ⟨hnorm, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
    ((QuotientGroup.quotientKerEquivOfSurjective f hsurj).trans e)

end Dec12Ctx

end Setting

end Gap6

end CFSG.Quasithin
