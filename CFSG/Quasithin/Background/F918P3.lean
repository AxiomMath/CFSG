module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.F9Section

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Act

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

@[expose] noncomputable def tildeHom (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) :
    ↥H →* ↥(tildeOf V₁ H) :=
  ((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp (Subgroup.inclusion hV₁)).codRestrict
    (tildeOf V₁ H) fun x =>
      secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := H)
        (x := ⟨x, hV₁ x.2⟩) x.2

theorem tildeHom_coe (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (x : ↥H) :
    ((tildeHom hV₁ x : ↥(tildeOf V₁ H)) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hV₁ x.2⟩ := rfl

theorem tildeHom_surjective (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) :
    Function.Surjective (tildeHom hV₁) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_secImg.mp hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

@[expose] noncomputable def actH (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) : ↥H →* MulAut ↥(tildeOf V₁ IH) :=
  (Setup.rho (tildeOf V₁ IH) (tildeOf V₁ H) (secImg_le_normalizer_secImg hIH)).comp
    (tildeHom hV₁)

theorem actH_apply_coe (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (x : ↥H) (w : ↥(tildeOf V₁ IH)) :
    ((actH hV₁ hIH x w : ↥(tildeOf V₁ IH)) : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hV₁ x.2⟩ *
        (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) *
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hV₁ x.2⟩)⁻¹ :=
  Setup.rho_apply_coe _ _ _

theorem autOn_tilde_eq_map_actH (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) {X : Subgroup G} (hXH : X ≤ H) :
    autOn (tildeOf V₁ X) (tildeOf V₁ IH) = (X.subgroupOf H).map (actH hV₁ hIH) := by
  have hXP : tildeOf V₁ X ≤ tildeOf V₁ H := secImg_mono hXH
  have hP : tildeOf V₁ H ≤
      Subgroup.normalizer ((tildeOf V₁ IH : Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) := secImg_le_normalizer_secImg hIH
  ext φ
  rw [Setup.mem_autOn_iff_rho hP hXP, Subgroup.mem_map]
  constructor
  · rintro ⟨p, hpX, rfl⟩
    obtain ⟨x, hx, hxp⟩ := mem_secImg.mp (show (p : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
      secImg (Subgroup.normalizer (V₁ : Set G)) V₁ X from hpX)
    refine ⟨⟨x, hXH hx⟩, hx, ?_⟩
    have : tildeHom hV₁ ⟨x, hXH hx⟩ = p := Subtype.ext hxp
    simp only [actH, MonoidHom.comp_apply, this]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨tildeHom hV₁ x, ?_, rfl⟩
    show secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hV₁ x.2⟩ ∈
      secImg (Subgroup.normalizer (V₁ : Set G)) V₁ X
    exact secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := X)
      (x := ⟨x, hV₁ x.2⟩) hx

end Act

section Dict

variable {G : Type} [Group G] {V₁ IH H : Subgroup G}

@[expose] def subM (V₁ IH J : Subgroup G) : Subgroup ↥(tildeOf V₁ IH) :=
  (tildeOf V₁ J).subgroupOf (tildeOf V₁ IH)

theorem mem_subM_iff {J : Subgroup G} {w : ↥(tildeOf V₁ IH)} :
    w ∈ subM V₁ IH J ↔
      (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ J := Iff.rfl

theorem exists_mk_of_mem_tilde (w : ↥(tildeOf V₁ IH)) :
    ∃ a : Subgroup.normalizer (V₁ : Set G), (a : G) ∈ IH ∧
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ a =
        (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) :=
  mem_secImg.mp w.2

theorem secMk_mem_tildeOf_iff {J : Subgroup G} (hV₁J : V₁ ≤ J)
    {a : Subgroup.normalizer (V₁ : Set G)} :
    secMk (Subgroup.normalizer (V₁ : Set G)) V₁ a ∈ tildeOf V₁ J ↔ (a : G) ∈ J :=
  secMk_mem_secImg_iff hV₁J

@[expose, reducible] def commGroupOfFact {S : Type} [Group S] (E : Subgroup S)
    [Fact (IsElemAbelian 2 E)] : CommGroup ↥E := commGroupOfElemAbelian (Fact.out)

attribute [local instance] commGroupOfFact

@[expose] def modMk (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) (a : G) (ha : a ∈ IH) :
    ↥(tildeOf V₁ IH) :=
  ⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a, hIHN ha⟩,
    secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := IH)
      (x := ⟨a, hIHN ha⟩) ha⟩

theorem modMk_mem_subM_iff (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {J : Subgroup G}
    (hV₁J : V₁ ≤ J) {a : G} (ha : a ∈ IH) : modMk hIHN a ha ∈ subM V₁ IH J ↔ a ∈ J :=
  secMk_mem_tildeOf_iff (a := ⟨a, hIHN ha⟩) hV₁J

theorem actH_modMk [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) (x : ↥H) {a : G} (ha : a ∈ IH) :
    actH hV₁ hIH x (modMk hIHN a ha) =
      modMk hIHN ((x : G) * a * (x : G)⁻¹)
        ((Subgroup.mem_normalizer_iff.mp (hIH x.2) a).mp ha) := by
  apply Subtype.ext
  rw [actH_apply_coe]
  simp only [modMk, ← map_inv, ← map_mul]
  rfl

theorem actH_mem_stabSub_subM_iff [Fact (IsElemAbelian 2 (tildeOf V₁ IH))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (IH : Set G)) {J : Subgroup G} (hV₁J : V₁ ≤ J) (hJI : J ≤ IH)
    (x : ↥H) :
    actH hV₁ hIH x ∈ stabSub (subM V₁ IH J) ↔ (x : G) ∈ Subgroup.normalizer (J : Set G) := by
  have hmod : ∀ a (ha : a ∈ IH), actH hV₁ hIH x (modMk hIHN a ha) ∈ subM V₁ IH J ↔
      (x : G) * a * (x : G)⁻¹ ∈ J := fun a ha => by
    rw [actH_modMk hV₁ hIHN hIH x ha]
    exact modMk_mem_subM_iff hIHN hV₁J _
  constructor
  · intro hst
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hxIH : ∀ g : G, (x : G) * g * (x : G)⁻¹ ∈ IH → g ∈ IH := fun g hg => by
      have := (Subgroup.mem_normalizer_iff.mp (hIH (H.inv_mem x.2)) _).mp hg
      simpa [mul_assoc] using this
    constructor
    · intro hg
      have hgIH : g ∈ IH := hJI hg
      have h1 := (hst (modMk hIHN g hgIH)).mpr ((modMk_mem_subM_iff hIHN hV₁J hgIH).mpr hg)
      exact (hmod g hgIH).mp h1
    · intro hg
      have hgIH : g ∈ IH := hxIH g (hJI hg)
      have h1 := (hmod g hgIH).mpr hg
      exact (modMk_mem_subM_iff hIHN hV₁J hgIH).mp ((hst (modMk hIHN g hgIH)).mp h1)
  · intro hx u
    obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde u
    have hu : u = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
    rw [hu, hmod (a : G) haIH, modMk_mem_subM_iff hIHN hV₁J haIH]
    exact (Subgroup.mem_normalizer_iff.mp hx (a : G)).symm

theorem modMk_one (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) :
    modMk hIHN 1 IH.one_mem = 1 := Subtype.ext (map_one _)

theorem modMk_mul (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {a b : G} (ha : a ∈ IH)
    (hb : b ∈ IH) :
    modMk hIHN (a * b) (IH.mul_mem ha hb) = modMk hIHN a ha * modMk hIHN b hb := by
  apply Subtype.ext
  show secMk _ _ ⟨a * b, hIHN (IH.mul_mem ha hb)⟩ = secMk _ _ ⟨a, hIHN ha⟩ * secMk _ _ ⟨b, hIHN hb⟩
  rw [← map_mul]
  rfl

theorem modMk_inv (hIHN : IH ≤ Subgroup.normalizer (V₁ : Set G)) {a : G} (ha : a ∈ IH) :
    modMk hIHN a⁻¹ (IH.inv_mem ha) = (modMk hIHN a ha)⁻¹ := by
  apply Subtype.ext
  show secMk _ _ ⟨a⁻¹, hIHN (IH.inv_mem ha)⟩ = (secMk _ _ ⟨a, hIHN ha⟩)⁻¹
  rw [← map_inv]
  rfl

section Gen

variable {I : Subgroup G}

theorem iSup_actH_subM_eq_top [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G)) (hV₁I : V₁ ≤ I) :
    (⨆ m ∈ (H.subgroupOf H).map (actH hV₁ hIH),
      (subM V₁ (conjClosure I H) I).map m.toMonoidHom) = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
  have key : ∀ x (hx : x ∈ conjClosure I H), modMk hIHN x hx ∈
      ⨆ m ∈ (H.subgroupOf H).map (actH hV₁ hIH), (subM V₁ (conjClosure I H) I).map m.toMonoidHom := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hx
      have hzIH : z ∈ conjClosure I H := le_conjClosure I H hz
      have key := actH_modMk hV₁ hIHN hIH ⟨h, hh⟩ hzIH
      refine Subgroup.mem_iSup_of_mem (actH hV₁ hIH ⟨h, hh⟩) (Subgroup.mem_iSup_of_mem ?_ ?_)
      · exact ⟨⟨h, hh⟩, Subgroup.mem_subgroupOf.mpr hh, rfl⟩
      · exact ⟨modMk hIHN z hzIH, (modMk_mem_subM_iff hIHN hV₁I hzIH).mpr hz, key.symm⟩
    | one => rw [modMk_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      have := mul_mem ihx ihy
      rwa [← modMk_mul hIHN hx hy] at this
    | inv x hx ih =>
      have := inv_mem ih
      rwa [← modMk_inv hIHN hx] at this
  rw [hw]
  exact key _ haIH

theorem subM_conjClosure_le_orbSup [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G)) {T : Subgroup G} (hTH : T ≤ H)
    (hV₁I : V₁ ≤ I) :
    subM V₁ (conjClosure I H) (conjClosure I T) ≤
      orbSup ((T.subgroupOf H).map (actH hV₁ hIH)) (subM V₁ (conjClosure I H) I) := by
  intro w hw
  have hCT : conjClosure I T ≤ conjClosure I H := conjClosure_mono le_rfl hTH
  obtain ⟨a, haCT, hau⟩ := mem_secImg.mp hw
  have haIH : (a : G) ∈ conjClosure I H := hCT haCT
  have hw' : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
  have key : ∀ x (hx : x ∈ conjClosure I T) (hxH : x ∈ conjClosure I H), modMk hIHN x hxH ∈
      orbSup ((T.subgroupOf H).map (actH hV₁ hIH)) (subM V₁ (conjClosure I H) I) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hxH
      obtain ⟨t, ht, z, hz, rfl⟩ := hx
      have hzIH : z ∈ conjClosure I H := le_conjClosure I H hz
      have key := actH_modMk hV₁ hIHN hIH ⟨t, hTH ht⟩ hzIH
      have hmem : actH hV₁ hIH ⟨t, hTH ht⟩ ∈ (T.subgroupOf H).map (actH hV₁ hIH) :=
        ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      refine Subgroup.mem_iSup_of_mem (actH hV₁ hIH ⟨t, hTH ht⟩) (Subgroup.mem_iSup_of_mem hmem ?_)
      exact ⟨modMk hIHN z hzIH, (modMk_mem_subM_iff hIHN hV₁I hzIH).mpr hz, key.symm⟩
    | one => intro hxH; rw [modMk_one]; exact one_mem _
    | mul x y hx hy ihx ihy =>
      intro hxyH
      have hxH : x ∈ conjClosure I H := hCT hx
      have hyH : y ∈ conjClosure I H := hCT hy
      have := mul_mem (ihx hxH) (ihy hyH)
      rwa [← modMk_mul hIHN hxH hyH] at this
    | inv x hx ih =>
      intro hxH
      have hxH' : x ∈ conjClosure I H := hCT hx
      have := inv_mem (ih hxH')
      rwa [← modMk_inv hIHN hxH'] at this
  rw [hw']
  exact key _ haCT haIH

theorem map_actH_le_stabSub_iff [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIHN : conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H ≤ Subgroup.normalizer (conjClosure I H : Set G)) (hV₁I : V₁ ≤ I) :
    (H.subgroupOf H).map (actH hV₁ hIH) ≤ stabSub (subM V₁ (conjClosure I H) I) ↔
      H ≤ Subgroup.normalizer (I : Set G) := by
  constructor
  · intro h x hx
    exact (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV₁I (le_conjClosure I H) ⟨x, hx⟩).mp
      (h ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  · rintro hn _ ⟨x, -, rfl⟩
    exact (actH_mem_stabSub_subM_iff hV₁ hIHN hIH hV₁I (le_conjClosure I H) x).mpr (hn x.2)

end Gen

end Dict

end CFSG.Quasithin
