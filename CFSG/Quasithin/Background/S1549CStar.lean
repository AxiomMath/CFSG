module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1bTransvection
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.S1417Natural

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

namespace S1549C

section Gen

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

@[expose, instance_reducible] noncomputable def modInst (h : HypF91 T V L V₁ Vp H) :
    CommGroup ↥(tildeOf V₁ (conjClosure Vp H)) :=
  commGroupOfElemAbelian h.isElemAbelian_tilde

@[expose] noncomputable def tildeHom (h : HypF91 T V L V₁ Vp H) :
    ↥H →* ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))) :=
  ((secMk (Subgroup.normalizer (V₁ : Set G)) V₁).comp
      (Subgroup.inclusion h.H_normalizes_V₁)).codRestrict _
    (fun x => HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) (H := H) le_rfl
      (mem_secImg.mpr ⟨Subgroup.inclusion h.H_normalizes_V₁ x, x.2, rfl⟩))

@[expose] noncomputable def starHom (h : HypF91 T V L V₁ Vp H) :
    ↥H →* MulAut ↥(tildeOf V₁ (conjClosure Vp H)) :=
  (conjAct (tildeOf V₁ (conjClosure Vp H))).comp (tildeHom h)

omit [Finite G] in
theorem autOn_tilde_eq_map_starHom (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} (hXH : X ≤ H) :
    autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure Vp H)) = (X.subgroupOf H).map (starHom h) := by
  ext y
  unfold autOn
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hg
    obtain ⟨x, hxX, hx⟩ := mem_secImg.mp hg
    refine ⟨⟨(x : G), hXH hxX⟩, Subgroup.mem_subgroupOf.mpr hxX, ?_⟩
    have : tildeHom h ⟨(x : G), hXH hxX⟩ = g := Subtype.ext hx
    simp only [starHom, MonoidHom.comp_apply, this]
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    refine ⟨tildeHom h x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact secMk_mem_secImg (X := X) (x := Subgroup.inclusion h.H_normalizes_V₁ x) hx

theorem starHom_eq_one_iff (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    starHom h x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  have hV₁H : V₁ ≤ H := h.V₁_le_V.trans h.V_le_H
  unfold starHom
  rw [MonoidHom.comp_apply, A1b.conjAct_eq_one_iff]
  have hmem : ((tildeHom h x : ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
      Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))) :
      SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ H :=
    secMk_mem_secImg (X := H) (x := Subgroup.inclusion h.H_normalizes_V₁ x) x.2
  have e := h.tilde_inf_centralizer_pCoreOf (B := H) le_rfl
  rw [inf_eq_right.mpr (pCoreOf_le 2 H)] at e
  constructor
  · intro hc
    have h1 : ((tildeHom h x : ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ (pCoreOf 2 H) := by
      rw [← e]
      exact ⟨hmem, hc⟩
    have h2 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (Subgroup.inclusion h.H_normalizes_V₁ x) ∈
        secImg (Subgroup.normalizer (V₁ : Set G)) V₁ (pCoreOf 2 H) := h1
    exact (secMk_mem_secImg_iff (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      h.V₁_le_pCoreOf).mp h2
  · intro hq
    have h1 : ((tildeHom h x : ↥(Subgroup.normalizer (tildeOf V₁ (conjClosure Vp H) :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))) :
        SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈ tildeOf V₁ (pCoreOf 2 H) :=
      secMk_mem_secImg (X := pCoreOf 2 H) (x := Subgroup.inclusion h.H_normalizes_V₁ x) hq
    rw [← e] at h1
    exact h1.2

omit [Finite G] in
@[expose] noncomputable def preStar (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) : Subgroup G :=
  (A.comap (starHom h)).map H.subtype

omit [Finite G] in
theorem mem_preStar_iff (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} {x : G} :
    x ∈ preStar h A ↔ ∃ hx : x ∈ H, starHom h ⟨x, hx⟩ ∈ A := by
  unfold preStar
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hA⟩
    exact ⟨⟨x, hx⟩, hA, rfl⟩

omit [Finite G] in
theorem preStar_le (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) : preStar h A ≤ H := by
  intro x hx
  exact ((mem_preStar_iff h).mp hx).1

theorem pCoreOf_le_preStar (h : HypF91 T V L V₁ Vp H)
    (A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))) : pCoreOf 2 H ≤ preStar h A := by
  intro x hx
  refine (mem_preStar_iff h).mpr ⟨pCoreOf_le 2 H hx, ?_⟩
  rw [(starHom_eq_one_iff h ⟨x, pCoreOf_le 2 H hx⟩).mpr hx]
  exact A.one_mem

omit [Finite G] in
theorem starHom_mem_iff (h : HypF91 T V L V₁ Vp H)
    {A : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure Vp H)))} {x : ↥H} :
    (x : G) ∈ preStar h A ↔ starHom h x ∈ A := by
  rw [mem_preStar_iff]
  exact ⟨fun ⟨_, h2⟩ => h2, fun h2 => ⟨x.2, h2⟩⟩

omit [Finite G] in
theorem autOn_tilde_conjSub (h : HypF91 T V L V₁ Vp H) {X : Subgroup G} (hXH : X ≤ H)
    {c : G} (hc : c ∈ H) :
    autOn (tildeOf V₁ (conjSub c X)) (tildeOf V₁ (conjClosure Vp H)) =
      (autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure Vp H))).map
        (MulAut.conj (starHom h ⟨c, hc⟩)).toMonoidHom := by
  have hcX : conjSub c X ≤ H := by
    intro y hy
    have := mem_conjSub.mp hy
    have e : y = c * (c⁻¹ * y * c) * c⁻¹ := by group
    rw [e]
    exact H.mul_mem (H.mul_mem hc (hXH this)) (H.inv_mem hc)
  rw [autOn_tilde_eq_map_starHom h hXH, autOn_tilde_eq_map_starHom h hcX]
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : c⁻¹ * x * c ∈ X := mem_conjSub.mp hx
    have hxH : (x : G) ∈ H := x.2
    refine ⟨starHom h ⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hxH) hc⟩,
      ⟨⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hxH) hc⟩,
        Subgroup.mem_subgroupOf.mpr hx', rfl⟩, ?_⟩
    have e : x = ⟨c, hc⟩ * ⟨c⁻¹ * x * c, H.mul_mem (H.mul_mem (H.inv_mem hc) hxH) hc⟩ *
        ⟨c, hc⟩⁻¹ := Subtype.ext (by
          show (x : G) = c * (c⁻¹ * x * c) * c⁻¹
          group)
    show starHom h ⟨c, hc⟩ * starHom h _ * (starHom h ⟨c, hc⟩)⁻¹ = starHom h x
    rw [← map_inv, ← map_mul, ← map_mul, ← e]
  · rintro ⟨y', ⟨x, hx, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hx
    have hxH : (x : G) ∈ H := x.2
    refine ⟨⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      refine mem_conjSub.mpr ?_
      have e : c⁻¹ * (c * (x : G) * c⁻¹) * c = x := by group
      simpa [e] using hx
    · show starHom h ((⟨c, hc⟩ : ↥H) * x * ⟨c, hc⟩⁻¹) =
        starHom h ⟨c, hc⟩ * starHom h x * (starHom h ⟨c, hc⟩)⁻¹
      rw [map_mul, map_mul, map_inv]

end Gen

end S1549C

end CFSG.Quasithin
