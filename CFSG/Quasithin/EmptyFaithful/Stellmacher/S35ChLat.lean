module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

include c

omit [Finite G] in
theorem π_eq_iff (x y : ↥(Vn δ)) : c.π x = c.π y ↔ (x : G) * (y : G)⁻¹ ∈ Zv δ := by
  have h := c.π_eq_one (x * y⁻¹)
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  rw [h]
  rfl

omit [Finite G] in
theorem Vn_le_normalizer_Zv : Vn δ ≤ Subgroup.normalizer (Zv δ : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ y ∈ Vn δ, ∀ z ∈ Zv δ, y * z * y⁻¹ ∈ Zv δ := by
    intro y hy z hz
    have hzV : z ∈ Vn δ := c.le hz
    have hm : y * z * y⁻¹ ∈ Vn δ := (Vn δ).mul_mem ((Vn δ).mul_mem hy hzV) ((Vn δ).inv_mem hy)
    have h1 : c.π ⟨y * z * y⁻¹, hm⟩ = 1 := by
      have : (⟨y * z * y⁻¹, hm⟩ : ↥(Vn δ)) = ⟨y, hy⟩ * ⟨z, hzV⟩ * ⟨y, hy⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, (c.π_eq_one ⟨z, hzV⟩).mpr hz, mul_one]
      exact mul_inv_cancel _
    exact (c.π_eq_one _).mp h1
  intro x
  refine ⟨key y hy x, fun hx => ?_⟩
  have := key y⁻¹ ((Vn δ).inv_mem hy) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem comm_mem_iff (g : ↥(stab δ)) (x : ↥(Vn δ)) :
    (g : G) * (x : G) * (g : G)⁻¹ * (x : G)⁻¹ ∈ Zv δ ↔ orth.act (c.θ g) (c.π x) = c.π x := by
  rw [← c.π_conj, c.π_eq_iff]
  rfl

@[expose] def bar (A : Subgroup G) : Subgroup (Perm (Fin 5)) := (A.subgroupOf (stab δ)).map c.θ

@[expose] def img (U : Subgroup G) : Subgroup orth.W := (U.subgroupOf (Vn δ)).map c.π

omit [Finite G] in
theorem mem_bar_iff {A : Subgroup G} {σ : Perm (Fin 5)} :
    σ ∈ c.bar A ↔ ∃ a : ↥(stab δ), (a : G) ∈ A ∧ c.θ a = σ := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

omit [Finite G] in
theorem bar_mono {A B : Subgroup G} (h : A ≤ B) : c.bar A ≤ c.bar B :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem mem_bar_of_mem {A : Subgroup G} {a : G} (ha : a ∈ A) (has : a ∈ stab δ) :
    c.θ ⟨a, has⟩ ∈ c.bar A :=
  (c.mem_bar_iff).mpr ⟨⟨a, has⟩, ha, rfl⟩

omit [Finite G] in
theorem bar_zpowers {x : G} (hx : x ∈ stab δ) :
    c.bar (Subgroup.zpowers x) = Subgroup.zpowers (c.θ ⟨x, hx⟩) := by
  have : (Subgroup.zpowers x).subgroupOf (stab δ) = Subgroup.zpowers (⟨x, hx⟩ : ↥(stab δ)) := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k, by simp⟩
  unfold bar
  rw [this, MonoidHom.map_zpowers]

omit [Finite G] in
theorem mem_img_iff' {U : Subgroup G} {w : orth.W} :
    w ∈ c.img U ↔ ∃ x : ↥(Vn δ), (x : G) ∈ U ∧ c.π x = w := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem mem_img_iff {U : Subgroup G} (hZU : Zv δ ≤ U) (x : ↥(Vn δ)) :
    c.π x ∈ c.img U ↔ (x : G) ∈ U := by
  rw [mem_img_iff']
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h1 : (y : G) * (x : G)⁻¹ ∈ Zv δ := (c.π_eq_iff y x).mp hyx
    have : (x : G) = ((y : G) * (x : G)⁻¹)⁻¹ * (y : G) := by group
    rw [this]
    exact U.mul_mem (U.inv_mem (hZU h1)) hy
  · intro h
    exact ⟨x, h, rfl⟩

omit [Finite G] in
theorem img_mono {U U' : Subgroup G} (h : U ≤ U') : c.img U ≤ c.img U' :=
  Subgroup.map_mono fun _ hx => h hx

omit [Finite G] in
theorem img_le_img_iff {U U' : Subgroup G} (hZU' : Zv δ ≤ U') :
    c.img U ≤ c.img U' ↔ U ⊓ Vn δ ≤ U' := by
  constructor
  · intro h x hx
    have hx1 : c.π ⟨x, hx.2⟩ ∈ c.img U := (c.mem_img_iff' ).mpr ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    exact (c.mem_img_iff hZU' ⟨x, hx.2⟩).mp (h hx1)
  · intro h w hw
    obtain ⟨x, hxU, rfl⟩ := (c.mem_img_iff').mp hw
    exact (c.mem_img_iff' ).mpr ⟨x, h ⟨hxU, x.2⟩, rfl⟩

omit [Finite G] in
theorem img_le_img_iff' {U U' : Subgroup G} (hZU' : Zv δ ≤ U') (hUV : U ≤ Vn δ) :
    c.img U ≤ c.img U' ↔ U ≤ U' := by
  rw [c.img_le_img_iff hZU']
  exact ⟨fun h x hx => h ⟨hx, hUV hx⟩, fun h x hx => h hx.1⟩

omit [Finite G] in
theorem img_injOn {U U' : Subgroup G} (hZU : Zv δ ≤ U) (hUV : U ≤ Vn δ) (hZU' : Zv δ ≤ U')
    (hUV' : U' ≤ Vn δ) (h : c.img U = c.img U') : U = U' :=
  le_antisymm ((c.img_le_img_iff' hZU' hUV).mp h.le) ((c.img_le_img_iff' hZU hUV').mp h.ge)

omit [Finite G] in
theorem index_img {U : Subgroup G} (hZU : Zv δ ≤ U) (_hUV : U ≤ Vn δ) :
    (c.img U).index = U.relIndex (Vn δ) := by
  have hker : c.π.ker ≤ U.subgroupOf (Vn δ) := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hZU ((c.π_eq_one x).mp hx))
  exact Subgroup.index_map_eq _ c.π_surj hker

omit [Finite G] in
theorem card_img {U : Subgroup G} (_hZU : Zv δ ≤ U) (hUV : U ≤ Vn δ) :
    Nat.card (c.img U) = (Zv δ).relIndex U := by
  have hker : c.π.ker = (Zv δ).subgroupOf (Vn δ) := by
    ext x
    rw [MonoidHom.mem_ker, c.π_eq_one, Subgroup.mem_subgroupOf]
  have := Subgroup.relIndex_ker (K := U.subgroupOf (Vn δ)) c.π
  rw [hker, Subgroup.relIndex_subgroupOf hUV] at this
  exact this.symm

omit c [Finite G] in
theorem le_normalizer_of_forall' {K U : Subgroup G} (h : ∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) :
    K ≤ Subgroup.normalizer (U : Set G) := fun g hg => by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have h1 := h g⁻¹ (K.inv_mem hg) _ hx
  rwa [inv_inv, show g⁻¹ * (g * x * g⁻¹) * g = x by group] at h1

omit [Finite G] in
theorem mem_fixSecIn_iff {A : Subgroup G} (hA : A ≤ stab δ) (x : ↥(Vn δ)) :
    (x : G) ∈ fixSecIn A (Zv δ) (Vn δ) ↔ c.π x ∈ fixW orth (c.bar A) := by
  rw [F53B3.N37.mem_fixSecIn_iff c.le c.Vn_le_normalizer_Zv]
  constructor
  · rintro ⟨-, h⟩ σ hσ
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
    exact (c.comm_mem_iff a x).mp (h a ha)
  · intro h
    refine ⟨x.2, fun a ha => ?_⟩
    exact (c.comm_mem_iff ⟨a, hA ha⟩ x).mpr (h _ (c.mem_bar_of_mem ha (hA ha)))

omit [Finite G] in
theorem Zv_le_fixSecIn {A : Subgroup G} (hA : A ≤ stab δ) : Zv δ ≤ fixSecIn A (Zv δ) (Vn δ) := by
  intro z hz
  have := (c.mem_fixSecIn_iff hA ⟨z, c.le hz⟩).mpr (by
    rw [(c.π_eq_one ⟨z, c.le hz⟩).mpr hz]
    exact Subgroup.one_mem _)
  exact this

omit [Finite G] in
theorem img_fixSecIn {A : Subgroup G} (hA : A ≤ stab δ) :
    c.img (fixSecIn A (Zv δ) (Vn δ)) = fixW orth (c.bar A) := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, rfl⟩ := (c.mem_img_iff').mp hw
    exact (c.mem_fixSecIn_iff hA x).mp hx
  · intro hw
    obtain ⟨x, rfl⟩ := c.π_surj w
    exact (c.mem_img_iff' ).mpr ⟨x, (c.mem_fixSecIn_iff hA x).mpr hw, rfl⟩

omit c [Finite G] in
theorem fixSecIn_le_Vn (A : Subgroup G) : fixSecIn A (Zv δ) (Vn δ) ≤ Vn δ :=
  F53B3.N37.fixSecIn_le A _ _

omit [Finite G] in
theorem relIndex_fixSecIn {A : Subgroup G} (hA : A ≤ stab δ) :
    (fixSecIn A (Zv δ) (Vn δ)).relIndex (Vn δ) = (fixW orth (c.bar A)).index := by
  rw [← c.img_fixSecIn hA, c.index_img (c.Zv_le_fixSecIn hA) (fixSecIn_le_Vn A)]

omit [Finite G] in
theorem secIdx_eq_idx {x : G} (hx : x ∈ stab δ) :
    secIdx (Subgroup.zpowers x) (Zv δ) (Vn δ) = idx orth (c.θ ⟨x, hx⟩) := by
  have hle : Subgroup.zpowers x ≤ stab δ := Subgroup.zpowers_le.mpr hx
  unfold secIdx idx
  rw [c.relIndex_fixSecIn hle, c.bar_zpowers hx]

omit [Finite G] in
theorem commSec_le_Vn {A : Subgroup G} (hA : A ≤ stab δ) : commSec A (Zv δ) (Vn δ) ≤ Vn δ := by
  refine sup_le ?_ c.le
  rw [Subgroup.commutator_le]
  intro x hx a ha
  have h1 := conj_mem_Vn (hA ha) ((Vn δ).inv_mem hx)
  have : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact (Vn δ).mul_mem hx h1

omit c [Finite G] in
theorem Zv_le_commSec (A : Subgroup G) : Zv δ ≤ commSec A (Zv δ) (Vn δ) := le_sup_right

omit [Finite G] in
theorem img_commSec {A : Subgroup G} (hA : A ≤ stab δ) :
    c.img (commSec A (Zv δ) (Vn δ)) = commW orth (c.bar A) ⊤ := by
  apply le_antisymm
  · set K : Subgroup G := ((commW orth (c.bar A) ⊤).comap c.π).map (Vn δ).subtype with hK
    have hmemK : ∀ x : ↥(Vn δ), (x : G) ∈ K ↔ c.π x ∈ commW orth (c.bar A) ⊤ := by
      intro x
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro h
        exact ⟨x, h, rfl⟩
    have hle : commSec A (Zv δ) (Vn δ) ≤ K := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx a ha
        have hcx : ⁅x, a⁆ ∈ Vn δ := c.commSec_le_Vn hA (le_sup_left (a := ⁅Vn δ, A⁆)
          (Subgroup.commutator_mem_commutator hx ha))
        have e : (⟨⁅x, a⁆, hcx⟩ : ↥(Vn δ)) = (conjV ⟨a, hA ha⟩ ⟨x, hx⟩ * ⟨x, hx⟩⁻¹)⁻¹ := by
          apply Subtype.ext
          simp [commutatorElement_def, mul_assoc]
        refine (hmemK ⟨_, hcx⟩).mpr ?_
        rw [e, map_inv, map_mul, map_inv, c.π_conj]
        refine Subgroup.inv_mem _ (Subgroup.subset_closure ⟨c.θ ⟨a, hA ha⟩, ?_, c.π ⟨x, hx⟩,
          Subgroup.mem_top _, rfl⟩)
        exact c.mem_bar_of_mem ha (hA ha)
      · intro z hz
        refine (hmemK ⟨z, c.le hz⟩).mpr ?_
        rw [(c.π_eq_one _).mpr hz]
        exact Subgroup.one_mem _
    intro w hw
    obtain ⟨x, hxU, rfl⟩ := (c.mem_img_iff').mp hw
    exact (hmemK x).mp (hle hxU)
  · unfold commW
    rw [Subgroup.closure_le]
    rintro _ ⟨σ, hσ, u, -, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
    obtain ⟨v, rfl⟩ := c.π_surj u
    refine (c.mem_img_iff').mpr ⟨conjV a v * v⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_sup_left ?_
      have e : ((conjV a v * v⁻¹ : ↥(Vn δ)) : G) = (⁅(v : G), (a : G)⁆)⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [e]
      exact (⁅Vn δ, A⁆).inv_mem (Subgroup.commutator_mem_commutator v.2 ha)
    · rw [map_mul, map_inv, c.π_conj]

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
