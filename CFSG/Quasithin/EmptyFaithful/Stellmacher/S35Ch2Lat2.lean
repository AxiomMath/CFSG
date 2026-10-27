module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Lat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch2

open S35.Ch
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Chart2

variable {δ : Geo H M} (c : Chart2 δ)

include c

omit [Finite G] in
theorem card_commSec {A : Subgroup G} (hA : A ≤ stab δ) :
    (Cb δ).relIndex (commSec A (Cb δ) (Vn δ)) = Nat.card (commW orth (c.bar A) ⊤) := by
  rw [← c.img_commSec hA, c.card_img (Cb_le_commSec A) (c.commSec_le_Vn hA)]

omit [Finite G] in
@[expose] def pre (Y : Subgroup orth.W) : Subgroup G := (Y.comap c.π).map (Vn δ).subtype

omit [Finite G] in
theorem mem_pre_iff {Y : Subgroup orth.W} (x : ↥(Vn δ)) : (x : G) ∈ c.pre Y ↔ c.π x ∈ Y := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

omit [Finite G] in
theorem pre_le_Vn (Y : Subgroup orth.W) : c.pre Y ≤ Vn δ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

omit [Finite G] in
theorem Cb_le_pre (Y : Subgroup orth.W) : Cb δ ≤ c.pre Y := fun z hz => by
  refine (c.mem_pre_iff ⟨z, c.le hz⟩).mpr ?_
  rw [(c.π_eq_one _).mpr hz]
  exact Y.one_mem

omit [Finite G] in
theorem img_pre (Y : Subgroup orth.W) : c.img (c.pre Y) = Y := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, rfl⟩ := (c.mem_img_iff').mp hw
    exact (c.mem_pre_iff x).mp hx
  · intro hw
    obtain ⟨x, rfl⟩ := c.π_surj w
    exact (c.mem_img_iff').mpr ⟨x, (c.mem_pre_iff x).mpr hw, rfl⟩

omit [Finite G] in
theorem le_pre_iff {U : Subgroup G} (hUV : U ≤ Vn δ) {Y : Subgroup orth.W} :
    U ≤ c.pre Y ↔ c.img U ≤ Y := by
  constructor
  · intro h w hw
    obtain ⟨x, hxU, rfl⟩ := (c.mem_img_iff').mp hw
    exact (c.mem_pre_iff x).mp (h hxU)
  · intro h x hx
    exact (c.mem_pre_iff ⟨x, hUV hx⟩).mpr (h ((c.mem_img_iff').mpr ⟨⟨x, hUV hx⟩, hx, rfl⟩))

omit [Finite G] in
theorem forall_conj_mem_iff {K U : Subgroup G} (hK : K ≤ stab δ) (hZU : Cb δ ≤ U)
    (hUV : U ≤ Vn δ) :
    (∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) ↔ IsInvSub orth (c.bar K) (c.img U) := by
  constructor
  · intro h σ hσ w hw
    obtain ⟨k, hk, rfl⟩ := (c.mem_bar_iff).mp hσ
    obtain ⟨x, hxU, rfl⟩ := (c.mem_img_iff').mp hw
    rw [← c.π_conj]
    exact (c.mem_img_iff hZU _).mpr (h k hk x hxU)
  · intro h k hk u hu
    have hu' : c.π ⟨u, hUV hu⟩ ∈ c.img U := (c.mem_img_iff').mpr ⟨_, hu, rfl⟩
    have := h _ (c.mem_bar_of_mem hk (hK hk)) _ hu'
    rw [← c.π_conj] at this
    exact (c.mem_img_iff hZU ⟨_, conj_mem_Vn (hK hk) (hUV hu)⟩).mp this

omit [Finite G] in
theorem le_normalizer_iff {K U : Subgroup G} (hK : K ≤ stab δ) (hZU : Cb δ ≤ U)
    (hUV : U ≤ Vn δ) :
    K ≤ Subgroup.normalizer (U : Set G) ↔ IsInvSub orth (c.bar K) (c.img U) := by
  rw [← c.forall_conj_mem_iff hK hZU hUV]
  exact ⟨fun h k hk u hu => (Subgroup.mem_normalizer_iff.mp (h hk) u).mp hu,
    le_normalizer_of_forall'⟩

omit [Finite G] in
theorem bar_stab : c.bar (stab δ) = ⊤ := by
  unfold bar
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact c.surj

theorem ker_iff (hS : Sit H M S) (hδ : vtype δ = false) (x : ↥(stab δ)) :
    c.θ x = 1 ↔ (x : G) ∈ Qv δ := by
  constructor
  · intro hx
    obtain ⟨n, ψ, hn, hψs, hψk⟩ := F53.exists_quotHom hS.glob.amalg δ
    rcases hn with ⟨rfl, -⟩ | ⟨-, hv⟩
    swap
    · rw [hδ] at hv
      exact absurd hv (by decide)
    have hle : ψ.ker ≤ c.θ.ker := by
      intro y hy
      rw [MonoidHom.mem_ker, hψk] at hy
      rw [MonoidHom.mem_ker, c.θ_eq_one]
      intro v hv
      exact S34.Zv_le_Cb hS.glob hδ (comm_mem_Zv_of_Qv hS hδ hy hv)
    have hmul := Subgroup.relIndex_mul_index hle
    rw [index_ker_five c.θ c.surj, index_ker_five ψ hψs] at hmul
    have h1 : ψ.ker.relIndex c.θ.ker = 1 := by omega
    have h2 := Subgroup.relIndex_eq_one.mp h1
    have h3 := h2 (show x ∈ c.θ.ker from hx)
    rwa [MonoidHom.mem_ker, hψk] at h3
  · intro hx
    rw [c.θ_eq_one]
    intro v hv
    exact S34.Zv_le_Cb hS.glob hδ (comm_mem_Zv_of_Qv hS hδ hx hv)

theorem ker_eq_Qv (hS : Sit H M S) (hδ : vtype δ = false) :
    c.θ.ker = (Qv δ).subgroupOf (stab δ) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, c.ker_iff hS hδ]

@[expose] def preθ (D : Subgroup (Perm (Fin 5))) : Subgroup G := (D.comap c.θ).map (stab δ).subtype

omit [Finite G] in
theorem mem_preθ_iff {D : Subgroup (Perm (Fin 5))} (x : ↥(stab δ)) :
    (x : G) ∈ c.preθ D ↔ c.θ x ∈ D := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

omit [Finite G] in
theorem preθ_le_stab (D : Subgroup (Perm (Fin 5))) : c.preθ D ≤ stab δ := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem Qv_le_preθ (hS : Sit H M S) (hδ : vtype δ = false) (D : Subgroup (Perm (Fin 5))) :
    Qv δ ≤ c.preθ D := fun q hq => by
  refine (c.mem_preθ_iff ⟨q, Qv_le_stab' δ hq⟩).mpr ?_
  rw [(c.ker_iff hS hδ ⟨q, Qv_le_stab' δ hq⟩).mpr hq]
  exact D.one_mem

omit [Finite G] in
theorem bar_preθ (D : Subgroup (Perm (Fin 5))) : c.bar (c.preθ D) = D := by
  ext σ
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp h
    exact (c.mem_preθ_iff a).mp ha
  · intro h
    obtain ⟨a, rfl⟩ := c.surj σ
    exact (c.mem_bar_iff).mpr ⟨a, (c.mem_preθ_iff a).mpr h, rfl⟩

theorem preθ_bar (hS : Sit H M S) (hδ : vtype δ = false) {A : Subgroup G} (hA : A ≤ stab δ)
    (hQ : Qv δ ≤ A) : c.preθ (c.bar A) = A := by
  apply le_antisymm
  · intro x hx
    have hxs : x ∈ stab δ := c.preθ_le_stab _ hx
    obtain ⟨a, ha, hax⟩ := (c.mem_bar_iff).mp ((c.mem_preθ_iff ⟨x, hxs⟩).mp hx)
    have hq : (a : G)⁻¹ * x ∈ Qv δ := by
      have : c.θ (a⁻¹ * ⟨x, hxs⟩) = 1 := by rw [map_mul, map_inv, hax, inv_mul_cancel]
      exact (c.ker_iff hS hδ _).mp this
    have : x = (a : G) * ((a : G)⁻¹ * x) := by group
    rw [this]
    exact A.mul_mem ha (hQ hq)
  · intro x hx
    exact (c.mem_preθ_iff ⟨x, hA hx⟩).mpr (c.mem_bar_of_mem hx (hA hx))

theorem card_bar (hS : Sit H M S) (hδ : vtype δ = false) {A : Subgroup G} (hA : A ≤ stab δ)
    (_hQ : Qv δ ≤ A) : Nat.card (c.bar A) = (Qv δ).relIndex A := by
  have := Subgroup.relIndex_ker (K := A.subgroupOf (stab δ)) c.θ
  rw [c.ker_eq_Qv hS hδ, Subgroup.relIndex_subgroupOf hA] at this
  exact this.symm

end Chart2

end S35.Ch2

end F53.Stellmacher

end CFSG.Quasithin
