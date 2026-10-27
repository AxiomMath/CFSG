module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatAct

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T M L : Subgroup G}

namespace HatModel

variable (D : HatModel T M)

noncomputable def img (K : Subgroup G) : Subgroup (D.V ≃ₗ[ZMod 2] D.V) :=
  (K.subgroupOf (Subgroup.normalizer (uOfL22 T M : Set G))).map D.rho

variable {D}

theorem mem_img {K : Subgroup G} {γ : D.V ≃ₗ[ZMod 2] D.V} :
    γ ∈ D.img K ↔ ∃ x ∈ K, ∃ hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G),
      D.rho ⟨x, hx⟩ = γ := by
  unfold img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxK, rfl⟩
    exact ⟨x.1, hxK, x.2, rfl⟩
  · rintro ⟨x, hxK, hxN, rfl⟩
    exact ⟨⟨x, hxN⟩, hxK, rfl⟩

theorem rho_mem_img {K : Subgroup G} {x : G} (hxK : x ∈ K)
    (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) : D.rho ⟨x, hxN⟩ ∈ D.img K :=
  mem_img.2 ⟨x, hxK, hxN, rfl⟩

theorem img_mono {K K' : Subgroup G} (hKK' : K ≤ K') : D.img K ≤ D.img K' :=
  Subgroup.map_mono (fun _ hx => hKK' hx)

theorem card_img_eq_relIndex {K Kc : Subgroup G}
    (hKN : K ≤ Subgroup.normalizer (uOfL22 T M : Set G))
    (hker : ∀ x ∈ K, (∃ hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G),
      D.rho ⟨x, hxN⟩ = 1) ↔ x ∈ Kc) :
    Nat.card (D.img K) = Kc.relIndex K := by
  set N := Subgroup.normalizer (uOfL22 T M : Set G) with hNdef
  set f := D.rho.domRestrict (K.subgroupOf N) with hf
  have hrange : f.range = D.img K := MonoidHom.domRestrict_range _ _
  have hker' : f.ker = (Kc.subgroupOf N).subgroupOf (K.subgroupOf N) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hxK : (x : G) ∈ K := x.2
    have h1 := hker (x : G) hxK
    have h2 : f x = D.rho (x : N) := rfl
    rw [h2]
    constructor
    · intro h3
      exact h1.1 ⟨(x : N).2, by simpa using h3⟩
    · intro h3
      obtain ⟨hxN, h4⟩ := h1.2 h3
      simpa using h4
  rw [← hrange, ← Subgroup.index_ker f, hker']
  exact Subgroup.relIndex_subgroupOf hKN

theorem rho_sub_π {x : G} (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) {u : G}
    (hu : u ∈ uOfL22 T M) :
    D.rho ⟨x, hxN⟩ (D.π u) - D.π u = D.π (x * u * x⁻¹ * u⁻¹) := by
  have h1 : x * u * x⁻¹ * u⁻¹ ∈ uOfL22 T M :=
    (uOfL22 T M).mul_mem (HatModel.conj_mem_uOfL22 hxN hu) ((uOfL22 T M).inv_mem hu)
  have h2 := D.π_mul _ h1 u hu
  have e : x * u * x⁻¹ * u⁻¹ * u = x * u * x⁻¹ := by group
  rw [e] at h2
  rw [D.rho_π _ hu, h2]
  abel

end HatModel

namespace Hyp1281Two

variable [Finite G]

theorem rho_eq_one_of_mem (h : Hyp1281Two G T M L) (D : HatModel T M) {u : G}
    (hu : u ∈ uOfL22 T M) (hN : u ∈ Subgroup.normalizer (uOfL22 T M : Set G)) :
    D.rho ⟨u, hN⟩ = 1 :=
  (D.rho_eq_one_iff ⟨u, hN⟩).2 fun _ hu' =>
    h.omegaOneCenter_le_centerOf_uOfL22 (h.commutator_mem_omegaOneCenter hu hu')

theorem img_sup_eq_of_le (h : Hyp1281Two G T M L) (D : HatModel T M) {K E : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (uOfL22 T M : Set G)) (hE : E ≤ uOfL22 T M) :
    D.img (K ⊔ E) = D.img K := by
  have hEN : E ≤ Subgroup.normalizer (uOfL22 T M : Set G) := hE.trans Subgroup.le_normalizer
  unfold HatModel.img
  rw [Subgroup.subgroupOf_sup hK hEN, Subgroup.map_sup]
  have : (E.subgroupOf (Subgroup.normalizer (uOfL22 T M : Set G))).map D.rho = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker]
    have := h.rho_eq_one_of_mem D (hE hx) x.2
    simpa using this
  rw [this, sup_bot_eq]

end Hyp1281Two

end CFSG.Quasithin
