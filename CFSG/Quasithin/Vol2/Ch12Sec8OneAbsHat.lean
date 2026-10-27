module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped commutatorElement

namespace L128A

namespace HatU

variable {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)

theorem π_one : D.π 1 = 0 := by
  have := D.π_mul 1 U.one_mem 1 U.one_mem
  simpa using this

theorem π_eq_zero_iff {a : G} (ha : a ∈ U) : D.π a = 0 ↔ a ∈ centerOf U := by
  rw [← π_one D, D.π_eq_iff a ha 1 U.one_mem]
  simp

theorem π_inv {a : G} (ha : a ∈ U) : D.π a⁻¹ = -D.π a := by
  have h := D.π_mul a ha a⁻¹ (U.inv_mem ha)
  rw [mul_inv_cancel, π_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem B_isAlt (v : D.V) : D.B v v = 0 := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  exact (D.B_spec u hu u hu).mpr (by group)

theorem zmod_two_eq_of_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b
  decide

theorem B_symm (v w : D.V) : D.B v w = D.B w v := by
  obtain ⟨a, ha, rfl⟩ := D.π_surj v
  obtain ⟨b, hb, rfl⟩ := D.π_surj w
  apply zmod_two_eq_of_iff
  rw [D.B_spec a ha b hb, D.B_spec b hb a ha]
  constructor
  · intro he
    have : a * b = b * a := by
      calc a * b = (a * b * a⁻¹ * b⁻¹) * b * a := by group
        _ = b * a := by rw [he]; group
    calc b * a * b⁻¹ * a⁻¹ = (a * b) * b⁻¹ * a⁻¹ := by rw [this]
      _ = 1 := by group
  · intro he
    have : b * a = a * b := by
      calc b * a = (b * a * b⁻¹ * a⁻¹) * a * b := by group
        _ = a * b := by rw [he]; group
    calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [this]
      _ = 1 := by group

theorem B_nondegenerate (v : D.V) (hv : ∀ w, D.B v w = 0) : v = 0 := by
  obtain ⟨a, ha, rfl⟩ := D.π_surj v
  rw [π_eq_zero_iff D ha]
  refine ⟨ha, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have h1 := (D.B_spec a ha u hu).mp (hv (D.π u))
  calc u * a = (a * u * a⁻¹ * u⁻¹)⁻¹ * a * u := by group
    _ = a * u := by rw [h1]; group

@[expose] def hatSub (A : Subgroup G) : Submodule (ZMod 2) D.V where
  carrier := {v | ∃ a ∈ A, a ∈ U ∧ D.π a = v}
  add_mem' := by
    rintro _ _ ⟨a, haA, haU, rfl⟩ ⟨b, hbA, hbU, rfl⟩
    exact ⟨a * b, A.mul_mem haA hbA, U.mul_mem haU hbU, D.π_mul a haU b hbU⟩
  zero_mem' := ⟨1, A.one_mem, U.one_mem, π_one D⟩
  smul_mem' := by
    intro c v hv
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]
      exact ⟨1, A.one_mem, U.one_mem, π_one D⟩
    · rw [one_smul]
      exact hv

theorem hat_eq_hatSub (A : Subgroup G) : D.hat A = hatSub D A := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ⟨haA, haU⟩, rfl⟩
    exact ⟨a, haA, haU, rfl⟩
  · rintro _ ⟨a, haA, haU, rfl⟩
    exact Submodule.subset_span ⟨a, ⟨haA, haU⟩, rfl⟩

theorem mem_hat {A : Subgroup G} {v : D.V} : v ∈ D.hat A ↔ ∃ a ∈ A, a ∈ U ∧ D.π a = v := by
  rw [hat_eq_hatSub]
  rfl

theorem π_mem_hat {A : Subgroup G} {a : G} (haA : a ∈ A) (haU : a ∈ U) : D.π a ∈ D.hat A :=
  (mem_hat D).2 ⟨a, haA, haU, rfl⟩

theorem hat_mono {A A' : Subgroup G} (hAA' : A ≤ A') : D.hat A ≤ D.hat A' := fun _ hv => by
  obtain ⟨a, ha, haU, hv⟩ := (mem_hat D).1 hv
  exact (mem_hat D).2 ⟨a, hAA' ha, haU, hv⟩

theorem conj_mem {x u : G} (hx : x ∈ Subgroup.normalizer (U : Set G)) (hu : u ∈ U) :
    x * u * x⁻¹ ∈ U :=
  (Subgroup.mem_normalizer_iff.mp hx u).mp hu

theorem B_rho (x : Subgroup.normalizer (U : Set G)) (v w : D.V) :
    D.B (D.ρ x v) (D.ρ x w) = D.B v w := by
  obtain ⟨a, ha, rfl⟩ := D.π_surj v
  obtain ⟨b, hb, rfl⟩ := D.π_surj w
  rw [D.ρ_π x a ha, D.ρ_π x b hb]
  have hcomm : ((x : G) * a * (x : G)⁻¹) * ((x : G) * b * (x : G)⁻¹) *
      ((x : G) * a * (x : G)⁻¹)⁻¹ * ((x : G) * b * (x : G)⁻¹)⁻¹ =
        (x : G) * (a * b * a⁻¹ * b⁻¹) * (x : G)⁻¹ := by group
  apply zmod_two_eq_of_iff
  rw [D.B_spec _ (conj_mem x.2 ha) _ (conj_mem x.2 hb), D.B_spec a ha b hb, hcomm]
  constructor
  · intro he
    have : (x : G)⁻¹ * ((x : G) * (a * b * a⁻¹ * b⁻¹) * (x : G)⁻¹) * x =
        a * b * a⁻¹ * b⁻¹ := by group
    rw [← this, he]
    group
  · intro he
    rw [he]
    group

theorem rho_eq_one_iff (x : Subgroup.normalizer (U : Set G)) :
    D.ρ x = 1 ↔ ∀ u ∈ U, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ centerOf U := by
  constructor
  · intro h1 u hu
    have h2 : D.ρ x (D.π u) = D.π u := by rw [h1]; rfl
    rw [D.ρ_π x u hu, D.π_eq_iff _ (conj_mem x.2 hu) _ hu] at h2
    have h3 := (centerOf U).inv_mem h2
    have hz : u⁻¹ * ((x : G) * u * (x : G)⁻¹) ∈ centerOf U := by
      have e : (((x : G) * u * (x : G)⁻¹)⁻¹ * u)⁻¹ = u⁻¹ * ((x : G) * u * (x : G)⁻¹) := by group
      rwa [e] at h3
    have hcomm := Subgroup.mem_centralizer_iff.mp hz.2 u hu
    have e2 : (x : G) * u * (x : G)⁻¹ * u⁻¹ = u⁻¹ * ((x : G) * u * (x : G)⁻¹) := by
      calc (x : G) * u * (x : G)⁻¹ * u⁻¹ = u * (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u⁻¹ := by
            group
        _ = (u⁻¹ * ((x : G) * u * (x : G)⁻¹)) * u * u⁻¹ := by rw [hcomm]
        _ = u⁻¹ * ((x : G) * u * (x : G)⁻¹) := by group
    rw [e2]
    exact hz
  · intro hall
    ext v
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    show D.ρ x (D.π u) = D.π u
    rw [D.ρ_π x u hu, D.π_eq_iff _ (conj_mem x.2 hu) _ hu]
    have hd' := (centerOf U).inv_mem (hall u hu)
    have hcomm := Subgroup.mem_centralizer_iff.mp hd'.2 u⁻¹ (U.inv_mem hu)
    have e : ((x : G) * u * (x : G)⁻¹)⁻¹ * u = ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ := by
      calc ((x : G) * u * (x : G)⁻¹)⁻¹ * u
          = u⁻¹ * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ * u := by group
        _ = (((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ * u⁻¹) * u := by rw [hcomm]
        _ = ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact hd'

theorem rho_sub_π {x : G} (hxN : x ∈ Subgroup.normalizer (U : Set G)) {u : G} (hu : u ∈ U) :
    D.ρ ⟨x, hxN⟩ (D.π u) - D.π u = D.π (x * u * x⁻¹ * u⁻¹) := by
  have h1 : x * u * x⁻¹ * u⁻¹ ∈ U := U.mul_mem (conj_mem hxN hu) (U.inv_mem hu)
  have h2 := D.π_mul _ h1 u hu
  have e : x * u * x⁻¹ * u⁻¹ * u = x * u * x⁻¹ := by group
  rw [e] at h2
  rw [D.ρ_π _ u hu, h2]
  abel

theorem mem_img {K : Subgroup G} {γ : D.V ≃ₗ[ZMod 2] D.V} :
    γ ∈ D.img K ↔ ∃ x ∈ K, ∃ hx : x ∈ Subgroup.normalizer (U : Set G), D.ρ ⟨x, hx⟩ = γ := by
  unfold HatModelU.img
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxK, rfl⟩
    exact ⟨x.1, hxK, x.2, rfl⟩
  · rintro ⟨x, hxK, hxN, rfl⟩
    exact ⟨⟨x, hxN⟩, hxK, rfl⟩

theorem rho_mem_img {K : Subgroup G} {x : G} (hxK : x ∈ K)
    (hxN : x ∈ Subgroup.normalizer (U : Set G)) : D.ρ ⟨x, hxN⟩ ∈ D.img K :=
  (mem_img D).2 ⟨x, hxK, hxN, rfl⟩

theorem card_img_eq_relIndex {K Kc : Subgroup G} (hKN : K ≤ Subgroup.normalizer (U : Set G))
    (hker : ∀ x ∈ K, (∃ hxN : x ∈ Subgroup.normalizer (U : Set G), D.ρ ⟨x, hxN⟩ = 1) ↔ x ∈ Kc) :
    Nat.card (D.img K) = Kc.relIndex K := by
  set N := Subgroup.normalizer (U : Set G) with hNdef
  set f := D.ρ.domRestrict (K.subgroupOf N) with hf
  have hrange : f.range = D.img K := MonoidHom.domRestrict_range _ _
  have hker' : f.ker = (Kc.subgroupOf N).subgroupOf (K.subgroupOf N) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have hxK : (x : G) ∈ K := x.2
    have h1 := hker (x : G) hxK
    have h2 : f x = D.ρ (x : N) := rfl
    rw [h2]
    constructor
    · intro h3
      exact h1.1 ⟨(x : N).2, by simpa using h3⟩
    · intro h3
      obtain ⟨hxN, h4⟩ := h1.2 h3
      simpa using h4
  rw [← hrange, ← Subgroup.index_ker f, hker']
  exact Subgroup.relIndex_subgroupOf hKN

theorem rho_eq_one_of_mem (hc : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U) {u : G}
    (hu : u ∈ U) (hN : u ∈ Subgroup.normalizer (U : Set G)) : D.ρ ⟨u, hN⟩ = 1 :=
  (rho_eq_one_iff D ⟨u, hN⟩).2 fun _ hu' => hc u hu _ hu'

theorem img_sup_eq_of_le (hc : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ centerOf U)
    {K E : Subgroup G} (hK : K ≤ Subgroup.normalizer (U : Set G)) (hE : E ≤ U) :
    D.img (K ⊔ E) = D.img K := by
  have hEN : E ≤ Subgroup.normalizer (U : Set G) := hE.trans Subgroup.le_normalizer
  unfold HatModelU.img
  rw [Subgroup.subgroupOf_sup hK hEN, Subgroup.map_sup]
  have : (E.subgroupOf (Subgroup.normalizer (U : Set G))).map D.ρ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker]
    have := rho_eq_one_of_mem D hc (hE hx) x.2
    simpa using this
  rw [this, sup_bot_eq]

end HatU

end L128A

end CFSG.Quasithin.H13
