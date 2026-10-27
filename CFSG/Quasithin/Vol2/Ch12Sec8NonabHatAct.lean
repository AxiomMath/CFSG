module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {T M L : Subgroup G}

theorem zmod_two_eq_of_iff {a b : ZMod 2} (h : a = 0 ↔ b = 0) : a = b := by
  revert a b
  decide

namespace HatModel

variable (D : HatModel T M)

noncomputable def rep (v : D.V) : G := Classical.choose (D.π_surj v)

theorem rep_mem (v : D.V) : D.rep v ∈ uOfL22 T M := (Classical.choose_spec (D.π_surj v)).1

theorem π_rep (v : D.V) : D.π (D.rep v) = v := (Classical.choose_spec (D.π_surj v)).2

omit D in
theorem conj_mem_uOfL22 {x u : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hu : u ∈ uOfL22 T M) : x * u * x⁻¹ ∈ uOfL22 T M :=
  (Subgroup.mem_normalizer_iff.mp hx u).mp hu

noncomputable def actFun (x : G) (v : D.V) : D.V := D.π (x * D.rep v * x⁻¹)

theorem actFun_π {x u : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hu : u ∈ uOfL22 T M) : D.actFun x (D.π u) = D.π (x * u * x⁻¹) := by
  unfold actFun
  have h1 := (D.π_eq_iff _ (D.rep_mem (D.π u)) u hu).mp (D.π_rep (D.π u))
  rw [D.π_eq_iff _ (conj_mem_uOfL22 hx (D.rep_mem _)) _ (conj_mem_uOfL22 hx hu)]
  have e : (x * D.rep (D.π u) * x⁻¹)⁻¹ * (x * u * x⁻¹) =
      x * ((D.rep (D.π u))⁻¹ * u) * x⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centerOf _ hx) _).mp h1

noncomputable def act {x : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) :
    D.V →ₗ[ZMod 2] D.V where
  toFun := D.actFun x
  map_add' := by
    intro v w
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    obtain ⟨u', hu', rfl⟩ := D.π_surj w
    rw [← D.π_mul u hu u' hu', D.actFun_π hx hu, D.actFun_π hx hu',
      D.actFun_π hx ((uOfL22 T M).mul_mem hu hu')]
    have e : x * (u * u') * x⁻¹ = (x * u * x⁻¹) * (x * u' * x⁻¹) := by group
    rw [e, D.π_mul _ (conj_mem_uOfL22 hx hu) _ (conj_mem_uOfL22 hx hu')]
  map_smul' := by
    intro c v
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      rw [← D.π_one, D.actFun_π hx (uOfL22 T M).one_mem]
      simp [D.π_one]
    · simp only [one_smul, RingHom.id_apply]

theorem act_π {x u : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hu : u ∈ uOfL22 T M) : D.act hx (D.π u) = D.π (x * u * x⁻¹) := D.actFun_π hx hu

theorem act_act {x y : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hy : y ∈ Subgroup.normalizer (uOfL22 T M : Set G)) (v : D.V) :
    D.act hx (D.act hy v) = D.act ((Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem hx hy) v := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  rw [D.act_π hy hu, D.act_π hx (conj_mem_uOfL22 hy hu),
    D.act_π ((Subgroup.normalizer (uOfL22 T M : Set G)).mul_mem hx hy) hu]
  congr 1
  group

theorem act_one (v : D.V) :
    D.act (Subgroup.one_mem (Subgroup.normalizer (uOfL22 T M : Set G))) v = v := by
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  rw [D.act_π _ hu]
  congr 1
  group

theorem act_congr {x y : G} (hxy : x = y) (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hy : y ∈ Subgroup.normalizer (uOfL22 T M : Set G)) (v : D.V) :
    D.act hx v = D.act hy v := by
  subst hxy
  rfl

theorem act_mul_inv {x : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) (v : D.V) :
    D.act hx (D.act ((Subgroup.normalizer (uOfL22 T M : Set G)).inv_mem hx) v) = v := by
  rw [D.act_act, D.act_congr (mul_inv_cancel x) _ (Subgroup.one_mem _), D.act_one]

theorem act_inv_mul {x : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) (v : D.V) :
    D.act ((Subgroup.normalizer (uOfL22 T M : Set G)).inv_mem hx) (D.act hx v) = v := by
  rw [D.act_act, D.act_congr (inv_mul_cancel x) _ (Subgroup.one_mem _), D.act_one]

noncomputable def actEquiv {x : G} (hx : x ∈ Subgroup.normalizer (uOfL22 T M : Set G)) :
    D.V ≃ₗ[ZMod 2] D.V :=
  LinearEquiv.ofLinearMap (D.act hx)
    (D.act ((Subgroup.normalizer (uOfL22 T M : Set G)).inv_mem hx))
    (by
      ext v
      exact D.act_mul_inv hx v)
    (by
      ext v
      exact D.act_inv_mul hx v)

noncomputable def rho : Subgroup.normalizer (uOfL22 T M : Set G) →* (D.V ≃ₗ[ZMod 2] D.V) where
  toFun x := D.actEquiv x.2
  map_one' := by
    ext v
    exact D.act_one v
  map_mul' := fun x y => by
    ext v
    exact (D.act_act x.2 y.2 v).symm

theorem rho_π (x : Subgroup.normalizer (uOfL22 T M : Set G)) {u : G} (hu : u ∈ uOfL22 T M) :
    D.rho x (D.π u) = D.π (x * u * (x : G)⁻¹) := D.act_π x.2 hu

theorem B_rho (x : Subgroup.normalizer (uOfL22 T M : Set G)) (v w : D.V) :
    D.B (D.rho x v) (D.rho x w) = D.B v w := by
  obtain ⟨a, ha, rfl⟩ := D.π_surj v
  obtain ⟨b, hb, rfl⟩ := D.π_surj w
  rw [D.rho_π x ha, D.rho_π x hb]
  have hcomm : ((x : G) * a * (x : G)⁻¹) * ((x : G) * b * (x : G)⁻¹) * ((x : G) * a * (x : G)⁻¹)⁻¹ *
      ((x : G) * b * (x : G)⁻¹)⁻¹ = (x : G) * (a * b * a⁻¹ * b⁻¹) * (x : G)⁻¹ := by group
  apply zmod_two_eq_of_iff
  rw [D.B_spec _ (conj_mem_uOfL22 x.2 ha) _ (conj_mem_uOfL22 x.2 hb), D.B_spec a ha b hb, hcomm]
  constructor
  · intro he
    have : (x : G)⁻¹ * ((x : G) * (a * b * a⁻¹ * b⁻¹) * (x : G)⁻¹) * x = a * b * a⁻¹ * b⁻¹ := by
      group
    rw [← this, he]
    group
  · intro he
    rw [he]
    group

theorem rho_eq_one_iff (x : Subgroup.normalizer (uOfL22 T M : Set G)) :
    D.rho x = 1 ↔ ∀ u ∈ uOfL22 T M, (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ centerOf (uOfL22 T M) := by
  constructor
  · intro h1 u hu
    have h2 : D.rho x (D.π u) = D.π u := by rw [h1]; rfl
    rw [D.rho_π x hu, D.π_eq_iff _ (conj_mem_uOfL22 x.2 hu) _ hu] at h2
    obtain ⟨z, hzdef⟩ : ∃ z, z = u⁻¹ * ((x : G) * u * (x : G)⁻¹) := ⟨_, rfl⟩
    have hz : z ∈ centerOf (uOfL22 T M) := by
      rw [hzdef]
      have h3 := (centerOf (uOfL22 T M)).inv_mem h2
      have e : (((x : G) * u * (x : G)⁻¹)⁻¹ * u)⁻¹ = u⁻¹ * ((x : G) * u * (x : G)⁻¹) := by group
      rwa [e] at h3
    have e2 : (x : G) * u * (x : G)⁻¹ * u⁻¹ = u * z * u⁻¹ := by
      rw [hzdef]
      group
    rw [e2]
    have hcomm := Subgroup.mem_centralizer_iff.mp hz.2 u hu
    have e3 : u * z * u⁻¹ = z := by
      rw [hcomm]
      group
    rw [e3]
    exact hz
  · intro hall
    ext v
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    show D.rho x (D.π u) = D.π u
    rw [D.rho_π x hu, D.π_eq_iff _ (conj_mem_uOfL22 x.2 hu) _ hu]
    have hd := hall u hu
    have hd' := (centerOf (uOfL22 T M)).inv_mem hd
    have hcomm := Subgroup.mem_centralizer_iff.mp hd'.2 u⁻¹ ((uOfL22 T M).inv_mem hu)
    have e : ((x : G) * u * (x : G)⁻¹)⁻¹ * u = ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ := by
      have e1 : ((x : G) * u * (x : G)⁻¹)⁻¹ * u =
          u⁻¹ * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ * u := by group
      rw [e1]
      calc u⁻¹ * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ * u
          = (((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ * u⁻¹) * u := by rw [hcomm]
        _ = ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact hd'

end HatModel

end CFSG.Quasithin
