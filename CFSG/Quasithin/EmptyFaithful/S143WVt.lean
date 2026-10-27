module

public import CFSG.Quasithin.EmptyFaithful.S143VBr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143W

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem quotSetting (h : Hyp1281Two G T M L) :
    QuotSetting (mcOf T) (uOfL22 T M) (quasithinOmegaOneCenter T) where
  S₂_le := fun z hz => (h.omegaOneCenter_le_centerOf_uOfL22 hz).1
  Sx_le := h.uOfL22_le_g1
  nS := fun x hx y hy => HatModel.conj_mem_uOfL22 (h.g1_le_normalizer_uOfL22 hx) hy
  nS₂ := fun x hx y hy => by
    have h1 : y * x = x * y := Subgroup.mem_centralizer_iff.mp hx y hy
    have e : x * y * x⁻¹ = y := by
      calc x * y * x⁻¹ = (y * x) * x⁻¹ := by rw [h1]
        _ = y := by group
    rw [e]
    exact hy
  abel := fun a ha b hb => h.commutator_mem_omegaOneCenter ha hb
  sq := fun a ha => by
    have := h.sq_mem_omegaOneCenter ha
    rwa [pow_two] at this

structure TildeModel (T M : Subgroup G) where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod 2) V]
  [finite : Finite V]
  c : ↥(uOfL22 T M) → V
  c_mul : ∀ u u' : ↥(uOfL22 T M), c (u * u') = c u + c u'
  c_surj : Function.Surjective c
  c_eq_iff : ∀ u u' : ↥(uOfL22 T M),
    c u = c u' ↔ (u : G)⁻¹ * (u' : G) ∈ quasithinOmegaOneCenter T
  ρ : ↥(mcOf T) →* (V ≃ₗ[ZMod 2] V)
  ρ_c : ∀ (x : ↥(mcOf T)) (u : ↥(uOfL22 T M)) (hxu : (x : G) * (u : G) * (x : G)⁻¹ ∈ uOfL22 T M),
    ρ x (c u) = c ⟨(x : G) * (u : G) * (x : G)⁻¹, hxu⟩

attribute [instance] TildeModel.addCommGroup TildeModel.module TildeModel.finite

@[expose] def addEquivToLin {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] (e : A ≃+ A) :
    A ≃ₗ[ZMod 2] A :=
  { (e.toAddMonoidHom).toZModLinearMap 2 with
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv }

theorem exists_tildeModel (h : Hyp1281Two G T M L) : Nonempty (TildeModel T M) := by
  classical
  have hQS := quotSetting h
  have hN : ((quasithinOmegaOneCenter T).subgroupOf (uOfL22 T M)).Normal := hQS.normal
  let _ : CommGroup (SecQuot (uOfL22 T M) (quasithinOmegaOneCenter T)) := hQS.quotCommGroup
  let _ : Module (ZMod 2) (Additive (SecQuot (uOfL22 T M) (quasithinOmegaOneCenter T))) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show (2 : ℕ) • x = 0
      rw [two_nsmul]
      exact Additive.toMul.injective (by simpa using hQS.quot_sq (Additive.toMul x)))
  have hfin : Finite (Additive (SecQuot (uOfL22 T M) (quasithinOmegaOneCenter T))) :=
    inferInstanceAs (Finite (SecQuot (uOfL22 T M) (quasithinOmegaOneCenter T)))
  refine ⟨{
    V := Additive (SecQuot (uOfL22 T M) (quasithinOmegaOneCenter T))
    finite := hfin
    c := fun u => Additive.ofMul (secMk (uOfL22 T M) (quasithinOmegaOneCenter T) u)
    c_mul := fun u u' => by
      show Additive.ofMul (secMk _ _ (u * u')) =
        Additive.ofMul (secMk _ _ u) + Additive.ofMul (secMk _ _ u')
      rw [map_mul]
      rfl
    c_surj := fun v => by
      obtain ⟨u, hu⟩ := secMk_surjective (A := uOfL22 T M) (B := quasithinOmegaOneCenter T)
        (Additive.toMul v)
      exact ⟨u, by simp [hu]⟩
    c_eq_iff := fun u u' => by
      show Additive.ofMul (secMk _ _ u) = Additive.ofMul (secMk _ _ u') ↔ _
      rw [Additive.ofMul.injective.eq_iff, secMk_eq_secMk_iff]
    ρ := {
      toFun := fun x => addEquivToLin (MulEquiv.toAdditive (hQS.convAct x))
      map_one' := by
        ext v
        show (MulEquiv.toAdditive (hQS.convAct 1)) v = v
        rw [map_one]
        rfl
      map_mul' := fun x y => by
        ext v
        show (MulEquiv.toAdditive (hQS.convAct (x * y))) v =
          (MulEquiv.toAdditive (hQS.convAct x)) ((MulEquiv.toAdditive (hQS.convAct y)) v)
        rw [map_mul]
        rfl }
    ρ_c := fun x u hxu => by
      show (MulEquiv.toAdditive (hQS.convAct x)) (Additive.ofMul (secMk _ _ u)) =
        Additive.ofMul (secMk _ _ ⟨(x : G) * (u : G) * (x : G)⁻¹, hxu⟩)
      exact congrArg Additive.ofMul (hQS.convAct_mk x u) }⟩

namespace TildeModel

variable (E : TildeModel T M)

omit [Finite G] in
theorem c_one : E.c 1 = 0 := by
  have := E.c_mul 1 1
  rw [mul_one] at this
  simpa using this

omit [Finite G] in
theorem c_eq_zero_iff (u : ↥(uOfL22 T M)) :
    E.c u = 0 ↔ (u : G) ∈ quasithinOmegaOneCenter T := by
  rw [← E.c_one, E.c_eq_iff]
  simp

omit [Finite G] in
noncomputable def rep (v : E.V) : ↥(uOfL22 T M) := Function.surjInv E.c_surj v

omit [Finite G] in
theorem c_rep (v : E.V) : E.c (E.rep v) = v := Function.surjInv_eq E.c_surj v

section Phi

variable (h : Hyp1281Two G T M L) (D : HatModel T M)

noncomputable def phiFun (v : E.V) : D.V := D.π ((E.rep v : ↥(uOfL22 T M)) : G)

include h in
theorem phiFun_eq {u : ↥(uOfL22 T M)} {v : E.V} (hv : E.c u = v) : E.phiFun D v = D.π (u : G) := by
  unfold phiFun
  have h1 : E.c (E.rep v) = E.c u := by rw [E.c_rep, hv]
  have h2 := (E.c_eq_iff _ _).mp h1
  exact (D.π_eq_iff _ (E.rep v).2 _ u.2).mpr (h.omegaOneCenter_le_centerOf_uOfL22 h2)

noncomputable def phi : E.V →ₗ[ZMod 2] D.V where
  toFun := E.phiFun D
  map_add' := fun v w => by
    have h1 : E.c (E.rep v * E.rep w) = v + w := by rw [E.c_mul, E.c_rep, E.c_rep]
    have hmul : ((E.rep v * E.rep w : ↥(uOfL22 T M)) : G) = (E.rep v : G) * (E.rep w : G) := rfl
    rw [E.phiFun_eq h D h1, hmul, D.π_mul _ (E.rep v).2 _ (E.rep w).2]
    unfold phiFun
    rfl
  map_smul' := fun c v => by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simp only [zero_smul, RingHom.id_apply]
      have h1 : E.c 1 = 0 := E.c_one
      rw [E.phiFun_eq h D h1]
      have : (((1 : ↥(uOfL22 T M)) : ↥(uOfL22 T M)) : G) = 1 := rfl
      rw [this, D.π_one]
    · simp only [one_smul, RingHom.id_apply]

theorem phi_c (u : ↥(uOfL22 T M)) : E.phi h D (E.c u) = D.π (u : G) := E.phiFun_eq h D rfl

theorem phi_surjective : Function.Surjective (E.phi h D) := by
  intro w
  obtain ⟨u, hu, rfl⟩ := D.π_surj w
  exact ⟨E.c ⟨u, hu⟩, E.phi_c h D ⟨u, hu⟩⟩

theorem phi_eq_zero_iff (v : E.V) :
    E.phi h D v = 0 ↔ ∃ u : ↥(uOfL22 T M), (u : G) ∈ centerOf (uOfL22 T M) ∧ E.c u = v := by
  constructor
  · intro hv
    refine ⟨E.rep v, ?_, E.c_rep v⟩
    have : D.π ((E.rep v : ↥(uOfL22 T M)) : G) = 0 := hv
    exact (D.π_eq_zero_iff (E.rep v).2).mp this
  · rintro ⟨u, hu, rfl⟩
    rw [E.phi_c h D, D.π_eq_zero_iff u.2]
    exact hu

theorem phi_ρ (x : ↥(mcOf T)) (v : E.V) :
    E.phi h D (E.ρ x v) = S143V.rhoH h D x (E.phi h D v) := by
  obtain ⟨u, rfl⟩ := E.c_surj v
  have hxN : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 x.2
  have hxu : (x : G) * (u : G) * (x : G)⁻¹ ∈ uOfL22 T M :=
    HatModel.conj_mem_uOfL22 hxN u.2
  rw [E.ρ_c x u hxu, E.phi_c h D, E.phi_c h D, S143V.rhoH_apply h D x hxN, D.rho_π ⟨x, hxN⟩ u.2]

end Phi

end TildeModel

end S143W

end CFSG.Quasithin
