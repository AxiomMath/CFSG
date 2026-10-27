module

public import CFSG.Quasithin.EmptyFaithful.S143WVt

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G]

structure TildeModel619 (H U Z : Subgroup G) where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod 2) V]
  [finite : Finite V]
  c : ↥U → V
  c_mul : ∀ u u' : ↥U, c (u * u') = c u + c u'
  c_surj : Function.Surjective c
  c_eq_iff : ∀ u u' : ↥U, c u = c u' ↔ (u : G)⁻¹ * (u' : G) ∈ Z
  ρ : ↥H →* (V ≃ₗ[ZMod 2] V)
  ρ_c : ∀ (x : ↥H) (u : ↥U) (hxu : (x : G) * (u : G) * (x : G)⁻¹ ∈ U),
    ρ x (c u) = c ⟨(x : G) * (u : G) * (x : G)⁻¹, hxu⟩

attribute [instance] TildeModel619.addCommGroup TildeModel619.module TildeModel619.finite

theorem exists_tildeModel619 [Finite G] {H U Z : Subgroup G} (hQS : QuotSetting H U Z) :
    Nonempty (TildeModel619 H U Z) := by
  classical
  have hN : (Z.subgroupOf U).Normal := hQS.normal
  let _ : CommGroup (SecQuot U Z) := hQS.quotCommGroup
  let _ : Module (ZMod 2) (Additive (SecQuot U Z)) :=
    AddCommGroup.zmodModule (n := 2) (fun x => by
      show (2 : ℕ) • x = 0
      rw [two_nsmul]
      exact Additive.toMul.injective (by simpa using hQS.quot_sq (Additive.toMul x)))
  have hfin : Finite (Additive (SecQuot U Z)) := inferInstanceAs (Finite (SecQuot U Z))
  refine ⟨{
    V := Additive (SecQuot U Z)
    finite := hfin
    c := fun u => Additive.ofMul (secMk U Z u)
    c_mul := fun u u' => by
      show Additive.ofMul (secMk _ _ (u * u')) =
        Additive.ofMul (secMk _ _ u) + Additive.ofMul (secMk _ _ u')
      rw [map_mul]
      rfl
    c_surj := fun v => by
      obtain ⟨u, hu⟩ := secMk_surjective (A := U) (B := Z) (Additive.toMul v)
      exact ⟨u, by simp [hu]⟩
    c_eq_iff := fun u u' => by
      show Additive.ofMul (secMk _ _ u) = Additive.ofMul (secMk _ _ u') ↔ _
      rw [Additive.ofMul.injective.eq_iff, secMk_eq_secMk_iff]
    ρ := {
      toFun := fun x => S143W.addEquivToLin (MulEquiv.toAdditive (hQS.convAct x))
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

namespace TildeModel619

variable {H U Z : Subgroup G} (E : TildeModel619 H U Z)

theorem c_one : E.c 1 = 0 := by
  have := E.c_mul 1 1
  rw [mul_one] at this
  simpa using this

theorem c_eq_zero_iff (u : ↥U) : E.c u = 0 ↔ (u : G) ∈ Z := by
  rw [← E.c_one, E.c_eq_iff]
  simp

theorem c_inv (u : ↥U) : E.c u⁻¹ = -E.c u := by
  have h := E.c_mul u⁻¹ u
  rw [inv_mul_cancel, E.c_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

noncomputable def rep (v : E.V) : ↥U := Function.surjInv E.c_surj v

theorem c_rep (v : E.V) : E.c (E.rep v) = v := Function.surjInv_eq E.c_surj v

theorem span_orbit_eq_top {H S Z : Subgroup G} (E : TildeModel619 H (conjClosure S H) Z)
    (vv : E.V) (hS : ∀ s : ↥(conjClosure S H), (s : G) ∈ S → E.c s = 0 ∨ E.c s = vv) :
    Submodule.span (ZMod 2) (Set.range fun x : ↥H => E.ρ x vv) = ⊤ := by
  set Sp := Submodule.span (ZMod 2) (Set.range fun x : ↥H => E.ρ x vv) with hSp
  have key : ∀ x (hx : x ∈ Subgroup.closure {y | ∃ k ∈ H, ∃ z ∈ S, k * z * k⁻¹ = y}),
      ∃ hxU : x ∈ conjClosure S H, E.c ⟨x, hxU⟩ ∈ Sp := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hx
      have hzU : z ∈ conjClosure S H := le_conjClosure _ _ hz
      have hxU : k * z * k⁻¹ ∈ conjClosure S H := mem_conjClosure hk hz
      refine ⟨hxU, ?_⟩
      rw [← E.ρ_c ⟨k, hk⟩ ⟨z, hzU⟩ hxU]
      rcases hS ⟨z, hzU⟩ hz with h0 | h0
      · rw [h0, map_zero]
        exact Sp.zero_mem
      · rw [h0]
        exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
    | one =>
      refine ⟨(conjClosure S H).one_mem, ?_⟩
      have : (⟨1, (conjClosure S H).one_mem⟩ : ↥(conjClosure S H)) = 1 := rfl
      rw [this, E.c_one]
      exact Sp.zero_mem
    | mul x y hx hy ihx ihy =>
      obtain ⟨hxU, hxS⟩ := ihx
      obtain ⟨hyU, hyS⟩ := ihy
      refine ⟨(conjClosure S H).mul_mem hxU hyU, ?_⟩
      have e : (⟨x * y, (conjClosure S H).mul_mem hxU hyU⟩ : ↥(conjClosure S H)) =
          ⟨x, hxU⟩ * ⟨y, hyU⟩ := rfl
      rw [e, E.c_mul]
      exact Sp.add_mem hxS hyS
    | inv x hx ih =>
      obtain ⟨hxU, hxS⟩ := ih
      refine ⟨(conjClosure S H).inv_mem hxU, ?_⟩
      have e : (⟨x⁻¹, (conjClosure S H).inv_mem hxU⟩ : ↥(conjClosure S H)) = ⟨x, hxU⟩⁻¹ := rfl
      rw [e, E.c_inv]
      exact Sp.neg_mem hxS
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, rfl⟩ := E.c_surj v
  exact (key (u : G) u.2).2

section Phi

variable {A : Type} [AddCommGroup A] [Module (ZMod 2) A] (β : ↥U →* Multiplicative A)
  (hβ : ∀ u : ↥U, (u : G) ∈ Z → β u = 1)

omit [Module (ZMod 2) A] in
include hβ in
theorem β_eq_of_c_eq {u u' : ↥U} (h : E.c u = E.c u') : β u = β u' := by
  have h1 := hβ (u⁻¹ * u') ((E.c_eq_iff u u').mp h)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

noncomputable def phi : E.V →ₗ[ZMod 2] A where
  toFun v := Multiplicative.toAdd (β (E.rep v))
  map_add' v w := by
    have h1 : E.c (E.rep (v + w)) = E.c (E.rep v * E.rep w) := by
      rw [E.c_mul, E.c_rep, E.c_rep, E.c_rep]
    rw [E.β_eq_of_c_eq β hβ h1, map_mul, toAdd_mul]
  map_smul' c v := by
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · have h1 : E.c (E.rep 0) = E.c 1 := by rw [E.c_rep, E.c_one]
      simp only [RingHom.id_apply, zero_smul]
      rw [E.β_eq_of_c_eq β hβ h1, map_one, toAdd_one]
    · simp only [one_smul, RingHom.id_apply]

theorem phi_c (u : ↥U) : E.phi β hβ (E.c u) = Multiplicative.toAdd (β u) := by
  show Multiplicative.toAdd (β (E.rep (E.c u))) = _
  rw [E.β_eq_of_c_eq β hβ (E.c_rep (E.c u))]

theorem phi_surjective (hs : Function.Surjective β) : Function.Surjective (E.phi β hβ) := by
  intro a
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd a)
  exact ⟨E.c u, by rw [E.phi_c β hβ, hu, toAdd_ofAdd]⟩

theorem phi_eq_zero_iff {ZU : Subgroup G} (hk : ∀ u : ↥U, β u = 1 ↔ (u : G) ∈ ZU) (v : E.V) :
    E.phi β hβ v = 0 ↔ ∃ u : ↥U, (u : G) ∈ ZU ∧ E.c u = v := by
  constructor
  · intro hv
    refine ⟨E.rep v, (hk _).mp ?_, E.c_rep v⟩
    have : Multiplicative.toAdd (β (E.rep v)) = 0 := hv
    exact Multiplicative.toAdd.injective (by rw [this, toAdd_one])
  · rintro ⟨u, hu, rfl⟩
    rw [E.phi_c β hβ, (hk u).mpr hu, toAdd_one]

theorem phi_ρ (ρ' : ↥H →* (A ≃ₗ[ZMod 2] A)) (hHN : ∀ x ∈ H, ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (heq : ∀ (h : ↥H) (u v : ↥U), (v : G) = h * u * (h : G)⁻¹ →
      Multiplicative.toAdd (β v) = ρ' h (Multiplicative.toAdd (β u)))
    (x : ↥H) (v : E.V) : E.phi β hβ (E.ρ x v) = ρ' x (E.phi β hβ v) := by
  obtain ⟨u, rfl⟩ := E.c_surj v
  have hxu := hHN x x.2 u u.2
  rw [E.ρ_c x u hxu, E.phi_c β hβ, E.phi_c β hβ]
  exact heq x u _ rfl

end Phi

end TildeModel619

end CFSG.Quasithin.H13
