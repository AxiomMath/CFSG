module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.G112A2

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem add_self_zmod2 (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

theorem vadd_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem symm_of_alt {B : LinearMap.BilinForm (ZMod 2) V} (halt : ∀ v, B v v = 0) (v w : V) :
    B v w = B w v := by
  have h := halt (v + w)
  simp only [map_add, LinearMap.add_apply, halt, zero_add, add_zero] at h
  calc B v w = B v w + (B w v + B v w) := by rw [h, add_zero]
    _ = B w v + (B v w + B v w) := by ring
    _ = B w v := by rw [add_self_zmod2, add_zero]

@[expose] noncomputable def sieg (B : LinearMap.BilinForm (ZMod 2) V) (halt : ∀ v, B v v = 0)
    (u w : V) (huw : B u w = 0) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofInvolutive
    { toFun := fun x => x + B x u • w + B x w • u
      map_add' := fun x y => by
        simp only [map_add, LinearMap.add_apply, add_smul]
        abel
      map_smul' := fun c x => by
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
    (fun x => by
      have hwu : B w u = 0 := by rw [symm_of_alt halt]; exact huw
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, halt, huw, hwu, mul_zero, add_zero, zero_smul]
      have key : ∀ a b : V, x + a + b + a + b = x := fun a b => by
        rw [show x + a + b + a + b = x + (a + a) + (b + b) by abel, vadd_self, vadd_self,
          add_zero, add_zero]
      exact key _ _)

theorem sieg_apply (B : LinearMap.BilinForm (ZMod 2) V) (halt : ∀ v, B v v = 0) (u w : V)
    (huw : B u w = 0) (x : V) : sieg B halt u w huw x = x + B x u • w + B x w • u := rfl


theorem two_eq_zero_zmod2 : (2 : ZMod 2) = 0 := rfl

theorem sieg_mem_orth {B : LinearMap.BilinForm (ZMod 2) V} (halt : ∀ v, B v v = 0)
    {q : V → ZMod 2} (hqB : ∀ v w, q (v + w) = q v + q w + B v w)
    (hqs : ∀ (c : ZMod 2) v, q (c • v) = c * c * q v) {u w : V} (huw : B u w = 0)
    (hu : q u = 0) (hw : q w = 0) : sieg B halt u w huw ∈ orthogonalSubgroupOf q := by
  intro x
  have hwu : B w u = 0 := by rw [symm_of_alt halt]; exact huw
  show q (sieg B halt u w huw x) = q x
  rw [sieg_apply, hqB, hqB, hqs, hqs, hu, hw]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, huw, hwu,
    halt, mul_zero, add_zero]
  linear_combination (B x u * B x w) * two_eq_zero_zmod2


theorem exists_dual {B : LinearMap.BilinForm (ZMod 2) V} (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    {p r : V} (hp : p ≠ 0) (hpr : p + r ≠ 0) : ∃ y, B p y = 1 ∧ B r y = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, B p y ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (hnd p h)
  obtain ⟨z, hz⟩ : ∃ z, B (p + r) z ≠ 0 := by
    by_contra h
    push Not at h
    exact hpr (hnd _ h)
  have hy1 : B p y = 1 := (zmod2_cases _).resolve_left hy
  have hz1 : B p z + B r z = 1 := by
    have := (zmod2_cases (B (p + r) z)).resolve_left hz
    simpa [map_add] using this
  rcases zmod2_cases (B r y) with h | h
  · exact ⟨y, hy1, h⟩
  rcases zmod2_cases (B p z) with h' | h'
  · have hrz : B r z = 1 := by rw [h', zero_add] at hz1; exact hz1
    refine ⟨y + z, ?_, ?_⟩
    · rw [map_add, hy1, h', add_zero]
    · rw [map_add, h, hrz]
      rfl
  · have hrz : B r z = 0 := by
      rw [h'] at hz1
      linear_combination hz1
    exact ⟨z, h', hrz⟩

theorem g112ConclA2_concl5 (B : LinearMap.BilinForm (ZMod 2) V)
    (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (v₁ : V) (W : Submodule (ZMod 2) V)
    (X X₀ : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : G111Hyp B Γ v₁ W X X₀) (h5 : G112Concl5 B Γ) :
    ∀ t ∈ X, Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2 →
      v₁ ∈ LinearMap.range (t.toLinearMap - LinearMap.id) → (∀ v, B v (t v) = 0) →
      ∃ γ ∈ Γ, (∀ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id),
        γ w ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) ∧ γ v₁ ≠ v₁ := by
  classical
  obtain ⟨-, q, hqB, hqs, -, hle, hidx⟩ := h5
  have halt := hH.alt
  intro t ht hr hv1 ha2
  set R := LinearMap.range (t.toLinearMap - LinearMap.id) with hR
  have htO : t ∈ orthogonalSubgroupOf q := hle (hH.X_le ht)
  have hneg : ∀ v : V, -v = v := fun v => neg_eq_of_add_eq_zero_right (vadd_self v)
  have hqR : ∀ x ∈ R, q x = 0 := by
    rintro _ ⟨v, rfl⟩
    have h1 : (t.toLinearMap - LinearMap.id : V →ₗ[ZMod 2] V) v = t v + v := by
      simp [sub_eq_add_neg, hneg]
    rw [h1, hqB, htO v, symm_of_alt halt, ha2, add_zero, add_self_zmod2]
  have hBR : ∀ x ∈ R, ∀ y ∈ R, B x y = 0 := fun x hx y hy => by
    have := hqB x y
    rw [hqR x hx, hqR y hy, hqR _ (R.add_mem hx hy)] at this
    simpa using this.symm
  have hv0 := hH.point
  obtain ⟨w, hwR, hw0, hwv⟩ : ∃ w ∈ R, w ≠ 0 ∧ w ≠ v₁ := by
    by_contra h
    push Not at h
    have hle' : R ≤ Submodule.span (ZMod 2) {v₁} := by
      intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [h x hx hx0]
        exact Submodule.mem_span_singleton_self _
    have := Submodule.finrank_mono hle'
    rw [hr, finrank_span_singleton hv0] at this
    omega
  have hvw : v₁ + w ≠ 0 := fun h =>
    hwv ((neg_eq_of_add_eq_zero_right h).symm.trans (hneg v₁))
  have hwv' : w + v₁ ≠ 0 := by rwa [add_comm]
  obtain ⟨y1, hy1a, hy1b⟩ := exists_dual hH.nondegenerate hv0 hvw
  obtain ⟨y2, hy2a, hy2b⟩ := exists_dual hH.nondegenerate hw0 hwv'
  set u1 := y1 + q y1 • v₁ with hu1
  set u2 := y2 + q y2 • w with hu2
  have hBvw := hBR v₁ hv1 w hwR
  have hBwv := hBR w hwR v₁ hv1
  have hqu1 : q u1 = 0 := by
    rw [hu1, hqB, hqs, hqR _ hv1, map_smul, symm_of_alt halt y1, hy1a]
    simp only [mul_zero, add_zero, smul_eq_mul, mul_one]
    exact add_self_zmod2 _
  have hqu2 : q u2 = 0 := by
    rw [hu2, hqB, hqs, hqR _ hwR, map_smul, symm_of_alt halt y2, hy2a]
    simp only [mul_zero, add_zero, smul_eq_mul, mul_one]
    exact add_self_zmod2 _
  have hv1u1 : B v₁ u1 = 1 := by simp [hu1, map_add, map_smul, halt, hy1a]
  have hwu1 : B w u1 = 0 := by simp [hu1, map_add, map_smul, hy1b, hBwv]
  have hwu2 : B w u2 = 1 := by simp [hu2, map_add, map_smul, halt, hy2a]
  have hv1u2 : B v₁ u2 = 0 := by simp [hu2, map_add, map_smul, hy2b, hBvw]
  have hu1w : B u1 w = 0 := by rw [symm_of_alt halt]; exact hwu1
  have hu2v : B u2 v₁ = 0 := by rw [symm_of_alt halt]; exact hv1u2
  set ρ1 := sieg B halt u1 w hu1w with hρ1
  set ρ2 := sieg B halt u2 v₁ hu2v with hρ2
  have hρ1O : ρ1 ∈ orthogonalSubgroupOf q := sieg_mem_orth halt hqB hqs hu1w hqu1 (hqR w hwR)
  have hρ2O : ρ2 ∈ orthogonalSubgroupOf q := sieg_mem_orth halt hqB hqs hu2v hqu2 (hqR v₁ hv1)
  have hρR : ∀ (u z : V) (huz : B u z = 0), z ∈ R → ∀ x ∈ R, sieg B halt u z huz x ∈ R := by
    intro u z huz hz x hx
    rw [sieg_apply, hBR x hx z hz, zero_smul, add_zero]
    exact R.add_mem hx (R.smul_mem _ hz)
  have hρ1v : ρ1 v₁ = v₁ + w := by
    rw [hρ1, sieg_apply, hv1u1, hBvw, one_smul, zero_smul, add_zero]
  have hρ1w : ρ1 w = w := by
    rw [hρ1, sieg_apply, hwu1, halt, zero_smul, zero_smul, add_zero, add_zero]
  have hρ2v : ρ2 v₁ = v₁ := by
    rw [hρ2, sieg_apply, hv1u2, halt, zero_smul, zero_smul, add_zero, add_zero]
  have hρ2w : ρ2 w = w + v₁ := by
    rw [hρ2, sieg_apply, hwu2, hBwv, one_smul, zero_smul, add_zero]
  set g := ρ1 * ρ2 with hg
  have hgO : g ∈ orthogonalSubgroupOf q := Subgroup.mul_mem _ hρ1O hρ2O
  have hgR : ∀ x ∈ R, g x ∈ R := fun x hx =>
    hρR _ _ hu1w hwR _ (hρR _ _ hu2v hv1 x hx)
  have hg2 : (g * g) v₁ = w := by
    show ρ1 (ρ2 (ρ1 (ρ2 v₁))) = w
    rw [hρ2v, hρ1v, map_add, hρ2v, hρ2w,
      show v₁ + (w + v₁) = w by rw [add_comm w, ← add_assoc, vadd_self, zero_add], hρ1w]
  have hγ : g * g ∈ Γ := by
    haveI : Finite (V ≃ₗ[ZMod 2] V) :=
      Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
        (fun a b h => LinearEquiv.ext (congrFun h))
    set H := Γ.subgroupOf (orthogonalSubgroupOf q) with hH'
    have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle2 : H.index ≤ 2 := hidx
    have hmem : (⟨g, hgO⟩ * ⟨g, hgO⟩ : ↥(orthogonalSubgroupOf q)) ∈ H := by
      rcases (show H.index = 1 ∨ H.index = 2 by omega) with h1 | h2
      · rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      · exact Subgroup.mul_self_mem_of_index_two h2 _
    exact Subgroup.mem_subgroupOf.mp hmem
  exact ⟨g * g, hγ, fun x hx => hgR _ (hgR x hx), by rw [hg2]; exact hwv⟩

end CFSG.Quasithin.G112A2
