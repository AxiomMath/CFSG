module

public import CFSG.RankThree.GroupTheory.SteinbergCDBinaryPrimeActionDegree

public section

namespace CFSG.RankThree.GroupTheory

open Module

theorem central_prime_actor_scalar_field_degree {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {L : Type*} [Group L] [Finite L] {b : L} (hb : b ∈ Subgroup.center L) (hbord : orderOf b = p)
    {V : Type*} [AddCommGroup V] [Module (ZMod q) V] [Module.Finite (ZMod q) V]
    [Nontrivial V] (ρ : L →* LinearMap.GeneralLinearGroup (ZMod q) V)
    (hirr : ∀ W : Submodule (ZMod q) V,
      (∀ g : L, ∀ v ∈ W, (ρ g : V →ₗ[ZMod q] V) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hT : ρ b ≠ 1) (E : Subalgebra (ZMod q) (Module.End (ZMod q) V))
    (hEdef : E = Algebra.adjoin (ZMod q) {((ρ b : LinearMap.GeneralLinearGroup (ZMod q) V) :
        Module.End (ZMod q) V)}) :
    ∃ (hE : IsField E) (e : ℕ), Nat.card E = q ^ e ∧
      IsLeast {j : ℕ | 0 < j ∧ q ^ j ≡ 1 [MOD p]} e ∧
      (letI : Field E := hE.toField;
        letI : Module E V := Module.compHom V (E.val : E →+* Module.End (ZMod q) V);
        (∀ (g : L) (a : E) (v : V),
          (ρ g : V →ₗ[ZMod q] V) (a • v) = a • (ρ g : V →ₗ[ZMod q] V) v) ∧
        (∀ W : Submodule E V,
          (∀ g : L, ∀ v ∈ W, (ρ g : V →ₗ[ZMod q] V) v ∈ W) → W = ⊥ ∨ W = ⊤) ∧
        ∀ g : L, ∃ W : Submodule E V, (W : Set V) = {v | (ρ g : V →ₗ[ZMod q] V) v = v} ∧
          finrank (ZMod q) (LinearMap.ker ((ρ g : V →ₗ[ZMod q] V) - 1)) = e * finrank E W) ∧
      (p = 5 → (q % 5 = 2 ∨ q % 5 = 3) → e = 4) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact p.Prime := ⟨hp⟩
  subst hEdef
  set E := Algebra.adjoin (ZMod q) {((ρ b : LinearMap.GeneralLinearGroup (ZMod q) V) :
    Module.End (ZMod q) V)} with hEdef
  set T : Module.End (ZMod q) V :=
    ((ρ b : LinearMap.GeneralLinearGroup (ZMod q) V) : Module.End (ZMod q) V) with hTdef
  have : Finite V := Module.finite_of_finite (ZMod q)
  have : Finite (Module.End (ZMod q) V) := Module.finite_of_finite (ZMod q)
  have : Finite E := Subtype.finite
  have hcommL : ∀ a ∈ E, ∀ g : L,
      a * (ρ g : V →ₗ[ZMod q] V) = (ρ g : V →ₗ[ZMod q] V) * a := by
    intro a ha g
    have hTg : Commute ((ρ g : LinearMap.GeneralLinearGroup (ZMod q) V) :
        Module.End (ZMod q) V) T := by
      change ((ρ g : LinearMap.GeneralLinearGroup (ZMod q) V) : Module.End (ZMod q) V) * T =
        T * ((ρ g : LinearMap.GeneralLinearGroup (ZMod q) V) : Module.End (ZMod q) V)
      rw [hTdef, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        Subgroup.mem_center_iff.mp hb g]
    exact (Algebra.commute_of_mem_adjoin_singleton_of_commute ha hTg).symm.eq
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hy
      (Algebra.commute_of_mem_adjoin_singleton_of_commute hx (Commute.refl T)).symm).eq
  have hinj : ∀ a ∈ E, a ≠ 0 → LinearMap.ker a = ⊥ := by
    intro a ha ha0
    rcases hirr (LinearMap.ker a) (fun g v hv => by
      rw [LinearMap.mem_ker] at hv ⊢
      have h := congrArg (fun f : Module.End (ZMod q) V => f v) (hcommL a ha g)
      simp only [Module.End.mul_apply] at h
      rw [h, hv, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) ha0
  have hE : IsField E := by
    refine ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩,
      fun x y => Subtype.ext (hcommE x x.2 y y.2), fun {a} ha => ?_⟩
    have ha0 : (a : Module.End (ZMod q) V) ≠ 0 := fun h => ha (Subtype.ext h)
    have hk := hinj a a.2 ha0
    have hmulinj : Function.Injective (fun x : E => a * x) := by
      intro x y hxy
      have h1 : (a : Module.End (ZMod q) V) * ((x : Module.End (ZMod q) V) - y) = 0 := by
        have h := congrArg Subtype.val hxy
        simp only [Subalgebra.coe_mul] at h
        rw [mul_sub, h, sub_self]
      apply Subtype.ext
      rw [← sub_eq_zero]
      refine LinearMap.ext fun v => ?_
      have h2 : (a : Module.End (ZMod q) V) (((x : Module.End (ZMod q) V) - y) v) = 0 := by
        rw [← Module.End.mul_apply, h1]
        rfl
      exact (LinearMap.ker_eq_bot'.mp hk) _ h2
    obtain ⟨c, hc⟩ := (Finite.injective_iff_surjective.mp hmulinj) 1
    exact ⟨c, hc⟩
  let : Field E := hE.toField
  set n := finrank (ZMod q) E with hn
  have hEcard : Nat.card E = q ^ n := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod q), Nat.card_zmod]
  have hn1 : 1 ≤ n := Module.finrank_pos
  set τ : E := ⟨T, Algebra.self_mem_adjoin_singleton _ T⟩ with hτ
  have hτp : τ ^ p = 1 := by
    apply Subtype.ext
    change T ^ p = 1
    rw [hTdef, ← Units.val_pow_eq_pow_val, ← map_pow, ← hbord, pow_orderOf_eq_one, map_one]
    rfl
  have hτ1 : τ ≠ 1 := fun h => hT (Units.ext (congrArg Subtype.val h))
  have hgen : ∀ σ : E ≃+* E, σ τ = τ → σ = 1 := by
    intro σ hσ
    refine RingEquiv.ext fun x => ?_
    obtain ⟨y, hy⟩ := x
    change σ ⟨y, hy⟩ = ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hσ
    | algebraMap r =>
      have he : (⟨_, Subalgebra.algebraMap_mem E r⟩ : E) = algebraMap (ZMod q) E r := rfl
      rw [he]
      exact DFunLike.congr_fun (RingHom.ext_zmod ((σ : E →+* E).comp (algebraMap (ZMod q) E))
        (algebraMap (ZMod q) E)) r
    | add x z hx hz ihx ihz =>
      have he : (⟨x + z, add_mem hx hz⟩ : E) = ⟨x, hx⟩ + ⟨z, hz⟩ := rfl
      rw [he, map_add, ihx, ihz]
    | mul x z hx hz ihx ihz =>
      have he : (⟨x * z, mul_mem hx hz⟩ : E) = ⟨x, hx⟩ * ⟨z, hz⟩ := rfl
      rw [he, map_mul, ihx, ihz]
  have hleast := isLeast_pow_modEq_one_of_generator hq hn1 hEcard hp hτp hτ1 hgen
  refine ⟨hE, n, hEcard, hleast, ?_, ?_⟩
  · let : Module E V := Module.compHom V (E.val : E →+* Module.End (ZMod q) V)
    have hsmul : ∀ (a : E) (v : V), a • v = (a : Module.End (ZMod q) V) v := fun _ _ => rfl
    have hlin : ∀ (g : L) (a : E) (v : V),
        (ρ g : V →ₗ[ZMod q] V) (a • v) = a • (ρ g : V →ₗ[ZMod q] V) v := by
      intro g a v
      rw [hsmul, hsmul]
      have h := congrArg (fun f : Module.End (ZMod q) V => f v) (hcommL a a.2 g)
      simp only [Module.End.mul_apply] at h
      exact h.symm
    refine ⟨hlin, fun W hW => ?_, fun g => ?_⟩
    ·
      let W' : Submodule (ZMod q) V :=
        { carrier := W
          add_mem' := W.add_mem
          zero_mem' := W.zero_mem
          smul_mem' := fun r v hv => by
            have h := W.smul_mem (algebraMap (ZMod q) E r) hv
            change ((algebraMap (ZMod q) E r : E) : Module.End (ZMod q) V) v ∈ W at h
            rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one,
              LinearMap.smul_apply, Module.End.one_apply] at h
            exact h }
      rcases hirr W' hW with h | h
      · left
        rw [Submodule.eq_bot_iff]
        intro v hv
        have hv' : v ∈ W' := hv
        rw [h] at hv'
        exact (Submodule.mem_bot _).mp hv'
      · right
        rw [eq_top_iff]
        intro v _
        have hv' : v ∈ W' := by rw [h]; exact Submodule.mem_top
        exact hv'
    ·
      let W : Submodule E V :=
        { carrier := {v | (ρ g : V →ₗ[ZMod q] V) v = v}
          add_mem' := fun {v w} hv hw => by
            change (ρ g : V →ₗ[ZMod q] V) (v + w) = v + w
            rw [map_add, hv, hw]
          zero_mem' := map_zero _
          smul_mem' := fun a v hv => by
            change (ρ g : V →ₗ[ZMod q] V) (a • v) = a • v
            rw [hlin g a v, hv] }
      refine ⟨W, rfl, ?_⟩
      have h1 : Nat.card (LinearMap.ker ((ρ g : V →ₗ[ZMod q] V) - 1)) = Nat.card W := by
        refine Nat.card_congr
          { toFun := fun x => ⟨x, ?_⟩
            invFun := fun x => ⟨x, ?_⟩
            left_inv := fun x => rfl
            right_inv := fun x => rfl }
        · have hx := x.2
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
          exact hx
        · have hx : (ρ g : V →ₗ[ZMod q] V) x = x := x.2
          rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
          exact hx
      have : Module.Finite E W := Module.Finite.of_finite
      have h2 := Module.natCard_eq_pow_finrank (K := ZMod q)
        (V := LinearMap.ker ((ρ g : V →ₗ[ZMod q] V) - 1))
      have h3 := Module.natCard_eq_pow_finrank (K := E) (V := W)
      rw [Nat.card_zmod] at h2
      rw [hEcard, ← pow_mul] at h3
      exact Nat.pow_right_injective hq.two_le (h2.symm.trans (h1.trans h3))
  · intro hp5 hq5
    subst hp5
    obtain ⟨⟨hn0, hnmod⟩, hmin⟩ := hleast
    have h4 : q ^ 4 ≡ 1 [MOD 5] := by
      unfold Nat.ModEq
      rw [Nat.pow_mod]
      rcases hq5 with h | h <;> rw [h]
    have hle : n ≤ 4 := hmin ⟨by norm_num, h4⟩
    have hge : 4 ≤ n := by
      by_contra hlt
      unfold Nat.ModEq at hnmod
      rw [Nat.pow_mod] at hnmod
      interval_cases n <;> rcases hq5 with h | h <;> rw [h] at hnmod <;> norm_num at hnmod
    omega

end CFSG.RankThree.GroupTheory
