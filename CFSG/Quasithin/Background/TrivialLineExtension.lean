module

public import CFSG.Quasithin.Background.JonesParshallBasic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.JonesParshall

section Binary

variable {B Q : Type*} [Group B] [AddCommGroup Q] [Module (ZMod 2) Q]

@[expose] noncomputable def trivialLineExtension
    (ρQ : Representation (ZMod 2) B Q)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ)) :
    Representation (ZMod 2) B (ZMod 2 × Q) where
  toFun g :=
    ((LinearMap.fst (ZMod 2) (ZMod 2) Q) +
        (d g).comp ((ρQ g).comp (LinearMap.snd (ZMod 2) (ZMod 2) Q))).prod
      ((ρQ g).comp (LinearMap.snd (ZMod 2) (ZMod 2) Q))
  map_one' := by
    have hd1 : d 1 = 0 := by
      have h := hd 1 1
      simp only [mul_one, map_one, Module.End.one_eq_id] at h
      change d 1 = d 1 + d 1 at h
      have h0 : d 1 + d 1 = 0 := ZModModule.add_self (d 1)
      rw [h0] at h
      exact h
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, q⟩ := x
    change (a + d 1 (ρQ 1 q), ρQ 1 q) = (a, q)
    simp [hd1]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, q⟩ := x
    have hc := congrArg (fun f : Module.Dual (ZMod 2) Q => f (ρQ (g * h) q)) (hd g h)
    simp only [LinearMap.add_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply] at hc
    have hq : ρQ g⁻¹ (ρQ (g * h) q) = ρQ h q := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]
    rw [hq] at hc
    simp only [map_mul, Module.End.mul_apply] at hc
    change (a + d (g * h) (ρQ (g * h) q), ρQ (g * h) q) =
      (a + d h (ρQ h q) + d g (ρQ g (ρQ h q)), ρQ g (ρQ h q))
    simp only [map_mul, Module.End.mul_apply]
    rw [hc]
    abel_nf

@[simp] theorem trivialLineExtension_apply
    (ρQ : Representation (ZMod 2) B Q)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ)) (g : B) (a : ZMod 2) (q : Q) :
    trivialLineExtension ρQ d hd g (a, q) = (a + d g (ρQ g q), ρQ g q) := rfl

theorem trivialLineExtension_fixed_iff
    (ρQ : Representation (ZMod 2) B Q)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hQfix : ∀ q : Q, (∀ g : B, ρQ g q = q) → q = 0)
    (a : ZMod 2) (q : Q) :
    (∀ g : B, trivialLineExtension ρQ d hd g (a, q) = (a, q)) ↔ q = 0 := by
  constructor
  · intro h
    exact hQfix q fun g => by
      simpa using congrArg Prod.snd (h g)
  · rintro rfl
    intro g
    simp [trivialLineExtension_apply]

theorem trivialLineExtension_noInvariantFunctional
    (ρQ : Representation (ZMod 2) B Q)
    (d : B → Module.Dual (ZMod 2) Q)
    (hd : d ∈ Z1 (Representation.dual ρQ))
    (hdn : d ∉ B1 (Representation.dual ρQ))
    (hQ : ∀ ψ : Q →ₗ[ZMod 2] ZMod 2,
      (∀ g q, ψ (ρQ g q) = ψ q) → ψ = 0) :
    ∀ ψ : (ZMod 2 × Q) →ₗ[ZMod 2] ZMod 2,
      (∀ g e, ψ (trivialLineExtension ρQ d hd g e) = ψ e) → ψ = 0 := by
  intro ψ hψ
  let r : ZMod 2 := ψ (1, 0)
  let ℓ : Q →ₗ[ZMod 2] ZMod 2 := ψ.comp (LinearMap.inr (ZMod 2) (ZMod 2) Q)
  have hdecomp : ∀ (a : ZMod 2) (q : Q), ψ (a, q) = a * r + ℓ q := by
    intro a q
    have h : (a, q) = a • ((1, 0) : ZMod 2 × Q) + (0, q) := by
      ext <;> simp
    rw [h, map_add, map_smul, smul_eq_mul]
    rfl
  have hrel : ∀ (g : B) (q : Q), d g (ρQ g q) * r = ℓ q - ℓ (ρQ g q) := by
    intro g q
    have h := hψ g (0, q)
    simp only [trivialLineExtension_apply, zero_add] at h
    rw [hdecomp (d g (ρQ g q)) (ρQ g q), hdecomp 0 q, zero_mul, zero_add] at h
    exact eq_sub_iff_add_eq.mpr h
  have hsplit : r = 0 ∨ r = 1 := by
    have hlt : r.val < 2 := ZMod.val_lt r
    have hle : r.val ≤ 1 := Nat.lt_succ_iff.mp hlt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · left
      exact (ZMod.val_eq_zero r).mp h
    · right
      exact (ZMod.val_eq_one (by decide : 1 < 2) r).mp h
  rcases hsplit with hr | hr
  ·
    have hell : ∀ (g : B) (q : Q), ℓ (ρQ g q) = ℓ q := by
      intro g q
      have h := hrel g q
      rw [hr, mul_zero] at h
      exact (sub_eq_zero.mp h.symm).symm
    have hℓ : ℓ = 0 := hQ ℓ hell
    refine LinearMap.ext fun x => ?_
    obtain ⟨a, q⟩ := x
    rw [hdecomp a q, hr, hℓ]
    simp
  ·
    have hcob : d = coboundary (Representation.dual ρQ) ℓ := by
      funext g
      ext q
      have h := hrel g (ρQ g⁻¹ q)
      simp only [Representation.self_inv_apply, hr, mul_one] at h
      simp only [coboundary, LinearMap.coe_mk, AddHom.coe_mk, Representation.dual_apply,
        Module.Dual.transpose_apply, LinearMap.sub_apply, LinearMap.comp_apply]
      exact h
    exact absurd ⟨ℓ, hcob.symm⟩ hdn

end Binary

end CFSG.Quasithin.JonesParshall

end
