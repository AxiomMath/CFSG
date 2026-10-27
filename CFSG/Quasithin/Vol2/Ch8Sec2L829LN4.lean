module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN3

public section

namespace CFSG.Quasithin.H13.L829N

open Module

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def algOf (S : Subgroup (W ≃ₗ[ZMod 2] W)) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) W) :=
  Algebra.adjoin (ZMod 2) (Set.range fun s : S => ((s : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W))

theorem mem_algOf_of_mem (S : Subgroup (W ≃ₗ[ZMod 2] W)) {s : W ≃ₗ[ZMod 2] W} (hs : s ∈ S) :
    (s : Module.End (ZMod 2) W) ∈ algOf S :=
  Algebra.subset_adjoin (Set.mem_range.mpr ⟨⟨s, hs⟩, rfl⟩)

theorem commute_of_commute_gens (S : Subgroup (W ≃ₗ[ZMod 2] W)) {f : Module.End (ZMod 2) W}
    (hf : ∀ s ∈ S, f * (s : Module.End (ZMod 2) W) = (s : Module.End (ZMod 2) W) * f) :
    ∀ a ∈ algOf S, f * a = a * f := by
  have hle : algOf S ≤ Subalgebra.centralizer (ZMod 2) ({f} : Set (Module.End (ZMod 2) W)) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    refine (Subalgebra.mem_centralizer_iff (ZMod 2)).mpr (fun g hg => ?_)
    rw [Set.mem_singleton_iff.mp hg]
    exact hf s s.2
  intro a ha
  exact (Subalgebra.mem_centralizer_iff (ZMod 2)).mp (hle ha) f (Set.mem_singleton f)

theorem invUnder_algOf (S : Subgroup (W ≃ₗ[ZMod 2] W)) {P : Submodule (ZMod 2) W}
    (hP : InvUnder S P) : ∀ a ∈ algOf S, ∀ w ∈ P, a w ∈ P := by
  let Stab : Subalgebra (ZMod 2) (Module.End (ZMod 2) W) :=
    { carrier := {a | ∀ w ∈ P, a w ∈ P}
      mul_mem' := fun {a b} ha hb w hw => ha _ (hb w hw)
      one_mem' := fun w hw => hw
      add_mem' := fun {a b} ha hb w hw => P.add_mem (ha w hw) (hb w hw)
      zero_mem' := fun w _ => P.zero_mem
      algebraMap_mem' := fun r w hw => by
        rw [Module.algebraMap_end_apply]
        exact P.smul_mem r hw }
  have hle : algOf S ≤ Stab := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    exact fun w hw => hP s s.2 w hw
  exact fun a ha w hw => hle ha w hw

theorem conj_mem_algOf (S : Subgroup (W ≃ₗ[ZMod 2] W)) {t : W ≃ₗ[ZMod 2] W}
    (ht : ∀ s ∈ S, t * s * t⁻¹ ∈ S) :
    ∀ a ∈ algOf S, (t : Module.End (ZMod 2) W) * a *
      ((t⁻¹ : W ≃ₗ[ZMod 2] W) : Module.End (ZMod 2) W) ∈ algOf S := by
  have hle : algOf S ≤ Subalgebra.comap (t.conjAlgEquiv (ZMod 2)).toAlgHom (algOf S) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    refine (Subalgebra.mem_comap _ _ _).mpr ?_
    exact mem_algOf_of_mem S (ht s s.2)
  intro a ha
  exact (Subalgebra.mem_comap _ _ _).mp (hle ha)

theorem invUnder_sup [Finite W] {S₁ S₂ S₃ : Subgroup (W ≃ₗ[ZMod 2] W)}
    {P : Submodule (ZMod 2) W} (h₁ : InvUnder S₁ P) (h₂ : InvUnder S₂ P) (h₃ : InvUnder S₃ P) :
    InvUnder (S₁ ⊔ S₂ ⊔ S₃) P := by
  let H : Subgroup (W ≃ₗ[ZMod 2] W) :=
    { carrier := {y | ∀ w ∈ P, y w ∈ P}
      mul_mem' := fun {a b} ha hb w hw => ha _ (hb w hw)
      one_mem' := fun w hw => hw
      inv_mem' := fun {y} hy w hw => by
        have hinj : Function.Injective (fun v : P => (⟨y (v : W), hy (v : W) v.2⟩ : P)) := by
          intro a b hab
          have h2 : y (a : W) = y (b : W) := congrArg Subtype.val hab
          exact Subtype.ext (y.injective h2)
        obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨w, hw⟩
        have hvw : y (v : W) = w := congrArg Subtype.val hv
        subst hvw
        have hinv : (y⁻¹ : W ≃ₗ[ZMod 2] W) (y (v : W)) = (v : W) := y.symm_apply_apply v
        rw [hinv]
        exact v.2 }
  have hle : S₁ ⊔ S₂ ⊔ S₃ ≤ H :=
    sup_le (sup_le (fun s hs => h₁ s hs) (fun s hs => h₂ s hs)) (fun s hs => h₃ s hs)
  exact fun s hs w hw => hle hs w hw

@[expose] noncomputable def toSubmoduleA (S : Subgroup (W ≃ₗ[ZMod 2] W)) (P : Submodule (ZMod 2) W)
    (hP : InvUnder S P) : Submodule (algOf S) W where
  carrier := P
  add_mem' := fun {x y} hx hy => P.add_mem hx hy
  zero_mem' := P.zero_mem
  smul_mem' := fun a {x} hx => invUnder_algOf S hP a a.2 x hx

theorem invUnder_of_submoduleA (S : Subgroup (W ≃ₗ[ZMod 2] W)) (Q : Submodule (algOf S) W) :
    ∀ s ∈ S, ∀ w ∈ Q, s w ∈ Q := by
  intro s hs w hw
  exact Q.smul_mem ⟨(s : Module.End (ZMod 2) W), mem_algOf_of_mem S hs⟩ hw

@[expose] noncomputable def toSubmoduleF2 (S : Subgroup (W ≃ₗ[ZMod 2] W))
    (Q : Submodule (algOf S) W) : Submodule (ZMod 2) W where
  carrier := Q
  add_mem' := fun {x y} hx hy => Q.add_mem hx hy
  zero_mem' := Q.zero_mem
  smul_mem' := fun c {x} hx => by
    have h := Q.smul_mem (algebraMap (ZMod 2) (algOf S) c) hx
    have e : (algebraMap (ZMod 2) (algOf S) c) • x = c • x := by
      show (algebraMap (ZMod 2) (Module.End (ZMod 2) W) c) x = c • x
      rw [Module.algebraMap_end_apply]
    rw [e] at h
    exact h

end CFSG.Quasithin.H13.L829N
