module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.Quasithin

open Module

theorem mem_of_forall_dual_apply_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Subspace K (Module.Dual K V)) (f : Module.Dual K V)
    (hf : ∀ v : V, (∀ w ∈ W, w v = 0) → f v = 0) : f ∈ W := by
  have : FiniteDimensional K W := inferInstance
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)]
  rw [Submodule.mem_dualAnnihilator]
  intro v hv
  exact hf v (by simpa [Submodule.mem_dualCoannihilator] using hv)

theorem pairing_dual {A B C : Type*} [Group A] [CommGroup B] [CommGroup C] [Finite B]
    (hB : ∀ b : B, b ^ 2 = 1) (hC : Nat.card C = 2) (Φ : A →* (B →* C)) :
    (∀ f : B →* C, (∀ b : B, (∀ a, Φ a b = 1) → f b = 1) → f ∈ Φ.range) ∧
      Nat.card Φ.range * Nat.card {b : B // ∀ a, Φ a b = 1} = Nat.card B := by
  classical
  have hcyc : IsCyclic C := isCyclic_of_prime_card (p := 2) (hp := ⟨Nat.prime_two⟩) hC
  have hcardM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  let ι : C ≃* Multiplicative (ZMod 2) := mulEquivOfCyclicCardEq (hC.trans hcardM.symm)
  have h2 : ∀ x : Additive B, (2 : ℕ) • x = 0 := fun x => by
    have := hB (Additive.toMul x)
    apply Additive.toMul.injective
    simpa [pow_two] using this
  let _ : Module (ZMod 2) (Additive B) := AddCommGroup.zmodModule h2
  have : Finite (Additive B) := inferInstanceAs (Finite B)
  have : FiniteDimensional (ZMod 2) (Additive B) := Module.Finite.of_finite
  have he_nsmul : ∀ (g : B →* C) (n : ℕ) (x : Additive B),
      Multiplicative.toAdd (ι (g (Additive.toMul (n • x)))) =
        n • Multiplicative.toAdd (ι (g (Additive.toMul x))) := by
    intro g n x
    induction n with
    | zero => simp
    | succ n ih => rw [succ_nsmul, succ_nsmul, ← ih]; simp
  let e : (B →* C) → Module.Dual (ZMod 2) (Additive B) := fun g =>
    { toFun := fun a => Multiplicative.toAdd (ι (g (Additive.toMul a)))
      map_add' := fun a b => by simp
      map_smul' := fun c x => by
        rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul (ZMod 2), he_nsmul]
        simp [nsmul_eq_mul] }
  have he_apply : ∀ g a, e g a = Multiplicative.toAdd (ι (g (Additive.toMul a))) :=
    fun g a => rfl
  have he_inj : Function.Injective e := by
    intro g₁ g₂ h
    ext b
    have := congrArg (fun φ => φ (Additive.ofMul b)) h
    simpa [he_apply] using this
  have he_mul : ∀ g₁ g₂, e (g₁ * g₂) = e g₁ + e g₂ := by
    intro g₁ g₂
    ext a
    simp [he_apply]
  have he_one : e 1 = 0 := by
    ext a
    simp [he_apply]
  have he_pow : ∀ (g : B →* C) (n : ℕ), e (g ^ n) = n • e g := by
    intro g n
    induction n with
    | zero => rw [pow_zero, he_one, zero_smul]
    | succ n ih => rw [pow_succ, he_mul, ih, succ_nsmul]
  let W'' : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Additive B)) :=
    { carrier := e '' (Φ.range : Set (B →* C))
      zero_mem' := ⟨1, Φ.range.one_mem, he_one⟩
      add_mem' := by
        rintro _ _ ⟨g₁, hg₁, rfl⟩ ⟨g₂, hg₂, rfl⟩
        exact ⟨g₁ * g₂, Φ.range.mul_mem hg₁ hg₂, he_mul g₁ g₂⟩
      smul_mem' := by
        rintro c _ ⟨g, hg, rfl⟩
        refine ⟨g ^ c.val, Φ.range.pow_mem hg _, ?_⟩
        rw [he_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val] }
  have hmem : ∀ g : B →* C, e g ∈ W'' ↔ g ∈ Φ.range := by
    intro g
    constructor
    · rintro ⟨g', hg', hgg⟩
      exact he_inj hgg ▸ hg'
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hcoann : ∀ v : Additive B,
      v ∈ W''.dualCoannihilator ↔ ∀ a, Φ a (Additive.toMul v) = 1 := by
    intro v
    rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro h a
      have := h (e (Φ a)) ((hmem _).mpr ⟨a, rfl⟩)
      have h3 : ι (Φ a (Additive.toMul v)) = 1 := by
        have := congrArg Multiplicative.ofAdd this
        simpa [he_apply] using this
      simpa using h3
    · intro h φ hφ
      obtain ⟨g, ⟨a, rfl⟩, rfl⟩ := hφ
      simp [he_apply, h a]
  refine ⟨fun f hf => ?_, ?_⟩
  · have key := mem_of_forall_dual_apply_eq_zero W'' (e f) (fun v hv => by
      have h1 : f (Additive.toMul v) = 1 := hf _ (fun a => (hcoann v).mp (by
        rw [Submodule.mem_dualCoannihilator]; exact hv) a)
      simp [he_apply, h1])
    exact (hmem f).mp key
  · have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq W''
    have c1 : Nat.card Φ.range = Nat.card W'' := by
      refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨e g.1, (hmem g.1).mpr g.2⟩) ⟨?_, ?_⟩)
      · intro g₁ g₂ h
        exact Subtype.ext (he_inj (congrArg Subtype.val h))
      · rintro ⟨φ, hφ⟩
        obtain ⟨g, hg, rfl⟩ := hφ
        exact ⟨⟨g, hg⟩, rfl⟩
    have c2 : Nat.card {b : B // ∀ a, Φ a b = 1} = Nat.card W''.dualCoannihilator := by
      refine Nat.card_congr
        { toFun := fun b => ⟨Additive.ofMul b.1, (hcoann _).mpr (by simpa using b.2)⟩
          invFun := fun v => ⟨Additive.toMul v.1, (hcoann _).mp v.2⟩
          left_inv := fun b => rfl
          right_inv := fun v => rfl }
    have c3 : Nat.card B = Nat.card (Additive B) := rfl
    let _ : AddCommGroup (ZMod 2) := Ring.toAddCommGroup
    have p1 : Nat.card (Additive B) = Nat.card (ZMod 2) ^ finrank (ZMod 2) (Additive B) :=
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive B)
    have p2 : Nat.card W'' = Nat.card (ZMod 2) ^ finrank (ZMod 2) W'' :=
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W'')
    have p3 : Nat.card W''.dualCoannihilator =
        Nat.card (ZMod 2) ^ finrank (ZMod 2) W''.dualCoannihilator :=
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W''.dualCoannihilator)
    rw [c1, c2, c3, p1, p2, p3, ← pow_add, hdim]

private theorem card_range_mul_card_ker {X Y : Type*} [Group X] [Group Y] [Finite X]
    (F : X →* Y) : Nat.card F.range * Nat.card F.ker = Nat.card X := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup F.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange F).toEquiv]

@[expose] def pairingToHom {A B C : Type*} [Group A] [CommGroup B] [CommGroup C] (β : A → B → C)
    (h1 : ∀ a₁ a₂ b, β (a₁ * a₂) b = β a₁ b * β a₂ b)
    (h2 : ∀ a b₁ b₂, β a (b₁ * b₂) = β a b₁ * β a b₂) : A →* (B →* C) where
  toFun a :=
    { toFun := β a
      map_one' := by
        have := h2 a 1 1
        simpa using this
      map_mul' := h2 a }
  map_one' := by
    ext b
    have := h1 1 1 b
    simpa using this
  map_mul' a₁ a₂ := by
    ext b
    exact h1 a₁ a₂ b

theorem card_mul_card_radical_eq {A B C : Type*} [Group A] [CommGroup B] [CommGroup C]
    [Finite A] [Finite B] (hB : ∀ b : B, b ^ 2 = 1)
    (hC : Nat.card C = 2) (β : A → B → C) (h1 : ∀ a₁ a₂ b, β (a₁ * a₂) b = β a₁ b * β a₂ b)
    (h2 : ∀ a b₁ b₂, β a (b₁ * b₂) = β a b₁ * β a b₂) :
    Nat.card A * Nat.card {b : B // ∀ a, β a b = 1} =
      Nat.card B * Nat.card {a : A // ∀ b, β a b = 1} := by
  let Φ : A →* (B →* C) := pairingToHom β h1 h2
  have hΦ : Nat.card Φ.range * Nat.card {b : B // ∀ a, β a b = 1} = Nat.card B :=
    (pairing_dual hB hC Φ).2
  have hkerΦ : Nat.card Φ.ker = Nat.card {a : A // ∀ b, β a b = 1} := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, fun b => by
          have := congrArg (fun f : B →* C => f b) (MonoidHom.mem_ker.mp a.2)
          simpa [Φ, pairingToHom] using this⟩
        invFun := fun a => ⟨a.1, MonoidHom.mem_ker.mpr (by
          ext b
          simpa [Φ, pairingToHom] using a.2 b)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  have e1 := card_range_mul_card_ker Φ
  rw [hkerΦ] at e1
  rw [← e1, ← hΦ]
  ring

end CFSG.Quasithin
