module

public import CFSG.Quasithin.Background.G12Orbit

public section

namespace CFSG.Quasithin.G11

section NoInst

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def FormInv (K : Subgroup (GLV V)) (f : LinearMap.BilinForm (ZMod 2) V) : Prop :=
  ∀ k ∈ K, ∀ x y, f (k x) (k y) = f x y

@[expose] def FormSymm (f : LinearMap.BilinForm (ZMod 2) V) : Prop := ∀ x y, f x y = f y x

theorem formInv_zero (K : Subgroup (GLV V)) : FormInv K (0 : LinearMap.BilinForm (ZMod 2) V) :=
  fun _ _ _ _ => rfl

theorem FormInv.add {K : Subgroup (GLV V)} {f g : LinearMap.BilinForm (ZMod 2) V}
    (hf : FormInv K f) (hg : FormInv K g) : FormInv K (f + g) := fun k hk x y => by
  simp only [LinearMap.add_apply, hf k hk, hg k hk]

theorem FormSymm.add {f g : LinearMap.BilinForm (ZMod 2) V} (hf : FormSymm f) (hg : FormSymm g) :
    FormSymm (f + g) := fun x y => by
  simp only [LinearMap.add_apply, hf x y, hg x y]

@[expose] def g12FormT (f : LinearMap.BilinForm (ZMod 2) V) : LinearMap.BilinForm (ZMod 2) V :=
  f.flip

theorem g12FormT_apply (f : LinearMap.BilinForm (ZMod 2) V) (x y : V) : g12FormT f x y = f y x := rfl

theorem FormInv.g12FormT {K : Subgroup (GLV V)} {f : LinearMap.BilinForm (ZMod 2) V}
    (hf : FormInv K f) : FormInv K (g12FormT f) := fun k hk x y => by
  simp only [g12FormT_apply, hf k hk]

theorem g12FormT_add_symm (f : LinearMap.BilinForm (ZMod 2) V) : FormSymm (f + g12FormT f) := fun x y => by
  simp only [LinearMap.add_apply, g12FormT_apply]
  rw [add_comm]


@[expose] def g12FormAct (g : GLV V) (B : LinearMap.BilinForm (ZMod 2) V) :
    LinearMap.BilinForm (ZMod 2) V :=
  B.compl₁₂ (g.symm : V →ₗ[ZMod 2] V) (g.symm : V →ₗ[ZMod 2] V)

theorem g12FormAct_apply (g : GLV V) (B : LinearMap.BilinForm (ZMod 2) V) (x y : V) :
    g12FormAct g B x y = B (g.symm x) (g.symm y) := rfl

theorem g12FormAct_one (B : LinearMap.BilinForm (ZMod 2) V) : g12FormAct 1 B = B := rfl

theorem g12FormAct_mul (g h : GLV V) (B : LinearMap.BilinForm (ZMod 2) V) :
    g12FormAct (g * h) B = g12FormAct g (g12FormAct h B) := rfl

theorem g12FormAct_zero (g : GLV V) : g12FormAct g (0 : LinearMap.BilinForm (ZMod 2) V) = 0 := by
  ext x y
  simp [g12FormAct_apply]

abbrev SymmInv (K : Subgroup (GLV V)) : Type :=
  {f : LinearMap.BilinForm (ZMod 2) V // FormInv K f ∧ FormSymm f}

theorem g12FormAct_mem {K : Subgroup (GLV V)} {g : GLV V} (hg : ∀ k ∈ K, g⁻¹ * k * g ∈ K)
    {B : LinearMap.BilinForm (ZMod 2) V} (hB : FormInv K B ∧ FormSymm B) :
    FormInv K (g12FormAct g B) ∧ FormSymm (g12FormAct g B) := by
  refine ⟨fun k hk x y => ?_, fun x y => hB.2 _ _⟩
  rw [g12FormAct_apply, g12FormAct_apply]
  have h1 : ∀ z, g.symm (k z) = (g⁻¹ * k * g) (g.symm z) := fun z => by
    have e : (g⁻¹ * k * g) (g.symm z) = g.symm (k (g (g.symm z))) := rfl
    rw [e, LinearEquiv.apply_symm_apply]
  rw [h1 x, h1 y]
  exact hB.1 _ (hg k hk) _ _

@[expose] def g12FormSmul (K Q : Subgroup (GLV V)) (hnorm : ∀ g ∈ Q, ∀ k ∈ K, g⁻¹ * k * g ∈ K)
    (g : ↥Q) (B : SymmInv K) : SymmInv K :=
  ⟨g12FormAct (g : GLV V) B.1, g12FormAct_mem (hnorm g g.2) B.2⟩

@[expose, instance_reducible] def g12FormActSub (K Q : Subgroup (GLV V))
    (hnorm : ∀ g ∈ Q, ∀ k ∈ K, g⁻¹ * k * g ∈ K) : MulAction ↥Q (SymmInv K) where
  smul := g12FormSmul K Q hnorm
  one_smul B := Subtype.ext (g12FormAct_one B.1)
  mul_smul g h B := Subtype.ext (g12FormAct_mul (g : GLV V) (h : GLV V) B.1)

theorem two_dvd_natCard_of_free_involution {α : Type*} [Finite α] (e : α → α)
    (he : ∀ a, e (e a) = a) (hne : ∀ a, e a ≠ a) : 2 ∣ Nat.card α := by
  have := Fintype.ofFinite α
  classical
  let f : Function.End α := e
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext a
    exact he a
  have h := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := f) (p := 2) (n := 1) hf
  have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨a, ha⟩ => hne a ha⟩
  rw [h0] at h
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd).1 h

theorem finite_bilinForm [Finite V] : Finite (LinearMap.BilinForm (ZMod 2) V) :=
  Finite.of_injective (fun (f : LinearMap.BilinForm (ZMod 2) V) (x y : V) => f x y)
    (fun f g h => by
      ext x y
      exact congrFun (congrFun h x) y)

theorem FormInv.zero_or_nondeg {K : Subgroup (GLV V)} (hirr : IsIrr K ⊤)
    {f : LinearMap.BilinForm (ZMod 2) V} (hf : FormInv K f) :
    f = 0 ∨ ∀ x, (∀ y, f x y = 0) → x = 0 := by
  have hinv : Invariant K (LinearMap.ker f) := by
    intro k hk u hu
    rw [LinearMap.mem_ker] at hu ⊢
    ext y
    have h1 : f (k u) y = f (k u) (k (k.symm y)) := by rw [LinearEquiv.apply_symm_apply]
    have h2 : f u = 0 := hu
    rw [LinearMap.zero_apply, h1, hf k hk, h2]
    simp
  rcases hirr.2.2 (LinearMap.ker f) hinv bot_le le_top with h | h
  · right
    intro x hx
    have : x ∈ LinearMap.ker f := LinearMap.mem_ker.2 (LinearMap.ext hx)
    rw [h] at this
    simpa using this
  · left
    ext x y
    have : x ∈ LinearMap.ker f := by rw [h]; trivial
    rw [LinearMap.mem_ker] at this
    simp [this]

theorem g12_exists_ne_zero_ne [Finite V] (hd : 2 ≤ Module.finrank (ZMod 2) V) (x : V) :
    ∃ y, y ≠ 0 ∧ y ≠ x := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hle : (⊤ : Submodule (ZMod 2) V) ≤ Submodule.span (ZMod 2) {x} := by
    intro y _
    rw [Submodule.mem_span_singleton]
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · exact ⟨1, by rw [one_smul]; exact (hcon y hy).symm⟩
  have h1 := Submodule.finrank_mono hle
  rw [finrank_top] at h1
  have h2 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {x}) ≤ 1 := by
    by_cases hx : x = 0
    · rw [hx, Submodule.span_zero_singleton, finrank_bot]; exact Nat.zero_le _
    · rw [finrank_span_singleton hx]
  omega

theorem FormInv.alternating_of_symm [Finite V] {K : Subgroup (GLV V)} (hirr : IsIrr K ⊤)
    (hd : 3 ≤ Module.finrank (ZMod 2) V) {f : LinearMap.BilinForm (ZMod 2) V} (hf : FormInv K f)
    (hs : FormSymm f) : ∀ x, f x x = 0 := by
  have hadd : ∀ a b, f (a + b) (a + b) = f a a + f b b := by
    intro a b
    simp only [map_add, LinearMap.add_apply]
    have h1 := hs b a
    have h2 : f a b + f b a = 0 := by rw [← h1]; exact g12_add_self _
    calc f a a + f b a + (f a b + f b b) = f a a + f b b + (f a b + f b a) := by ring
      _ = f a a + f b b := by rw [h2, add_zero]
  let N : Submodule (ZMod 2) V :=
    { carrier := {x | f x x = 0}
      add_mem' := fun {a b} ha hb => by
        show f (a + b) (a + b) = 0
        rw [hadd]
        have ha' : f a a = 0 := ha
        have hb' : f b b = 0 := hb
        rw [ha', hb', add_zero]
      zero_mem' := by
        show f 0 0 = 0
        simp
      smul_mem' := fun c x hx => by
        show f (c • x) (c • x) = 0
        have hx' : f x x = 0 := hx
        simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hx', mul_zero] }
  have hN : Invariant K N := fun k hk u hu => by
    show f (k u) (k u) = 0
    rw [hf k hk]
    exact hu
  rcases hirr.2.2 N hN bot_le le_top with h | h
  · exfalso
    have hx : ∃ x : V, x ≠ 0 := by
      have : 0 < Module.finrank (ZMod 2) V := by omega
      exact Module.finrank_pos_iff_exists_ne_zero.1 this
    obtain ⟨x, hx0⟩ := hx
    obtain ⟨y, hy0, hyx⟩ := g12_exists_ne_zero_ne (by omega) x
    have hfx : f x x = 1 := by
      by_contra hne
      apply hx0
      have : x ∈ N := by
        show f x x = 0
        rcases g12_eq_zero_or_one (f x x) with h0 | h1
        · exact h0
        · exact absurd h1 hne
      rw [h] at this
      simpa using this
    have hfy : f y y = 1 := by
      by_contra hne
      apply hy0
      have : y ∈ N := by
        show f y y = 0
        rcases g12_eq_zero_or_one (f y y) with h0 | h1
        · exact h0
        · exact absurd h1 hne
      rw [h] at this
      simpa using this
    have hxy : x + y ∈ N := by
      show f (x + y) (x + y) = 0
      rw [hadd, hfx, hfy]
      decide
    rw [h] at hxy
    have hxy' : x + y = 0 := by simpa using hxy
    apply hyx
    calc y = y + (x + x) := by rw [g12_vadd_self, add_zero]
      _ = (x + y) + x := by abel
      _ = x := by rw [hxy', zero_add]
  · intro x
    have : x ∈ N := by rw [h]; trivial
    exact this

theorem g12_eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide


theorem g12_exists_symplectic_form [Finite V] {K Q : Subgroup (GLV V)} (hirr : IsIrr K ⊤)
    (hd : 3 ≤ Module.finrank (ZMod 2) V)
    (hexists : ∃ f0 : LinearMap.BilinForm (ZMod 2) V, f0 ≠ 0 ∧ FormInv K f0)
    (hnorm : ∀ g ∈ Q, ∀ k ∈ K, g⁻¹ * k * g ∈ K) (hQ2 : ∀ a ∈ Q, a * a = 1) :
    ∃ f : LinearMap.BilinForm (ZMod 2) V, IsSymplectic f ∧ FormInv K f ∧
      ∀ g ∈ Q, ∀ x y, f (g x) (g y) = f x y := by
  obtain ⟨f0, hf0, hf0i⟩ := hexists
  obtain ⟨f1, hf1ne, hf1i, hf1s⟩ : ∃ f1 : LinearMap.BilinForm (ZMod 2) V,
      f1 ≠ 0 ∧ FormInv K f1 ∧ FormSymm f1 := by
    by_cases h : f0 + g12FormT f0 = 0
    · refine ⟨f0, hf0, hf0i, fun x y => ?_⟩
      have := LinearMap.congr_fun₂ h x y
      simp only [LinearMap.add_apply, g12FormT_apply, LinearMap.zero_apply] at this
      exact g12_eq_of_add_eq_zero _ _ this
    · exact ⟨f0 + g12FormT f0, h, hf0i.add hf0i.g12FormT, g12FormT_add_symm f0⟩
  have hfin : Finite (LinearMap.BilinForm (ZMod 2) V) := finite_bilinForm
  have : Finite (SymmInv K) := Subtype.finite
  let _ : MulAction ↥Q (SymmInv K) := g12FormActSub K Q hnorm
  have hG : IsPGroup 2 ↥Q := fun g => ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (hQ2 g g.2)⟩
  have hdvd : 2 ∣ Nat.card (SymmInv K) := by
    refine two_dvd_natCard_of_free_involution
      (fun B => ⟨B.1 + f1, B.2.1.add hf1i, B.2.2.add hf1s⟩) (fun B => ?_) (fun B h => ?_)
    · apply Subtype.ext
      ext x y
      simp only [LinearMap.add_apply]
      rw [add_assoc, g12_add_self, add_zero]
    · apply hf1ne
      have := congrArg (fun C : SymmInv K => (C.1 : LinearMap.BilinForm (ZMod 2) V)) h
      simp only at this
      ext x y
      have h2 := LinearMap.congr_fun₂ this x y
      simp only [LinearMap.add_apply] at h2
      exact g12_eq_zero_of_eq_add _ _ h2.symm
  let z0 : SymmInv K := ⟨0, formInv_zero K, fun _ _ => rfl⟩
  obtain ⟨⟨f, hf⟩, hfix, hne⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point (SymmInv K)
    hdvd (a := z0) (MulAction.mem_fixedPoints.2 fun g => Subtype.ext (g12FormAct_zero (g : GLV V)))
  have hf0' : f ≠ 0 := fun h => hne (Subtype.ext h.symm)
  have hfix' : ∀ g ∈ Q, ∀ x y, f (g x) (g y) = f x y := by
    intro g hg x y
    have := congrArg (fun F : SymmInv K => (F.1 : LinearMap.BilinForm (ZMod 2) V) (g x) (g y))
      (MulAction.mem_fixedPoints.1 hfix ⟨g, hg⟩)
    simp only at this
    have e : ((⟨g, hg⟩ : ↥Q) • (⟨f, hf⟩ : SymmInv K) : SymmInv K).1 (g x) (g y) = f x y := by
      show g12FormAct g f (g x) (g y) = f x y
      rw [g12FormAct_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rw [e] at this
    exact this.symm
  rcases hf.1.zero_or_nondeg hirr with h | hnd
  · exact absurd h hf0'
  · exact ⟨f, ⟨hf.1.alternating_of_symm hirr hd hf.2, hnd⟩, hf.1, hfix'⟩

end NoInst

end CFSG.Quasithin.G11
