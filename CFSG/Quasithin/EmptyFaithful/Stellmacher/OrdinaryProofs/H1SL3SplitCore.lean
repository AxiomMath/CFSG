module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitLift

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

structure SplitSetup (A H E N : Type*) [Group A] [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup N] [Module (ZMod 2) N] where
  ψ : A →* H
  ρE : A →* AddMonoid.End E
  ρN : H →* AddMonoid.End N
  π : E →ₗ[ZMod 2] N
  hequiv : ∀ (a : A) (e : E), π (ρE a e) = ρN (ψ a) (π e)
  htriv : ∀ (a : A) (z : E), π z = 0 → ρE a z = z
  hker : ∀ a : A, ψ a = 1 → ∀ e : E, ρE a e = e

section Core

variable {A H E N : Type*} [Group A] [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup N] [Module (ZMod 2) N]

omit [Module (ZMod 2) E] [Module (ZMod 2) N] in
theorem rep_apply_inv_apply (ρ : H →* AddMonoid.End N) (g : H) (x : N) :
    ρ g (ρ g⁻¹ x) = x ∧ ρ g⁻¹ (ρ g x) = x := by
  constructor
  · have h : ρ (g * g⁻¹) x = ρ g (ρ g⁻¹ x) := by
      rw [map_mul]
      rfl
    rw [← h, mul_inv_cancel, map_one]
    rfl
  · have h : ρ (g⁻¹ * g) x = ρ g⁻¹ (ρ g x) := by
      rw [map_mul]
      rfl
    rw [← h, inv_mul_cancel, map_one]
    rfl

@[expose] def sectionDefect (D : SplitSetup A H E N) (σ : N →+ E) (a : A) (x : N) : E :=
  D.ρE a (σ (D.ρN (D.ψ a)⁻¹ x)) - σ x

theorem sectionDefect_mem (D : SplitSetup A H E N) (σ : N →+ E)
    (hσ : ∀ x, D.π (σ x) = x) (a : A) (x : N) :
    D.π (sectionDefect D σ a x) = 0 := by
  unfold sectionDefect
  rw [map_sub, D.hequiv]
  simp only [hσ]
  rw [(rep_apply_inv_apply D.ρN (D.ψ a) x).1, sub_self]

theorem sectionDefect_add (D : SplitSetup A H E N) (σ : N →+ E) (a : A) (x y : N) :
    sectionDefect D σ a (x + y) = sectionDefect D σ a x + sectionDefect D σ a y := by
  unfold sectionDefect
  simp only [map_add]
  abel

theorem sectionDefect_zero (D : SplitSetup A H E N) (σ : N →+ E) (a : A) :
    sectionDefect D σ a 0 = 0 := by
  unfold sectionDefect
  simp

@[expose] def defectHom (D : SplitSetup A H E N) (σ : N →+ E)
    (hσ : ∀ x, D.π (σ x) = x) (a : A) : N →+ LinearMap.ker D.π where
  toFun x := ⟨sectionDefect D σ a x, LinearMap.mem_ker.mpr (sectionDefect_mem D σ hσ a x)⟩
  map_zero' := Subtype.ext (sectionDefect_zero D σ a)
  map_add' x y := Subtype.ext (sectionDefect_add D σ a x y)

theorem sectionDefect_mul (D : SplitSetup A H E N) (σ : N →+ E)
    (hσ : ∀ x, D.π (σ x) = x) (a b : A) (x : N) :
    sectionDefect D σ (a * b) x =
      sectionDefect D σ a x + sectionDefect D σ b (D.ρN (D.ψ a)⁻¹ x) := by
  have hmul : D.ρN (D.ψ (a * b))⁻¹ x = D.ρN (D.ψ b)⁻¹ (D.ρN (D.ψ a)⁻¹ x) := by
    rw [map_mul, mul_inv_rev, map_mul]
    rfl
  have hρ : ∀ z, D.ρE (a * b) z = D.ρE a (D.ρE b z) := fun z => by
    rw [map_mul]
    rfl
  have hDker : D.π (sectionDefect D σ b (D.ρN (D.ψ a)⁻¹ x)) = 0 :=
    sectionDefect_mem D σ hσ b _
  have hDa : D.ρE a (sectionDefect D σ b (D.ρN (D.ψ a)⁻¹ x)) =
      sectionDefect D σ b (D.ρN (D.ψ a)⁻¹ x) :=
    D.htriv a _ hDker
  have hsplit : D.ρE b (σ (D.ρN (D.ψ b)⁻¹ (D.ρN (D.ψ a)⁻¹ x))) =
      sectionDefect D σ b (D.ρN (D.ψ a)⁻¹ x) + σ (D.ρN (D.ψ a)⁻¹ x) := by
    unfold sectionDefect
    abel
  show D.ρE (a * b) (σ (D.ρN (D.ψ (a * b))⁻¹ x)) - σ x =
    (D.ρE a (σ (D.ρN (D.ψ a)⁻¹ x)) - σ x) + sectionDefect D σ b (D.ρN (D.ψ a)⁻¹ x)
  rw [hmul, hρ, hsplit, map_add, hDa]
  abel

theorem defectHom_mul (D : SplitSetup A H E N) (σ : N →+ E)
    (hσ : ∀ x, D.π (σ x) = x) (a b : A) :
    defectHom D σ hσ (a * b) = defectHom D σ hσ a + homAct D.ρN (D.ψ a) (defectHom D σ hσ b) :=
  AddMonoidHom.ext fun x => Subtype.ext (sectionDefect_mul D σ hσ a b x)

theorem defectHom_ker (D : SplitSetup A H E N) (σ : N →+ E)
    (hσ : ∀ x, D.π (σ x) = x) (a : A) (ha : D.ψ a = 1) :
    defectHom D σ hσ a = 0 :=
  AddMonoidHom.ext fun x => Subtype.ext (by
    show sectionDefect D σ a x = 0
    have h1 : D.ρN (D.ψ a)⁻¹ x = x := by
      rw [ha, inv_one, map_one]
      rfl
    unfold sectionDefect
    rw [h1, D.hker a ha (σ x), sub_self])

theorem exists_complement_core (D : SplitSetup A H E N)
    (hψ : Function.Surjective D.ψ) (hπ : Function.Surjective D.π)
    (hprin : ∀ f : H → (N →+ LinearMap.ker D.π),
      (∀ g h, f (g * h) = f g + homAct D.ρN g (f h)) →
        ∃ w : N →+ LinearMap.ker D.π, ∀ g, f g = w - homAct D.ρN g w) :
    ∃ X : AddSubgroup E, (∀ a : A, ∀ x ∈ X, D.ρE a x ∈ X) ∧
      (∀ x ∈ X, D.π x = 0 → x = 0) ∧ (∀ e : E, ∃ x ∈ X, D.π (e - x) = 0) := by
  obtain ⟨σ₀, hσ₀⟩ := LinearMap.exists_rightInverse_of_surjective D.π
    (LinearMap.range_eq_top.mpr hπ)
  obtain ⟨σ, hσ⟩ : ∃ σ : N →+ E, ∀ x, D.π (σ x) = x :=
    ⟨σ₀.toAddMonoidHom, fun x => LinearMap.congr_fun hσ₀ x⟩
  obtain ⟨f, hfa, hf⟩ := crossedHom_lift D.ψ hψ (homAct D.ρN) (defectHom D σ hσ)
    (fun a b => defectHom_mul D σ hσ a b) (fun k hk => defectHom_ker D σ hσ k hk)
  obtain ⟨w, hw⟩ := hprin f hf
  have hpt : ∀ a x, sectionDefect D σ a x =
      (w x : E) - (w (D.ρN (D.ψ a)⁻¹ x) : E) := by
    intro a x
    have h1 : defectHom D σ hσ a = w - homAct D.ρN (D.ψ a) w :=
      (hfa a).symm.trans (hw (D.ψ a))
    have h2 := congrArg (fun φ : N →+ LinearMap.ker D.π => (φ x : E)) h1
    exact h2
  obtain ⟨sig, hsig⟩ : ∃ s : N →+ E, ∀ x, s x = σ x + (w x : E) :=
    ⟨σ + (LinearMap.ker D.π).subtype.toAddMonoidHom.comp w, fun x => rfl⟩
  have hπsig : ∀ x, D.π (sig x) = x := by
    intro x
    rw [hsig, map_add, hσ, LinearMap.mem_ker.mp (w x).2, add_zero]
  have hinv : ∀ a x, D.ρE a (sig (D.ρN (D.ψ a)⁻¹ x)) = sig x := by
    intro a x
    have hpt' := hpt a x
    have hwy := D.htriv a (w (D.ρN (D.ψ a)⁻¹ x) : E)
      (LinearMap.mem_ker.mp (w _).2)
    rw [hsig, hsig, map_add, hwy]
    have h3 : D.ρE a (σ (D.ρN (D.ψ a)⁻¹ x)) =
        ((w x : E) - (w (D.ρN (D.ψ a)⁻¹ x) : E)) + σ x := by
      unfold sectionDefect at hpt'
      rw [← hpt']
      abel
    rw [h3]
    abel
  refine ⟨AddMonoidHom.range sig, ?_, ?_, ?_⟩
  · intro a x hx
    obtain ⟨u, rfl⟩ := hx
    have h := hinv a (D.ρN (D.ψ a) u)
    rw [(rep_apply_inv_apply D.ρN (D.ψ a) u).2] at h
    exact AddMonoidHom.mem_range.mpr ⟨_, h.symm⟩
  · intro x hx hπx
    obtain ⟨u, rfl⟩ := hx
    rw [hπsig] at hπx
    rw [hπx, map_zero]
  · intro e
    refine ⟨sig (D.π e), AddMonoidHom.mem_range.mpr ⟨D.π e, rfl⟩, ?_⟩
    rw [map_sub, hπsig, sub_self]

end Core

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
