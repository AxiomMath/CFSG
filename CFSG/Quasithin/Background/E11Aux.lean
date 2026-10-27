module

public import CFSG.Quasithin.Background.E11Sub
public import CFSG.Quasithin.Background.E11End

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {H : Subgroup (GLV V)}
  {I : Submodule (ZMod 2) V}

namespace E11Data

theorem natCard_U (D : E11Data H I) : Nat.card D.U = Nat.card D.F ^ Module.finrank D.F D.U :=
  Module.natCard_eq_pow_finrank

theorem natCard_irrPlus (D : E11Data H I) :
    Nat.card D.U - 1 = Nat.card {J : Submodule (ZMod 2) V // IrrPlus H J} * (Nat.card D.F - 1) := by
  rw [Projectivization.card D.F D.U, Nat.card_congr D.ψ]

theorem natCard_eq_pow_of_stable [Finite V] (D : E11Data H I) (M : Submodule (ZMod 2) V)
    (hM : ∀ (f : D.F), ∀ v ∈ M, D.κ f v ∈ M) : ∃ j : ℕ, Nat.card M = Nat.card D.F ^ j := by
  let κM : D.F →+* Module.End (ZMod 2) M :=
    { toFun := fun f => (D.κ f).restrict (fun v hv => hM f v hv)
      map_one' := by
        refine LinearMap.ext fun v => Subtype.ext ?_
        simp
      map_mul' := fun f f' => by
        refine LinearMap.ext fun v => Subtype.ext ?_
        simp
      map_zero' := by
        refine LinearMap.ext fun v => Subtype.ext ?_
        simp
      map_add' := fun f f' => by
        refine LinearMap.ext fun v => Subtype.ext ?_
        simp }
  let _ : Module D.F M := Module.compHom M κM
  have : Module.Finite D.F M := Module.Finite.of_finite
  exact ⟨_, Module.natCard_eq_pow_finrank (K := D.F) (V := M)⟩

theorem finrank_dvd_of_stable [Finite V] (D : E11Data H I) (M : Submodule (ZMod 2) V)
    (hM : ∀ (f : D.F), ∀ v ∈ M, D.κ f v ∈ M) :
    Module.finrank (ZMod 2) D.F ∣ Module.finrank (ZMod 2) M := by
  obtain ⟨j, hj⟩ := D.natCard_eq_pow_of_stable M hM
  exact ⟨j, by rw [E11.finrank_eq_mul_of_card hj, mul_comm]⟩

theorem finrank_dvd_fixedSpace [Finite V] (D : E11Data H I) (Y : Subgroup (GLV V))
    (hY : ∀ y ∈ Y, ∀ f : D.F, (y : Module.End (ZMod 2) V) * D.κ f =
      D.κ f * (y : Module.End (ZMod 2) V)) :
    Module.finrank (ZMod 2) D.F ∣ Module.finrank (ZMod 2) (fixedSpace Y) := by
  refine D.finrank_dvd_of_stable (fixedSpace Y) fun f v hv y hy => ?_
  have := congrArg (fun T : Module.End (ZMod 2) V => T v) (hY y hy f)
  have h2 : y (D.κ f v) = D.κ f (y v) := this
  show y (D.κ f v) = D.κ f v
  rw [h2]
  exact congrArg (D.κ f) (hv y hy)

theorem endEquiv_conj (D : E11Data H I) {g : GLV V}
    (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (hgI : conjSub g I = I)
    (τ : D.F ≃+* D.F) (σ : D.U →ₛₗ[(τ : D.F →+* D.F)] D.U) (hσ : Function.Bijective σ)
    (hcompat : ∀ c c' : Subgroup.centralizer (H : Set (GLV V)),
      (c' : GLV V) * g = g * c → ∀ u : D.U, D.θ c' (σ u) = σ (D.θ c u))
    (f₀ f₁ : endOn H I)
    (h : ∀ i j : I, g (i : V) = (j : V) → g ((f₀.1 i : I) : V) = ((f₁.1 j : I) : V)) :
    D.endEquiv f₁ = τ (D.endEquiv f₀) := by
  have hk := D.κ_conj g hg τ σ hσ hcompat (D.endEquiv f₀)
  set f₂ : endOn H I := D.endEquiv.symm (τ (D.endEquiv f₀)) with hf₂
  have hf₂' : D.endEquiv f₂ = τ (D.endEquiv f₀) := D.endEquiv.apply_symm_apply _
  have hmem : ∀ j : I, g.symm (j : V) ∈ I := fun j => by
    have : (j : V) ∈ conjSub g I := by rw [hgI]; exact j.2
    exact mem_conjSub.1 this
  have : f₂ = f₁ := by
    refine Subtype.ext (LinearMap.ext fun j => Subtype.ext ?_)
    set i : I := ⟨g.symm (j : V), hmem j⟩ with hi
    have hij : g (i : V) = (j : V) := g.apply_symm_apply _
    have h1 := congrArg (fun T : Module.End (ZMod 2) V => T (i : V)) hk
    have h2 : g (D.κ (D.endEquiv f₀) (i : V)) = D.κ (τ (D.endEquiv f₀)) (g (i : V)) := h1
    rw [D.κ_apply f₀ i, ← hf₂', hij, D.κ_apply f₂ j] at h2
    exact h2.symm.trans (h i j hij)
  rw [← this, hf₂']

end E11Data

namespace E11

section Conj

variable {g : GLV V}

theorem exists_conj_endOn (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (hI : Invariant H I)
    (hgI : conjSub g I = I) (f₀ : endOn H I) :
    ∃ f₁ : endOn H I, ∀ i j : I, g (i : V) = (j : V) →
      g ((f₀.1 i : I) : V) = ((f₁.1 j : I) : V) := by
  have hmem : ∀ j : I, g.symm (j : V) ∈ I := fun j => by
    have : (j : V) ∈ conjSub g I := by rw [hgI]; exact j.2
    exact mem_conjSub.1 this
  have hmem2 : ∀ x : I, g (x : V) ∈ I := fun x => by
    have : g (x : V) ∈ conjSub g I := apply_mem_conjSub x.2
    rwa [hgI] at this
  let f₁ : Module.End (ZMod 2) ↥I :=
    { toFun := fun j => ⟨g ((f₀.1 ⟨g.symm (j : V), hmem j⟩ : I) : V), hmem2 _⟩
      map_add' := fun j j' => by
        refine Subtype.ext ?_
        have h1 : (⟨g.symm ((j + j' : I) : V), hmem _⟩ : I) =
            ⟨g.symm (j : V), hmem j⟩ + ⟨g.symm (j' : V), hmem j'⟩ := Subtype.ext (by simp)
        show g ((f₀.1 ⟨g.symm ((j + j' : I) : V), hmem _⟩ : I) : V) =
          g ((f₀.1 ⟨g.symm (j : V), hmem j⟩ : I) : V) +
            g ((f₀.1 ⟨g.symm (j' : V), hmem j'⟩ : I) : V)
        rw [h1, map_add, Submodule.coe_add, map_add]
      map_smul' := fun c j => by
        refine Subtype.ext ?_
        have h1 : (⟨g.symm ((c • j : I) : V), hmem _⟩ : I) = c • ⟨g.symm (j : V), hmem j⟩ :=
          Subtype.ext (by simp)
        show g ((f₀.1 ⟨g.symm ((c • j : I) : V), hmem _⟩ : I) : V) =
          c • g ((f₀.1 ⟨g.symm (j : V), hmem j⟩ : I) : V)
        rw [h1, map_smul, Submodule.coe_smul, map_smul] }
  have hf₁ : f₁ ∈ endOn H I := by
    refine (mem_endOn_iff f₁ hI).2 fun h hh i => ?_
    have hh' : g⁻¹ * h * g ∈ H := by
      simpa using (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) h).1 hh
    set x : I := ⟨g.symm (i : V), hmem i⟩ with hx
    have key : (⟨g.symm (h (i : V)), hmem ⟨h (i : V), hI h hh i i.2⟩⟩ : I) =
        ⟨(g⁻¹ * h * g) (x : V), hI _ hh' x x.2⟩ := Subtype.ext (by simp [hx])
    have h3 := (mem_endOn_iff f₀.1 hI).1 f₀.2 _ hh' x
    show h (g ((f₀.1 x : I) : V)) = g ((f₀.1 ⟨g.symm (h (i : V)), _⟩ : I) : V)
    rw [key, ← h3]
    simp
  exact ⟨⟨f₁, hf₁⟩, fun i j hij => by
    have h1 : g.symm (j : V) = (i : V) := by
      rw [← hij]
      exact g.symm_apply_apply _
    have : (⟨g.symm (j : V), hmem j⟩ : I) = i := Subtype.ext h1
    show g ((f₀.1 i : I) : V) = g ((f₀.1 ⟨g.symm (j : V), hmem j⟩ : I) : V)
    rw [this]⟩

end Conj

end E11

namespace E11Data

theorem tau_eq_one_iff (D : E11Data H I) (hI : Invariant H I) {g : GLV V}
    (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (hgI : conjSub g I = I)
    (τ : D.F ≃+* D.F) (σ : D.U →ₛₗ[(τ : D.F →+* D.F)] D.U) (hσ : Function.Bijective σ)
    (hcompat : ∀ c c' : Subgroup.centralizer (H : Set (GLV V)),
      (c' : GLV V) * g = g * c → ∀ u : D.U, D.θ c' (σ u) = σ (D.θ c u)) :
    (∀ f : D.F, τ f = f) ↔
      ∀ (f : endOn H I) (i j : I), g (i : V) = (j : V) →
        g ((f.1 i : I) : V) = ((f.1 j : I) : V) := by
  constructor
  · intro hτ f i j hij
    obtain ⟨f₁, hf₁⟩ := E11.exists_conj_endOn hg hI hgI f
    have := D.endEquiv_conj hg hgI τ σ hσ hcompat f f₁ hf₁
    rw [hτ] at this
    have hff : f₁ = f := D.endEquiv.injective this
    rw [hf₁ i j hij, hff]
  · intro h f
    obtain ⟨f₀, rfl⟩ := D.endEquiv.surjective f
    exact (D.endEquiv_conj hg hgI τ σ hσ hcompat f₀ f₀ (h f₀)).symm

theorem comm_kappa_iff (D : E11Data H I) (hI : Invariant H I) {g : GLV V}
    (hg : g ∈ Subgroup.normalizer (H : Set (GLV V))) (hgI : conjSub g I = I) :
    (∀ f : D.F, (g : Module.End (ZMod 2) V) * D.κ f = D.κ f * (g : Module.End (ZMod 2) V)) ↔
      ∀ (f : endOn H I) (i j : I), g (i : V) = (j : V) →
        g ((f.1 i : I) : V) = ((f.1 j : I) : V) := by
  obtain ⟨τ, σ, hσ, -, hcompat⟩ := D.semilinear g hg
  constructor
  · intro hc f₀ i j hij
    have h1 := congrArg (fun T : Module.End (ZMod 2) V => T (i : V)) (hc (D.endEquiv f₀))
    have h2 : g (D.κ (D.endEquiv f₀) (i : V)) = D.κ (D.endEquiv f₀) (g (i : V)) := h1
    rw [D.κ_apply f₀ i, hij] at h2
    rw [h2]
    have := D.κ_apply f₀ j
    exact this
  · intro h f
    have hτ := (D.tau_eq_one_iff hI hg hgI τ σ hσ hcompat).2 h
    have := D.κ_conj g hg τ σ hσ hcompat f
    rw [this, hτ f]

end E11Data

end G11

end CFSG.Quasithin
