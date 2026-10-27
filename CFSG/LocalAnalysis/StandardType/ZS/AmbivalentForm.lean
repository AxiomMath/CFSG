module

import CFSG.LocalAnalysis.StandardType.ZS.OrthExtLemmas

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private noncomputable def subgroupRep (A : Subgroup (V ≃ₗ[K] V)) : Representation K A V :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp A.subtype

private theorem subgroupRep_apply (A : Subgroup (V ≃ₗ[K] V)) (g : A) (v : V) :
    subgroupRep A g v = (g : V ≃ₗ[K] V) v := rfl

private theorem finrank_invariants_linHom_self [Module.Finite K V] [Nontrivial V]
    {A : Subgroup (V ≃ₗ[K] V)} (ρ : Representation K A V)
    (hact : ∀ (g : A) (v : V), ρ g v = (g : V ≃ₗ[K] V) v)
    (hend : ∀ T : V →ₗ[K] V, (∀ a : A, T ∘ₗ (a : V →ₗ[K] V) =
      (a : V →ₗ[K] V) ∘ₗ T) → ∃ c : K, T = c • LinearMap.id) :
    Module.finrank K (Representation.invariants (Representation.linHom ρ ρ)) = 1 := by
  classical
  have hE : Representation.invariants (Representation.linHom ρ ρ) =
      Submodule.span K {(LinearMap.id : V →ₗ[K] V)} := by
    refine le_antisymm ?_ ?_
    · intro T hT
      rw [Representation.mem_invariants] at hT
      have hcomm : ∀ a : A, T ∘ₗ (a : V →ₗ[K] V) = (a : V →ₗ[K] V) ∘ₗ T := by
        intro a
        have h := hT a
        rw [Representation.linHom_apply] at h
        ext v
        have hv := congrArg (fun f : V →ₗ[K] V => f (ρ a v)) h
        simpa [LinearMap.comp_apply, hact] using hv.symm
      obtain ⟨c, hc⟩ := hend T hcomm
      rw [hc]
      exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_le]
      intro T hT
      rw [Set.mem_singleton_iff] at hT
      subst T
      refine (Representation.mem_invariants _ _).2 ?_
      intro a
      rw [Representation.linHom_apply]
      ext v
      simp [LinearMap.comp_apply, hact]
  rw [hE]
  have hid : (LinearMap.id : V →ₗ[K] V) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have : v = 0 := by
      have := congrArg (fun f : V →ₗ[K] V => f v) h
      simpa using this
    exact hv this
  exact finrank_span_singleton (K := K) hid

private theorem invariants_linHom_dual_ne_bot [Module.Finite K V] [Nontrivial V]
    {A : Subgroup (V ≃ₗ[K] V)} [Fintype A] (ρ : Representation K A V)
    (hact : ∀ (g : A) (v : V), ρ g v = (g : V ≃ₗ[K] V) v)
    (hend : ∀ T : V →ₗ[K] V, (∀ a : A, T ∘ₗ (a : V →ₗ[K] V) =
      (a : V →ₗ[K] V) ∘ₗ T) → ∃ c : K, T = c • LinearMap.id)
    (hcard : (Nat.card A : K) ≠ 0)
    (hchar : ∀ g : A, ρ.character g⁻¹ = ρ.character g) :
    Representation.invariants (V := V →ₗ[K] Module.Dual K V)
      (Representation.linHom ρ ρ.dual) ≠ ⊥ := by
  classical
  have hfin : Module.finrank K
      (Representation.invariants (Representation.linHom ρ ρ)) = 1 :=
    finrank_invariants_linHom_self ρ hact hend
  have hsum : ∑ g : A, Representation.character (V := V →ₗ[K] Module.Dual K V)
      (Representation.linHom ρ ρ.dual) g =
      ∑ g : A, (Representation.linHom ρ ρ).character g := by
    refine Finset.sum_congr rfl ?_
    intro g _
    rw [Representation.char_linHom, Representation.char_dual,
      Representation.char_linHom, hchar g]
  let : Invertible (Nat.card A : K) := invertibleOfNonzero hcard
  have hcardE := Representation.card_inv_mul_sum_char_eq_finrank (ρ :=
    Representation.linHom ρ ρ)
  rw [hfin, Nat.cast_one] at hcardE
  have hS : ∑ g : A, (Representation.linHom ρ ρ).character g = (Nat.card A : K) := by
    have h := congrArg (fun x : K => (Nat.card A : K) * x) hcardE
    rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul, mul_one] at h
    exact h
  have hfinD : (Module.finrank K (Representation.invariants (V := V →ₗ[K] Module.Dual K V)
      (Representation.linHom ρ ρ.dual)) : K) = 1 := by
    have hD := Representation.card_inv_mul_sum_char_eq_finrank (V := V →ₗ[K] Module.Dual K V)
      (ρ := Representation.linHom ρ ρ.dual)
    rw [hsum, hS, inv_mul_cancel₀ hcard] at hD
    exact hD.symm
  intro hbot
  rw [hbot, finrank_bot, Nat.cast_zero] at hfinD
  exact zero_ne_one hfinD

private theorem exists_invariant_bilinForm_of_character [Module.Finite K V] [Nontrivial V]
    {A : Subgroup (V ≃ₗ[K] V)} [Fintype A] (ρ : Representation K A V)
    (hact : ∀ (g : A) (v : V), ρ g v = (g : V ≃ₗ[K] V) v)
    (hend : ∀ T : V →ₗ[K] V, (∀ a : A, T ∘ₗ (a : V →ₗ[K] V) =
      (a : V →ₗ[K] V) ∘ₗ T) → ∃ c : K, T = c • LinearMap.id)
    (hcard : (Nat.card A : K) ≠ 0)
    (hchar : ∀ g : A, ρ.character g⁻¹ = ρ.character g) :
    ∃ β : LinearMap.BilinForm K V, β ≠ 0 ∧
      ∀ g : A, ∀ u v, β ((g : V ≃ₗ[K] V) u) ((g : V ≃ₗ[K] V) v) = β u v := by
  classical
  obtain ⟨φ, hφmem, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (invariants_linHom_dual_ne_bot ρ hact hend hcard hchar)
  refine ⟨φ, hφne, ?_⟩
  intro g u v
  have hfix : (Representation.linHom ρ ρ.dual) g φ = φ :=
    ((Representation.mem_invariants _ _).mp hφmem) g
  rw [Representation.linHom_apply] at hfix
  have hpt : ∀ u w, φ (ρ g⁻¹ u) (ρ g⁻¹ w) = φ u w := by
    intro u w
    have h1 := congrArg (fun f : V →ₗ[K] Module.Dual K V => f u) hfix
    simp only [LinearMap.comp_apply] at h1
    have h2 := congrArg (fun f : V →ₗ[K] K => f w) h1
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h2
  have hcancel : ∀ x : V, ρ g⁻¹ (ρ g x) = x := by
    intro x
    simp
  have h := hpt (ρ g u) (ρ g v)
  rw [hcancel u, hcancel v] at h
  simpa [hact] using h.symm

end Generic

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

private theorem nondegenerate_of_absIrred [Module.Finite (ZMod p) W]
    {A : Subgroup (W ≃ₗ[ZMod p] W)} (hA : AbsIrred p A)
    {β : LinearMap.BilinForm (ZMod p) W} (hβne : β ≠ 0)
    (hβinv : ∀ g ∈ A, ∀ u v, β (g u) (g v) = β u v) :
    LinearMap.BilinForm.Nondegenerate β := by
  have hker_inv : ∀ g ∈ A, ∀ w ∈ LinearMap.ker β, g w ∈ LinearMap.ker β := by
    intro g hg w hw
    rw [LinearMap.mem_ker] at hw ⊢
    ext v
    have h := hβinv g hg w ((g : W ≃ₗ[ZMod p] W)⁻¹ v)
    have hgg : (g : W ≃ₗ[ZMod p] W) ((g : W ≃ₗ[ZMod p] W)⁻¹ v) = v := by simp
    rw [hgg] at h
    have hzero : β w ((g : W ≃ₗ[ZMod p] W)⁻¹ v) = 0 := by
      rw [hw, LinearMap.zero_apply]
    exact h.trans hzero
  rcases hA.1 (LinearMap.ker β) hker_inv with h | h
  · rwa [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]
  · exact absurd h (fun htop => hβne (LinearMap.ker_eq_top.mp htop))

private theorem flip_eq_self_or_neg_self_of_absIrred [Module.Finite (ZMod p) W]
    {A : Subgroup (W ≃ₗ[ZMod p] W)} (hA : AbsIrred p A)
    {β : LinearMap.BilinForm (ZMod p) W} (hβne : β ≠ 0)
    (hβnd : LinearMap.BilinForm.Nondegenerate β)
    (hβinv : ∀ g ∈ A, ∀ u v, β (g u) (g v) = β u v) :
    β.flip = β ∨ β.flip = -β := by
  have hflipinv : ∀ g ∈ A, ∀ u v, β.flip (g u) (g v) = β.flip u v := by
    intro g hg u v
    rw [LinearMap.BilinForm.flip_apply, LinearMap.BilinForm.flip_apply]
    exact hβinv g hg v u
  obtain ⟨c, hc⟩ := exists_eq_smul_of_absIrred (U := W) hA (B := β) (C := β.flip)
    hβnd hβinv hflipinv
  have hpt : ∀ u v, β u v = c * β v u := by
    intro u v
    have := congrArg (fun B : LinearMap.BilinForm (ZMod p) W => B v u) hc
    simpa [LinearMap.BilinForm.flip_apply, LinearMap.smul_apply] using this
  have hcc : c * c = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, β u ≠ 0 := by
      by_contra h
      push Not at h
      exact hβne (LinearMap.ext fun u => LinearMap.ext fun v =>
        congrArg (fun f : W →ₗ[ZMod p] ZMod p => f v) (h u))
    obtain ⟨v, hv⟩ : ∃ v, β u v ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (LinearMap.ext h)
    have h1 : β u v = (c * c) * β u v := by
      calc β u v = c * β v u := hpt u v
        _ = c * (c * β u v) := by rw [hpt v u]
        _ = (c * c) * β u v := by ring
    have h2 : (c * c - 1) * β u v = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    have h3 : c * c - 1 = 0 := (mul_eq_zero.mp h2).resolve_right hv
    exact sub_eq_zero.mp h3
  have hcpm : c = 1 ∨ c = -1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by
      have h1 : c * c - 1 = 0 := by rw [hcc]; ring
      calc (c - 1) * (c + 1) = c * c - 1 := by ring
        _ = 0 := h1
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  rcases hcpm with rfl | hneg
  · exact Or.inl (by simpa only [one_smul] using hc)
  · exact Or.inr (by rw [hc, hneg]; exact neg_one_smul (ZMod p) β)

theorem exists_invariant_bilinForm_of_isConj_inv [Module.Finite (ZMod p) W] [Nontrivial W]
    {A : Subgroup (W ≃ₗ[ZMod p] W)} (hA : AbsIrred p A) (hcard : (Nat.card A : ZMod p) ≠ 0)
    (hinv : ∀ g ∈ A, ∃ k ∈ A, k * g * k⁻¹ = g⁻¹) :
    ∃ β : LinearMap.BilinForm (ZMod p) W, β ≠ 0 ∧ ∀ g ∈ A, ∀ u v, β (g u) (g v) = β u v := by
  classical
  have : Finite A := Nat.finite_of_card_ne_zero fun h => hcard (by rw [h, Nat.cast_zero])
  have : Fintype A := Fintype.ofFinite A
  have hchar : ∀ g : A, (subgroupRep A).character g⁻¹ = (subgroupRep A).character g := by
    intro g
    obtain ⟨k, hk, hkg⟩ := hinv g g.2
    have hAeq : (⟨k, hk⟩ * g * ⟨k, hk⟩⁻¹ : A) = g⁻¹ := Subtype.ext hkg
    have h := Representation.char_conj (ρ := subgroupRep A) g ⟨k, hk⟩
    rwa [hAeq] at h
  obtain ⟨β, hβne, hβinv⟩ := exists_invariant_bilinForm_of_character (K := ZMod p)
    (subgroupRep A) (fun g v => subgroupRep_apply A g v)
    (fun T hcomm => hA.2 T fun g hg => hcomm ⟨g, hg⟩) hcard hchar
  exact ⟨β, hβne, fun g hg u v => hβinv ⟨g, hg⟩ u v⟩

theorem exists_isIsom_of_isConj_inv (hp : p ≠ 2) [Module.Finite (ZMod p) W]
    {A : Subgroup (W ≃ₗ[ZMod p] W)} (hA : AbsIrred p A) (hcard : (Nat.card A : ZMod p) ≠ 0)
    (hodd : Odd (Module.finrank (ZMod p) W)) (hinv : ∀ g ∈ A, ∃ k ∈ A, k * g * k⁻¹ = g⁻¹) :
    ∃ Q : QuadraticForm (ZMod p) W, (QuadraticMap.polarBilin Q).Nondegenerate ∧
      ∀ g ∈ A, IsIsom p Q g := by
  have hpos : 0 < Module.finrank (ZMod p) W := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨β, hβne, hβinv⟩ := exists_invariant_bilinForm_of_isConj_inv hA hcard hinv
  have hβnd : LinearMap.BilinForm.Nondegenerate β :=
    nondegenerate_of_absIrred hA hβne hβinv
  rcases flip_eq_self_or_neg_self_of_absIrred hA hβne hβnd hβinv with hsymm | halt
  · let Q : QuadraticForm (ZMod p) W := β.toQuadraticMap
    have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have hpolar : QuadraticMap.polarBilin Q = (2 : ZMod p) • β := by
      change QuadraticMap.polarBilin β.toQuadraticMap = (2 : ZMod p) • β
      rw [LinearMap.BilinMap.polarBilin_toQuadraticMap]
      change β + LinearMap.flip β = (2 : ZMod p) • β
      rw [show LinearMap.flip β = β from hsymm, two_smul]
    have hndQ : LinearMap.BilinForm.Nondegenerate (QuadraticMap.polarBilin Q) := by
      rw [hpolar, LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot,
        LinearMap.ker_smul β (2 : ZMod p) h2ne]
      exact LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mp hβnd
    refine ⟨Q, hndQ, ?_⟩
    intro g hg v
    change β ((g : W ≃ₗ[ZMod p] W) v) ((g : W ≃ₗ[ZMod p] W) v) = β v v
    exact hβinv g hg v v
  · exfalso
    have halt' : β.IsAlt := by
      intro u
      have h1 : β u u = -(β u u) := by
        have h := congrArg (fun B : LinearMap.BilinForm (ZMod p) W => B u u) halt
        simpa using h
      have h2 : (2 : ZMod p) * β u u = 0 := by
        rw [two_mul]
        nth_rewrite 1 [h1]
        rw [neg_add_cancel]
      exact (mul_eq_zero.mp h2).resolve_left (ZMod.prime_ne_zero p 2 hp)
    obtain ⟨m, hm⟩ := LinearMap.BilinForm.IsAlt.even_finrank (K := ZMod p) halt' hβnd
    obtain ⟨k, hk⟩ := hodd
    omega

end CFSG.StandardType.ZS

end
