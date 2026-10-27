module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenElt

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

section Model

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_weylGenModel (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusWeylGenElt p r R) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (hr : p ^ r ≤ Nat.card A)
    (h3 : p ^ 3 ≤ Nat.card A) :
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R)
      (σ : Multiplicative (Fin k → ZMod p) →* L')
      (Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A),
      Function.Injective τ ∧ (∀ f, ψ (σ f) = τ f) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        ∃ u ∈ Subgroup.closure (ggTorusInducedReflSet p τ),
          ∀ f, ψ n * τ f * (ψ n)⁻¹ = τ (u f) := by
  classical
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  obtain ⟨k, τ, hτinj, hτE, hsec, hnorm⟩ := h E hEab (hcardE ▸ hr) (hcardE ▸ h3)
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : Multiplicative (Fin k → ZMod p) →* ↥A := (Λ.comp τ).codRestrict A hτmem with hΘ₀
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτE] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij with hΘ
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  obtain ⟨σ, hσ⟩ := hsec L' ψ hψ hker
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => by rw [← MonoidHom.comp_apply, hσ]
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  refine ⟨k, τ, σ, Θ, hτinj, hψσ, hΘσ, fun n hn => ?_⟩
  have hψn : ψ n ∈ Subgroup.normalizer (E : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr
      show Λ (ψ n * r * (ψ n)⁻¹) ∈ A
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp hr
    · intro hr
      have h2 : Λ (ψ n * r * (ψ n)⁻¹) ∈ A := hr
      rw [map_mul, map_mul, map_inv, hΛn] at h2
      exact (Subgroup.mem_normalizer_iff.mp hn _).mpr h2
  exact hnorm (ψ n) hψn

end Model

end CFSG.StandardType

end
