module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNormModel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

namespace NbrFrameNine

@[expose] def GGTorusOrderNineElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ ∧ τ.range = E ∧
      ∃ (w : R) (s : MulAut (Multiplicative (Fin k → ZMod p))),
        (∀ f, w * τ f * w⁻¹ = τ (s f)) ∧ 9 ∣ orderOf s

theorem ggTorusOrderNine_of_elt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hZp : GGCenterPrime p R) (h : GGTorusOrderNineElt p r R) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusOrderNine p A := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, -⟩ := hA
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
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
      exact TableB.IsElemAbelian.comm hAe e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe.2 _ he
  obtain ⟨k, τ, hτinj, hτE, w, s, hws, h9⟩ := h E hEab (hcardE ▸ hr) (hcardE ▸ h3)
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
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    rw [TableBUR.ker_eq_center_of_surjective hψ hker hZ]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (hZp L' ψ hψ hker hperf)
  have hτab : IsElemAbelian p τ.range := hτE ▸ hEab
  obtain ⟨σ₀, hσ₀⟩ := OrthRest.exists_section_of_coprime hψ hker hp hcop hτab
  set σ : Multiplicative (Fin k → ZMod p) →* L' := σ₀.comp τ.rangeRestrict with hσ
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => hσ₀ (τ.rangeRestrict f)
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  obtain ⟨n, rfl⟩ := hψ w
  have hconjψ : ∀ f, ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ (s f)) := fun f => by
    rw [hψσ, hψσ]
    exact hws f
  obtain ⟨hn, heq⟩ := exists_ggConjAut_eq_congr hker Θ hΘσ hconjψ
  refine ⟨n, hn, ggTorusWeylElt_of_model hker Θ hΘσ (fun f => ⟨s f, hconjψ f⟩), ?_⟩
  rw [heq, MulEquiv.orderOf_eq]
  exact h9

end NbrFrameNine

end CFSG.StandardType

end
