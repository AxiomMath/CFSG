module

public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneCoord
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneEltDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFrameNineTransfer
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative NbrFrameOne

theorem ggTorusCoordModel {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hp2 : p ≠ 2) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R)
    (Q : ∀ k : ℕ, (Multiplicative (Fin k → ZMod p) →* R) → Prop)
    (h : ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ ∧
        τ.range = E ∧ Q k τ)
    (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p r R I L' ψ A) :
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R)
      (Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A),
      Function.Injective τ ∧ Q k τ ∧
      ∀ (φ : MulAut (Multiplicative (Fin k → ZMod p))) (w : R),
        (∀ f, w⁻¹ * τ f * w = τ (φ f)) →
        ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          GGTorusWeylElt p A n ∧ ggConjAut A hn = MulAut.congr Θ φ := by
  classical
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hAe.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
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
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛeq rfl, hn] at h1
    exact h1
  obtain ⟨k, τ, hτinj, hτE, hQ⟩ := h E hEab (hcardE ▸ h3) hscE
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
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hcpL
  have hτab : IsElemAbelian p τ.range := hτE ▸ hEab
  obtain ⟨σ₀, hσ₀⟩ := OrthRest.exists_section_of_coprime hψ hker hp hcop hτab
  set σ : Multiplicative (Fin k → ZMod p) →* L' := σ₀.comp τ.rangeRestrict with hσ
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => hσ₀ (τ.rangeRestrict f)
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  refine ⟨k, τ, Θ, hτinj, hQ, fun φ w hw => ?_⟩
  obtain ⟨n, hnψ⟩ := hψ w⁻¹
  have hconjψ : ∀ f, ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ (φ f)) := by
    intro f
    rw [hnψ, hψσ, hψσ, inv_inv, hw f]
  obtain ⟨hn, heq⟩ := exists_ggConjAut_eq_congr hker Θ hΘσ hconjψ
  exact ⟨n, hn, ggTorusWeylElt_of_model hker Θ hΘσ (fun f => ⟨φ f, hconjψ f⟩), heq⟩

end CFSG.StandardType

end
