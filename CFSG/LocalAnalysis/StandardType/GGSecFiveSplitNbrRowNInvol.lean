module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
import CFSG.LocalAnalysis.StandardType.GGNbrFrameOneTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

@[expose] def GGTorusInvolFrameElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ ∧ τ.range = E ∧
      ∃ s₁ ∈ NbrTableBExc.ggTorusInvolSet p τ, ∃ s₂ ∈ NbrTableBExc.ggTorusInvolSet p τ,
        4 ∣ orderOf (s₁ * s₂)

theorem ggTorusFrame_of_involFrameElt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusInvolFrameElt p r R) :
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p r R I L' ψ A → GGTorusFrame p A := by
  classical
  intro L' _ _ ψ A hA
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
  set E : Subgroup R := A.comap Λ
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
  obtain ⟨k, τ, hτinj, hτE, s₁, hs₁, s₂, hs₂, h4⟩ := h E hEab (hcardE ▸ hr) (hcardE ▸ h3) hscE
  obtain ⟨hs₁sq, hs₁fix, w₁, hw₁⟩ := hs₁
  obtain ⟨hs₂sq, hs₂fix, w₂, hw₂⟩ := hs₂
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : Multiplicative (Fin k → ZMod p) →* ↥A := (Λ.comp τ).codRestrict A hτmem
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτE] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    rw [TableBUR.ker_eq_center_of_surjective hψ hker hZ]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hcpL
  have hτab : IsElemAbelian p τ.range := hτE ▸ hEab
  obtain ⟨σ₀, hσ₀⟩ := OrthRest.exists_section_of_coprime hψ hker hp hcop hτab
  set σ : Multiplicative (Fin k → ZMod p) →* L' := σ₀.comp τ.rangeRestrict
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => hσ₀ (τ.rangeRestrict f)
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  obtain ⟨n₁, hn₁ψ⟩ := hψ w₁
  have hconjψ₁ : ∀ f, ψ n₁ * ψ (σ f) * (ψ n₁)⁻¹ = ψ (σ (s₁ f)) := fun f => by
    rw [hn₁ψ, hψσ, hψσ, hw₁ f]
  obtain ⟨hn₁, heq₁⟩ := exists_ggConjAut_eq_congr hker Θ hΘσ hconjψ₁
  obtain ⟨n₂, hn₂ψ⟩ := hψ w₂
  have hconjψ₂ : ∀ f, ψ n₂ * ψ (σ f) * (ψ n₂)⁻¹ = ψ (σ (s₂ f)) := fun f => by
    rw [hn₂ψ, hψσ, hψσ, hw₂ f]
  obtain ⟨hn₂, heq₂⟩ := exists_ggConjAut_eq_congr hker Θ hΘσ hconjψ₂
  refine ⟨ggConjAut A hn₁, ⟨n₁, hn₁, ggTorusWeylElt_of_model hker Θ hΘσ
      (fun f => ⟨s₁ f, hconjψ₁ f⟩), rfl, heq₁ ▸ ggIsReflection_congr Θ hs₁sq hs₁fix⟩,
    ggConjAut A hn₂, ⟨n₂, hn₂, ggTorusWeylElt_of_model hker Θ hΘσ
      (fun f => ⟨s₂ f, hconjψ₂ f⟩), rfl, heq₂ ▸ ggIsReflection_congr Θ hs₂sq hs₂fix⟩, ?_⟩
  rw [heq₁, heq₂, ← map_mul, MulEquiv.orderOf_eq]
  exact h4

theorem ggTorusInvolFrameElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGTorusInvolFrameElt p r R') : GGTorusInvolFrameElt p r R := by
  intro E hE hr h3 hsc
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp b.2
      change (↑a : R') * ↑b = ↑b * ↑a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha' hb']
    · obtain ⟨x', hx', hx'e⟩ := Subgroup.mem_map.mp hx
      rw [← hx'e, ← map_pow, hE.2 x' hx', map_one]
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) e.injective
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    have hg₀ : e.symm g ∈ E := by
      refine hsc (e.symm g) (fun x hx => ?_) (by rw [← map_pow, hgp, map_one])
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨e.symm g, hg₀, by simp⟩
  obtain ⟨k, τ', hτ'inj, hτ'range, s₁, hs₁, s₂, hs₂, h4⟩ :=
    h (E.map e.toMonoidHom) hE' (by rw [hcard]; exact hr) (by rw [hcard]; exact h3) hsc'
  refine ⟨k, e.symm.toMonoidHom.comp τ', e.symm.injective.comp hτ'inj, ?_, s₁, ?_, s₂, ?_, h4⟩
  · rw [MonoidHom.range_comp, hτ'range, Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  · rw [NbrTableBExc.ggTorusInvolSet_comp_mulEquiv]
    exact hs₁
  · rw [NbrTableBExc.ggTorusInvolSet_comp_mulEquiv]
    exact hs₂

theorem ggTorusInvolFrameElt_of_conj {p r k : ℕ} {R : Type} [Group R]
    (e₀ : Multiplicative (Fin k → ZMod p) →* R) (he₀ : Function.Injective e₀)
    (hs : ∃ s₁ ∈ NbrTableBExc.ggTorusInvolSet p e₀, ∃ s₂ ∈ NbrTableBExc.ggTorusInvolSet p e₀,
      4 ∣ orderOf (s₁ * s₂))
    (hconj : ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
      (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∃ c : R, E = e₀.range.map (MulAut.conj c).toMonoidHom) :
    GGTorusInvolFrameElt p r R := by
  intro E hE hr h3 hsc
  obtain ⟨c, hc⟩ := hconj E hE hr h3 hsc
  obtain ⟨s₁, hs₁, s₂, hs₂, h4⟩ := hs
  refine ⟨k, (MulAut.conj c).toMonoidHom.comp e₀, (MulAut.conj c).injective.comp he₀, ?_, s₁,
    ?_, s₂, ?_, h4⟩
  · rw [MonoidHom.range_comp, hc]
  · rw [NbrTableBExc.ggTorusInvolSet_comp_mulEquiv]
    exact hs₁
  · rw [NbrTableBExc.ggTorusInvolSet_comp_mulEquiv]
    exact hs₂

end CFSG.StandardType

end
