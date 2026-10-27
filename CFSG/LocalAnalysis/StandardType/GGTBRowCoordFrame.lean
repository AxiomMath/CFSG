module

public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBExcInduced
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusCoordFrame (p : ℕ) {R : Type} [Group R] {k : ℕ}
    (τ : Multiplicative (Fin k → ZMod p) →* R) {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  ∃ s : ι → MulAut (Multiplicative (Fin k → ZMod p)),
    (∀ i, s i ∈ NbrTableBExc.ggTorusInvolSet p τ) ∧
    ∃ e : M.Group ≃* ↥(ggTorusInduced τ),
      ∀ i, (e (M.simple i) : MulAut (Multiplicative (Fin k → ZMod p))) = s i

@[expose] def GGTorusCoordFrameElt (p r : ℕ) (R : Type) [Group R] {ι : Type}
    (M : CoxeterMatrix ι) : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∀ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ →
      τ.range = E → GGTorusCoordFrame p τ M

@[expose] def GGTorusWeylFrameW (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) {ι : Type}
    (M : CoxeterMatrix ι) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A → GGWeylFrame p A M

theorem ggTorusWeylFrameW_of_coordFrameElt {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type}
    [Group R] {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hG : GGTorusWeylGenElt p r R) {ι : Type}
    {M : CoxeterMatrix ι} (hF : GGTorusCoordFrameElt p r R M) :
    GGTorusWeylFrameW p r R I M := by
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, -⟩ := hA
  obtain ⟨k, τ, σ, Θ, hτ, hψσ, hΘ, hModelN⟩ :=
    exists_weylGenModel hp hp2 hI hZ hG hψ hker hperf hAe hAI hr h3
  have hrefl : ggTorusInducedReflSet p τ ⊆ (ggTorusInduced τ : Set _) := by
    rintro u ⟨-, -, w, hw⟩
    exact mem_ggTorusInduced.mpr ⟨w, hw⟩
  have hnorm : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u ∈ ggTorusInduced τ, ∀ f, ψ n * τ f * (ψ n)⁻¹ = τ (u f) := by
    intro n hn
    obtain ⟨u, hu, hnu⟩ := hModelN n hn
    exact ⟨u, (Subgroup.closure_le (ggTorusInduced τ)).mpr hrefl hu, hnu⟩
  have hcard : Nat.card τ.range = Nat.card A :=
    Nat.card_congr ((MonoidHom.ofInjective hτ).toEquiv.symm.trans Θ.toEquiv)
  have hEab : IsElemAbelian p τ.range :=
    isElemAbelian_range (fun a b => mul_comm a b)
      (fun a => pow_eq_one_of_multiplicative_fin_zmod a) τ
  have hrE : p ^ r ≤ Nat.card τ.range := by rw [hcard]; exact hr
  have h3E : p ^ 3 ≤ Nat.card τ.range := by rw [hcard]; exact h3
  have hAut := ggAutomizer_eq_map_ggTorusInduced hψ hker Θ hψσ hΘ hnorm
  obtain ⟨s, hs, e₀, he₀⟩ := hF (τ.range) hEab hrE h3E k τ hτ rfl
  have hdata : ∀ i : ι, ∃ (n : L')
      (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      GGTorusWeylElt p A n ∧ GGIsReflection p (MulAut.congr Θ (s i)) ∧
        ggConjAut A hn = MulAut.congr Θ (s i) := by
    intro i
    have hsi := hs i
    simp only [NbrTableBExc.ggTorusInvolSet, Set.mem_setOf_eq] at hsi
    obtain ⟨hs2, hsfix, w, hw⟩ := hsi
    obtain ⟨n, rfl⟩ := hψ w
    have hconjψ : ∀ f, ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ (s i f)) :=
      fun f => by simpa only [hψσ] using hw f
    obtain ⟨hn, heq⟩ := exists_ggConjAut_eq_congr hker Θ hΘ hconjψ
    exact ⟨n, hn, ggTorusWeylElt_of_model hker Θ hΘ (fun f => ⟨s i f, hconjψ f⟩),
      ⟨by rw [← map_pow, hs2, map_one],
        (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs2) hsfix).2⟩, heq⟩
  choose n hn hweyl hrefl' heq using hdata
  have hrefl'' : ∀ i, GGIsReflection p (ggConjAut A (hn i)) := fun i => by
    rw [heq i]
    exact hrefl' i
  have hconj_inj : Function.Injective ((MulAut.congr Θ).toMonoidHom) :=
    fun a b h => (MulAut.congr Θ).injective h
  let Φ : ↥(ggTorusInduced τ) ≃*
      ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
    (Subgroup.equivMapOfInjective (ggTorusInduced τ) (MulAut.congr Θ).toMonoidHom
      hconj_inj).trans (MulEquiv.subgroupCongr hAut.symm)
  refine ⟨n, hn, hweyl, hrefl'', e₀.trans Φ, fun i => ?_⟩
  simp only [Φ, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    Subgroup.coe_equivMapOfInjective_apply, he₀ i, heq i]
  rfl

end CFSG.StandardType

end
