module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNormModel
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

namespace NbrTableBExc

@[expose] def ggTorusInvolSet (p : ℕ) {R : Type} [Group R] {k : ℕ}
    (τ : Multiplicative (Fin k → ZMod p) →* R) :
    Set (MulAut (Multiplicative (Fin k → ZMod p))) :=
  {s | s ^ 2 = 1 ∧
    Nat.card {f : Multiplicative (Fin k → ZMod p) // s f = f} * p =
      Nat.card (Multiplicative (Fin k → ZMod p)) ∧
    ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (s f)}

@[expose] def GGTorusInducedReflElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∀ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ → τ.range = E →
      ggTorusInduced τ ≤ Subgroup.closure (ggTorusInvolSet p τ)

@[expose] def GGTorusInducedCardElt (p r : ℕ) (R : Type) [Group R] (N : ℕ) : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∀ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* R), Function.Injective τ → τ.range = E →
      Nat.card (ggTorusInduced τ) = N

section Invariance

variable {p r : ℕ} {R : Type} [Group R]

private theorem mem_ggTorusInvolSet {p : ℕ} {R : Type} [Group R] {k : ℕ}
    {τ : Multiplicative (Fin k → ZMod p) →* R}
    {s : MulAut (Multiplicative (Fin k → ZMod p))} :
    s ∈ ggTorusInvolSet p τ ↔ s ^ 2 = 1 ∧
      Nat.card {f : Multiplicative (Fin k → ZMod p) // s f = f} * p =
        Nat.card (Multiplicative (Fin k → ZMod p)) ∧
      ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (s f) :=
  Iff.rfl

private theorem mulAut_congr_apply {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (f : MulAut G) (x : H) : MulAut.congr e f x = e (f (e.symm x)) := by
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply]

theorem ggTorusInvolSet_comp_mulEquiv {R' : Type} [Group R'] {k : ℕ} (e : R ≃* R')
    (τ : Multiplicative (Fin k → ZMod p) →* R) :
    ggTorusInvolSet p (e.toMonoidHom.comp τ) = ggTorusInvolSet p τ := by
  ext s
  simp only [mem_ggTorusInvolSet]
  constructor
  · rintro ⟨hs2, hfix, w, hw⟩
    refine ⟨hs2, hfix, e.symm w, fun f => e.injective ?_⟩
    have h1 := hw f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using h1
  · rintro ⟨hs2, hfix, w, hw⟩
    refine ⟨hs2, hfix, e w, fun f => ?_⟩
    have h1 := congrArg e (hw f)
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv] using h1

theorem mem_ggTorusInvolSet_comp_equiv {k m : ℕ}
    (γ : Multiplicative (Fin k → ZMod p) ≃* Multiplicative (Fin m → ZMod p))
    (χ : Multiplicative (Fin m → ZMod p) →* R) (s : MulAut (Multiplicative (Fin k → ZMod p))) :
    s ∈ ggTorusInvolSet p (χ.comp γ.toMonoidHom) ↔ MulAut.congr γ s ∈ ggTorusInvolSet p χ := by
  simp only [mem_ggTorusInvolSet]
  constructor
  · rintro ⟨hs2, hfix, w, hw⟩
    refine ⟨?_, ?_, w, fun f => ?_⟩
    · rw [← map_pow, hs2, map_one]
    · have hfix' : Nat.card {f : Multiplicative (Fin k → ZMod p) // s f = f} =
          Nat.card {g : Multiplicative (Fin m → ZMod p) //
            MulAut.congr γ s g = g} :=
        Nat.card_congr (Equiv.subtypeEquiv γ.toEquiv fun f => by
          simp only [mulAut_congr_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
            MulEquiv.symm_apply_apply]
          exact γ.injective.eq_iff.symm)
      have hcardVW : Nat.card (Multiplicative (Fin k → ZMod p)) =
          Nat.card (Multiplicative (Fin m → ZMod p)) := Nat.card_congr γ.toEquiv
      rw [← hfix', hfix, hcardVW]
    · have h1 := hw (γ.symm f)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mulAut_congr_apply,
        MulEquiv.apply_symm_apply] using h1
  · rintro ⟨hs2, hfix, w, hw⟩
    refine ⟨?_, ?_, w, fun f => ?_⟩
    · have h : MulAut.congr γ (s ^ 2) = MulAut.congr γ 1 := by
        rw [map_pow, hs2, map_one]
      exact (MulAut.congr γ).injective h
    · have hfix' : Nat.card {f : Multiplicative (Fin k → ZMod p) // s f = f} =
          Nat.card {g : Multiplicative (Fin m → ZMod p) //
            MulAut.congr γ s g = g} :=
        Nat.card_congr (Equiv.subtypeEquiv γ.toEquiv fun f => by
          simp only [mulAut_congr_apply, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv,
            MulEquiv.symm_apply_apply]
          exact γ.injective.eq_iff.symm)
      have hcardVW : Nat.card (Multiplicative (Fin k → ZMod p)) =
          Nat.card (Multiplicative (Fin m → ZMod p)) := Nat.card_congr γ.toEquiv
      rw [hfix', hfix, hcardVW]
    · have h1 := hw (γ f)
      simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mulAut_congr_apply,
        MulEquiv.symm_apply_apply] using h1

theorem ggTorusInducedReflElt_of_mulEquiv {R' : Type} [Group R'] (e : R ≃* R')
    (h : GGTorusInducedReflElt p r R') : GGTorusInducedReflElt p r R := by
  intro E hE hr h3 k τ hτ hτE
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hrange : (e.toMonoidHom.comp τ).range = E.map e.toMonoidHom := by
    rw [MonoidHom.range_comp, hτE]
  have key := h (E.map e.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3) k
    (e.toMonoidHom.comp τ) (e.injective.comp hτ) hrange
  rwa [ggTorusInduced_comp_mulEquiv e τ, ggTorusInvolSet_comp_mulEquiv e τ] at key

theorem ggTorusInducedCardElt_of_mulEquiv {R' : Type} [Group R'] {N : ℕ} (e : R ≃* R')
    (h : GGTorusInducedCardElt p r R' N) : GGTorusInducedCardElt p r R N := by
  intro E hE hr h3 k τ hτ hτE
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hrange : (e.toMonoidHom.comp τ).range = E.map e.toMonoidHom := by
    rw [MonoidHom.range_comp, hτE]
  have key := h (E.map e.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3) k
    (e.toMonoidHom.comp τ) (e.injective.comp hτ) hrange
  rwa [ggTorusInduced_comp_mulEquiv e τ] at key

end Invariance

section Transfer

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusTBGroup_pow {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    {A : Subgroup (MulAut L')} (hA : GGTorusTBGroup p r R I L' ψ A) :
    GGTorusTBGroup p r R {φ | φ ∈ I ∧ φ ^ p = 1} L' ψ A := by
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hA
  refine ⟨hψ, hker, hperf, hAe, fun a ha => ?_, hr, h3, hsc⟩
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨φ, ⟨hφ, ?_⟩, hφa⟩
  have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [hk p l, hAe.2 a ha]
  rfl

theorem ggTorusReflGenW_of_inducedReflElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hG : GGTorusWeylGenElt p r R) (hW : GGTorusInducedReflElt p r R) :
    GGTorusReflGenW p r R I := by
  intro L' _ _ ψ A hA v hv
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
  have hW' : ggTorusInduced τ ≤ Subgroup.closure (ggTorusInvolSet p τ) :=
    hW (τ.range) hEab hrE h3E k τ hτ rfl
  set H : Subgroup (MulAut (Multiplicative (Fin k → ZMod p))) :=
    (Subgroup.closure (ggTorusReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hgen : ∀ s ∈ ggTorusInvolSet p τ, s ∈ H := by
    intro s hs
    obtain ⟨hs2, hsfix, w, hw⟩ := mem_ggTorusInvolSet.mp hs
    obtain ⟨n, rfl⟩ := hψ w
    have hconjψ : ∀ f, ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ (s f)) :=
      fun f => by simpa only [hψσ] using hw f
    obtain ⟨hn, heq⟩ := exists_ggConjAut_eq_congr hker Θ hΘ hconjψ
    have hweyl : GGTorusWeylElt p A n :=
      ggTorusWeylElt_of_model hker Θ hΘ (fun f => ⟨s f, hconjψ f⟩)
    have hrefl2 : GGIsReflection p (MulAut.congr Θ s) :=
      ⟨by rw [← map_pow, hs2, map_one],
        (ggIsPseudoReflection_congr Θ (SpCoord.pow_sub_one_eq_one_of_sq hp hp2 hs2)
          hsfix).2⟩
    rw [hH]
    exact Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨n, hn, hweyl, heq.symm, hrefl2⟩)
  have hmem : Subgroup.closure (ggTorusInvolSet p τ) ≤ H := (Subgroup.closure_le H).mpr hgen
  have hAut := ggAutomizer_eq_map_ggTorusInduced hψ hker Θ hψσ hΘ hnorm
  rw [hAut] at hv
  obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp hv
  have huH : u ∈ H := hmem (hW' hu)
  rw [hH, Subgroup.mem_comap] at huH
  exact huv ▸ huH

theorem ggTorusAutCardDvdSCr_of_inducedCardElt {N : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hG : GGTorusWeylGenElt p r R) (hN : GGTorusInducedCardElt p r R N) :
    GGTorusAutCardDvdSCr p r R I N := by
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
  have hN' : Nat.card (ggTorusInduced τ) = N := hN (τ.range) hEab hrE h3E k τ hτ rfl
  have hcardAut : Nat.card ((ggTorusInduced τ).map (MulAut.congr Θ).toMonoidHom) =
      Nat.card (ggTorusInduced τ) :=
    Subgroup.card_map_of_injective (MulAut.congr Θ).injective
  rw [hAut]
  exact dvd_of_eq (by rw [hcardAut, hN'])

theorem ggTorusReflGenW_of_card_lt
    (hX : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3) : GGTorusReflGenW p r R I := by
  classical
  intro L' _ _ ψ A hA
  obtain ⟨hψ, hker, hperf, hAe, hAI, -, h3, -⟩ := hA
  exfalso
  have hXA : IsElemAbelian p (TypeA.inducedSub ψ A) := TypeA.isElemAbelian_inducedSub hψ hAe
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩)
  have hlt := hX _ hXI hXA
  rw [hcardX] at hlt
  omega

theorem ggTorusReflGenW_of_pow (h : GGTorusReflGenW p r R {φ | φ ∈ I ∧ φ ^ p = 1}) :
    GGTorusReflGenW p r R I :=
  fun L' _ _ ψ A hA => h L' ψ A (ggTorusTBGroup_pow hA)

theorem ggTorusAutCardDvdSCr_of_pow {N : ℕ}
    (h : GGTorusAutCardDvdSCr p r R {φ | φ ∈ I ∧ φ ^ p = 1} N) :
    GGTorusAutCardDvdSCr p r R I N :=
  fun L' _ _ ψ A hA => h L' ψ A (ggTorusTBGroup_pow hA)

end Transfer

end NbrTableBExc

end CFSG.StandardType

end
