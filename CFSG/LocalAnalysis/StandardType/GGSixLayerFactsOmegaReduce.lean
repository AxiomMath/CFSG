module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaDefs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSp
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin QuadraticMap

@[expose] def GGOrthCentralizerCoreInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    ∀ A : Subgroup (V ≃ₗ[K] V), A ≤ TauCeti.QuadraticMap.orthogonalGroup Q → Odd (Nat.card A) →
      ∃ (β : Type) (S : β → Subgroup (V ≃ₗ[K] V)),
        LayerCores.IsSubCoreFamily
          (Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ TauCeti.QuadraticMap.orthogonalGroup Q) S

namespace LayerFacts

section Inner

variable {L : Type*} [Group L] [Finite L] {G : Type*} [Group G]

theorem ggLayer_of_inner {ψ : L →* G} (hinj : Function.Injective ψ)
    (hZL : Subgroup.center L = ⊥) {p : ℕ} {E : Subgroup G} (hE : IsPGroup p E)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hinner : ∀ e ∈ E, ∃ g ∈ ψ.range, e * g ∈ Subgroup.centralizer (ψ.range : Set G))
    (hcore : ∀ A : Subgroup L, IsPGroup p A → (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      ∃ (β : Type) (S : β → Subgroup L),
        LayerCores.IsSubCoreFamily (Subgroup.centralizer (A : Set L)) S) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  have hker : ψ.ker ≤ Subgroup.center L := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hinj]
    exact bot_le
  have hZ1 : ∀ g : L, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [hZL, Subgroup.mem_bot] at h
  set A := ggConjLifts ψ E with hA
  have hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ := by
    intro e he
    obtain ⟨g, ⟨s, rfl⟩, hcg⟩ := hinner e he
    refine ⟨s⁻¹, fun u => ?_⟩
    have h := Subgroup.mem_centralizer_iff.mp hcg (ψ (s⁻¹ * u * s)) ⟨_, rfl⟩
    have h2 : ψ (s⁻¹ * u * s) * e * ψ s = e * ψ u * ψ s := by
      calc ψ (s⁻¹ * u * s) * e * ψ s = ψ (s⁻¹ * u * s) * (e * ψ s) := by group
        _ = e * ψ s * ψ (s⁻¹ * u * s) := h
        _ = e * ψ (s * (s⁻¹ * u * s)) := by rw [map_mul ψ s]; group
        _ = e * ψ u * ψ s := by rw [show s * (s⁻¹ * u * s) = u * s by group, map_mul]; group
    rw [inv_inv]
    calc ψ (s⁻¹ * u * s) = ψ (s⁻¹ * u * s) * e * ψ s * (ψ s)⁻¹ * e⁻¹ := by group
      _ = e * ψ u * ψ s * (ψ s)⁻¹ * e⁻¹ := by rw [h2]
      _ = e * ψ u * e⁻¹ := by group
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨e, he, hea⟩ := mem_ggConjLifts.mp ha
    obtain ⟨e', he', heb⟩ := mem_ggConjLifts.mp hb
    have h1 := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hea heb)
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem heb hea))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hcomm e he e' he',
      mul_inv_cancel] at h1
    exact mul_inv_eq_one.mp (hZ1 _ h1)
  have hAp : IsPGroup p A := by
    intro t
    obtain ⟨e, he, het⟩ := mem_ggConjLifts.mp t.2
    obtain ⟨k, hk⟩ := hE ⟨e, he⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hek : e ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h1 := (ggConjPairs ψ).pow_mem het (p ^ k)
    rw [Prod.pow_mk, hek] at h1
    simpa using hZ1 _ h1
  have hH : ψ.range ⊓ Subgroup.centralizer (E : Set G) =
      (Subgroup.centralizer (A : Set L)).map ψ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨⟨u, rfl⟩, hu⟩ := Subgroup.mem_inf.mp hx
      refine ⟨u, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_, rfl⟩
      obtain ⟨e, he, het⟩ := mem_ggConjLifts.mp ht
      have h2 : e * ψ u * e⁻¹ = ψ u := by
        rw [Subgroup.mem_centralizer_iff.mp hu e he]
        group
      have h3 := hinj ((het u).trans h2)
      calc t * u = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [h3]
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨u, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
      obtain ⟨t, het⟩ := hlift e he
      have htA : t ∈ A := mem_ggConjLifts.mpr ⟨e, he, het⟩
      have h1 := het u
      have h2 : t * u * t⁻¹ = u := by
        rw [Subgroup.mem_centralizer_iff.mp hu t htA]
        group
      rw [h2] at h1
      calc e * ψ u = e * ψ u * e⁻¹ * e := by group
        _ = ψ u * e := by rw [← h1]
  obtain ⟨β, S, hS⟩ := hcore A hAp hAcomm
  rw [hH]
  refine (ggLayer_of_subcore ψ hker le_rfl ?_ (ggCommutator_self_le _) hS).2
  rw [Subgroup.subgroupOf_self]
  infer_instance

end Inner

end LayerFacts

namespace LayerCores

section Spin

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
theorem finite_linearEquiv [FiniteDimensional K V] : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)

variable [CharP K 2] {Q : QuadraticForm K V}

theorem exists_subCoreFamily_spin (hcore : GGOrthCentralizerCoreInput)
    (hQ : (polarBilin Q).Nondegenerate) (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (A : Subgroup (spinGroup Q)) (hA : Odd (Nat.card A)) :
    ∃ (β : Type) (S : β → Subgroup (spinGroup Q)),
      IsSubCoreFamily (Subgroup.centralizer (A : Set (spinGroup Q))) S := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set A' := A.map (spinAction Q) with hA'
  have hA'O : A' ≤ O := by
    rintro _ ⟨a, -, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q a v
  have hA'odd : Odd (Nat.card A') := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv.symm]
    exact hA
  obtain ⟨β, S, hS⟩ := hcore K V Q hQ A' hA'O hA'odd
  have hS' := (hS.inf_of_commutator_le (N := ⁅O, O⁆)
    (Subgroup.commutator_mono inf_le_right inf_le_right)).comap (spinAction Q) hinj
    (by rw [hrange]; exact inf_le_right)
  have hC : ((Subgroup.centralizer (A' : Set (V ≃ₗ[K] V)) ⊓ O) ⊓ ⁅O, O⁆).comap (spinAction Q) =
      Subgroup.centralizer (A : Set (spinGroup Q)) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨⟨hx, -⟩, -⟩ a ha
      exact hinj (by rw [map_mul, map_mul]; exact hx _ ⟨a, ha, rfl⟩)
    · intro hx
      refine ⟨⟨?_, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q x v⟩,
        by rw [← hrange]; exact ⟨x, rfl⟩⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, ← map_mul, hx a ha]
  rw [hC] at hS'
  exact ⟨β, _, hS'⟩

theorem odd_card_of_isPGroup {L : Type*} [Group L] [Finite L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {A : Subgroup L} (hA : IsPGroup p A) : Odd (Nat.card A) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  rw [hk]
  exact (hp.odd_of_ne_two hp2).pow

end Spin

end LayerCores

namespace LayerFacts

open LayerCores

variable {G : Type*} [Group G] {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggLayer_spinPlus (hcore : GGOrthCentralizerCoreInput) (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n K) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (plusDatum n K hn) ψ e) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  have hZ := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have := finite_linearEquiv (K := K) (V := Fin n ⊕ Fin n → K)
  have : Finite (spinGroup (quadPlus n K)) :=
    Finite.of_injective _ (RootCentOmega.spinAction_quadPlus_injective (n := n) (K := K))
  exact ggLayer_of_inner hinj hZ hE hcomm
    (fun e he => PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hdiag e he))
    fun A hA _ => exists_subCoreFamily_spin hcore (nondegenerate_polarBilin_quadPlus n K)
      RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus_eq_commutator hn) A
      (odd_card_of_isPGroup hp hp2 hA)

theorem ggLayer_spinMinus (hcore : GGOrthCentralizerCoreInput) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsPGroup p E) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ e) :
    Odd (Nat.card (Subgroup.center
        ↥(LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G))))) ∧
      ∀ X : Subgroup G, X ≤ ψ.range ⊓ Subgroup.centralizer (E : Set G) → ⁅X, X⁆ = X →
        X ≤ LargeEvenLayer (ψ.range ⊓ Subgroup.centralizer (E : Set G)) := by
  have hZ := PsiDiag.SpinM.center_eq_bot hirr hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have := finite_linearEquiv (K := K) (V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
  have : Finite (spinGroup (quadMinus n K b c)) :=
    Finite.of_injective _ (RootCentOmega.spinAction_quadMinus_injective (n := n) hirr)
  exact ggLayer_of_inner hinj hZ hE hcomm
    (fun e he => PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker (hdiag e he))
    fun A hA _ => exists_subCoreFamily_spin hcore
      (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (RootCentOmega.spinAction_quadMinus_injective hirr)
      (range_spinAction_quadMinus_eq_commutator hn hirr) A (odd_card_of_isPGroup hp hp2 hA)

end LayerFacts

section Tags

theorem ggLayerTags_POmegaPlus_of_core (hcore : GGOrthCentralizerCoreInput) :
    GGLayerCentreOddTag .POmegaPlus ∧ GGLayerPerfectTag .POmegaPlus := by
  refine ⟨fun G _ _ n f => ?_, fun G _ _ n f => ?_⟩ <;>
  · by_cases hn : 3 ≤ n
    · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
          plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
      intro ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag
      obtain ⟨-, ⟨hrange, hker⟩, -, -⟩ := hpres
      subst hrange
      have h := LayerFacts.ggLayer_spinPlus (K := GaloisField 2 f) hcore hn hker hp hp2 hE hcomm
        hdiag
      first
      | exact h.1
      | exact h.2
    · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
      intro ψ G₀ hpres
      exact absurd hpres.1.2 (by decide)

theorem ggLayerTags_POmegaMinus_of_core (hcore : GGOrthCentralizerCoreInput) :
    GGLayerCentreOddTag .POmegaMinus ∧ GGLayerPerfectTag .POmegaMinus := by
  refine ⟨fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_,
    fun G _ _ n f ψ G₀ hpres _ p hp hp2 E hE hcomm _ hdiag => ?_⟩ <;>
  · obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    obtain ⟨-, -, hn⟩ := hadm
    subst hrange
    have h := LayerFacts.ggLayer_spinMinus (K := GaloisField 2 f) hcore (minusCoeffs_irr 2 f) hn
      hker hp hp2 hE hcomm hdiag
    first
    | exact h.1
    | exact h.2

end Tags

end CFSG.StandardType
