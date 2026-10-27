module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsOmegaCent
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin QuadraticMap

namespace LayerExcThree

open LayerCores LayerFacts

section Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_subCoreFamily_spin_excThree (hQ : (polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (A : Subgroup (spinGroup Q)) (hA : Odd (Nat.card A)) (hK4 : 4 ≤ Nat.card K) :
    ∃ (β : Type) (S : β → Subgroup (spinGroup Q)),
      IsSubCoreFamily (Subgroup.centralizer (A : Set (spinGroup Q))) S ∧
        ∀ c, GGNotExcThreeOrder (ggCQ (S c)) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set A' := A.map (spinAction Q) with hA'
  have hA'O : A' ≤ O := by
    rintro _ ⟨a, -, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q a v
  have hA'odd : Odd (Nat.card A') := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv.symm]
    exact hA
  obtain ⟨β, S, hS, hSp⟩ := exists_subCoreFamily_orthCent_excThree hQ hA'O hA'odd hK4
  have hSinf := hS.inf_of_commutator_le (N := ⁅O, O⁆)
    (Subgroup.commutator_mono inf_le_right inf_le_right)
  have hle : ∀ c, S c ≤ (spinAction Q).range := fun c => by
    rw [hrange]
    exact (hSinf.1 c).trans inf_le_right
  have hS' := hSinf.comap (spinAction Q) hinj (by rw [hrange]; exact inf_le_right)
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
  refine ⟨β, _, hS', fun c => ?_⟩
  rw [ggCQ_comap_of_injective _ hinj (hle c)]
  exact hSp c

end Spin

section Inner

variable {L : Type*} [Group L] [Finite L] {G : Type*} [Group G]

theorem ggNotExcThree_of_isComponentOf_inner [Finite G] {ψ : L →* G}
    (hinj : Function.Injective ψ) (hZL : Subgroup.center L = ⊥) {p : ℕ} {E : Subgroup G}
    (hE : IsPGroup p E) (hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ)
    (hcore : ∀ A : Subgroup L, IsPGroup p A → ∃ (β : Type) (S : β → Subgroup L),
      IsSubCoreFamily (Subgroup.centralizer (A : Set L)) S ∧
        ∀ c, GGNotExcThreeOrder (ggCQ (S c)))
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    GGNotExcThreeOrder (ggCQ K) := by
  have hker : ψ.ker ≤ Subgroup.center L := by
    rw [(MonoidHom.ker_eq_bot_iff ψ).mpr hinj]
    exact bot_le
  have hZ1 : ∀ g : L, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [hZL, Subgroup.mem_bot] at h
  set A := ggConjLifts ψ E with hA
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
  obtain ⟨β, S, hS, hgood⟩ := hcore A hAp
  rw [hH] at hK
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf_sub ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) hS hK
  rw [ggCQ_map_of_injective _ hinj]
  exact hgood c

end Inner

section SpinGroups

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggNotExcThree_of_isComponentOf_spinPlus (hn : 3 ≤ n) {ψ : spinGroup (quadPlus n K) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {y : G} (hy : y ^ p = 1)
    (hdiag : GGPsiInnerDiag (plusDatum n K hn) ψ y) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer ({y} : Set G))) :
    GGNotExcThreeOrder (ggCQ L) := by
  have hZ := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have := finite_linearEquiv (K := K) (V := Fin n ⊕ Fin n → K)
  have : Finite (spinGroup (quadPlus n K)) :=
    Finite.of_injective _ (RootCentOmega.spinAction_quadPlus_injective (n := n) (K := K))
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hdiag)
  have hC : Subgroup.centralizer (Subgroup.zpowers y : Set G) = Subgroup.centralizer {y} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hC] at hL
  refine ggNotExcThree_of_isComponentOf_inner hinj hZ (ggIsPGroup_zpowers_of_pow_eq_one hy)
    (fun e he => ?_) (fun A hA => ?_) hL
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨t ^ k, (ggConjPairs ψ).zpow_mem ht k⟩
  · exact exists_subCoreFamily_spin_excThree (nondegenerate_polarBilin_quadPlus n K)
      RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus_eq_commutator hn) A
      (odd_card_of_isPGroup hp hp2 hA) hK4

theorem ggNotExcThree_of_isComponentOf_spinMinus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn : 4 ≤ n) {ψ : spinGroup (quadMinus n K b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK4 : 4 ≤ Nat.card K) {y : G} (hy : y ^ p = 1)
    (hdiag : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ y) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer ({y} : Set G))) :
    GGNotExcThreeOrder (ggCQ L) := by
  have hZ := PsiDiag.SpinM.center_eq_bot hirr hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have := finite_linearEquiv (K := K) (V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
  have : Finite (spinGroup (quadMinus n K b c)) :=
    Finite.of_injective _ (RootCentOmega.spinAction_quadMinus_injective (n := n) hirr)
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hdiag)
  have hC : Subgroup.centralizer (Subgroup.zpowers y : Set G) = Subgroup.centralizer {y} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hC] at hL
  refine ggNotExcThree_of_isComponentOf_inner hinj hZ (ggIsPGroup_zpowers_of_pow_eq_one hy)
    (fun e he => ?_) (fun A hA => ?_) hL
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ⟨t ^ k, (ggConjPairs ψ).zpow_mem ht k⟩
  · exact exists_subCoreFamily_spin_excThree
      (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
      (RootCentOmega.spinAction_quadMinus_injective hirr)
      (range_spinAction_quadMinus_eq_commutator hn hirr) A (odd_card_of_isPGroup hp hp2 hA) hK4

end SpinGroups

theorem ggAKFG_four_le_card_galoisField {f : ℕ} (hf : 2 ≤ f) :
    4 ≤ Nat.card (GaloisField 2 f) := by
  rw [GaloisField.card 2 f (by omega)]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end LayerExcThree

section Tags

theorem ggAKFG_excThree_POmegaPlus : ∀ (G : Type) [Group G] [Finite G] (n f : ℕ)
    (ψ : (ggU .POmegaPlus n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ → 2 ≤ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ y : G, y ^ p = 1 → GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        GGNotExcThreeOrder (ggCQ C) := by
  intro G _ _ n f
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    intro ψ G₀ hpres hf p hp hp2 y hy hdiag C hC
    obtain ⟨⟨-, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    exact LayerExcThree.ggNotExcThree_of_isComponentOf_spinPlus hn hker hp hp2
      (LayerExcThree.ggAKFG_four_le_card_galoisField hf) hy hdiag hC
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ G₀ hpres
    exact absurd hpres.1.2 (by decide)

theorem ggAKFG_excThree_POmegaMinus : ∀ (G : Type) [Group G] [Finite G] (n f : ℕ)
    (ψ : (ggU .POmegaMinus n f).K →* G) (G₀ : Subgroup G),
    GGPresentsG0 G₀ (ggU .POmegaMinus n f).D .POmegaMinus n f ψ → 2 ≤ f →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ y : G, y ^ p = 1 →
      GGPsiInnerDiag (ggU .POmegaMinus n f).D ψ y →
      ∀ C : Subgroup G, IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y}) →
        GGNotExcThreeOrder (ggCQ C) := by
  intro G _ _ n f ψ G₀ hpres hf2 p hp hp2 y hy hdiag C hC
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, -, hn⟩ := hadm
  subst hrange
  exact LayerExcThree.ggNotExcThree_of_isComponentOf_spinMinus (K := GaloisField 2 f)
    (minusCoeffs_irr 2 f) hn hker hp hp2 (LayerExcThree.ggAKFG_four_le_card_galoisField hf2) hy
    hdiag hC

theorem ggLayerNotDFourTwoTag_POmegaPlus : GGLayerNotDFourTwoTag .POmegaPlus := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree
    (ggAKFG_excThree_POmegaPlus G n f ψ G₀ hpres hf p hp hp2 y hy hdiag C hC)).1

theorem ggLayerNotDFourTwoTag_POmegaMinus : GGLayerNotDFourTwoTag .POmegaMinus := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree
    (ggAKFG_excThree_POmegaMinus G n f ψ G₀ hpres hf p hp hp2 y hy hdiag C hC)).1

theorem ggLayerNotUFourAltSixTag_POmegaPlus : GGLayerNotUFourAltSixTag .POmegaPlus := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree
    (ggAKFG_excThree_POmegaPlus G n f ψ G₀ hpres hf p hp hp2 y hy hdiag C hC)).2

theorem ggLayerNotUFourAltSixTag_POmegaMinus : GGLayerNotUFourAltSixTag .POmegaMinus := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree
    (ggAKFG_excThree_POmegaMinus G n f ψ G₀ hpres hf p hp hp2 y hy hdiag C hC)).2

end Tags

end CFSG.StandardType
