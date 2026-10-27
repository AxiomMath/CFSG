module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivOmegaCent
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivSUTag
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin QuadraticMap

namespace LayerPDiv

open LayerCores LayerFacts

section Spin

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_subCoreFamily_spin_pDiv (hQ : (polarBilin Q).Nondegenerate)
    (hinj : Function.Injective (spinAction Q))
    (hrange : (spinAction Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (A : Subgroup (spinGroup Q)) (hA : Odd (Nat.card A)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ (β : Type) (S : β → Subgroup (spinGroup Q)),
      IsSubCoreFamily (Subgroup.centralizer (A : Set (spinGroup Q))) S ∧
        ∀ c, p ∣ Nat.card (S c) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  set A' := A.map (spinAction Q) with hA'
  have hA'O : A' ≤ O := by
    rintro _ ⟨a, -, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction Q a v
  have hA'odd : Odd (Nat.card A') := by
    rw [hA', Nat.card_congr (A.equivMapOfInjective _ hinj).toEquiv.symm]
    exact hA
  obtain ⟨β, S, hS, hSp⟩ := exists_subCoreFamily_orthCent_pDiv hQ hA'O hA'odd hp hp2 hpK
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
  rw [card_comap_of_le_range hinj (hle c)]
  exact hSp c

end Spin

theorem exists_eq_map_of_isComponentOf_sub {L : Type*} [Group L] [Finite L] {G : Type*}
    [Group G] [Finite G] (ψ : L →* G) (hker : ψ.ker ≤ Subgroup.center L) {H : Subgroup G}
    {C₀ : Subgroup L} (hC₀H : C₀.map ψ ≤ H) (hnorm : ((C₀.map ψ).subgroupOf H).Normal)
    (hcomm : ⁅H, H⁆ ≤ C₀.map ψ) {β : Type} {S : β → Subgroup L} (hS : IsSubCoreFamily C₀ S)
    {K : Subgroup G} (hK : IsComponentOf K H) : ∃ b, K = (S b).map ψ := by
  obtain ⟨hSC, hSn, hSq, hder, -⟩ := hS
  have hcomp : ∀ b, IsComponentOf ((S b).map ψ) H := by
    intro b
    have hKq : CFSG.Assembly.IsQuasisimple ((S b).map ψ) := by
      refine (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (CFSG.LocalCores.isQuasisimple_map (hSq b) ψ fun hle => ?_)
      obtain ⟨a, a', haa⟩ := exists_mul_ne_of_isQuasisimple (hSq b)
      exact haa (Subtype.ext (Subgroup.mem_center_iff.mp (hker (hle a.2)) a').symm)
    exact ⟨(Subgroup.map_mono (hSC b)).trans hC₀H,
      ggSubnormal_trans (ggSubnormal_map ψ (hSn b))
        (IsSubnormal.step hC₀H hnorm (IsSubnormal.refl H)), hKq⟩
  obtain ⟨k, hk⟩ := hder
  have hKq := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
    hK.2.2
  have hKle : K ≤ (⨆ b, S b).map ψ :=
    calc K = ggDer K (k + 1) :=
          (ggDer_of_perfect (ggCommutator_eq_of_isQuasisimple hKq) _).symm
      _ ≤ ggDer H (k + 1) := ggDer_mono hK.1 _
      _ = ggDer ⁅H, H⁆ k := ggDer_succ' H k
      _ ≤ ggDer (C₀.map ψ) k := ggDer_mono hcomm k
      _ = (ggDer C₀ k).map ψ := (map_ggDer ψ C₀ k).symm
      _ ≤ (⨆ b, S b).map ψ := Subgroup.map_mono hk
  by_contra hne
  have hc : ∀ b, (S b).map ψ ≤ Subgroup.centralizer (K : Set G) := by
    intro b
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK (hcomp b) with h | h
    · exact absurd ⟨b, h⟩ hne
    · rw [Subgroup.commutator_comm] at h
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hKc : K ≤ Subgroup.centralizer (K : Set G) := by
    refine hKle.trans ?_
    rw [Subgroup.map_iSup]
    exact iSup_le hc
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isQuasisimple hKq
  exact hab (Subtype.ext (Subgroup.mem_centralizer_iff.mp (hKc b.2) a a.2))

section Inner

variable {L : Type*} [Group L] [Finite L] {G : Type*} [Group G]

omit [Finite L] in
theorem exists_mem_ggConjPairs_of_inner {ψ : L →* G} {e : G}
    (h : ∃ g ∈ ψ.range, e * g ∈ Subgroup.centralizer (ψ.range : Set G)) :
    ∃ t, (e, t) ∈ ggConjPairs ψ := by
  obtain ⟨g, ⟨s, rfl⟩, hcg⟩ := h
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

theorem dvd_card_of_isComponentOf_inner [Finite G] {ψ : L →* G} (hinj : Function.Injective ψ)
    (hZL : Subgroup.center L = ⊥) {p : ℕ} {E : Subgroup G} (hE : IsPGroup p E)
    (hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ)
    (hcore : ∀ A : Subgroup L, IsPGroup p A → ∃ (β : Type) (S : β → Subgroup L),
      IsSubCoreFamily (Subgroup.centralizer (A : Set L)) S ∧ ∀ c, p ∣ Nat.card (S c))
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card K := by
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
  obtain ⟨β, S, hS, hdvd⟩ := hcore A hAp
  rw [hH] at hK
  obtain ⟨c, rfl⟩ := exists_eq_map_of_isComponentOf_sub ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) hS hK
  rw [Subgroup.card_map_of_injective hinj]
  exact hdvd c

end Inner

section SpinGroups

variable {G : Type*} [Group G] [Finite G] {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem dvd_card_of_isComponentOf_spinPlus_of_lifts (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n K) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {E : Subgroup G} (hE : IsPGroup p E)
    (hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card L := by
  have hZ := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have := finite_linearEquiv (K := K) (V := Fin n ⊕ Fin n → K)
  have : Finite (spinGroup (quadPlus n K)) :=
    Finite.of_injective _ (RootCentOmega.spinAction_quadPlus_injective (n := n) (K := K))
  refine dvd_card_of_isComponentOf_inner hinj hZ hE hlift (fun A hA => ?_) hL
  exact exists_subCoreFamily_spin_pDiv (nondegenerate_polarBilin_quadPlus n K)
    RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus_eq_commutator hn) A
    (odd_card_of_isPGroup hp hp2 hA) hp hp2 hpK

theorem dvd_card_of_isComponentOf_spinPlus_family (hn : 3 ≤ n)
    {ψ : spinGroup (quadPlus n K) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (plusDatum n K hn) ψ e) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card L :=
  dvd_card_of_isComponentOf_spinPlus_of_lifts hn hker hp hp2 hpK hE
    (fun e he => exists_mem_ggConjPairs_of_inner
      (PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hdiag e he))) hL

theorem dvd_card_of_isComponentOf_spinPlus (hn : 3 ≤ n) {ψ : spinGroup (quadPlus n K) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n K))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {y : G} (hy : y ^ p = 1)
    (hdiag : GGPsiInnerDiag (plusDatum n K hn) ψ y) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer ({y} : Set G))) :
    p ∣ Nat.card L := by
  obtain ⟨t, ht⟩ := exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hdiag)
  have hC : Subgroup.centralizer (Subgroup.zpowers y : Set G) = Subgroup.centralizer {y} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hC] at hL
  refine dvd_card_of_isComponentOf_spinPlus_of_lifts hn hker hp hp2 hpK
    (ggIsPGroup_zpowers_of_pow_eq_one hy) (fun e he => ?_) hL
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  exact ⟨t ^ k, (ggConjPairs ψ).zpow_mem ht k⟩

theorem dvd_card_of_isComponentOf_spinMinus_of_lifts {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {E : Subgroup G} (hE : IsPGroup p E)
    (hlift : ∀ e ∈ E, ∃ t, (e, t) ∈ ggConjPairs ψ) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card L := by
  have hZ := PsiDiag.SpinM.center_eq_bot hirr hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  have := finite_linearEquiv (K := K) (V := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)
  have : Finite (spinGroup (quadMinus n K b c)) :=
    Finite.of_injective _ (RootCentOmega.spinAction_quadMinus_injective (n := n) hirr)
  refine dvd_card_of_isComponentOf_inner hinj hZ hE hlift (fun A hA => ?_) hL
  exact exists_subCoreFamily_spin_pDiv (nondegenerate_polarBilin_quadMinus_of_finite n K hirr)
    (RootCentOmega.spinAction_quadMinus_injective hirr)
    (range_spinAction_quadMinus_eq_commutator hn hirr) A (odd_card_of_isPGroup hp hp2 hA) hp
    hp2 hpK

theorem dvd_card_of_isComponentOf_spinMinus_family {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n)
    {ψ : spinGroup (quadMinus n K b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {E : Subgroup G} (hE : IsPGroup p E)
    (hdiag : ∀ e ∈ E, GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ e) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (E : Set G))) :
    p ∣ Nat.card L :=
  dvd_card_of_isComponentOf_spinMinus_of_lifts hirr hn hker hp hp2 hpK hE
    (fun e he => exists_mem_ggConjPairs_of_inner
      (PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker (hdiag e he))) hL

theorem dvd_card_of_isComponentOf_spinMinus {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hn : 4 ≤ n) {ψ : spinGroup (quadMinus n K b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n K b c))) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K ^ 2 - 1) {y : G} (hy : y ^ p = 1)
    (hdiag : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ y) {L : Subgroup G}
    (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer ({y} : Set G))) :
    p ∣ Nat.card L := by
  obtain ⟨t, ht⟩ := exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hdiag)
  have hC : Subgroup.centralizer (Subgroup.zpowers y : Set G) = Subgroup.centralizer {y} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hC] at hL
  refine dvd_card_of_isComponentOf_spinMinus_of_lifts hirr hn hker hp hp2 hpK
    (ggIsPGroup_zpowers_of_pow_eq_one hy) (fun e he => ?_) hL
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
  exact ⟨t ^ k, (ggConjPairs ψ).zpow_mem ht k⟩

end SpinGroups

end LayerPDiv

section Tags

theorem ggLayerPDivTag_POmegaPlus : GGLayerPDivTag .POmegaPlus := by
  intro G _ _ n f
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    intro ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    exact LayerPDiv.dvd_card_of_isComponentOf_spinPlus hn hker hp hp2
      (by rw [hF]; exact LayerPDiv.dvd_sq_sub_one hpq) hy hdiag hK
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ G₀ hpres
    exact absurd hpres.1.2 (by decide)

theorem ggLayerPDivTag_POmegaMinus : GGLayerPDivTag .POmegaMinus := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hpq y hy _ hdiag K hK
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn⟩ := hadm
  subst hrange
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  exact LayerPDiv.dvd_card_of_isComponentOf_spinMinus (K := GaloisField 2 f)
    (minusCoeffs_irr 2 f) hn hker hp hp2 (by rw [hF]; exact LayerPDiv.dvd_sq_sub_one hpq) hy
    hdiag hK

theorem ggLayerPDivInput_of_remaining_five (hF4 : GGLayerPDivTag .F4)
    (hE6 : GGLayerPDivTag .E6) (hE7 : GGLayerPDivTag .E7) (hE8 : GGLayerPDivTag .E8)
    (hTwE6 : GGLayerPDivTag .twistedE6) : GGLayerPDivInput :=
  ggLayerPDivInput_of_remaining_seven ggLayerPDivTag_POmegaPlus ggLayerPDivTag_POmegaMinus hF4 hE6
    hE7 hE8 hTwE6

theorem ggSixLayerCXInput_of_pDivTags_five (hF4 : GGLayerPDivTag .F4)
    (hE6 : GGLayerPDivTag .E6) (hE7 : GGLayerPDivTag .E7) (hE8 : GGLayerPDivTag .E8)
    (hTwE6 : GGLayerPDivTag .twistedE6) (hNS : GGSixLayerCXNonsplitInput) : GGSixLayerCXInput :=
  ggSixLayerCXInput_of_split (ggLayerPDivInput_of_remaining_five hF4 hE6 hE7 hE8 hTwE6) hNS

end Tags

end CFSG.StandardType
