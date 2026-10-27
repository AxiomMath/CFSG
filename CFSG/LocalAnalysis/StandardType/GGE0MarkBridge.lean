module

public import CFSG.LocalAnalysis.StandardType.GGE0Frame
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIInnDiag
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcCore
public import CFSG.LocalAnalysis.StandardType.GGCanonicalToLegacy
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma31g
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.S10
open RawAutSmall

private theorem ggE0_pquot_le_center {G : Type} [Group G] {L : Subgroup G} {p : ℕ}
    (hL : CFSG.Assembly.IsQuasisimple ↥L)
    (hmark : CFSG.Assembly.LargeEvenMarking (PQuot p L) (fun _ _ _ _ _ _ => True)) :
    CFSG.Open.GLAPPrimeCore p ↥L ≤ Subgroup.center ↥L := by
  rcases CFSG.GH74.GLS.IVK.Proofs2.Lemma31g.normal_le_center_or_eq_top
      (⟨hL.1⟩ : Group.IsPerfect ↥L) hL.2 (CFSG.Open.GLAPPrimeCore p ↥L) with hle | htop
  · exact hle
  · exfalso
    obtain ⟨-, lab, hlab, hraw⟩ := hmark
    obtain ⟨S, _, I, F, _hs, hna, θ, -⟩ :=
      CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
    haveI : Subsingleton (PQuot p L) := by
      change Subsingleton (↥L ⧸ CFSG.Open.GLAPPrimeCore p ↥L)
      rw [QuotientGroup.subsingleton_iff]
      exact htop
    obtain ⟨a, b, hab⟩ := hna
    have hab' : a = b := θ.symm.injective (Subsingleton.elim (θ.symm a) (θ.symm b))
    exact hab (by rw [hab'])

private theorem ggE0_centerQuot_equiv {G H : Type*} [Group G] [Group H]
    (hG : commutator G = ⊤) (ψ : G →* H) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center G) :
    ∃ e : G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H,
      ∀ g : G, e (QuotientGroup.mk g) = QuotientGroup.mk (ψ g) := by
  let χ : G →* H ⧸ Subgroup.center H :=
    (QuotientGroup.mk' (Subgroup.center H)).comp ψ
  have hχ : Function.Surjective χ := (QuotientGroup.mk'_surjective _).comp hψ
  have hkerχ : χ.ker = Subgroup.center G := by
    have h1 : χ.ker = (Subgroup.center H).comap ψ := by
      change ((QuotientGroup.mk' (Subgroup.center H)).comp ψ).ker = _
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rw [h1]
    exact CFSG.LocalCores.comap_center_eq_of_perfect ⟨hG⟩ ψ hψ hker
  refine ⟨QuotientGroup.liftEquiv (N := Subgroup.center G) hχ hkerχ.symm, ?_⟩
  intro g
  exact QuotientGroup.liftEquiv_mk (N := Subgroup.center G) hχ hkerχ.symm g

private theorem ggE0_marking_of_innDiagOn {G : Type} [Group G] {X : Subgroup G} {ε : G}
    (hq : CFSG.Assembly.IsQuasisimple ↥X)
    (hmark : CFSG.Assembly.LargeEvenMarking (PQuot 2 X)
      (fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ (indRel 2 X ε) φ)) :
    CFSG.Assembly.LargeEvenMarking ↥X
      (fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
        (fun l l' : ↥X => (l' : G) = ε⁻¹ * l * ε) φ) := by
  let O : Subgroup ↥X := CFSG.Open.GLAPPrimeCore 2 ↥X
  have hO : O ≤ Subgroup.center ↥X := ggE0_pquot_le_center (L := X) (p := 2) hq
    (CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hmark)
  let κ : ↥X →* PQuot 2 X := QuotientGroup.mk' O
  have hκsurj : Function.Surjective κ := QuotientGroup.mk'_surjective O
  have hκker : κ.ker ≤ Subgroup.center ↥X := by
    simpa only [κ, QuotientGroup.ker_mk'] using hO
  obtain ⟨e, he⟩ := ggE0_centerQuot_equiv hq.1 κ hκsurj hκker
  refine CFSG.StandardType.Canonical.largeEvenMarking_mono ?_
    (CFSG.LocalAnalysis.GLTheoremA.K155X.l154_marking_transport hq.1 e.symm hmark)
  intro lab R _ I F θ hψ
  obtain ⟨φ, hφI, hind⟩ := hψ
  refine ⟨φ, hφI, fun x y hxy => ?_⟩
  have hrel : indRel 2 X ε (κ x) (κ y) := ⟨x, y, rfl, rfl, hxy⟩
  have h2 := hind (κ x) (κ y) hrel
  have hx : e.symm (QuotientGroup.mk (κ x)) = QuotientGroup.mk x := by
    rw [← he x, MulEquiv.symm_apply_apply]
  have hy : e.symm (QuotientGroup.mk (κ y)) = QuotientGroup.mk y := by
    rw [← he y, MulEquiv.symm_apply_apply]
  simpa only [MulEquiv.trans_apply, hx, hy] using h2

private theorem ggE0_rawDatum_legacy_of_canonical {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q)
    (hG2 : ∀ {K : Type} [Field K] [Finite K], Nat.card K = 2 →
      Q (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevParentIDImage LargeEvenCartanG2 K (LargeEvenChevGroup LargeEvenCartanG2 K)
          (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)) →
      Q (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true))
        (LargeEvenChevFieldImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K true)))
    (hTwF4 : ∀ {a : ℕ} {K : Type} [Field K] [Finite K], a = 0 →
      Nat.card K = 2 ^ (2 * a + 1) →
      Q (LargeEvenCenterQuot (LargeEvenTwF4H a K))
        (LargeEvenChevParentIDImage LargeEvenCartanF4 K (LargeEvenTwF4Parent a K)
          (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) →
      Q (LargeEvenCenterQuot (LargeEvenTwF4H a K))
        (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))) :
    LargeEvenRawDatumLegacy lab Q := by
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRawDatumLegacy] at h ⊢
  all_goals first
    | exact h
    | (dsimp only [LargeEvenRecipeG2Derived, LargeEvenRecipeChevalley] at h ⊢
       obtain ⟨K, hf, hfin, hK, hQ⟩ := h
       exact ⟨K, hf, hfin, hK, hG2 hK hQ⟩)
    | (dsimp only [LargeEvenRecipeTwF4Inherited, LargeEvenRecipeTwF4] at h ⊢
       obtain ⟨K, hf, hfin, hK, hQ⟩ := h
       by_cases ha : (n - 1) / 2 = 0
       · rw [if_pos ha] at hQ
         exact ⟨K, hf, hfin, hK, hTwF4 ha hK hQ⟩
       · rw [if_neg ha] at hQ
         exact ⟨K, hf, hfin, hK, hQ⟩)

private theorem ggE0_induces_pow_eq_one {G : Type*} [Group G] {R : Type} [Group R]
    (L : Subgroup G) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R) {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) {m : ℕ} (hbm : b ^ m = 1) {φ : MulAut R}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) : φ ^ m = 1 := by
  rw [eq_ggLAut_of_induces L θ hb h, ← map_pow]
  have hpow : (⟨b⁻¹, inv_mem hb⟩ : Subgroup.normalizer (L : Set G)) ^ m = 1 := by
    ext
    simp [inv_pow, hbm]
  rw [hpow, map_one]

private theorem ggE0_canonical_to_legacy
    {G : Type} [Group G] {E X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hE : ∀ ε ∈ E, ε ^ p = 1)
    (hN : E ≤ Subgroup.normalizer (X : Set G))
    (M : CFSG.Assembly.LargeEvenMarking ↥X (fun lab _ _ I _ θ => GGChevStTag lab ∧
      ∀ ε ∈ E, ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
        (fun l l' : ↥X => (l' : G) = ε⁻¹ * l * ε) φ)) :
    CFSG.StandardType.LargeEvenMarking ↥X (fun lab _ _ I _ θ => GGChevStTag lab ∧
      ∀ ε ∈ E, ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
        (fun l l' : ↥X => (l' : G) = ε⁻¹ * l * ε) φ) := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := M
  refine ⟨hperf, lab, hlab, ?_⟩
  refine ggE0_rawDatum_legacy_of_canonical hraw ?_ ?_
  · intro K _ _ hK hQ
    obtain ⟨hs, hna, θ, hChev, hφ⟩ := hQ
    refine ⟨hs, hna, θ, hChev, fun ε hε => ?_⟩
    obtain ⟨φ, hφI, hind⟩ := hφ ε hε
    have hm : Odd p := hp.odd_of_ne_two hp2
    have hφp : φ ^ p = 1 := ggE0_induces_pow_eq_one X θ (hN hε) (hE ε hε) hind
    have hinner := RawAutSmall.mem_inner_g2der hK hna hm hφp
    obtain ⟨r, rfl⟩ := hinner
    exact ⟨MulAut.conj r, conj_mem_chevIDImage _ r, hind⟩
  · intro a K _ _ ha hK hQ
    obtain ⟨hs, hna, θ, hChev, hφ⟩ := hQ
    refine ⟨hs, hna, θ, hChev, fun ε hε => ?_⟩
    obtain ⟨φ, hφI, hind⟩ := hφ ε hε
    have hm : Odd p := hp.odd_of_ne_two hp2
    have hφp : φ ^ p = 1 := ggE0_induces_pow_eq_one X θ (hN hε) (hE ε hε) hind
    have h2 : IsPGroup 2 (Outer (LargeEvenCenterQuot (LargeEvenTwF4H a K))) :=
      RawAutSmall.isPGroup_outer_twF4der ha hK
    have hinner := RawAut.mem_inner_of_isPGroup_outer h2 hm hφp
    obtain ⟨r, rfl⟩ := hinner
    exact ⟨MulAut.conj r, conj_mem_chevIDImage _ r, hind⟩

theorem ggE0Concl_of_innDiagOn_family {G : Type} [Group G] [Finite G] {E X : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hE : ∀ ε ∈ E, ε ^ p = 1)
    (hN : E ≤ Subgroup.normalizer (X : Set G))
    (hS2 : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GGChevStTag lab))
    (hI : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E, CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers ε) X) :
    GGE0Concl E X := by
  refine ⟨hN, fun hm => ?_⟩
  have hq : CFSG.Assembly.IsQuasisimple ↥X := isQuasisimple_of_largeEvenMarking hm
  have Mtag : CFSG.Assembly.LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GGChevStTag lab) :=
    largeEvenMarkingLegacy_to_canonical_carrier (hS2 hm)
  have h₁ : ∀ ε ∈ (E : Set G), CFSG.Assembly.LargeEvenMarking ↥X
      (fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ
        (fun l l' : ↥X => (l' : G) = ε⁻¹ * l * ε) φ) := by
    intro ε hε
    obtain ⟨-, hmark⟩ := hI hm ε hε
    exact ggE0_marking_of_innDiagOn hq
      (CFSG.StandardType.Canonical.largeEvenMarking_mono
        (fun _ _ _ I _ θ hP => hP ε (Subgroup.mem_zpowers ε)) hmark)
  have Mmerged := CFSG.LocalAnalysis.GLTheoremA.MI.marking_transport_family
    (fun (ε : G) (l l' : ↥X) => (l' : G) = ε⁻¹ * l * ε) (E : Set G) (Set.toFinite _) h₁ Mtag
  exact ggE0_canonical_to_legacy hp hp2 hE hN Mmerged

end CFSG.StandardType
