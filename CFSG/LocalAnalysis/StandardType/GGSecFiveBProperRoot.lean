module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootDefs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3BridgeA2
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootPerm
import CFSG.LocalAnalysis.StandardType.GGSecFiveBProperRootTransp
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G] [Finite G]

private theorem mulAut_ne_one_of_normalizes_two {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hne : B ≠ Bs) {g : G}
    {τ : MulAut ↥Bs} (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1)
    (hτcoe : ∀ b : ↥Bs, ((τ b : ↥Bs) : G) = g * (b : G) * g⁻¹) : τ ≠ 1 := by
  classical
  intro hτ1
  have hcomm : ∀ b : ↥Bs, (b : G) * g = g * (b : G) := by
    intro b
    have hb : g * (b : G) * g⁻¹ = (b : G) := by
      rw [← hτcoe b, hτ1, MulAut.one_apply]
    calc (b : G) * g = (g * (b : G) * g⁻¹) * g := by rw [hb]
      _ = g * (b : G) := by group
  let T : Subgroup G := Subgroup.zpowers g
  have hT1 : T ≠ ⊥ := by
    change Subgroup.zpowers g ≠ ⊥
    rw [Subgroup.zpowers_ne_bot]
    exact hg1
  have hT2 : IsPGroup 2 T :=
    IsPGroup.of_card (n := 1) (by
      change Nat.card (Subgroup.zpowers g) = 2 ^ 1
      rw [Nat.card_zpowers, orderOf_eq_prime hg2 hg1, pow_one])
  have hTN : Bs ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    have hbg : b * g * b⁻¹ = g := by
      rw [hcomm ⟨b, hb⟩]
      group
    have hfixb : ∀ y ∈ Subgroup.zpowers g, b * y * b⁻¹ = y := by
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow, hbg]
    have hfixi : ∀ y ∈ Subgroup.zpowers g, b⁻¹ * y * b = y := by
      intro y hy
      calc b⁻¹ * y * b = b⁻¹ * (b * y * b⁻¹) * b := by rw [hfixb y hy]
        _ = y := by group
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hfixb y hy]
      exact hy
    · intro hy
      have h1 := hfixi (b * y * b⁻¹) hy
      rw [show b⁻¹ * (b * y * b⁻¹) * b = y by group] at h1
      rwa [h1]
  exact hne (ggBstar_eq_of_normalizes_two hcfg hT2 hT1 hTN).symm


private theorem exists_pair_of_unitary_range {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hne : B ≠ Bs) {F : Type} [Field F] [Finite F] {f d : ℕ}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBL : B ≤ Subgroup.normalizer (L : Set G)) {φ : ↥(unitarySU 2 f F d) →* ↥L}
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t)
    (hd : 4 ≤ d) (hpq : p ∣ 2 ^ f + 1) (hf1 : 1 ≤ f) :
    ∃ s t : Fin d, s ≠ t ∧ ∀ a ∈ (ggGamma L hBL).range,
      ∀ σ : Fin d → Fˣ, SmallU.ActsU φ a σ → σ s = σ t := by
  classical
  obtain ⟨hp, -⟩ := ggRouteCfg_prime hR
  let : Fact p.Prime := ⟨hp⟩
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBs := hcfg.2.1.2.1
  have hL : commutator L = ⊤ := hR.1.2.2.1.1.1
  obtain ⟨θ, hZR, hOD, h3⟩ :=
    exists_theta_center_ggOutdiagOdd_of_unitary hBBs hN hM hdiag hf1 hd
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ggLNoncyclicInput_holds G p B x L hcfg.1
  obtain ⟨V, hV1, hV2, hBV⟩ :=
    hcfg.beta_twoLocal_of_ne hnc hL θ hBL h3 hOD hne
  set A : Subgroup (MulAut ↥L) := (ggGamma L hBL).range with hA
  have hdiagA : ∀ a ∈ A, ∃ t : Fin d → F, LineU.ActsDiagU φ a t := by
    rintro _ ⟨b, rfl⟩
    have h := hdiag (ggGamma L hN ⟨b.1, hBBs b.2⟩) ⟨⟨b.1, hBBs b.2⟩, rfl⟩
    rw [ggGamma_y_eq_of_le hN hBL b.2 (hBBs b.2)] at h
    exact h
  have hAp : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨b, rfl⟩
    have hb : (b : ↥B) ^ p = 1 := Subtype.ext (by simpa using hBs.2 b.1 (hBBs b.2))
    rw [← map_pow, hb, map_one]
  have hK : Nat.card F = (2 ^ f) ^ 2 := by
    rw [hM.field.card, ← pow_mul, Nat.mul_comm]
  have hAU : ∀ a ∈ A, ∀ l : ↥L, ggQuotHom θ l ∈ V → ggQuotHom θ (a l) ∈ V := by
    rintro _ ⟨b, rfl⟩ l hl
    have h := hBV (ggBeta L θ hBL b) ⟨b, rfl⟩ (ggQuotHom θ l) hl
    rw [← ggBeta_ggQuotHom]
    exact h
  exact SmallU.exists_pair hM hK hd hp hpq (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hZR hAp hdiagA hV1 hV2 hAU

theorem GGSecFiveRouteCfg.exists_equal_pair_of_unitary {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hne : B ≠ Bs) {F : Type} [Field F] [Finite F] {f d : ℕ}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {φ : ↥(unitarySU 2 f F d) →* ↥L}
    (hM : UnitTB.Model φ)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → F, LineU.ActsDiagU φ a t)
    (hd : 4 ≤ d) (hpq : p ∣ 2 ^ f + 1) :
    ∃ s t : Fin d, s ≠ t ∧ ∀ b : ↥Bs, (b : G) ∈ B →
      ∀ σ : Fin d → Fˣ, SmallU.ActsU φ (ggGamma L hN b) σ → σ s = σ t := by
  have hBBs : B ≤ Bs := hR.1.1.2.1.1
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
  have hp : p.Prime := (ggRouteCfg_prime hR).1
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with hf0 | hfpos
    · rw [hf0] at hpq
      exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by simpa using hpq))
        (ggRouteCfg_prime hR).2
    · exact hfpos
  obtain ⟨s, t, hst, hpair⟩ :=
    exists_pair_of_unitary_range hR hne hN hBL hM hdiag hd hpq hf1
  refine ⟨s, t, hst, ?_⟩
  intro b hb σ hσ
  have hγ : ggGamma L hN b = ggGamma L hBL ⟨b.1, hb⟩ := ggGamma_y_eq_of_le hN hBL hb b.2
  rw [hγ] at hσ
  exact hpair _ ⟨⟨b.1, hb⟩, rfl⟩ σ hσ

theorem ggSecFiveBProperRootInput_of_model (h : GGSecFiveBPermUnitaryModelInput) :
    GGSecFiveBProperRootInput := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 hR hne n eta hJoin hAut
  obtain ⟨F, hF, hFfin, _, f, d, hN, φ, hd, hpq, _, hM, hdiag⟩ :=
    h G p B Bs x L D J 𝒦 hR hne n eta hJoin hAut
  have hcfg : GGConfig p B Bs x L D J := hR.1.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hBs := hcfg.2.1.2.1
  have hcard : Nat.card Bs ≤ p * Nat.card B := hcfg.2.1.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  obtain ⟨s, t, hst, hpair⟩ :=
    GGSecFiveRouteCfg.exists_equal_pair_of_unitary hR hne hN hM hdiag hd hpq
  obtain ⟨g, hgL, hgN, hg1, hg2, hgfix⟩ :=
    exists_native_transposition hM (by omega : 3 ≤ d) hN hBs hSC hdiag hst
  let τ : MulAut ↥Bs := Bs.normalizerMonoidHom ⟨g, hgN⟩
  have hτcoe : ∀ b : ↥Bs, ((τ b : ↥Bs) : G) = g * (b : G) * g⁻¹ := fun b =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Bs ⟨g, hgN⟩ b
  have hτind : τ ∈ ggInduced L Bs := ⟨g, hgL, hgN, hτcoe⟩
  have hτL : τ ∈ ggAutomizer L Bs := Subgroup.subset_closure hτind
  have hg2' : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (Bs : Set G))) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using hg2
  have hτ2 : τ ^ 2 = 1 := by
    change (Bs.normalizerMonoidHom ⟨g, hgN⟩) ^ 2 = 1
    rw [← map_pow, hg2', map_one]
  have hfix : ∀ b : ↥Bs, (b : G) ∈ B → τ b = b := by
    intro b hb
    apply Subtype.ext
    rw [hτcoe b]
    exact (hgfix b).mpr (hpair b hb)
  have hτ1 : τ ≠ 1 :=
    mulAut_ne_one_of_normalizes_two hcfg hne hg1 hg2 hτcoe
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  exact exists_root_hyperplane_of_involution hp hp2 hBBs hBs hcard hne eta hAut hτL hτ2 hτ1 hfix

end CFSG.StandardType

end
