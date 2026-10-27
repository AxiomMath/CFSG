module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUInnerShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SULift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2SUNCShort
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ItemThree
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverNC
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSU
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryMain

public section

namespace CFSG.StandardType.LieKnownR2.PSU

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open CFSG.LieType.BorelTits (unitaryInvolution)

private theorem l10sbsu_ggRootSub_id {U : Type} [Group U] (Δ : UniversalRootDatum U)
    (γ : Fin Δ.rank → ℤ) (u : U) :
    ggRootSub Δ (MonoidHom.id U) γ u =
      (Δ.rootGroup γ).map (MulAut.conj u).toMonoidHom := by
  rw [ggRootSub, Subgroup.map_id]

private theorem l10sbsu_false_of_mem_roots_trivialUniversal (L : LieUniversal)
    (hL : L = trivialUniversal) {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots) : False := by
  subst hL
  rcases hβ with ⟨w, i, -⟩ | ⟨w, i, -, -⟩ <;> exact i.elim0

private theorem l10sbsu_pow_two_eq_two {f : ℕ} (h : 2 ^ f = 2) : f = 1 :=
  Nat.pow_right_injective (le_refl 2) (h.trans (pow_one 2).symm)

private theorem l10sbsu_pair_ne_of_not {f n : ℕ} (hnf : ¬ (n = 3 ∧ f = 1)) :
    (n, 2 ^ f) ≠ (3, 2) := by
  rintro h
  exact hnf ⟨congrArg Prod.fst h, l10sbsu_pow_two_eq_two (congrArg Prod.snd h)⟩

private theorem l10sbsu_one_le_of_card_eq_sq {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) : 1 ≤ f := by
  by_contra h
  have hf0 : f = 0 := by omega
  have h1 : Nat.card F = 1 := by simpa [hf0] using hF
  haveI : Fintype F := Fintype.ofFinite F
  have h2 : 1 < Fintype.card F := Fintype.one_lt_card
  rw [Nat.card_eq_fintype_card] at h1
  omega

private theorem l10sbsu_inner_range_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    (L : LieUniversal)
    (hL : L = ⟨Unitary.SU (unitaryInvolution F 2 f) n, Unitary.rootDatum hF n⟩)
    {X : Type} [Group X] [Finite X] (φ : L.K →* X)
    (hker : φ.ker ≤ Subgroup.center L.K)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots)
    (hpos : GGLongRoot L.D β ∨ (6 ≤ n ∧ 2 ≤ f ∧ 2 • β ∉ L.D.roots))
    (u : L.K) :
    GGRootNormInner ((ggRootSub L.D φ β u).subgroupOf φ.range) := by
  subst hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map, l10sbsu_ggRootSub_id]
  have hR : IsPGroup 2 (((Unitary.rootDatum hF n).rootGroup β).map
      (MulAut.conj u).toMonoidHom) :=
    (CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF)
      (CFSG.LieType.Universal.Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβ)).map
      (MulAut.conj u).toMonoidHom
  have hI : PSL.GGRootNormInnerZ
      (((Unitary.rootDatum hF n).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
    rcases hpos with hl | ⟨h6, hf2, h2β⟩
    · exact ggRootNormInnerZ_su_long hF hn hnf hl u
    · by_cases hs : GGLongRoot (Unitary.rootDatum hF n) β
      · exact ggRootNormInnerZ_su_long hF hn hnf hs u
      · exact ggRootNormInnerZ_su_short hF h6 hf2 hβ hs h2β u
  exact ggRootNormInner_map_SU hF hn hnf φ hker hR hI

private theorem l10sbsu_noCentralAt_of_eq {F : Type} [Field F] [Finite F] [CharP F 2]
    {f n : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1))
    (L : LieUniversal)
    (hL : L = ⟨Unitary.SU (unitaryInvolution F 2 f) n, Unitary.rootDatum hF n⟩)
    {X : Type} [Group X] [Finite X] (φ : L.K →* X)
    (hker : φ.ker ≤ Subgroup.center L.K)
    {β : Fin L.D.rank → ℤ} (hβ : β ∈ L.D.roots)
    (hpos : GGLongRoot L.D β ∨ (6 ≤ n ∧ 2 ≤ f ∧ 2 • β ∉ L.D.roots))
    (u : L.K) :
    GGRootNoCentralAt φ.range (ggRootSub L.D φ β u) := by
  subst hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hf1 : 1 ≤ f := l10sbsu_one_le_of_card_eq_sq hF
  have hodd : Odd (Nat.card φ.ker) := by
    have h1 : Nat.card φ.ker ∣ Nat.card (Subgroup.center
        ↥(Unitary.SU (unitaryInvolution F 2 f) n)) := Subgroup.card_dvd_of_le hker
    exact Odd.of_dvd_nat
      (CFSG.SeitzReduction.SymplecticPilot.odd_card_center_SU hF hf1 hn
        (l10sbsu_pair_ne_of_not hnf)) h1
  have hR : IsPGroup 2 (ggRootSub (Unitary.rootDatum hF n) (MonoidHom.id _) β u) := by
    rw [l10sbsu_ggRootSub_id]
    exact (CFSG.LieType.Steinberg.isPGroup_rootGroup
      (CFSG.LieType.BorelTits.unitaryInvolution_involutive hF)
      (CFSG.LieType.Universal.Unitary.SUExtras.toStd_ne_zero_of_mem_roots hβ)).map
      (MulAut.conj u).toMonoidHom
  have hNCC : GGRootNoCentralAt (⊤ : Subgroup ↥(Unitary.SU (unitaryInvolution F 2 f) n))
      (ggRootSub (Unitary.rootDatum hF n) (MonoidHom.id _) β u) := by
    rw [l10sbsu_ggRootSub_id]
    rcases hpos with hl | ⟨h6, hf2, h2β⟩
    · exact ggRootNoCentral_su_long hF hn hnf hl u
    · by_cases hs : GGLongRoot (Unitary.rootDatum hF n) β
      · exact ggRootNoCentral_su_long hF hn hnf hs u
      · exact ggRootNoCentral_su_short hF hf2 hβ hs h2β u
  have hmap := CFSG.StandardType.LieKnownR2.SpecialLinearNC.ggRootNoCentralAt_map_of_odd_central_ker
    φ hker hodd hR hNCC
  rwa [← CFSG.StandardType.LieKnownR2.Short.ggRootSub_eq_map] at hmap

private theorem l10sbsu_inner_range
    {n f : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1)) {X : Type} [Group X] [Finite X]
    (φ : (ggU .PSU n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .PSU n f).K)
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hpos : GGLongRoot (ggU .PSU n f).D β ∨
      (6 ≤ n ∧ 2 ≤ f ∧ 2 • β ∉ (ggU .PSU n f).D.roots))
    (u : (ggU .PSU n f).K) :
    GGRootNormInner ((ggRootSub (ggU .PSU n f).D φ β u).subgroupOf φ.range) := by
  have hf1 : 1 ≤ f := by
    by_contra h
    have e : ggU .PSU n f = trivialUniversal := by
      simp only [ggU, lieUniversal, h, ↓reduceDIte]
    exact l10sbsu_false_of_mem_roots_trivialUniversal _ e hβ
  have e : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) n⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
  exact l10sbsu_inner_range_of_eq (card_galoisField_two_mul 2 f hf1) hn hnf _ e φ hker hβ hpos u

theorem ggRootInnerAt_ggU_psu
    {n f : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1)) {X : Type} [Group X] [Finite X]
    (φ : (ggU .PSU n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .PSU n f).K)
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hpos : GGLongRoot (ggU .PSU n f).D β ∨
      (6 ≤ n ∧ 2 ≤ f ∧ 2 • β ∉ (ggU .PSU n f).D.roots))
    (u : (ggU .PSU n f).K) :
    GGRootInnerAt φ.range (ggRootSub (ggU .PSU n f).D φ β u) := by
  have hI := l10sbsu_inner_range hn hnf φ hker hβ hpos u
  intro Y hY2 hYK hYR hNY
  refine ggRootNormInner_le_sup_centralizer ?_ hYK hYR hY2 hNY hI
  exact Subgroup.map_le_range _ _

theorem itemThree_ggU_psu
    {n f : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1)) {X : Type} [Group X] [Finite X]
    (ψ : (ggU .PSU n f).K →* X) (hker : ψ.ker ≤ Subgroup.center (ggU .PSU n f).K)
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hpos : GGLongRoot (ggU .PSU n f).D β ∨
      (6 ≤ n ∧ 2 ≤ f ∧ 2 • β ∉ (ggU .PSU n f).D.roots))
    (u : (ggU .PSU n f).K) {R : Subgroup X} (hR : R = ggRootSub (ggU .PSU n f).D ψ β u) :
    ∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
      Y ≤ Subgroup.normalizer (R : Set X) →
      ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
        pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
      Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X) := by
  have hI := l10sbsu_inner_range hn hnf ψ hker hβ hpos u
  intro Y hY2 hYK hYR hcomm
  refine ggRootNormInner_le_sup_centralizer_of_commutator ?_ hYK hYR hY2 hcomm ?_
  · rw [hR]
    exact Subgroup.map_le_range _ _
  · rw [hR]
    exact hI

theorem ggRootNoCentralAt_ggU_psu
    {n f : ℕ} (hn : 3 ≤ n) (hnf : ¬ (n = 3 ∧ f = 1)) {X : Type} [Group X] [Finite X]
    (φ : (ggU .PSU n f).K →* X) (hker : φ.ker ≤ Subgroup.center (ggU .PSU n f).K)
    {β : Fin (ggU .PSU n f).D.rank → ℤ} (hβ : β ∈ (ggU .PSU n f).D.roots)
    (hpos : GGLongRoot (ggU .PSU n f).D β ∨
      (6 ≤ n ∧ 2 ≤ f ∧ 2 • β ∉ (ggU .PSU n f).D.roots))
    (u : (ggU .PSU n f).K) :
    GGRootNoCentralAt φ.range (ggRootSub (ggU .PSU n f).D φ β u) := by
  have hf1 : 1 ≤ f := by
    by_contra h
    have e0 : ggU .PSU n f = trivialUniversal := by
      simp only [ggU, lieUniversal, h, ↓reduceDIte]
    exact l10sbsu_false_of_mem_roots_trivialUniversal _ e0 hβ
  have e : ggU .PSU n f = ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
      Unitary.rootDatum (card_galoisField_two_mul 2 f hf1) n⟩ := by
    simp only [ggU, lieUniversal, hf1, ↓reduceDIte]
  exact l10sbsu_noCentralAt_of_eq (card_galoisField_two_mul 2 f hf1) hn hnf _ e φ hker hβ hpos u

end CFSG.StandardType.LieKnownR2.PSU
