module

public import CFSG.Assembly.LargeEvenDefs
import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly

private theorem kg7canon_induces_pow_three {R : Type} [Group R] {Kc : Subgroup R}
    {φ : MulAut R} (hφ : ∀ x ∈ Kc, φ x ∈ Kc) (hφ3 : φ ^ 3 = 1)
    {R' : Type} [Group R'] {θ : ↥Kc ⧸ Subgroup.center ↥Kc ≃* R'} {ψ : MulAut R'}
    (hind : LargeEvenInduces θ (fun l l' : ↥Kc => (l' : R) = φ l) ψ) : ψ ^ 3 = 1 := by
  let f : ↥Kc → ↥Kc := fun l => ⟨φ (l : R), hφ (l : R) l.2⟩
  have hf3 : ∀ l : ↥Kc, f (f (f l)) = l := by
    intro l
    apply Subtype.ext
    have hφ3' : φ * φ * φ = 1 := by rw [← pow_three']; exact hφ3
    have h := congrArg (fun e : MulAut R => e (l : R)) hφ3'
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    simpa [f] using h
  rw [pow_three']
  ext y
  obtain ⟨q, rfl⟩ := θ.surjective y
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, hind l (f l) rfl,
    hind (f l) (f (f l)) rfl, hind (f (f l)) (f (f (f l))) rfl, hf3 l]

private theorem kg7canon_rawDatum_legacy_of_canonical {lab : LargeEvenLabel}
    {Q : LargeEvenRawCont}
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

theorem legacyMarking_of_canonical_induces
    {R : Type} [Group R] {Kc : Subgroup R}
    {φ : MulAut R} (hφ : ∀ x ∈ Kc, φ x ∈ Kc) (hφ3 : φ ^ 3 = 1)
    (h : CFSG.Assembly.LargeEvenMarking ↥Kc fun _ _ _ I _ θ =>
      ∃ ψ ∈ I, LargeEvenInduces θ (fun l l' : ↥Kc => (l' : R) = φ l) ψ) :
    CFSG.StandardType.LargeEvenMarking ↥Kc fun _ _ _ I _ θ =>
      ∃ ψ ∈ I, LargeEvenInduces θ (fun l l' : ↥Kc => (l' : R) = φ l) ψ := by
  obtain ⟨hc, lab, hlab, hraw⟩ := h
  refine ⟨hc, lab, hlab, ?_⟩
  refine kg7canon_rawDatum_legacy_of_canonical hraw ?_ ?_
  · intro K _ _ hK hQ
    obtain ⟨hs, hna, θ, ψ, _, hind⟩ := hQ
    refine ⟨hs, hna, θ, ψ, ?_, hind⟩
    have hψ3 : ψ ^ 3 = 1 := kg7canon_induces_pow_three hφ hφ3 hind
    obtain ⟨r, rfl⟩ := RawAutSmall.mem_inner_g2der hK hna ⟨1, rfl⟩ hψ3
    exact conj_mem_chevIDImage _ r
  · intro a K _ _ ha hK hQ
    obtain ⟨hs, hna, θ, ψ, _, hind⟩ := hQ
    refine ⟨hs, hna, θ, ψ, ?_, hind⟩
    have hψ3 : ψ ^ 3 = 1 := kg7canon_induces_pow_three hφ hφ3 hind
    obtain ⟨r, rfl⟩ := RawAut.mem_inner_of_isPGroup_outer
      (RawAutSmall.isPGroup_outer_twF4der ha hK) ⟨1, rfl⟩ hψ3
    exact conj_mem_chevIDImage _ r

end CFSG.StandardType.TwE6KG7
