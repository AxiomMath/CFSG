module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5Cent
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineCoreAux
public import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem

theorem odd_card_primeCore_centralizer_of_twoLocalK (hK : T5TwoLocalK) {G : Type} [Group G]
    [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdTwD5 b₀ K E) {B : Basis3 G (5 + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD5 B b₀)
    (hD : Odd (Nat.card ↥(Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)))) {β : G} (hβ : β ∈ E) :
    Odd (Nat.card ↥(GLAPPrimeCoreOf 3 (Subgroup.centralizer ({β} : Set G)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstd0 : StdTwD5 b₀ K E := hstd
  obtain ⟨hGsimple, hHyp, hCanon⟩ := hstd
  obtain ⟨hb₀ord, hKC, hKn, hKz, hmark, hcyc, hrank, hconj, hEmax, hb₀E, hEcard, hXcard⟩ :=
    hHyp
  let Cβ : Subgroup G := Subgroup.centralizer ({β} : Set G)
  let N : Subgroup G := GLAPPrimeCoreOf 3 Cβ
  have hEelem : IsElemAbelian 3 E := hEmax.2.1
  have hEβ : E ≤ Cβ := by
    have hcent : E ≤ Subgroup.centralizer (E : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hEelem.1
    exact hcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hβ))
  have hNmap : N = (CFSG.pPrimeCore 3 ↥Cβ).map Cβ.subtype := rfl
  have hEnormN : E ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he n hn
    rw [hNmap, Subgroup.mem_map] at hn
    obtain ⟨a, ha, rfl⟩ := hn
    rw [hNmap, Subgroup.mem_map]
    refine ⟨⟨e, hEβ he⟩ * a * ⟨e, hEβ he⟩⁻¹, ?_, ?_⟩
    · exact (inferInstance : (CFSG.pPrimeCore 3 ↥Cβ).Normal).conj_mem a ha ⟨e, hEβ he⟩
    · simp
  have hNcop : Nat.Coprime 3 (Nat.card N) := by
    rw [hNmap, Subgroup.card_map_of_injective (Subgroup.subtype_injective Cβ)]
    exact CFSG.pPrimeCore_coprime_card
  have hle5 : twoLocalPrimeRank 3 ↥(Subgroup.centralizer ({b₀} : Set G)) ≤ 5 :=
    twoLocalPrimeRank_centralizer_le_five hKC hKn hKz hmark hcyc
      (centralizer_eq_sup_of_recOutTwD5 hstd0 hB hrec) hD hK
  rw [← Nat.not_even_iff_odd]
  intro hNeven
  have h2N : 2 ∣ Nat.card N := hNeven.two_dvd
  have hE3 : IsPGroup 3 E := hEelem.isPGroup
  obtain ⟨T, hTnorm, hTne⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      (GroupType := G) 3 2 Nat.prime_three Nat.prime_two E N hE3 hEnormN hNcop h2N
  let TG : Subgroup G := T.map N.subtype
  have hTG2 : IsPGroup 2 TG := T.isPGroup'.map N.subtype
  have hTGne : TG ≠ ⊥ := hTne
  have hETG : E ≤ Subgroup.normalizer (TG : Set G) := hTnorm
  have hTwoLocal : IsTwoLocal (Subgroup.normalizer (TG : Set G)) :=
    ⟨TG, hTGne, hTG2, rfl⟩
  have h6p : 6 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (TG : Set G)) :=
    fs81Nt_le_pRank (H := Subgroup.normalizer (TG : Set G)) (F := E) hETG hEelem hEcard
  have h6 : 6 ≤ twoLocalPrimeRank 3 G :=
    fs81Nt_le_twoLocalPrimeRank (H := Subgroup.normalizer (TG : Set G)) hTwoLocal h6p
  have h5 : twoLocalPrimeRank 3 G ≤ 5 := by
    rw [← hrank]
    exact hle5
  omega

end CFSG.StandardType.FrameRoute.FS81

end
