module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.TransLocal
import CFSG.CharacterTheory.BlockBasics.Sections
import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveTrivialCoreSupport
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five

theorem isCyclic_of_le_of_isoLie_sz32
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    {p : ℕ} (hp5 : p = 5) {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (hL : CFSG.RankThree.PartOne.Census3.IsoLie ↥(CFSG.generalizedFitting X) (.suzuki 2))
    {T : Subgroup X} (hTN : T ≤ N) (hT : IsPGroup 2 T) : IsCyclic T := by
  subst hp5
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  classical
  obtain ⟨-, -, hKn, hKC⟩ :=
    CFSG.RankThree.PartOne.Sec1511.spe_fstar (p := 5) Nat.prime_five hO hN
  obtain ⟨hv, ⟨e⟩⟩ := hL
  obtain ⟨R₀, hR₀syl, hR₀N⟩ := hN.exists_isSylowOf_le
  have hR₀index : ¬ 5 ∣ R₀.index := by
    have h := hR₀syl.2.2
    rwa [Subgroup.relIndex_top_right] at h
  let R : Sylow 5 X := hR₀syl.2.1.toSylow hR₀index
  have hRcoe : (R : Subgroup X) = R₀ := IsPGroup.toSylow_coe hR₀syl.2.1 hR₀index
  have h2R : 2 ≤ CFSG.Open.pRank 5 (R : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow R).1]
    exact h2
  obtain ⟨A, hAR, hAea, hAcard⟩ :=
    CFSG.AGLEmbedding.exists_isElemAbelian_card_sq_of_two_le_pRank (p := 5) Nat.prime_five h2R
  obtain ⟨z, -, hzord, -, hzpow, hzmax, -, hzC, -, -, -, -, -⟩ :=
    hSz ⟨.suzuki 2, hv⟩ rfl X (CFSG.generalizedFitting X) hKn hKC ⟨e⟩ 5 rfl R A hAR hAea hAcard
  have hRne : (R : Subgroup X) ≠ ⊥ := fun h => by
    rw [h, le_bot_iff] at hAR
    rw [hAR, Subgroup.card_bot] at hAcard
    norm_num at hAcard
  have hNnorm : N = Subgroup.normalizer ((R : Subgroup X) : Set X) :=
    (hzmax N (hN.normalizer_le hRne R.isPGroup' (hRcoe ▸ hR₀N))).resolve_right hN.1
  have hTN' : T ≤ Subgroup.normalizer ((R : Subgroup X) : Set X) := hNnorm ▸ hTN
  have hnormz : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set X) := by
    rw [hzpow]
    exact (le_inf le_rfl (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (R : Subgroup X))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTC : T ⊓ Subgroup.centralizer (Subgroup.zpowers z : Set X) = ⊥ :=
    (IsPGroup.disjoint_of_ne 2 5 (by norm_num) _ _ (hT.to_le inf_le_left)
      R.isPGroup').eq_bot_of_le ((le_inf (inf_le_left.trans hTN') (inf_le_right.trans
        (CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton z).le)).trans hzC)
  exact CFSG.Semidihedral.Principal.isCyclic_of_le_normalizer_of_inf_centralizer
    Nat.prime_five (Subgroup.zpowers z) T
    (by rw [Nat.card_zpowers, hzord]) (hTN'.trans hnormz) hTC

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five
