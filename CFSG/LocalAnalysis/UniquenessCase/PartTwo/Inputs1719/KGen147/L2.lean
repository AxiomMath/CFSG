module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen147.BorelRoute
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCatalog
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.LinTwo
import CFSG.RankThree.PartOne.K133.KillL2
import CFSG.LocalAnalysis.UniquenessCase.UC6C626L2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen

open Subgroup CFSG.Open
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive
  (isCoatom_normalizer_of_mulEquiv_psl2GF)
open CFSG.AGLEmbedding (PSL2GF)

theorem commutator_normalizer_sylow_le_of_mulEquiv_psl2GF {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) {K : Type} [Group K] [Finite K]
    (e : K ≃* PSL2GF p n) (T : Sylow p K) :
    ⁅normalizer ((T : Subgroup K) : Set K), normalizer ((T : Subgroup K) : Set K)⁆ ≤
      (T : Subgroup K) := by
  let U : Sylow p (PSL2GF p n) := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hU : (U : Subgroup (PSL2GF p n)) = (T : Subgroup K).map e.toMonoidHom :=
    Sylow.coe_mapSurjective e.surjective T
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have h2 : (2 : GaloisField p n) ≠ 0 := by
    intro h0
    have h0' : ((2 : ℕ) : GaloisField p n) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff (GaloisField p n) p] at h0'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h0')
  obtain ⟨c, hc⟩ := CFSG.GH74.GLS.IVK.L2Borel.exists_conj_eq_unipotent hF U
  have key : ⁅normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)),
      normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))⁆ ≤
        (U : Subgroup (PSL2GF p n)) := by
    rw [hc, ← Subgroup.map_equiv_normalizer_eq,
      CFSG.GH74.GLS.IVK.L2Borel.normalizer_unipotent_eq h2, ← Subgroup.map_commutator]
    apply Subgroup.map_mono
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact CFSG.LocalAnalysis.UniquenessCase.UC6.commutator_borel_mem_unipotent hg hh
  rw [hU, ← Subgroup.map_equiv_normalizer_eq, ← Subgroup.map_commutator] at key
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp key

theorem kGenSpans_of_lieModel_psl2 {K : Type} [Group K] [Finite K] {p f : ℕ}
    (h : CFSG.Blueprint.LieModel K .PSL 2 p f) (hG : IsSimpleGroup K)
    (hna : ∃ a b : K, a * b ≠ b * a) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 1)
    {B R : Subgroup K} (hBR : IsKGenPair B R) : KGenSpans B R := by
  obtain ⟨hp, hf, -⟩ := h.admissible
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField K 2 p f
    (h.statedClassicalModel_of_ne_zero two_ne_zero)
  by_cases hp7 : p = 7
  · subst hp7
    refine kGenSpans_of_isCoatom_normalizer hG hna h3 hBR ?_
    obtain ⟨T, hRT⟩ := hBR.2.1.isPGroup.exists_le_sylow
    exact ⟨T, hRT, T.isPGroup',
      isCoatom_normalizer_of_mulEquiv_psl2GF (by norm_num) hf e T,
      commutator_normalizer_sylow_le_of_mulEquiv_psl2GF (by norm_num) hf e T⟩
  · exfalso
    have hE : CFSG.IsElementaryAbelian 7 (R.map e.toMonoidHom) :=
      (hBR.2.1.map e.toMonoidHom).isElementaryAbelian
    have hne : ((7 : ℕ) : GaloisField p f) ≠ 0 := by
      intro h0
      have hdvd : p ∣ 7 := (CharP.cast_eq_zero_iff (GaloisField p f) p 7).mp h0
      exact hp7 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd)
    have : NeZero ((7 : ℕ) : GaloisField p f) := ⟨hne⟩
    have hle := CFSG.RankThree.PartOne.K133.psl2_elemAb_card_le (K := GaloisField p f)
      (by norm_num) (by norm_num) (R.map e.toMonoidHom) hE
    rw [Subgroup.card_map_of_injective e.injective, hBR.2.2.1] at hle
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGen
