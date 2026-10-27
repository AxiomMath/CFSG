module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Adapters.StatedPSLTwo
import CFSG.GH74.KGroups.PSL2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanRankOneDickson
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2Strong
import CFSG.LocalAnalysis.UniquenessCase.UC22Bar2A5
import CFSG.Quasithin.Vol2.F134J1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

private theorem eq_top_of_normalizer_eq_top_of_isAlt_five {S : Type} [Group S] [IsSimpleGroup S]
    {K : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) (h : normalizer (K : Set S) = ⊤) : K = ⊤ := by
  have : K.Normal := normalizer_eq_top_iff.mp h
  refine (Subgroup.Normal.eq_bot_or_eq_top K).resolve_left fun hK => ?_
  have h60 := card_eq_sixty_mul_of_isAlt_five hA5
  have h1 : Nat.card K = 1 := by
    rw [hK]
    exact Subgroup.card_bot
  omega

private theorem not_isSolvable_of_le_of_isAlt_five {S : Type} [Group S] {K W : Subgroup S}
    (hA5 : IsAlt (Bar2 K) 5) (hKW : K ≤ W) : ¬ Group.IsSolvable W := fun _ =>
  not_isSolvable_of_isAlt_five hA5
    (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKW))

open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs in
private theorem not_isPSolvable_three_of_le_of_isAlt_five {S : Type} [Group S] [Finite S]
    {K W : Subgroup S} (hA5 : IsAlt (Bar2 K) 5) (hKW : K ≤ W) :
    ¬ CFSG.HallHigman.IsPSolvable 3 W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ : Nonempty (Bar2 K ≃* alternatingGroup (Fin 5)) := hA5
  intro hW
  have h1 := QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv Subgroup.topEquiv.symm
    (PSolvableClosure.isPSolvable_of_le hW hKW)
  have h2 := PSolvableClosure.isPSolvable_map (QuotientGroup.mk' (CFSG.pCore 2 K)) h1
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  refine CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple
    (alternatingGroup.isSimpleGroup (by simp)) ?_ ?_
    (QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv (Subgroup.topEquiv.trans e) h2)
  · rw [alternatingGroup.isMulCommutative_iff_card_le_three, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    norm_num
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

theorem a5Normalizer_J1
    {S : Type} [Group S] [Finite S] (hS : IsSpor S .J1) {K D : Subgroup S}
    (hA5 : IsAlt (Bar2 K) 5) (hD : Nat.card D = 3)
    (hN : normalizer (D : Set S) ≤ normalizer (K : Set S)) : K = ⊤ := by
  obtain ⟨e⟩ : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hS
  let e' : S ≃* CFSG.Sporadic.J1.J := e.trans CFSG.Sporadic.J1.nativeEquiv
  have hcard : Nat.card S = 175560 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Quasithin.F134.card_carrier_J1
  have : IsSimpleGroup S := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J1.isSimpleGroup_J e'
  have hcyc : ∀ X : Subgroup S, IsPGroup 3 X → IsCyclic X := by
    intro X hX
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
    have hdvd : 3 ^ k ∣ 175560 := by
      rw [← hk, ← hcard]
      exact Subgroup.card_subgroup_dvd_card X
    have hk1 : k ≤ 1 := by
      by_contra! h
      have h2 : 2 ≤ k := h
      exact absurd ((Nat.pow_dvd_pow 3 h2).trans hdvd) (by norm_num)
    exact isCyclic_of_card_dvd_prime (p := 3)
      (hk ▸ (Nat.pow_dvd_pow 3 hk1).trans (pow_one 3).dvd)
  exact eq_top_of_normalizer_eq_top_of_isAlt_five hA5
    (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.overgroupEqTop_of_mulEquiv e'
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupJ1.overgroupEqTop_J hcyc D _ hD hN
      (not_isPSolvable_three_of_le_of_isAlt_five hA5 le_normalizer))

theorem a5Normalizer_psl2 {S : Type} [Group S] [Finite S]
    {p f : ℕ} (hS : LieModel S .PSL 2 p f) {K D : Subgroup S} (hA5 : IsAlt (Bar2 K) 5)
    (hD : Nat.card D = 3) (hN : normalizer (D : Set S) ≤ normalizer (K : Set S)) : K = ⊤ := by
  obtain ⟨hp, hf, -⟩ := hS.admissible
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup S := hS.isSimpleGroup_psl_two
  have hf0 : f ≠ 0 := by omega
  obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField p f) p f
    (by omega) (GaloisField.card p f hf0) hS
  have hD' : Nat.card (D.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hD]
  refine eq_top_of_normalizer_eq_top_of_isAlt_five hA5 ?_
  rcases eq_or_ne p 3 with rfl | hp3
  ·
    obtain ⟨R, hDR⟩ := (IsPGroup.of_card (p := 3) (n := 1)
      (hD'.trans (pow_one 3).symm)).exists_le_sylow
    obtain ⟨hRab, hRcard⟩ := CFSG.AGLEmbedding.psl2GF_sylow 3 f hf R
    have : IsMulCommutative (R : Subgroup (CFSG.AGLEmbedding.PSL2GF 3 f)) := hRab.1
    have hRN : (R : Subgroup (CFSG.AGLEmbedding.PSL2GF 3 f)) ≤
        (normalizer (K : Set S)).map e.toMonoidHom :=
      calc (R : Subgroup (CFSG.AGLEmbedding.PSL2GF 3 f))
          ≤ centralizer (R : Set (CFSG.AGLEmbedding.PSL2GF 3 f)) := Subgroup.le_centralizer _
        _ ≤ centralizer ((D.map e.toMonoidHom : Subgroup _) : Set _) :=
          Subgroup.centralizer_le hDR
        _ ≤ normalizer ((D.map e.toMonoidHom : Subgroup _) : Set _) :=
          centralizer_le_normalizer _
        _ = (normalizer (D : Set S)).map e.toMonoidHom := (map_equiv_normalizer_eq D e).symm
        _ ≤ (normalizer (K : Set S)).map e.toMonoidHom := Subgroup.map_mono hN
    have hdvd := Subgroup.card_dvd_of_le hRN
    rw [hRcard, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hdvd
    exact CFSG.AGLEmbedding.eq_top_of_dvd_card_of_equiv_psl2GF (by norm_num) hf0 e _ hdvd
      (not_isSolvable_of_le_of_isAlt_five hA5 le_normalizer)
  ·
    have h3 : ¬ 3 ∣ Nat.card (GaloisField p f) := by
      rw [GaloisField.card p f hf0]
      exact fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
        (Nat.prime_three.dvd_of_dvd_pow h)).symm
    exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupTransfer.eqTop_of_map_eq e rfl hN
      (not_isPSolvable_three_of_le_of_isAlt_five hA5 le_normalizer) fun W hNW hW =>
        CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2.psl2_overgroup_strong h3 hD' hNW hW

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
