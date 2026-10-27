module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
public import CFSG.HardMathSupport.Curtis.Proving.SmallOvergroupOrder
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Small
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockUniBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem exists_sylow_quotient_bot_not_normal {S : Type} [Group S] [Finite S]
    {J : Subgroup S} (T : Sylow 2 S) (hTJ : (T : Subgroup S) ≤ J)
    (hTN : Subgroup.normalizer (T : Set S) < J) :
    ∃ T₀ : Sylow 2 (↥J ⧸ (⊥ : Subgroup ↥J)),
      ¬ (T₀ : Subgroup (↥J ⧸ (⊥ : Subgroup ↥J))).Normal := by
  classical
  let tj : Subgroup ↥J := (T : Subgroup S).subgroupOf J
  have htjP : IsPGroup 2 ↥tj :=
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow T).2.1.of_equiv
      (Subgroup.subgroupOfEquivOfLe hTJ).symm
  have htjidx : ¬ 2 ∣ tj.index := by
    rw [show tj.index = T.relIndex J from rfl]
    exact fun h => T.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hTJ))
  let Tj : Sylow 2 ↥J := htjP.toSylow htjidx
  let T₀ : Sylow 2 (↥J ⧸ (⊥ : Subgroup ↥J)) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (⊥ : Subgroup ↥J)) Tj
  have hfinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup ↥J)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (QuotientGroup.ker_mk' ⊥)
  refine ⟨T₀, ?_⟩
  intro hN
  have htjN : tj.Normal := by
    have h := Subgroup.Normal.comap hN (QuotientGroup.mk' (⊥ : Subgroup ↥J))
    rw [show (T₀ : Subgroup (↥J ⧸ (⊥ : Subgroup ↥J))) =
        tj.map (QuotientGroup.mk' (⊥ : Subgroup ↥J)) from Sylow.coe_mapSurjective _ Tj,
      Subgroup.comap_map_eq_self_of_injective hfinj tj] at h
    exact h
  exact hTN.ne (le_antisymm hTN.le
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mp htjN))

private theorem not_isQuasisimple_top_perm_three :
    ¬ CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup (Equiv.Perm (Fin 3))) := fun hq =>
  CFSG.AGLEmbedding.LeviBlock.not_isQuasisimple_of_isSolvable
    (Equiv.Perm.isSolvable (by simp))
    (CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm hq)

private theorem hasLeviDataX_of_symThree_quotient {J : Type} [Group J] [Finite J]
    (f : (J ⧸ CFSG.pCore 2 J) →* Equiv.Perm (Fin 3))
    (hfs : Function.Surjective f) (hfbot : f.ker = ⊥) : HasLeviDataX True False J := by
  classical
  let G : Unit → Type := fun _ => Equiv.Perm (Fin 3)
  let S' : ∀ j : Unit, Subgroup (G j) := fun _ => ⊤
  let β : J →* (∀ j, G j) :=
    MonoidHom.pi fun _ => f.comp (QuotientGroup.mk' (CFSG.pCore 2 J))
  have hβker : β.ker = CFSG.pCore 2 J := by
    have h1 : β.ker = (f.comp (QuotientGroup.mk' (CFSG.pCore 2 J))).ker := by
      ext x
      simp [β, funext_iff, MonoidHom.pi_apply, Unique.forall_iff]
    rw [h1, MonoidHom.ker_comp_of_injective _ _ ((MonoidHom.ker_eq_bot_iff f).mp hfbot),
      QuotientGroup.ker_mk']
  have hβ : IsPGroup 2 β.ker := by
    rw [hβker]
    exact CFSG.pCore_isPGroup
  have hβs : Function.Surjective β := by
    intro y
    obtain ⟨z, hz⟩ := hfs (y ())
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 J) z
    refine ⟨x, ?_⟩
    funext i
    cases i
    simpa [β] using hz
  have hβrange : β.range = ⊤ := MonoidHom.range_eq_top.mpr hβs
  have hpi : Subgroup.pi Set.univ S' = ⊤ := Subgroup.pi_top Set.univ
  have hS : ∀ j, S' j = ⊥ ∨ IsLeviBlock ↥(S' j) :=
    fun _ => Or.inr (Or.inl ⟨Subgroup.topEquiv⟩)
  have halt : CensusAlt S' := by
    right
    intro j hq n hn
    exact absurd hq not_isQuasisimple_top_perm_three
  have hB : BlockFacts True False S' := by
    refine ⟨?_, ?_, Or.inl ?_⟩
    · intro j hq
      exact absurd hq not_isQuasisimple_top_perm_three
    · intro j _
      trivial
    · have h1 : Nat.card {j : Unit // S' j ≠ ⊥} ≤ Nat.card Unit := Finite.card_subtype_le _
      have h2 : Nat.card Unit = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_unit
      omega
  have hσker : (MonoidHom.id J).ker = ⊥ := by
    ext x
    simp
  refine ⟨J, inferInstance, inferInstance, MonoidHom.id J, Unit, inferInstance,
    G, inferInstance, inferInstance, S', β, ?_, ?_, ?_, hβ, ?_, ?_, ?_, hS, halt, hB⟩
  · intro x
    exact ⟨x, rfl⟩
  · rw [hσker]
    exact bot_le
  · rw [hσker, Subgroup.card_bot]
    exact odd_one
  · rw [hpi, hβrange]
  · rw [hpi, hβrange, Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top]
  · rw [hpi, hβrange, Subgroup.relIndex_top_left]
    norm_num

theorem hasLeviDataX_of_overgroupOrder96 {S : Type} [Group S] [Finite S]
    (h96 : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 S) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX True False ↥J := by
  classical
  obtain ⟨-, hJne, T, hTN⟩ := hJ
  have hTJ : (T : Subgroup S) ≤ J :=
    (Subgroup.le_normalizer (H := (T : Subgroup S))).trans hTN.le
  have h96J : Nat.card ↥J ∣ 96 :=
    h96 T J (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow T) hTJ hJne
  obtain ⟨T₀, hT₀⟩ := exists_sylow_quotient_bot_not_normal T hTJ hTN
  have h96q : Nat.card (↥J ⧸ (⊥ : Subgroup ↥J)) ∣ 96 := by
    rwa [Nat.card_congr QuotientGroup.quotientBot.toEquiv]
  obtain ⟨f, hfs, hfker, -, -⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.exists_symThree_quotient_of_not_normal_sylow
      (Z := (⊥ : Subgroup ↥J)) bot_le (by rw [Subgroup.card_bot]; exact odd_one) h96q hT₀
  have hfbot : f.ker = ⊥ := by
    refine le_bot_iff.mp ?_
    rwa [Subgroup.map_bot] at hfker
  exact hasLeviDataX_of_symThree_quotient f hfs hfbot

theorem hasLeviData_of_overgroupOrder96 {S : Type} [Group S] [Finite S]
    (h96 : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 S) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_overgroupOrder96 h96 hJ).hasLeviData

theorem overgroupOrder96_of_isAlt_six {S : Type} [Group S]
    (h : IsAlt S 6) : CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 S := by
  obtain ⟨e⟩ := h
  exact CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96.of_mulEquiv e.symm
    CFSG.HardMathSupport.Curtis.Proving.ordBound_alt_six

theorem overgroupOrder96_of_psu_three_three
    {S : Type} [Group S] (h : CFSG.Blueprint.LieModel S .PSU 3 3 1) :
    CFSG.HardMathSupport.Curtis.Proving.OvergroupOrder96 S :=
  CFSG.HardMathSupport.Curtis.Proving.ordBound_psu_three_three
    (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
