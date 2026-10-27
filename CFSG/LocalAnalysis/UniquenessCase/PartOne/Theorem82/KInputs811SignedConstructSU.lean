module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedModel
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpackSU
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedConstruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedConstructSU

open CFSG.Open CFSG.GroupTheory CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel

private theorem not_dvd_pow_add_one {r f : ℕ} (hr : r.Prime) (hf : f ≠ 0) : ¬ r ∣ r ^ f + 1 :=
  fun h => hr.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right (dvd_pow_self r hf)).1 h))

theorem signedModelK6c_of_lieModel_psu {n : ℕ} (hF : SUK6cFacts n) (hn : n = 6 ∨ n = 7)
    {Y : Type} [Group Y] {r f : ℕ} (hq : r ^ f % 3 = 1) (h : LieModel (Y ⧸ center Y) .PSU n r f) :
    SignedModelK6c Y := by
  haveI : Fact r.Prime := ⟨h.admissible.1⟩
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := ModelUnpackSU.exists_model_of_lieModel_psu_SU (by omega) h
  obtain ⟨c₀, h₀⟩ := hF hn K (unitaryInvolution K r f) (r ^ f) (unitaryInvolution_involutive hK)
    (exists_unitaryInvolution_eq_neg hK) (unitaryInvolution_apply K r f) hK hq
  unfold SignedModelK6c
  exact ⟨SU (unitaryInvolution K r f) n, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpackSU.not_dvd_card_scalars_SU (by omega) Nat.prime_three (by omega),
    ModelUnpackSU.uniqueElemSylow_statedProj_SU hK hq hn⟩

theorem signedModelK6r_of_lieModel_psu {n : ℕ} (hF : SUK6rFacts n) (hn : n = 6 ∨ n = 7)
    {Y : Type} [Group Y] {r f : ℕ} (hq : r ^ f % 3 = 1) (h : LieModel (Y ⧸ center Y) .PSU n r f) :
    SignedModelK6r Y r := by
  haveI : Fact r.Prime := ⟨h.admissible.1⟩
  obtain ⟨K, _, _, hchar, hK, ⟨e⟩⟩ := ModelUnpackSU.exists_model_of_lieModel_psu_SU (by omega) h
  obtain ⟨c₀, h₀, hr⟩ := hF hn K (unitaryInvolution K r f) (r ^ f)
    (unitaryInvolution_involutive hK) (exists_unitaryInvolution_eq_neg hK)
    (unitaryInvolution_apply K r f) hK hq
  unfold SignedModelK6r
  exact ⟨SU (unitaryInvolution K r f) n, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpackSU.not_dvd_card_scalars_SU (by omega) Nat.prime_three (by omega),
    ModelUnpackSU.uniqueElemSylow_statedProj_SU hK hq hn, fun hr5 =>
      ⟨ModelUnpackSU.not_dvd_card_scalars_SU (by omega) h.admissible.1
        (not_dvd_pow_add_one h.admissible.1 (by have := h.admissible.2.1; omega)),
        hr r h.admissible.1 hchar hr5⟩⟩

theorem signedModelK7_of_lieModel_psu {n : ℕ} (hF : SUK7Facts n) (hn : n = 6 ∨ n = 7)
    {Y : Type} [Group Y] {fam : LieFam811} (hfam : fam = .l6 ∨ fam = .l7) {r f : ℕ}
    (hq : r ^ f % 3 = 1) (h : LieModel (Y ⧸ center Y) .PSU n r f) : SignedModelK7 Y fam r f := by
  haveI : Fact r.Prime := ⟨h.admissible.1⟩
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := ModelUnpackSU.exists_model_of_lieModel_psu_SU (by omega) h
  obtain ⟨c₀, h₀, ha, hb⟩ := hF hn K (unitaryInvolution K r f) (r ^ f)
    (unitaryInvolution_involutive hK) (exists_unitaryInvolution_eq_neg hK)
    (unitaryInvolution_apply K r f) hK hq
  have hN3 : ¬ 3 ∣ Nat.card
      ((StatedScalars (Fin n) K).subgroupOf (SU (unitaryInvolution K r f) n)) :=
    ModelUnpackSU.not_dvd_card_scalars_SU (by omega) Nat.prime_three (by omega)
  haveI := ModelUnpack.isCyclic_scalars_subgroupOf (SU (unitaryInvolution K r f) n)
  unfold SignedModelK7
  refine ⟨SU (unitaryInvolution K r f) n, inferInstance, inferInstance, _, inferInstance, c₀, e,
    h₀, hN3, ModelUnpackSU.uniqueElemSylow_statedProj_SU hK hq hn,
    fun p hp hp5 hpq => ?_, fun _ p hp hp5 hpq => ?_,
    fun hf => by rcases hfam with rfl | rfl <;> rcases hf with hf | hf <;> cases hf⟩
  · rw [qMinusPi_of_mod_one hq] at hpq
    exact ⟨ModelUnpackSU.not_dvd_card_scalars_SU (by omega) hp
      (not_dvd_add_one_of_dvd_sub_one hp5 (by omega) hpq), ha p hp hp5 hpq⟩
  · rw [qPlusPi_of_mod_one hq] at hpq
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h2, h3⟩ := hb p hp hp5 hpq
    rcases hn with rfl | rfl
    · exact SignedConstruct.two_le_pRank_centralizer_map_mk_of_coprime hN3
        (ModelUnpackSU.not_dvd_card_scalars_SU_of_not_dvd hp (not_dvd_six hp hp5))
        h₀.isElemAbelian h2
    · exact ModelTransport.two_le_pRank_centralizer_map_mk_of_three_le hN3 h₀.isElemAbelian
        (h3 rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedConstructSU
