module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811SignedModel
import CFSG.GroupTheory.CoprimeCentralizerTransport
import CFSG.GroupTheory.WeirSylow.UniqueE27Linear
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.GroupTheory.WeirSylow.UniqueE27Symplectic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedConstruct

open CFSG.Open CFSG.GroupTheory Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedFacts
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedModel

theorem two_le_pRank_centralizer_map_mk_of_coprime {H : Type} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal] {p : ℕ} [Fact p.Prime] (hN3 : ¬ 3 ∣ Nat.card N)
    (hNp : ¬ p ∣ Nat.card N) {A₀ : Subgroup H} (hA₀ : IsElemAbelian 3 A₀)
    (h : 2 ≤ CFSG.Open.pRank p (centralizer (A₀ : Set H))) :
    2 ≤ CFSG.Open.pRank p
      (centralizer ((A₀.map (QuotientGroup.mk' N) : Subgroup (H ⧸ N)) : Set (H ⧸ N))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rwa [CoprimeTransport.pRank_centralizer_map_mk_eq (s := 3) hN3 hNp hA₀.isPGroup]

theorem signedModelK6c_of_lieModel_psp (hF : Sp6K6cFacts) {Y : Type} [Group Y] {r f : ℕ}
    (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .PSp 3 r f) : SignedModelK6c Y := by
  obtain ⟨K, _, _, _, _, hK3, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psp hr3 h
  obtain ⟨c₀, h₀⟩ := hF K (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3)
  unfold SignedModelK6c
  exact ⟨StatedSp 3 K, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_statedSp (by norm_num) Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedSp_three K hK3⟩

theorem signedModelK6r_of_lieModel_psp (hF : Sp6K6rFacts) {Y : Type} [Group Y] {r f : ℕ}
    (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .PSp 3 r f) : SignedModelK6r Y r := by
  obtain ⟨K, _, _, hchar, _, hK3, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psp hr3 h
  obtain ⟨c₀, h₀, hr⟩ := hF K (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3)
  unfold SignedModelK6r
  exact ⟨StatedSp 3 K, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_statedSp (by norm_num) Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedSp_three K hK3, fun hr5 =>
      ⟨ModelUnpack.not_dvd_card_scalars_statedSp (by norm_num) h.admissible.1 (by omega),
        hr r h.admissible.1 hchar hr5⟩⟩

theorem signedModelK7_of_lieModel_psp (hF : Sp6K7Facts) {Y : Type} [Group Y] {r f : ℕ}
    (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .PSp 3 r f) : SignedModelK7 Y .psp6 r f := by
  obtain ⟨K, _, _, _, hK, hK3, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psp hr3 h
  obtain ⟨c₀, h₀, ha, hb⟩ := hF K (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3)
  have hN : ∀ p : ℕ, p.Prime → 5 ≤ p →
      ¬ p ∣ Nat.card ((StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)) :=
    fun p hp hp5 => ModelUnpack.not_dvd_card_scalars_statedSp (by norm_num) hp (by omega)
  unfold SignedModelK7
  exact ⟨StatedSp 3 K, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_statedSp (by norm_num) Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedSp_three K hK3,
    fun p hp hp5 hpq => ⟨hN p hp hp5, ha p hp hp5 (by rwa [qMinusPi_eq_minusPi, ← hK] at hpq)⟩,
    fun hf => absurd hf (by decide),
    fun _ p hp hp5 hpq =>
      ⟨hN p hp hp5, hb p hp hp5 (by rwa [qPlusPi_eq_plusPi, ← hK] at hpq)⟩⟩

theorem signedModelK6c_of_lieModel_pomegaOdd (hF : Omega7K6cFacts) {Y : Type} [Group Y]
    {r f : ℕ} (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .POmegaOdd 3 r f) :
    SignedModelK6c Y := by
  obtain ⟨K, _, _, _, _, hodd, hK3, ⟨e⟩⟩ :=
    ModelUnpack.exists_model_of_lieModel_pomegaOdd hr3 h
  obtain ⟨c₀, h₀⟩ := hF K (ModelUnpack.two_ne_zero_of_charP h.admissible.1 h.admissible.2.2.2)
    (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3)
  unfold SignedModelK6c
  exact ⟨StatedOmega (StatedQuadOdd 3 K), inferInstance, inferInstance, _, inferInstance, c₀, e,
    h₀, ModelUnpack.not_dvd_card_scalars_statedOmega_quadOdd Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedOmega_quadOdd_three K hodd hK3⟩

theorem signedModelK6r_of_lieModel_pomegaOdd (hF : Omega7K6rFacts) {Y : Type} [Group Y]
    {r f : ℕ} (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .POmegaOdd 3 r f) :
    SignedModelK6r Y r := by
  obtain ⟨K, _, _, hchar, _, hodd, hK3, ⟨e⟩⟩ :=
    ModelUnpack.exists_model_of_lieModel_pomegaOdd hr3 h
  obtain ⟨c₀, h₀, hr⟩ := hF K
    (ModelUnpack.two_ne_zero_of_charP h.admissible.1 h.admissible.2.2.2)
    (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3)
  unfold SignedModelK6r
  exact ⟨StatedOmega (StatedQuadOdd 3 K), inferInstance, inferInstance, _, inferInstance, c₀, e,
    h₀, ModelUnpack.not_dvd_card_scalars_statedOmega_quadOdd Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedOmega_quadOdd_three K hodd hK3, fun hr5 =>
      ⟨ModelUnpack.not_dvd_card_scalars_statedOmega_quadOdd h.admissible.1 (by omega),
        hr r h.admissible.1 hchar hr5⟩⟩

theorem signedModelK7_of_lieModel_pomegaOdd (hF : Omega7K7Facts) {Y : Type} [Group Y]
    {r f : ℕ} (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .POmegaOdd 3 r f) :
    SignedModelK7 Y .omega7 r f := by
  obtain ⟨K, _, _, _, hK, hodd, hK3, ⟨e⟩⟩ :=
    ModelUnpack.exists_model_of_lieModel_pomegaOdd hr3 h
  obtain ⟨c₀, h₀, ha, hb⟩ := hF K
    (ModelUnpack.two_ne_zero_of_charP h.admissible.1 h.admissible.2.2.2)
    (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3)
  have hN : ∀ p : ℕ, p.Prime → 5 ≤ p →
      ¬ p ∣ Nat.card ((StatedScalars (Fin 3 ⊕ Fin 3 ⊕ Unit) K).subgroupOf
        (StatedOmega (StatedQuadOdd 3 K))) := fun p hp hp5 =>
    ModelUnpack.not_dvd_card_scalars_statedOmega_quadOdd hp (by omega)
  unfold SignedModelK7
  exact ⟨StatedOmega (StatedQuadOdd 3 K), inferInstance, inferInstance, _, inferInstance, c₀, e,
    h₀, ModelUnpack.not_dvd_card_scalars_statedOmega_quadOdd Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedOmega_quadOdd_three K hodd hK3,
    fun p hp hp5 hpq => ⟨hN p hp hp5, ha p hp hp5 (by rwa [qMinusPi_eq_minusPi, ← hK] at hpq)⟩,
    fun hf => absurd hf (by decide),
    fun _ p hp hp5 hpq =>
      ⟨hN p hp hp5, hb p hp hp5 (by rwa [qPlusPi_eq_plusPi, ← hK] at hpq)⟩⟩

theorem signedModelK6c_of_lieModel_pomegaMinus (hF : Omega8MinusK6cFacts) {Y : Type} [Group Y]
    {r f : ℕ} (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .POmegaMinus 4 r f) :
    SignedModelK6c Y := by
  obtain ⟨K, _, _, _, _, hK3, b, c, hbc, ⟨e⟩⟩ :=
    ModelUnpack.exists_model_of_lieModel_pomegaMinus hr3 h
  obtain ⟨c₀, h₀⟩ := hF K (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3) b c hbc
  unfold SignedModelK6c
  exact ⟨StatedOmega (StatedQuadMinus 4 K b c), inferInstance, inferInstance, _, inferInstance,
    c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_statedOmega_quadMinus b c Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedOmega_quadMinus_four K hbc hK3⟩

theorem signedModelK6r_of_lieModel_pomegaMinus (hF : Omega8MinusK6rFacts) {Y : Type} [Group Y]
    {r f : ℕ} (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .POmegaMinus 4 r f) :
    SignedModelK6r Y r := by
  obtain ⟨K, _, _, hchar, _, hK3, b, c, hbc, ⟨e⟩⟩ :=
    ModelUnpack.exists_model_of_lieModel_pomegaMinus hr3 h
  obtain ⟨c₀, h₀, hr⟩ := hF K (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3) b c hbc
  unfold SignedModelK6r
  exact ⟨StatedOmega (StatedQuadMinus 4 K b c), inferInstance, inferInstance, _, inferInstance,
    c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_statedOmega_quadMinus b c Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedOmega_quadMinus_four K hbc hK3, fun hr5 =>
      ⟨ModelUnpack.not_dvd_card_scalars_statedOmega_quadMinus b c h.admissible.1 (by omega),
        hr r h.admissible.1 hchar hr5⟩⟩

theorem signedModelK7_of_lieModel_pomegaMinus (hF : Omega8MinusK7Facts) {Y : Type} [Group Y]
    {r f : ℕ} (hr3 : r ≠ 3) (h : LieModel (Y ⧸ center Y) .POmegaMinus 4 r f) :
    SignedModelK7 Y .pomega8m r f := by
  obtain ⟨K, _, _, _, hK, hK3, b, c, hbc, ⟨e⟩⟩ :=
    ModelUnpack.exists_model_of_lieModel_pomegaMinus hr3 h
  obtain ⟨c₀, h₀, ha⟩ := hF K (ModelUnpack.three_ne_zero_of_charP h.admissible.1 hr3) b c hbc
  unfold SignedModelK7
  exact ⟨StatedOmega (StatedQuadMinus 4 K b c), inferInstance, inferInstance, _, inferInstance,
    c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_statedOmega_quadMinus b c Nat.prime_three (by norm_num),
    WeirSylow.uniqueElemSylow_statedProj_statedOmega_quadMinus_four K hbc hK3,
    fun p hp hp5 hpq => ⟨ModelUnpack.not_dvd_card_scalars_statedOmega_quadMinus b c hp (by omega),
      ha p hp hp5 (by rwa [qMinusPi_eq_minusPi, ← hK] at hpq)⟩,
    fun hf => absurd hf (by decide),
    fun hf => absurd hf (by decide)⟩

theorem signedModelK6c_of_lieModel_psl {n : ℕ} (hF : SLK6cFacts n) (hn : n = 6 ∨ n = 7)
    {Y : Type} [Group Y] {r f : ℕ} (hq : r ^ f % 3 = 2) (h : LieModel (Y ⧸ center Y) .PSL n r f) :
    SignedModelK6c Y := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psl (by omega) h
  have hK2 : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  obtain ⟨c₀, h₀⟩ := hF hn K hK2
  unfold SignedModelK6c
  exact ⟨StatedSL n K, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one Nat.prime_three (by omega) _,
    WeirSylow.uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two K hK2 hn⟩

theorem signedModelK6r_of_lieModel_psl {n : ℕ} (hF : SLK6rFacts n) (hn : n = 6 ∨ n = 7)
    {Y : Type} [Group Y] {r f : ℕ} (hq : r ^ f % 3 = 2) (h : LieModel (Y ⧸ center Y) .PSL n r f) :
    SignedModelK6r Y r := by
  obtain ⟨K, _, _, hchar, hK, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psl (by omega) h
  have hK2 : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  obtain ⟨c₀, h₀, hr⟩ := hF hn K hK2
  unfold SignedModelK6r
  refine ⟨StatedSL n K, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀,
    ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one Nat.prime_three (by omega) _,
    WeirSylow.uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two K hK2 hn, fun hr5 =>
      ⟨ModelUnpack.not_dvd_card_scalars_of_dvd_card h.admissible.1 ?_ _,
        hr r h.admissible.1 hchar hr5⟩⟩
  rw [hK]
  exact dvd_pow_self r (by have := h.admissible.2.1; omega)

theorem signedModelK7_of_lieModel_psl {n : ℕ} (hF : SLK7Facts n) (hn : n = 6 ∨ n = 7)
    {Y : Type} [Group Y] {fam : LieFam811} (hfam : fam = .l6 ∨ fam = .l7) {r f : ℕ}
    (hq : r ^ f % 3 = 2) (h : LieModel (Y ⧸ center Y) .PSL n r f) : SignedModelK7 Y fam r f := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psl (by omega) h
  have hK2 : Nat.card K % 3 = 2 := by rw [hK]; exact hq
  obtain ⟨c₀, h₀, ha, hb⟩ := hF hn K hK2
  have hN3 : ¬ 3 ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
    ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one Nat.prime_three (by omega) _
  haveI := ModelUnpack.isCyclic_scalars_subgroupOf (StatedSL n K)
  unfold SignedModelK7
  refine ⟨StatedSL n K, inferInstance, inferInstance, _, inferInstance, c₀, e, h₀, hN3,
    WeirSylow.uniqueElemSylow_statedProj_statedSL_of_mod_three_eq_two K hK2 hn,
    fun p hp hp5 hpq => ?_, fun _ p hp hp5 hpq => ?_,
    fun hf => by rcases hfam with rfl | rfl <;> rcases hf with hf | hf <;> cases hf⟩
  · rw [qMinusPi_of_mod_two hq, ← hK] at hpq
    exact ⟨ModelUnpack.not_dvd_card_scalars_of_not_dvd_card_sub_one hp
      (not_dvd_sub_one_of_dvd_add_one hp5 Nat.card_pos hpq) _, ha p hp hp5 hpq⟩
  · rw [qPlusPi_of_mod_two hq, ← hK] at hpq
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h2, h3⟩ := hb p hp hp5 hpq
    rcases hn with rfl | rfl
    · exact two_le_pRank_centralizer_map_mk_of_coprime hN3
        (ModelUnpack.not_dvd_card_scalars_statedSL hp (not_dvd_six hp hp5)) h₀.isElemAbelian h2
    · exact ModelTransport.two_le_pRank_centralizer_map_mk_of_three_le hN3 h₀.isElemAbelian
        (h3 rfl)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SignedConstruct
