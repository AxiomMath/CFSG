module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.GTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Res5ProofTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits
  CFSG.LieType.Universal CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus
open scoped commutatorElement

private theorem not_two_dvd_index_node {Y P : Type} [Group Y] [Group P] [Finite P]
    {D : UniversalRootDatum P} {n : Fin D.rank → P} {H : Fin D.rank → Subgroup P}
    {π' : P →* Y} {M : ℕ} (hQ : BorelQuotient D n H π' M) {A : Subgroup P}
    (hBA : borel D H ≤ A) {i : Fin D.rank} (hI : negIndices D A = {i}) :
    ¬ 2 ∣ ((rankOne D.rootGroup i).subgroupOf A ⊔
      (posUnipotentExcept D i).subgroupOf A).index := by
  have hUA : posUnipotentExcept D i ≤ A := posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne D.rootGroup i ≤ A :=
    rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hUplus : posUnipotent D ≤ A := posUnipotent_le_borel.trans hBA
  have hUp : posUnipotent D ≤ rankOne D.rootGroup i ⊔ posUnipotentExcept D i := by
    rw [posUnipotent_eq_sup hQ.extras i]
    exact sup_le le_sup_right (le_sup_of_le_left (le_sup_left : _ ≤ rankOne _ i))
  have hsub : (posUnipotent D).subgroupOf A ≤
      (rankOne D.rootGroup i).subgroupOf A ⊔ (posUnipotentExcept D i).subgroupOf A := by
    rw [← Subgroup.subgroupOf_sup hLA hUA]
    exact Subgroup.subgroupOf_mono A hUp
  have hoddA : ¬ 2 ∣ ((posUnipotent D).subgroupOf A).index := by
    intro h2
    refine hQ.not_dvd_index ?_
    rw [← Subgroup.relIndex_mul_index hUplus]
    exact dvd_mul_of_dvd_left h2 _
  exact fun h2 => hoddA (h2.trans (Subgroup.index_dvd_of_le hsub))

private theorem exists_oneBlock_node {Y P F : Type} [Group Y] [Group P] [Finite P]
    [Field F] [Finite F] [CharP F 2]
    {D : UniversalRootDatum P} {n : Fin D.rank → P} {H : Fin D.rank → Subgroup P}
    {π' : P →* Y} {M : ℕ} (hQ : BorelQuotient D n H π' M) {A : Subgroup P}
    (hBA : borel D H ≤ A) {i : Fin D.rank} (hI : negIndices D A = {i})
    (hLU : rankOne D.rootGroup i ⊓ posUnipotentExcept D i = ⊥)
    (h4 : 4 ≤ Nat.card F) (h2F : 2 ∣ Nat.card F)
    (e : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(rankOne D.rootGroup i)) :
    ∃ (U : Subgroup ↥A) (_ : U.Normal) (Λ : Subgroup ↥A), IsPGroup 2 U ∧ Λ ⊓ U = ⊥ ∧
      (∀ a b : ↥A, ⁅a, b⁆ ∈ Λ ⊔ U) ∧ ¬ 2 ∣ (Λ ⊔ U).index ∧
      IsLeviBlock ↥(Λ.map (QuotientGroup.mk' U)) ∧
      CFSG.Open.IsQuasisimple ↥(Λ.map (QuotientGroup.mk' U)) ∧
      3 ∣ Nat.card (↥(Λ.map (QuotientGroup.mk' U)) ⧸
        center ↥(Λ.map (QuotientGroup.mk' U))) := by
  set U : Subgroup ↥A := (posUnipotentExcept D i).subgroupOf A with hU
  set Λ : Subgroup ↥A := (rankOne D.rootGroup i).subgroupOf A with hΛ
  have hUA : posUnipotentExcept D i ≤ A := posUnipotentExcept_le_of_borel_le hBA i
  have hLA : rankOne D.rootGroup i ≤ A :=
    rankOne_le_of_mem_negIndices hBA (by rw [hI]; rfl)
  have hUn : U.Normal := (normal_subgroupOf_iff_le_normalizer hUA).mpr
    (le_normalizer_posUnipotentExcept_of_negIndices_eq hQ hBA hI)
  have hU2 : IsPGroup 2 U := (isPGroup_posUnipotentExcept hQ i).comap_subtype
  have hΛU : Λ ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hx : (x : P) ∈ rankOne D.rootGroup i ⊓ posUnipotentExcept D i :=
      ⟨Subgroup.mem_subgroupOf.mp hx1, Subgroup.mem_subgroupOf.mp hx2⟩
    rw [hLU, Subgroup.mem_bot] at hx
    exact Subgroup.mem_bot.2 (Subtype.ext hx)
  have hc : ∀ a b : ↥A, ⁅a, b⁆ ∈ Λ ⊔ U := by
    intro a b
    rw [hΛ, hU, ← Subgroup.subgroupOf_sup hLA hUA, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using commutator_mem_of_negIndices_eq hQ hBA hI a.2 b.2
  have hodd : ¬ 2 ∣ (Λ ⊔ U).index := not_two_dvd_index_node hQ hBA hI
  obtain ⟨eΛ⟩ := nonempty_mulEquiv_oneBlock U Λ hΛU
  have eSL : Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(Λ.map (QuotientGroup.mk' U)) :=
    e.trans ((Subgroup.subgroupOfEquivOfLe hLA).symm.trans eΛ)
  obtain ⟨hqs, hZS, hcard⟩ := sl2Block_facts h4 eSL
  have hLEV : IsLeviBlock ↥(Λ.map (QuotientGroup.mk' U)) := by
    refine Or.inr (Or.inr ⟨hqs, ?_, ?_⟩)
    · rw [hZS, Subgroup.card_bot]
      exact odd_one
    · rw [hcard]
      exact dvd_mul_of_dvd_left h2F _
  have h3 : 3 ∣ Nat.card (↥(Λ.map (QuotientGroup.mk' U)) ⧸
      center ↥(Λ.map (QuotientGroup.mk' U))) := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZS).trans
      QuotientGroup.quotientBot).toEquiv, hcard]
    exact CFSG.RankThree.PartTwo.Sec13.Res5Proof.three_dvd_mul_sq_sub_one _
  exact ⟨U, hUn, Λ, hU2, hΛU, hc, hodd, hLEV, hqs, h3⟩

private theorem censusAlt_blockFacts_oneBlock_fin_one {Q : Type} [Group Q] (B : Subgroup Q)
    (hqs : CFSG.Open.IsQuasisimple ↥B) (h3 : 3 ∣ Nat.card (↥B ⧸ center ↥B)) :
    CensusAlt (fun _ : Fin 1 => B) ∧ BlockFacts False False (fun _ : Fin 1 => B) := by
  have hcard : Nat.card {j : Fin 1 // (fun _ : Fin 1 => B) j ≠ ⊥} ≤ 2 := by
    have h1 : Nat.card {j : Fin 1 // (fun _ : Fin 1 => B) j ≠ ⊥} ≤ Nat.card (Fin 1) :=
      Finite.card_subtype_le _
    rw [Nat.card_fin] at h1
    omega
  refine ⟨Or.inl ⟨hcard, fun _ => Or.inr hqs⟩, ⟨fun _ _ => h3, ?_, Or.inl hcard⟩⟩
  intro j hj
  exact not_nonempty_mulEquiv_perm_three (H := B) (Or.inr hqs) hj

private theorem four_le_card_and_two_dvd_of_card_eq_two_pow {K : Type} {f : ℕ}
    (hKcard : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) :
    4 ≤ Nat.card K ∧ 2 ∣ Nat.card K := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  refine ⟨hK4, ?_⟩
  rw [hKcard]
  exact dvd_pow_self 2 (by omega : f ≠ 0)

private theorem hasLeviDataX_of_g2_of_model
    {S K : Type} [Group S] [Finite S] [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hKcard : Nat.card K = 2 ^ f) (hf2 : 2 ≤ f) (e : S ≃* CFSG.Blueprint.AdjointQuotient .G2 K)
    {J : Subgroup S} (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX False False ↥J := by
  classical
  obtain ⟨hK4, h2K⟩ := four_le_card_and_two_dvd_of_card_eq_two_pow hKcard hf2
  have : Finite ↥(adjointGroup .G2 K) := generated_group_finite .G2 K
  obtain ⟨T, hT⟩ := hJ.2.2
  obtain ⟨π', hQ, hBA₀, i, hI₀⟩ := exists_single_node_g2 e T hT.le hT.ne' hJ.2.1
  obtain ⟨eL⟩ := nonempty_sl2_mulEquiv_rankOne_g2 (F := K) i
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := sl2_isSimpleGroup hK4
  have : IsSimpleGroup ↥(rankOne (g2Datum K).rootGroup i) := eL.symm.isSimpleGroup
  have hnc : ∃ a b : ↥(rankOne (g2Datum K).rootGroup i), a * b ≠ b * a :=
    ⟨eL (sl2Upper 1 * sl2Lower 1), eL (sl2Upper 1), fun h =>
      sl2_upper_lower_not_commute (eL.injective (by simpa [map_mul] using h))⟩
  have hLU := rankOne_inf_posUnipotentExcept_eq_bot hQ i hnc
  let ρ : ↥(adjointGroup .G2 K) →* ↥(⊤ : Subgroup S) :=
    π'.codRestrict ⊤ fun _ => Subgroup.mem_top _
  let A : Subgroup ↥(adjointGroup .G2 K) := (J.subgroupOf (⊤ : Subgroup S)).comap ρ
  have hBA : borel (g2Datum K) (torus (τ := .G2) K) ≤ A := hBA₀
  have hI : negIndices (g2Datum K) A = {i} := hI₀
  obtain ⟨U, hUn, Λ, hU2, hΛU, hc, hodd, hLEV, hqs, h3blk⟩ :=
    exists_oneBlock_node hQ hBA hI hLU hK4 h2K eL
  let Sl : ∀ _ : Fin 1, Subgroup (↥A ⧸ U) := fun _ => Λ.map (QuotientGroup.mk' U)
  let β : ↥A →* ∀ _ : Fin 1, ↥A ⧸ U := MonoidHom.pi fun _ : Fin 1 => QuotientGroup.mk' U
  have hβ : IsPGroup 2 β.ker := isPGroup_ker_oneBlock U hU2
  have hpi : Subgroup.pi Set.univ Sl ≤ β.range := pi_le_range_oneBlock U Λ
  have hn : β.range ≤ Subgroup.normalizer
      (Subgroup.pi Set.univ Sl : Set (∀ _ : Fin 1, ↥A ⧸ U)) :=
    le_normalizer_of_commutator_le hpi (commutator_range_oneBlock_le U Λ hc)
  have hi : ¬ 2 ∣ (Subgroup.pi Set.univ Sl).relIndex β.range :=
    not_two_dvd_relIndex_pi_oneBlock U Λ hodd
  have hSl : ∀ j, Sl j = ⊥ ∨ IsLeviBlock ↥(Sl j) := fun _ => Or.inr hLEV
  have hCB := censusAlt_blockFacts_oneBlock_fin_one (Λ.map (QuotientGroup.mk' U)) hqs h3blk
  have hρ : Function.Surjective ρ := by
    intro x
    obtain ⟨c, hc'⟩ := hQ.surj (x : S)
    exact ⟨c, Subtype.ext hc'⟩
  have hker : ρ.ker = π'.ker := by
    ext z
    simp [ρ]
  have hcρ : ρ.ker ≤ Subgroup.center ↥(adjointGroup .G2 K) := fun z hz =>
    hQ.ker_central z (hker ▸ hz)
  have hoρ : Odd (Nat.card ρ.ker) := by
    rw [hker]
    exact odd_card_of_pow_eq_one (M := Nat.card K - 1) hQ.odd fun z =>
      Subtype.ext (by simpa using hQ.ker_pow (z : ↥(adjointGroup .G2 K)) z.2)
  exact hasLeviDataX_of_cover le_top ρ hρ hcρ hoρ β hβ hpi hn hi hSl hCB.1 hCB.2

theorem hasLeviDataX_of_g2
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : CFSG.Blueprint.LieModel S .G2 0 2 f) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviDataX False False ↥J := by
  obtain ⟨hadm, hmodel⟩ := h.chevalleyExceptionalModel (by decide)
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := hmodel
  have hf2 : 2 ≤ f := by
    by_contra hf
    have h1 : f ≤ 1 := by omega
    have h2 : 2 ^ f ≤ 2 := by
      calc 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    have h3 : 3 ≤ 2 ^ f := hadm.2.2.2
    omega
  have : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact hasLeviDataX_of_g2_of_model hKcard hf2 e hJ

theorem hasLeviData_of_g2
    {S : Type} [Group S] [Finite S] {f : ℕ}
    (h : CFSG.Blueprint.LieModel S .G2 0 2 f) {J : Subgroup S}
    (hJ : S19.IsNontrivialParabolic S J) : HasLeviData ↥J :=
  (hasLeviDataX_of_g2 h hJ).hasLeviData

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
