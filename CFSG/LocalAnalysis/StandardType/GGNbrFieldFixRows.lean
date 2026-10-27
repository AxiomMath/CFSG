module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem largeEvenLabelAll_rowPlain_typeA {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (h : lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p (lab.rank - 1)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn⟩ := h
  dsimp only at ht hl hpn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  have hr : l + 1 - 2 = l - 1 := by omega
  refine ⟨K, inferInstance, inferInstance, hK, hQ', fun g => ?_, ?_, fun _ _ => ?_⟩
  · have := RecipeFieldLinear.conj_mem_recI (d := l + 1) (K := K) g
    rwa [← SetLike.mem_coe, RecipeFieldLinear.coe_recI] at this
  · rw [← hr]
    exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (TypeA.ggTorusLift_sub_two hp hpK (by omega) (TypeA.slHasSections_of_five_le (by omega)))
  · rw [← hr]
    exact ggTorusNoLine_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
      (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ) (ggTorusNoLine_PSL hp hpK (by omega))

private theorem recipeSymplectic_rowPlain {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ GGNbrWeylRowPlain p l R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    fun g => RecipeFieldSp.mem_conjImage_iff_inn.mpr ⟨g, rfl⟩,
    TableBSymp.ggTorusLift_symplectic hp hp2 hpq hl,
    fun _ _ => ggTorusNoLine_of_ggTorusIrred hp
      (SpModel.ggTorusWeylInputs_symplectic hp hp2 hpq hl).2.1⟩

theorem largeEvenLabelAll_rowPlain_sp {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p lab.rank) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h hpn <;> subst h <;>
    exact recipeSymplectic_rowPlain hp hp2 hpn (le_trans (by norm_num) hlab.2.1) hQ

theorem largeEvenLabelAll_rowPlain_omegaPlus {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p lab.rank) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn⟩ := h
  dsimp only at ht hl hpn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => ⟨g, rfl⟩,
      TableBSymp.ggTorusLift_omegaPlus hp hp2 hpq (by omega),
      fun _ _ => ggTorusNoLine_of_ggTorusIrred hp
        (CorFourTwoMore.ggTorusIrred_omegaPlus hp hp2 hpq (by omega))⟩

theorem largeEvenLabelAll_rowPlain_omegaMinus {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p (lab.rank - 1)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpn⟩ := h
  dsimp only at ht hl hpn ⊢
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    have := charP_two_of_card hK
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', fun g => ⟨g, rfl⟩,
      TableBSymp.ggTorusLift_omegaMinus hp hp2 hpq (by omega) b c,
      fun _ _ => ggTorusNoLine_of_ggTorusIrred hp
        (CorFourTwoMore.ggTorusIrred_omegaMinus hp hp2 hpq (by omega) hbc)⟩

section ExceptionalRows

theorem largeEvenLabelAll_rowPlain_F4 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .F4 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 4) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at ht hpn
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => conj_mem_chevIDImage _ g,
    TableBF4.ggTorusLift_F4 hp hp2 hpq,
    fun _ _ => ggTorusNoLine_of_ggTorusIrred hp (CorFourTwoMore.ggTorusIrred_F4 hp hp2 hpq)⟩

theorem largeEvenLabelAll_rowPlain_E6 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h : lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 6) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at ht hpn
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => conj_mem_chevIDImage _ g,
    TableBExc.ggTorusLift_E6 hp hp2 hp3 hpq,
    fun _ _ => ggTorusNoLine_of_ggTorusIrred hp (CorFourTwoMore.ggTorusIrred_E6 hp hp2 hp3 hpq)⟩

theorem largeEvenLabelAll_rowPlain_E7 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .E7 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 7) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at ht hpn
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => conj_mem_chevIDImage _ g,
    TableBExc.ggTorusLift_E7 hp hp2 hpq,
    fun _ _ => ggTorusNoLine_of_ggTorusIrred hp (CorFourTwoMore.ggTorusIrred_E7 hp hp2 hpq)⟩

theorem largeEvenLabelAll_rowPlain_E8 {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : lab.tag = .E8 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p 8) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at ht hpn
  subst ht
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun g => conj_mem_chevIDImage _ g,
    TableBExc.ggTorusLift_E8 hp hp2 hpq,
    fun _ _ => ggTorusNoLine_of_ggTorusIrred hp (CorFourTwoMore.ggTorusIrred_E8 hp hp2 hpq)⟩

theorem largeEvenLabelAll_rowPlain_of_fieldFixRowLabel {p : ℕ} {lab : LargeEvenLabel}
    (hp : p.Prime) (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab) (h : GGFieldFixRowLabel p lab) :
    LargeEvenLabelAll lab (GGNbrWeylRowPlain p (ggFieldFixRank lab)) := by
  obtain ⟨hpn, h⟩ := h
  rcases h with (ht | ht | ht) | ⟨ht, hr⟩ | ⟨ht, hr, -⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hp3⟩
  · have e : ggFieldFixRank lab = 4 := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_F4 hp hp2 ⟨ht, hpn⟩
  · have e : ggFieldFixRank lab = 7 := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_E7 hp hp2 ⟨ht, hpn⟩
  · have e : ggFieldFixRank lab = 8 := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_E8 hp hp2 ⟨ht, hpn⟩
  · have e : ggFieldFixRank lab = lab.rank := by
      rcases ht with ht | ht <;> simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_sp hp hp2 hlab ⟨ht, hpn⟩
  · have e : ggFieldFixRank lab = lab.rank := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_omegaPlus hp hp2 ⟨ht, hr, hpn⟩
  · have e : ggFieldFixRank lab = lab.rank - 1 := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_omegaMinus hp hp2 ⟨ht, hr, hpn⟩
  · have e : ggFieldFixRank lab = lab.rank - 1 := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_typeA hp ⟨ht, hr, hpn⟩
  · have e : ggFieldFixRank lab = 6 := by simp [ggFieldFixRank, ht]
    rw [e]
    exact largeEvenLabelAll_rowPlain_E6 hp hp2 hp3 ⟨ht, hpn⟩

end ExceptionalRows

end CFSG.StandardType

end
