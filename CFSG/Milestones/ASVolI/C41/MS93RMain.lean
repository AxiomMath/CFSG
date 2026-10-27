module

public import CFSG.Quasithin.MS93.Burnside.MS93RB
public import CFSG.Quasithin.MS93.Burnside.MS93RS45
public import CFSG.Quasithin.MS93.ASHyp
public import CFSG.Quasithin.MS93.Burnside.MS93RRed

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem burnsideMS93R_eq_of_isModO2Surj {G : Type} [Group G] {K : Subgroup G} {n n' : ℕ}
    {F F' : Type} [Field F] [Fintype F] [Field F'] [Fintype F']
    {α : ↥K →* ↥(StatedSL 3 F)} {α' : ↥K →* ↥(StatedSL 3 F')} (hF : Fintype.card F = 2 ^ n)
    (hF' : Fintype.card F' = 2 ^ n') (hα : IsModO2Surj K α) (hα' : IsModO2Surj K α') :
    n = n' := by
  have hn := one_le_of_card_eq_two_pow hF
  have hn' := one_le_of_card_eq_two_pow hF'
  have e := (card_quot_of_isModO2Surj hα).symm.trans (card_quot_of_isModO2Surj hα')
  rw [card_statedSL3_eq hF, card_statedSL3_eq hF'] at e
  have hA : Odd (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have hB : Odd (((2 ^ n') ^ 2 - 1) * ((2 ^ n') ^ 3 - 1)) :=
    (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num)).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  have e' : 2 ^ (n * 3) * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) =
      2 ^ (n' * 3) * (((2 ^ n') ^ 2 - 1) * ((2 ^ n') ^ 3 - 1)) := by
    rw [pow_mul, pow_mul, ← mul_assoc, ← mul_assoc, e]
  have := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hA hB e'
  omega

section Main

set_option linter.unusedSectionVars false

theorem burnsideMS93R_exists
    {G : Type} [Group G] [Finite G] {G₀ R K : Subgroup G}
    (hMS : IsMSPair G₀ R) (hK : K ∈ cComp G₀) (hG : (G₀ : Set G) = (K : Set G) * (R : Set G))
    {n : ℕ} {F : Type} [Field F] [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)}
    (hF : Fintype.card F = 2 ^ n) (hα : IsModO2Surj K α)
    (h4 : C134CorrLocal.IsC134Case4Corr G₀ R K)
    (hlin : S4L.NoNonlinSLGt4 ∨ R ≤ K ⊔ pCoreOf 2 G₀) (h5 : n = 1 → MRes.S45C1BTwo) :
    ∃ T : Subgroup G, T ≤ R ∧ (T.subgroupOf R).Characteristic ∧
      (K ⊔ T) ⊓ pCoreOf 2 G₀ ≤ T ∧
      (pCoreOf 2 (K ⊔ T)).relIndex T = (2 ^ n) ^ 2 ∧
      c134CQ G₀ K ≤ CFSG.Quasithin.centerOf (K ⊔ T) := by
  have h := puHyp_of_msPair hMS hK hG
  obtain ⟨T, hTR, hTc, hTO, hT, hTmin, hTV⟩ := burnsideMS93R_exists_charMin h
  have hVQ : Vq (K ⊔ T) K = c134Q G₀ K := hTV
  have hlin' : S4L.NoNonlinSLGt4 ∨ T ≤ K ⊔ pCoreOf 2 (K ⊔ T) :=
    hlin.imp id fun hR => S34D.le_sup_pCoreOf_of_le h hT hTR (hTR.trans hR)
  obtain ⟨hb, hfull⟩ := burnsideMS93R_four_lt_and_full hT hTmin hVQ h4 hlin'
  obtain ⟨F', _, _, φ, hφ⟩ := isSL3Full_iff_exists_via.mp hfull
  have hF' : Fintype.card F' = 2 ^ n := by
    obtain ⟨⟨n', hn'⟩, hφs, -⟩ := hφ
    have hsurj : Function.Surjective (φ.comp (Subgroup.inclusion hT.L_le)) := fun y => by
      obtain ⟨ℓ, hℓK, hℓ⟩ := exists_mem_L_eq hT hφs y
      exact ⟨⟨ℓ, hℓK⟩, hℓ⟩
    rw [hn', burnsideMS93R_eq_of_isModO2Surj hF hn' hα
      (MRes.isModO2Surj_of_surjective hT hn' hsurj)]
  have h5' : Fintype.card F' = 2 → MRes.S45C1BTwo := fun hq => h5 (by
    rw [hF'] at hq
    exact Nat.pow_right_injective le_rfl (hq.trans (pow_one 2).symm))
  obtain ⟨hidx, -, hZ⟩ := burnsideMS93R_s45data hT hTmin hb hφ h5'
  have hCQ : c134CQ G₀ K = Vq (K ⊔ T) K ⊓ Subgroup.centralizer (K : Set G) := by
    rw [hVQ]
    rfl
  refine ⟨T, hTR, hTc, hTO, ?_, ?_⟩
  · rw [hidx, hF']
  · obtain ⟨-, hZM, -, -⟩ := s41_holds G (K ⊔ T) T K hT hfull
    rw [hCQ]
    exact le_inf (inf_le_left.trans (Vq_le hT.L_le)) (hZ.trans hZM)

end Main

end CFSG.ASVolI
