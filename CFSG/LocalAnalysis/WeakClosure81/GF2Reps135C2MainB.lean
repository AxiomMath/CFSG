module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LiftB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2A6
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcDirect
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2U33
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinRows
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslInner
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslOuter
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PslL42
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuInner
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuFourAll
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuOuter
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03A6
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U33
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03L4Two
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Gs03U62Holds
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2F4Direct
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2E6Direct
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2E7Direct
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2E8
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2GS03E8
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2D4Direct
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2TwE6Direct
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQ
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFour
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamily
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusFamily
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2SpFamily

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

private theorem w135c2_hnab_of_ctx (hctx : Is135Context Y L) :
    ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  obtain ⟨x, y, hxy⟩ := hq.2.2
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x', x'.2, y', y'.2, fun h => hxy ?_⟩
  have hL : (x' * y' : ↥L) = y' * x' := Subtype.ext h
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hL]

private theorem w135c2_ne_bot_of_ctx (hctx : Is135Context Y L) : L ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha, b, hb, hab⟩ := w135c2_hnab_of_ctx hctx
  rw [hbot] at ha hb
  rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb] at hab
  exact hab rfl

private theorem w135c2_conj_mem_of_ctx (hctx : Is135Context Y L) (htY : t ∈ Y) :
    ∀ g ∈ L, t * g * t⁻¹ ∈ L := by
  intro g hg
  have hLY : L ≤ Y := hctx.2.2.1
  have hmem := (w135_normal_of_ctx hctx).conj_mem
    (⟨g, hLY hg⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hg) (⟨t, htY⟩ : ↥Y)
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

theorem w135c2_tag_cases {S : Type} [Group S] {t : StatedLieTag} {n f : ℕ}
    (hlie : LieModel S t n 2 f) :
    Chev2DirectTag t ∨ t = .trialityD4 ∨ InnerDirectTag t ∨ t = .PSp ∨ t = .POmegaPlus ∨
      t = .POmegaMinus ∨ Chev2ExcDirectTag t := by
  have hadm := hlie.admissible
  cases t <;> first
    | (simp [Chev2DirectTag, InnerDirectTag, Chev2ExcDirectTag]; done)
    | (exfalso; simp [StatedLieAdmissible] at hadm)

theorem w135c2_branch_exc
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    {tag : StatedLieTag} {n f : ℕ} (hexc : Chev2ExcDirectTag tag)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) tag n 2 f) : W4Lem13_5Concl W Y L t := by
  exfalso
  have h4 : 4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
    rcases hexc with rfl | rfl | rfl | rfl | rfl
    · exact w135c2_four_le_mQuot_f4_direct hW hctx htY ht2 hlie
    · exact w135c2_four_le_mQuot_e6_direct hW hctx htY ht2 hlie
    · exact w135c2_four_le_mQuot_e7_direct hW hctx htY ht2 hlie
    · exact w135c2_four_le_mQuot_e8 gs03Alpha_e8 hW hctx htY ht2 hlie
    · exact w135c2_four_le_mQuot_twistedE6_direct hW hctx htY ht2 hlie
  omega

theorem w135c2_branch_omq
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (htY : t ∈ Y) (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    {tag : StatedLieTag} {n f : ℕ} (hom : OmQFamilyTag tag n f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) tag n 2 f) : W4Lem13_5Concl W Y L t := by
  rcases hom with ⟨rfl, hn, hf⟩ | ⟨rfl, hn, hf⟩
  · by_cases h4 : n = 4
    · subst h4
      exact w135c2_omPlus_four_f2 hW hctx htY ht2 hm hf hlie
    · exact w135c2_omPlus_f2 hW hctx htY ht2 hm (by omega) hf hlie
  · exact w135c2_omMinus_f2 hW hctx htY ht2 hm hn hf hlie

theorem w135c2_branch_omplus_two
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (htY : t ∈ Y) (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    {n f : ℕ} (hom : ¬ OmQFamilyTag .POmegaPlus n f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaPlus n 2 f) : W4Lem13_5Concl W Y L t := by
  obtain ⟨-, hf1, hn4⟩ := LieModel.admissible hlie
  have hf : f = 1 := by
    by_contra hf
    exact hom (Or.inl ⟨rfl, hn4, by omega⟩)
  subst hf
  exact w135c2_omPlus_two hW hctx htY ht2 hm hlie

theorem w135c2_branch_omminus_two
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L)
    (htY : t ∈ Y) (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    {n f : ℕ} (hom : ¬ OmQFamilyTag .POmegaMinus n f)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus n 2 f) : W4Lem13_5Concl W Y L t := by
  obtain ⟨-, hf1, hn4⟩ := LieModel.admissible hlie
  have hf : f = 1 := by
    by_contra hf
    exact hom (Or.inr ⟨rfl, hn4, by omega⟩)
  subst hf
  exact w135c2_omMinus_two hW hctx htY ht2 hm hlie

theorem w135c2_branch_psl
    (hGO : GS03AlphaOuterGeneral) (hRows : Chev135Rows) (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f) : W4Lem13_5Concl W Y L t := by
  by_cases htL : t ∈ L
  · exact w135c2_psl_inner hW hctx htL ht2 hm hlie
  by_cases h41 : n = 4 ∧ f = 1
  · obtain ⟨rfl, rfl⟩ := h41
    have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
    have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
    have hnab := w135c2_hnab_of_ctx hctx
    have hL := w135c2_ne_bot_of_ctx hctx
    have htN := w135c2_conj_mem_of_ctx hctx htY
    have hA3 : 3 ≤ gs03Bound .PSL 4 1 := w135c2_three_le_gs03Bound hlie
    obtain ⟨T, hTcard, hTconj, hTgen⟩ :=
      w135c2_gen_of_alpha_outer hGO hctx htY ht2 htL ⟨rfl, rfl, rfl⟩ hlie
    have hgen : rk W ≤ gs03Bound .PSL 4 1 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) :=
      w135c2_rk_le_mul_of_conj_gen hW hirr hL T hTconj hTgen hTcard
    obtain ⟨k, d, hk, hrk, hrange⟩ := w135c2_range hW hirr hnab htN ht2 hm hA3 hgen
    rcases chev2SmallModules_psl_l42 hW hq hirr hlie hk hrk hrange with hnat | hitem | hrow
    · exact w135c2_natural hctx htY ht2 hW hnat
    · exact w135c2_concl_of_item3 hitem
    · exfalso
      have hcard : Nat.card W = 2 ^ (k * d) := by rw [w135_card_eq_two_pow_rk hW, hrk]
      have h4 := w135c2_rows_of_idx hRows hrow W hW Y L t hctx htY ht2 hlie hcard
      omega
  · exact w135c2_psl_outer hRows hW hctx htY htL ht2 hm h41 hlie

theorem w135c2_branch_psu
    (hU6 : GS03AlphaU6) (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU n 2 f) : W4Lem13_5Concl W Y L t := by
  by_cases hn4 : n = 4
  · subst hn4
    exact w135c2_psu_four_all hW hctx htY ht2 hm hlie
  by_cases htL : t ∈ L
  · exact w135c2_psu_inner hW hctx htL ht2 hm hlie
  exact w135c2_psu_outer (psuSixOuterRow_of_gs03 hU6) hW hctx htY htL ht2 hm hn4 hlie

theorem w135c2_branch_triality
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .trialityD4 n 2 f) : W4Lem13_5Concl W Y L t := by
  exfalso
  have h4 := w135c2_four_le_mQuot_trialityD4_direct hW hctx htY ht2 hlie
  omega

theorem w135c2_branch_a6 (hGS : ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → ∀ A : ℕ, AlphaCase ↥S A → ∀ x : G, orderOf x = 2 → ∃ T :
    Finset G, T.card ≤ A ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧ S ≤ Subgroup.closure (T : Set G))
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hS : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6)))
    (hZ : Subgroup.center ↥L ≠ ⊥ → ¬ IsAlt (↥L ⧸ Subgroup.center ↥L) 6) :
    W4Lem13_5Concl W Y L t := by
  have hA6 := a6SmallModules_holds
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hL := w135c2_ne_bot_of_ctx hctx
  have hcenter : Subgroup.center ↥L = ⊥ := by
    by_contra hne
    exact hZ hne hS
  have hIsAlt : IsAlt ↥L 6 := by
    obtain ⟨e⟩ := hS
    exact ⟨QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hcenter).symm.trans e)⟩
  have hA : AlphaCase (↥L ⧸ Subgroup.center ↥L) 5 := Or.inl ⟨hS, rfl⟩
  obtain ⟨T, hTcard, hTconj, hTgen⟩ := w135c2_gen_of_alpha hGS hctx htY ht2 hA
  have hgen : rk W ≤ 5 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) :=
    w135c2_rk_le_mul_of_conj_gen hW hirr hL T hTconj hTgen hTcard
  have h15 : rk W ≤ 15 := by
    calc rk W ≤ 5 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hgen
      _ ≤ 5 * 3 := Nat.mul_le_mul_left 5 hm
      _ = 15 := by norm_num
  have hnat := hA6 W hW L hq hirr hIsAlt h15
  exact W4Lem13_5Concl.of_alt ⟨6, hIsAlt, hnat⟩

theorem w135c2_branch_u33 (hGS : ∀ (G : Type) [Group G] [Finite G] (S : Subgroup G), S.Normal →
    Subgroup.centralizer (S : Set G) = ⊥ → ∀ A : ℕ, AlphaCase ↥S A → ∀ x : G, orderOf x = 2 → ∃ T :
    Finset G, T.card ≤ A ∧ (∀ y ∈ T, ∃ s ∈ S, y = s * x * s⁻¹) ∧ S ≤ Subgroup.closure (T : Set
    G)) (hU : U33SmallModules)
    (hW : ∀ w : W, w ^ 2 = 1) (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 3 1) : W4Lem13_5Concl W Y L t := by
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have hL := w135c2_ne_bot_of_ctx hctx
  have hA : AlphaCase (↥L ⧸ Subgroup.center ↥L) 4 := Or.inr ⟨hlie, rfl⟩
  obtain ⟨T, hTcard, hTconj, hTgen⟩ := w135c2_gen_of_alpha hGS hctx htY ht2 hA
  have hgen : rk W ≤ 4 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) :=
    w135c2_rk_le_mul_of_conj_gen hW hirr hL T hTconj hTgen hTcard
  have h12 : rk W ≤ 12 := by
    calc rk W ≤ 4 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hgen
      _ ≤ 4 * 3 := Nat.mul_le_mul_left 4 hm
      _ = 12 := by norm_num
  obtain ⟨hPSU, hG2⟩ := hU W hW L hq hirr hlie h12
  exact Or.inr (Or.inl ⟨3, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hPSU, hG2⟩))))⟩)

theorem w4Lem13_5Chev2_holds
    : W4Lem13_5Chev2 := by
  unfold W4Lem13_5Chev2
  intro W _ _ hW Y L t hctx htY ht2 hm hS hZ
  obtain ⟨hGS, hGO⟩ :=
    w135c2_gs03_general gs03AlphaL4Two_holds gs03AlphaA6_holds gs03AlphaU33_holds
  have hU6 : GS03AlphaU6 := gs03AlphaU6_holds
  have hRows := chev135Rows_holds
  rcases hS with ⟨tag, n, f, -, hlie⟩ | hA6 | hU33
  · rcases w135c2_tag_cases hlie with hdir | rfl | hinn | rfl | rfl | rfl | hexc
    · exact w135c2_branch_direct hW hctx htY ht2 hm hdir hlie
    · exact w135c2_branch_triality hW hctx htY ht2 hm hlie
    · rcases hinn with rfl | rfl
      · exact w135c2_branch_psl hGO hRows hW hctx htY ht2 hm hlie
      · exact w135c2_branch_psu hU6 hW hctx htY ht2 hm hlie
    · exact w135c2_sp hW hctx htY ht2 hm hlie
    · by_cases hom : OmQFamilyTag .POmegaPlus n f
      · exact w135c2_branch_omq hW hctx htY ht2 hm hom hlie
      · exact w135c2_branch_omplus_two hW hctx htY ht2 hm hom hlie
    · by_cases hom : OmQFamilyTag .POmegaMinus n f
      · exact w135c2_branch_omq hW hctx htY ht2 hm hom hlie
      · exact w135c2_branch_omminus_two hW hctx htY ht2 hm hom hlie
    · exact w135c2_branch_exc hW hctx htY ht2 hm hexc hlie
  · exact w135c2_branch_a6 hGS hW hctx htY ht2 hm hA6 hZ
  · exact w135c2_branch_u33 hGS u33SmallModules_holds hW hctx htY ht2 hm hU33

end CFSG.LocalAnalysis.WeakClosure81
