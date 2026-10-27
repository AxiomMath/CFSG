module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityChief
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddChain
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeUC.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsChiefFactorUnder IsSylowOf)

variable {G : Type} [Group G] [Finite G]

private theorem r920ims_exists_isSylowOf_ge {p : ℕ} [Fact p.Prime] {K E : Subgroup G}
    (hEK : E ≤ K) (hE : IsPGroup p ↥E) :
    ∃ P : Subgroup G, IsSylowOf p P K ∧ E ≤ P := by
  obtain ⟨T, hT⟩ := (hE.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hEK hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem false_of_chief_factor_two {H S Y U W M : Subgroup G} (hSH : IsSylowOf 2 S H) (hUH : U ≤ H)
    (hSY : S ≤ Y) (hSM : S ≤ M) (hUW : IsChiefFactorUnder 2 Y U W) (hUM : U ⊓ M ≤ W) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSU : IsSylowOf 2 (S ⊓ U) U := by
    have hSyl : IsSylowOf 2 S (S ⊔ U) := hSH.of_le le_sup_left (sup_le hSH.le hUH)
    exact hSyl.inf_of_le_normalizer le_sup_right
      (sup_le (hSY.trans hUW.2.1) Subgroup.le_normalizer)
  have hle : S ⊓ U ≤ W :=
    (le_inf inf_le_right (inf_le_left.trans hSM)).trans hUM
  have hUnor : U ≤ normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu w hw
    exact hUW.2.2.2.1 u hu w hw
  haveI hWn : (W.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW.1.le).mpr hUnor
  have hP : IsPGroup 2 (↥U ⧸ W.subgroupOf U) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) g
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr
      (by simpa using (hUW.2.2.2.2.2.1 (x : G) x.2))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have hWidx : (W.subgroupOf U).index = 2 ^ k := by
    rw [Subgroup.index_eq_card, hk]
  have hdvd : (W.subgroupOf U).index ∣ ((S ⊓ U).subgroupOf U).index :=
    Subgroup.index_dvd_of_le fun _ hx => hle hx
  have hodd : ¬ 2 ∣ ((S ⊓ U).subgroupOf U).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hSU).2.2
  have hk0 : k = 0 := by
    by_contra hk0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    exact hodd (dvd_trans (hWidx ▸ dvd_pow_self 2 (Nat.succ_ne_zero j)) hdvd)
  have hWtop : W.subgroupOf U = ⊤ :=
    (Subgroup.index_eq_one).mp (by rw [hWidx, hk0, pow_zero])
  exact absurd (le_antisymm (Subgroup.subgroupOf_eq_top.mp hWtop) hUW.1.le)
    (ne_of_gt hUW.1)

theorem false_of_chief_factor_seven {M Y U W A : Subgroup G} (hM : rankThreeIsMaxTwoLocal M)
    (hAY : A ≤ Y) (hA7 : Nat.card A = 7) (hAu : A ∈ uniqueSet M)
    (hUW : IsChiefFactorUnder 7 Y U W) (hUM : U ⊓ M ≤ W) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hApg : IsPGroup 7 ↥A := IsPGroup.of_card (n := 1) (by rw [hA7]; norm_num)
  obtain ⟨P, hPsyl, hAP⟩ := r920ims_exists_isSylowOf_ge le_sup_right hApg
  have hPM : P ≤ M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.le_of_mem_uniqueSet_of_isPGroup
      hM hAu hAP hPsyl.isPGroup
  have hPU : IsSylowOf 7 (P ⊓ U) U :=
    hPsyl.inf_of_le_normalizer le_sup_left
      (sup_le Subgroup.le_normalizer (hAY.trans hUW.2.1))
  have hle : P ⊓ U ≤ W :=
    (le_inf inf_le_right (inf_le_left.trans hPM)).trans hUM
  have hUnor : U ≤ normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu w hw
    exact hUW.2.2.2.1 u hu w hw
  haveI hWn : (W.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUW.1.le).mpr hUnor
  have hPquot : IsPGroup 7 (↥U ⧸ W.subgroupOf U) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective (s := W.subgroupOf U) g
    rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr
      (by simpa using (hUW.2.2.2.2.2.1 (x : G) x.2))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 7)).mp hPquot
  have hWidx : (W.subgroupOf U).index = 7 ^ k := by
    rw [Subgroup.index_eq_card, hk]
  have hdvd : (W.subgroupOf U).index ∣ ((P ⊓ U).subgroupOf U).index :=
    Subgroup.index_dvd_of_le fun _ hx => hle hx
  have hodd : ¬ 7 ∣ ((P ⊓ U).subgroupOf U).index :=
    (CFSG.ABGLocalTools.isSylowOf_iff.mp hPU).2.2
  have hk0 : k = 0 := by
    by_contra hk0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    exact hodd (dvd_trans (hWidx ▸ dvd_pow_self 7 (Nat.succ_ne_zero j)) hdvd)
  have hWtop : W.subgroupOf U = ⊤ :=
    (Subgroup.index_eq_one).mp (by rw [hWidx, hk0, pow_zero])
  exact absurd (le_antisymm (Subgroup.subgroupOf_eq_top.mp hWtop) hUW.1.le)
    (ne_of_gt hUW.1)

theorem exists_chief_factor_under_of_le_normalizer {r : ℕ} {X Y U W : Subgroup G}
    (hXY : X ≤ Y) (hUW : IsChiefFactorUnder r Y U W) :
    ∃ U₁ : Subgroup G, W ≤ U₁ ∧ U₁ ≤ U ∧ X ≤ normalizer (U₁ : Set G) ∧ U₁ ≠ W ∧
      IsChiefFactorUnder r X U₁ W := by
  classical
  have hWU : W ≤ U := hUW.1.le
  have hXU : X ≤ normalizer (U : Set G) := hXY.trans hUW.2.1
  have hex : ∃ m : ℕ, ∃ U₁ : Subgroup G, W ≤ U₁ ∧ U₁ ≤ U ∧
      X ≤ normalizer (U₁ : Set G) ∧ U₁ ≠ W ∧ m = Nat.card U₁ :=
    ⟨Nat.card U, U, hWU, le_rfl, hXU, (ne_of_lt hUW.1).symm, rfl⟩
  obtain ⟨U₁, hWU₁, hU₁U, hXU₁, hU₁ne, hU₁card⟩ := Nat.find_spec hex
  have hmin : ∀ V : Subgroup G, W ≤ V → V ≤ U → X ≤ normalizer (V : Set G) → V ≠ W →
      Nat.card U₁ ≤ Nat.card V := by
    intro V hWV hVU hXV hVne
    rw [← hU₁card]
    exact Nat.find_min' hex ⟨V, hWV, hVU, hXV, hVne, rfl⟩
  refine ⟨U₁, hWU₁, hU₁U, hXU₁, hU₁ne, ?_⟩
  refine ⟨lt_of_le_of_ne hWU₁ (Ne.symm hU₁ne), hXU₁, hXY.trans hUW.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact hUW.2.2.2.1 x (hU₁U hx) y hy
  · intro x hx y hy
    exact hUW.2.2.2.2.1 x (hU₁U hx) y (hU₁U hy)
  · intro x hx
    exact hUW.2.2.2.2.2.1 x (hU₁U hx)
  · intro X' hWX' hX'U₁ hNX'
    by_cases hX'W : X' = W
    · exact Or.inl hX'W
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hX'U₁
        (hmin X' hWX' (hX'U₁.trans hU₁U) hNX' hX'W))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
