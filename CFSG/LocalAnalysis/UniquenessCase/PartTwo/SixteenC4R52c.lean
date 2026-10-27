module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4R52b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelTv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem exists_suSub_eq (E : Subgroup ↥(SUid F.σ 4)) :
    ∃ X : Subgroup (MulAut (Vtil V₀ V hV)), X ≤ lBar V₀ V hV L ∧ F.suSub X = E := by
  refine ⟨(E.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype,
    Subgroup.map_subtype_le _, ?_⟩
  have hXeq : ((E.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype).subgroupOf
      (lBar V₀ V hV L) = E.map F.π.toMonoidHom :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
  change (((E.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype).subgroupOf
      (lBar V₀ V hV L)).comap F.π.toMonoidHom = E
  rw [hXeq]
  exact Subgroup.comap_map_eq_self_of_injective F.π.injective E

theorem le_of_suSub_le {X Y : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ lBar V₀ V hV L)
    (hY : Y ≤ lBar V₀ V hV L) (h : F.suSub X ≤ F.suSub Y) : X ≤ Y := by
  intro φ hφ
  obtain ⟨γ, hγ⟩ := F.π.surjective ⟨φ, hX hφ⟩
  have hφeq : (F.π γ : MulAut (Vtil V₀ V hV)) = φ := by
    simpa using congrArg (fun g : ↥(lBar V₀ V hV L) => (g : MulAut (Vtil V₀ V hV))) hγ
  have hγX : γ ∈ F.suSub X := (F.mem_suSub X γ).2 (by rw [hφeq]; exact hφ)
  have hγY : γ ∈ F.suSub Y := h hγX
  have hmem : (F.π γ : MulAut (Vtil V₀ V hV)) ∈ Y := (F.mem_suSub Y γ).1 hγY
  rwa [hφeq] at hmem

end UFrame

theorem s16c4_card_preTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hle : V₀ ≤ V)
    (S : Subgroup (Vtil V₀ V hV)) :
    Nat.card (preTil V₀ V hV S) = Nat.card V₀ * Nat.card S := by
  unfold preTil
  rw [Subgroup.card_map_of_injective (IntMod.val_injective (hV := hV))]
  have hmod : Nat.card (modNull V₀ V hV) = Nat.card V₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hpre : Nat.card (S.comap (mkTil V₀ V hV)) =
      Nat.card (modNull V₀ V hV) * Nat.card S := by
    have h := Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet
      (modNull V₀ V hV) (S : Set (Vtil V₀ V hV)))
    rw [Nat.card_prod] at h
    exact h
  rw [hpre, hmod]

theorem s16c4_mSub_preTil {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hle : V₀ ≤ V)
    (S : Subgroup (Vtil V₀ V hV)) : mSub (preTil V₀ V hV S) = mSub V₀ + rk ↥S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold mSub rk
  rw [s16c4_card_preTil hV hle S]
  exact padicValNat.mul (card_subgroup_pos V₀).ne' (card_subgroup_pos S).ne'

theorem s16c4_r52_root_bar {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (F : UFrame V₀ V hV L) {X : Subgroup (MulAut (Vtil V₀ V hV))}
    (hXL : X ≤ lBar V₀ V hV L) (hX2 : IsElemAbelian2 X) (hXc : Nat.card X = 2 ^ 4) :
    ∃ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≤ X ∧ Nat.card B = 2 ∧
      Nat.card (fixV B) = 2 ^ 6 ∧ ∀ φ ∈ X, (∀ w ∈ fixV B, φ w = w) → φ ∈ B := by
  have hF : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  obtain ⟨hE2, hEc⟩ := F.suSub_sq_comm hXL hX2
  have hcard : Nat.card ↥(F.suSub X) = 2 ^ (4 * 1) := by
    rw [F.card_suSub hXL, hXc]
  obtain ⟨B₁, B₂, hB₁E, -, hB₁c, -, hB₁char, -, hB₁fix, -, -⟩ :=
    s16_C4ModelTv_two_root_groups F.isUnitary F.two_eq_zero (E := F.suSub X) hE2 hEc
      (n := 1) le_rfl hF hcard
  obtain ⟨B, hBL, hBsu⟩ := F.exists_suSub_eq B₁
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · exact F.le_of_suSub_le hBL hXL (by rw [hBsu]; exact hB₁E)
  · rw [← F.card_suSub hBL, hBsu, hB₁c]; norm_num
  · rw [F.card_fixV_eq hBL, hBsu, hB₁fix]
  · intro φ hφ hfix
    obtain ⟨γ, hγ⟩ := F.π.surjective ⟨φ, hXL hφ⟩
    have hφeq : (F.π γ : MulAut (Vtil V₀ V hV)) = φ := by
      simpa using congrArg (fun g : ↥(lBar V₀ V hV L) => (g : MulAut (Vtil V₀ V hV))) hγ
    have hγE : γ ∈ F.suSub X := (F.mem_suSub X γ).2 (by rw [hφeq]; exact hφ)
    have hγB₁ : γ ∈ B₁ := by
      rw [hB₁char γ]
      refine ⟨hγE, ?_⟩
      intro x hx
      have hof : F.ofVec x ∈ fixV B := by
        rw [F.mem_fixV_iff_fixSp hBL (F.ofVec x), F.vec_ofVec, hBsu]
        exact hx
      have hxh : φ (F.ofVec x) = F.ofVec x := hfix (F.ofVec x) hof
      have hv : F.vec (φ (F.ofVec x)) = F.vec (F.ofVec x) := congrArg F.vec hxh
      rw [show x = F.vec (F.ofVec x) from (F.vec_ofVec x).symm]
      rw [← F.vec_action γ (F.ofVec x), hφeq]
      exact hv
    have hmem : φ ∈ B := by
      rw [← hφeq]
      exact (F.mem_suSub B γ).1 (by rw [hBsu]; exact hγB₁)
    exact hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
