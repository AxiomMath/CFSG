module

public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecA13Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem fixV_autOn_eq_subgroupOf {L V : Subgroup G} [IsMulCommutative ↥V]
    (hL : L ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autOn L V) = (Subgroup.centralizer (L : Set G)).subgroupOf V :=
  CFSG.Quasithin.AutOn.fixV_autOn_eq hL

theorem card_subgroupOf_eq (H K : Subgroup G) : Nat.card (K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.card_map_of_injective H.subtype_injective, Subgroup.subgroupOf_map_subtype,
    inf_comm]

theorem conjClosure_bot (H : Subgroup G) : conjClosure (⊥ : Subgroup G) H = ⊥ := by
  rw [eq_bot_iff]
  refine conjClosure_le fun h _ z hz => ?_
  rw [Subgroup.mem_bot] at hz ⊢
  rw [hz, mul_one, mul_inv_cancel]

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem card_cV_le (h16 : ASInputs.AS_I_1_6) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    (KindSL3 L (fsuV T I) n ∧ fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∨
      ((KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧
        Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) ≤ 2 ^ n) := by
  obtain ⟨hcomm, -, -, -, hcases⟩ := h1102 G T L I n h
  have hLV := L_le_normalizer_fsuV h
  have hW2 : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hfix := fixV_autOn_eq_subgroupOf (V := fsuV T I) hLV
  have hcard : Nat.card ↥(fixV (autOn L (fsuV T I))) =
      Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [hfix, card_subgroupOf_eq]
  have hbound := fun d => (h16 ↥(fsuV T I) hW2 (autOn L (fsuV T I)) d).1
    (commV_autOn_eq_top h)
  rcases hcases with ⟨K, _, _, hK, he, π, hπ, -⟩ | ⟨K, _, _, hK, he, π, hπ, -⟩ |
    ⟨K, _, _, hK, he, hG⟩
  · left
    refine ⟨⟨K, inferInstance, inferInstance, hK, he⟩, ?_⟩
    rw [← hfix] at hπ
    have h0 := hbound 0 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, h.one_lt, rfl, K, inferInstance, inferInstance, hK, π, hπ⟩)))))
    rw [hcard, pow_zero] at h0
    exact Subgroup.eq_bot_of_card_le _ h0
  · right
    refine ⟨Or.inl ⟨K, inferInstance, inferInstance, hK, he⟩, ?_⟩
    rw [← hfix] at hπ
    have h0 := hbound n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, h.one_lt, rfl, K, inferInstance, inferInstance, hK, π, hπ⟩)))))))
    rwa [hcard] at h0
  · right
    refine ⟨Or.inr ⟨K, inferInstance, inferInstance, hK, he⟩, ?_⟩
    rw [← hfix] at hG
    have h0 := hbound n (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, by have := h.one_lt; omega, rfl, hG⟩))))))))
    rwa [hcard] at h0

theorem stmt11_0_3_three (h325 : Stmt3_2_5) (h1102 : Stmt11_0_2) (h324 : TmpL6_3_2_2_four)
    (h326 : TmpL6_3_2_2_six) (h16 : ASInputs.AS_I_1_6) (h331 : Stmt3_3_1)
    (h : Hyp11 G T L I n) :
    (fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ cVM T L I = ⊥) ∨
      ((KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ fsuV T I = VM T L I ∧
        E3.mQuot (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) ⊥ ≤ n ∧
        L = ⁅L, thompsonJ T⁆) := by
  by_cases hC : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥
  · left
    refine ⟨hC, ?_⟩
    obtain ⟨-, h2⟩ := h324 G T L I h.fsu
    rw [fsuCVM_eq h, fsuL0_eq h, fsuM_eq h, hC] at h2
    rw [h2, conjClosure_bot]
  · right
    rcases card_cV_le h16 h1102 h with ⟨-, hC'⟩ | ⟨hk, hcard⟩
    · exact absurd hC' hC
    have hVM := fsuV_eq_VM_of_ne_bot h325 h hC
    refine ⟨hk, hVM, ?_, ?_⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := ((isPGroup_fsuV h).to_le
        (inf_le_left : fsuV T I ⊓ Subgroup.centralizer (L : Set G) ≤ fsuV T I)).exists_card_eq
      rw [E3.mQuot, Subgroup.relIndex_bot_left, hk, padicValNat.prime_pow]
      rw [hk] at hcard
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hcard
    · have hne : fsuCVM T L I ≠ ⊥ := by
        rw [fsuCVM_eq h]
        intro hb
        apply hC
        rw [eq_bot_iff, ← hb]
        exact inf_le_inf_right _ (le_conjClosure _ _)
      have hU : IsUniqueM (fsuL0 T L ⊔ T) (fsuM T L) := by
        rw [fsuM_eq h, fsuL0_eq h]
        exact isUniqueM_LT h331 h
      have := (h326 G T L I h.fsu hne hU).1
      rwa [fsuL0_eq h] at this

end CFSG.Quasithin.Vol2.Ch11.SecA
