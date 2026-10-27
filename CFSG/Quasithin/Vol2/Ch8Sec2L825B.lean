module

public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Vol2.Ch8Sec2Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3
open scoped commutatorElement

section L825B

variable {G : Type} [Group G]

omit [Group G] in
theorem conjSub_eq_conjSubgroup_82 [Group G] (V : Subgroup G) (h : G) :
    B6.conjSub h V = conjSubgroup V h⁻¹ := by
  ext x
  rw [B6.mem_conjSub, mem_conjSubgroup_iff, inv_inv]

variable [Finite G]

theorem mQuot_conjSub_ch82A_82 {V : Subgroup G} (hV : IsElemAbelian 2 V) {h : G} {k : ℕ}
    (hAC : ch82A V h ⊓ Subgroup.centralizer (V : Set G) = ch82ZI V h)
    (hm : mQuot (ch82A V h) (ch82A V h ⊓ Subgroup.centralizer (V : Set G)) + k =
      mQuot V (ch82ZI V h)) :
    mQuot (B6.conjSub h V) (ch82A V h) = k := by
  have hA : ch82A V h ≤ B6.conjSub h V := inf_le_left
  have hZA : ch82ZI V h ≤ ch82A V h := by rw [← hAC]; exact inf_le_left
  have hZV : ch82ZI V h ≤ V := inf_le_left
  have hVp : IsPGroup 2 ↥V := B2F.isPGroup_of_isElemAbelian hV
  have hVh : IsElemAbelian 2 (B6.conjSub h V) := by
    rw [conjSub_eq_conjSubgroup_82]
    exact isElemAbelian_conjSubgroup hV _
  have hVhp : IsPGroup 2 ↥(B6.conjSub h V) := B2F.isPGroup_of_isElemAbelian hVh
  have hZVh : ch82ZI V h ≤ B6.conjSub h V := inf_le_right
  have hcard : Nat.card ↥V = Nat.card ↥(B6.conjSub h V) := by
    rw [conjSub_eq_conjSubgroup_82, card_conjSubgroup]
  have h1 := mQuot_eq_of_card_eq hVp hVhp hZV hZVh hcard
  have h2 := mQuot_add hZA hA
  rw [hAC] at hm
  omega

theorem wParam_le_82 {T V : Subgroup G} (hV : IsElemAbelian 2 V) {h : G} {k : ℕ}
    (hAT : ch82A V h ≤ T) (hk : mQuot (B6.conjSub h V) (ch82A V h) = k) (hkV : k < rk ↥V)
    (hAC : ¬ ch82A V h ≤ Subgroup.centralizer (V : Set G)) : wParam T V ≤ (k : ℕ∞) := by
  have hAg : ch82A V h ≤ conjSubgroup V h⁻¹ := by
    rw [← conjSub_eq_conjSubgroup_82]
    exact inf_le_left
  have hk' : mQuot (conjSubgroup V h⁻¹) (ch82A V h) ≤ k := by
    rw [← conjSub_eq_conjSubgroup_82, hk]
  have hW : ch82A V h ≤ wClos V k T := le_wClos_of_mQuot_le hV h⁻¹ hAT hAg hk' hkV
  have hmem : k ∈ {j : ℕ | ¬ wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G)} := by
    intro hle
    exact hAC ((hW.trans hle).trans inf_le_right)
  exact iInf₂_le k hmem

omit [Finite G] in
theorem isWOffender_ch82A_82 {T V : Subgroup G} {h : G} {k : ℕ}
    (hA7 : ch82A V h = B6.conjSub h V ⊓ Subgroup.normalizer (V : Set G))
    (hk : mQuot (B6.conjSub h V) (ch82A V h) = k)
    (hAC : ¬ ch82A V h ≤ Subgroup.centralizer (V : Set G)) (hw : wParam T V = (k : ℕ∞)) :
    IsWOffender T V (ch82A V h) := by
  refine ⟨h⁻¹, ?_, ?_, ?_⟩
  · rw [hA7, conjSub_eq_conjSubgroup_82]
  · intro hbot
    apply hAC
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hah : a ∈ conjSubgroup V h⁻¹ := by
      rw [← conjSub_eq_conjSubgroup_82]
      exact ha.1
    have h1 : ⁅v, a⁆ ∈ ⁅V, conjSubgroup V h⁻¹⁆ := Subgroup.commutator_mem_commutator hv hah
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · rw [hw, ← conjSub_eq_conjSubgroup_82, ← hA7, hk]

omit [Finite G] in
theorem le_nParam_82 {H : Subgroup G} {k : ℕ} (hk : ∃ m : ℕ, E1.nParam H = ((k * m : ℕ) : ℕ∞))
    (hev : ¬ Odd (Nat.card ↥H)) : (k : ℕ∞) ≤ E1.nParam H := by
  obtain ⟨m, hm⟩ := hk
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · exfalso
    rw [mul_zero] at hm
    unfold E1.nParam at hm
    simp only [hev, ↓reduceIte] at hm
    have h1 : (1 : ℕ∞) ≤ ⨅ i ∈ {i : ℕ | 0 < i ∧ E1.InE i H}, (i : ℕ∞) := by
      refine le_iInf₂ fun i hi => ?_
      exact_mod_cast hi.1
    rw [hm] at h1
    exact absurd h1 (by norm_num)
  · rw [hm]
    exact_mod_cast Nat.le_mul_of_pos_right k hm0

end L825B

end CFSG.Quasithin.H13
