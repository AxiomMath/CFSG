module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAEFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Coprime
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrCaseEleven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenCfg10Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenOrd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_aSet_eq_empty_of_rk_lt {W : Type*} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {k : ℕ}
    (h : ∀ A : Subgroup (MulAut W), A ≤ X → A ≠ ⊥ → IsElemAbelian2 A → rk ↥A < k) :
    E3.aSet k X = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  have h1 : k ≤ E3.mQuot A ⊥ := E3.le_mQuot_bot_of_mem_aSet hA
  have hmq : E3.mQuot A ⊥ = rk ↥A := by
    unfold E3.mQuot
    rw [Subgroup.relIndex_bot_left]
    rfl
  have h2 := h A hA.1 hA.2.1 hA.2.2.1
  omega

theorem s16t_aSet_two_eq_empty_of_odd_fstar {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hodd : ¬ 2 ∣ Nat.card ↥(Fstar X)) : E3.aSet 2 X = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro A hA
  obtain ⟨hFX, hFn, hself⟩ := s16c167_cfg10_fstar_facts X
  have hAY : A ≤ Subgroup.normalizer (Fstar X : Set (MulAut W)) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨fun hf => hFn a (hA.1 ha) f hf, fun hf => ?_⟩
    have h := hFn a⁻¹ (X.inv_mem (hA.1 ha)) (a * f * a⁻¹) hf
    simpa [mul_assoc] using h
  have hcent := s16c11_le_centralizer_of_mem_aSet_two hW hA hodd hAY
  have hAF : A ≤ Fstar X := fun a ha =>
    hself a (hA.1 ha) fun f hf => (Subgroup.mem_centralizer_iff.1 (hcent ha) f hf).symm
  obtain ⟨t, htA, hto⟩ :=
    E3.exists_orderOf_two_of_isPGroup (E3.isPGroup_of_isElemAbelian2 hA.2.2.1) hA.2.1
  exact hodd (hto ▸ Subgroup.orderOf_dvd_natCard (Fstar X) (hAF htA))

theorem s16t_calABar_eq_empty_of_case168_8 (D : Data G) {V : Subgroup G}
    {hV : IsElemAbelian 2 V} (h8 : Case168_8 D ⊥ V hV) {k : ℕ} (hk : 2 ≤ k) :
    calABar k D.M ⊥ V hV = ∅ := by
  have hodd : ¬ 2 ∣ Nat.card ↥(Fstar (Mbar D.M ⊥ V hV)) := by
    have hc : Nat.card ↥(fstarBar D.M ⊥ V hV) = 3 ^ 2 := s16c167_card_isElemAbelianOfRank h8.1
    change ¬ 2 ∣ Nat.card ↥(fstarBar D.M ⊥ V hV)
    rw [hc]
    norm_num
  have h2 := s16t_aSet_two_eq_empty_of_odd_fstar (s15_Infra_vtil_sq_eq_one ⊥ V hV) hodd
  have h3 := E3.aSet_anti hk (Mbar D.M ⊥ V hV)
  rw [h2] at h3
  exact Set.subset_empty_iff.1 h3

theorem s16t_calABar_eq_empty_of_case168_10 (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (h10 : Case168_10 D ⊥ V hV L) {k : ℕ} (hk : 2 ≤ k) :
    calABar k D.M ⊥ V hV = ∅ := by
  obtain ⟨p, hp, h10p⟩ := h10
  have hodd : ¬ 2 ∣ Nat.card ↥(Fstar (Mbar D.M ⊥ V hV)) := by
    change ¬ 2 ∣ Nat.card ↥(fstarBar D.M ⊥ V hV)
    rcases hp with rfl | rfl
    · rw [s16c167_card_isElemAbelianOfRank h10p.2.2.2.2]
      norm_num
    · rw [s16c167_card_isElemAbelianOfRank h10p.2.2.2.2]
      norm_num
  have h2 := s16t_aSet_two_eq_empty_of_odd_fstar (s15_Infra_vtil_sq_eq_one ⊥ V hV) hodd
  have h3 := E3.aSet_anti hk (Mbar D.M ⊥ V hV)
  rw [h2] at h3
  exact Set.subset_empty_iff.1 h3

theorem s16t_calABar_eq_empty_of_case168_11 (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hm : 1 < mBar D.M ⊥ V hV)
    (h : Case168_11 D ⊥ V hV L) : calABar (mBar D.M ⊥ V hV) D.M ⊥ V hV = ∅ := by
  refine s16t_aSet_eq_empty_of_rk_lt fun A hAX _ hAel => ?_
  have h1 := s16c167_rk_le_one_of_case168_11 D hV hc h hAX hAel
  omega

theorem s16t_calABar_eq_empty_of_case168_4With (D : Data G) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hm : 1 < mBar D.M ⊥ V hV) {r : ℕ}
    (hr : 3 ≤ r) (h : Case168_4With D ⊥ V hV L r) :
    calABar (mBar D.M ⊥ V hV) D.M ⊥ V hV = ∅ := by
  obtain ⟨p, hp, h4At⟩ := h
  have hpp : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpcore := s16n9b_case4_pcore D hV hc hpp (by omega : 1 < r) h4At.1
  have hLX : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := hpcore.trans (Subgroup.map_subtype_le _)
  have hge : 3 ≤ CFSG.Open.pRank p (Mbar D.M ⊥ V hV) := by
    obtain ⟨e⟩ := h4At.1
    have hcomm : ∀ a b : ↥(lBar ⊥ V hV L), a * b = b * a := fun a b =>
      e.injective (by rw [map_mul, map_mul, mul_comm])
    have hpow : ∀ a : ↥(lBar ⊥ V hV L), a ^ p = 1 := fun a => e.injective (by
      rw [map_pow, map_one]
      ext i
      simp)
    have hel : IsElemAbelian p (lBar ⊥ V hV L) :=
      ⟨⟨⟨hcomm⟩⟩,
        fun x hx => by simpa using congrArg Subtype.val (hpow ⟨x, hx⟩)⟩
    have h1 := CFSG.SectionRank.le_pRank hpp.one_lt hLX hel
      (s16c167_card_isElemAbelianOfRank h4At.1)
    omega
  exact s16ae_aSet_eq_empty_of_symSum (s15_Infra_vtil_sq_eq_one ⊥ V hV) hp (by omega) h4At.1
    hpcore h4At.2.1 hge hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
