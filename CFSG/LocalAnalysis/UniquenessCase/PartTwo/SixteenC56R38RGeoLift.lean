module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem r38_geometry_lift (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) {m : ℕ}
    (hm : Case1633 D V₀ V hV L m) {n : ℕ} (hn : n + 2 ≤ 2 * m) {g : G}
    (hO : InCalOStar n D.M V₀ V g) (S : OmegaModel (Vtil V₀ V hV))
    (hSω : S.omega = lBar V₀ V hV L) (hSK : Nat.card S.K = 2 ^ m) :
    ∃ (y : G) (hys : y ∈ stabTil V₀ V), y ∈ D.M ∧ y ^ (2 ^ m - 1) = 1 ∧
      (∀ v ∈ V, y * v * y⁻¹ = v → v ∈ NOf D.M V g) ∧
      ∃ e : Vtil V₀ V hV, e ≠ 1 ∧ S.Q e = 0 ∧
        ∀ w : Vtil V₀ V hV, actTil V₀ V hV ⟨y, hys⟩ w = w ↔ ∃ c : S.K, w = S.smul c e := by
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have h64 : Hyp64 n D.M V₀ V g := hyp64_of_hyp125 hH125 hO
  have h64' : Hyp64 n D.M V₀ V g := { h64 with elemAbelian := hV }
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64'
  have hM : D.M ≤ normalizer (V : Set G) := h64'.normalizer_eq.symm.le
  have hM₀ : D.M ≤ normalizer (V₀ : Set G) := h64'.le_normalizer₀
  obtain ⟨Y, hYtor⟩ := exists_isFixedPointFreeTorus h64'
  have hYcard : Nat.card Y = 2 ^ m - 1 := by
    rw [hYtor.1.2.1, r38_mQuot_UOf_eq D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK]
  have hm_ge2 : 2 ≤ m := by rcases hm with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hYgt1 : 1 < Nat.card Y := by
    rw [hYcard]
    have h2m : 4 ≤ 2 ^ m := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm_ge2
    omega
  have hYne : Y ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot Y).1 hYgt1
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hYne
    exact ⟨y, y.2, fun h => hy (Subtype.ext h)⟩
  have hYM : Y ≤ D.M :=
    fun z hz => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hYtor.1.1 hz)).1).2
  have hys : y ∈ stabTil V₀ V := le_stabTil hM hM₀ (hYM hyY)
  have hyq : y ^ (2 ^ m - 1) = 1 := by
    have hmem : (⟨y, hyY⟩ : ↥Y) ^ Nat.card Y = 1 := pow_card_eq_one'
    have h1 : y ^ Nat.card Y = 1 := by
      have h := congrArg (fun z : ↥Y => (z : G)) hmem
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h
      exact h
    rwa [hYcard] at h1
  have hm1 : 1 ≤ m := by omega
  have h2m_eq : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  have hq : Odd (2 ^ m - 1) := by
    refine ⟨2 ^ (m - 1) - 1, ?_⟩
    have hpos : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    omega
  obtain ⟨e, he1, heQ, hline⟩ :=
    r38_fixV_line D hSg h1219 h21 h22 h61 hext h5 hS hm hn hO S hSω hSK
  refine ⟨y, hys, hYM hyY, hyq, hYtor.2 y hyY hy1, e, he1, heQ, fun w => ⟨?_, ?_⟩⟩
  · intro hw
    obtain ⟨v, hv_eq, hv_fix⟩ := exists_fixed_lift_of_pow_eq_one hV hys hq hyq hw
    have hvN : v.val ∈ NOf D.M V g := hYtor.2 y hyY hy1 v.val v.val_mem hv_fix
    have hmem : mkTil V₀ V hV v ∈ imgTil V₀ V hV (NOf D.M V g) :=
      (mem_imgTil V₀ V hV (NOf D.M V g) (mkTil V₀ V hV v)).2 ⟨v, hvN, rfl⟩
    rw [← hv_eq]
    exact (hline _).1 (imgTil_NOf_le_fixV_barSub h64' hmem)
  · intro hw
    have haY : actTil V₀ V hV ⟨y, hys⟩ ∈ barSub V₀ V hV Y := actTil_mem_barSub V₀ V hV hyY hys
    exact barSub_fixes_fixV_BOf h64' hgen hYtor.1.1 _ haY w ((hline w).2 hw)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
