module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1GR41Kit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1F431Kit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpLift
public import CFSG.RankThree.PartTwo.KFacts.K412AlternatingSix
public import CFSG.RankThree.PartTwo.KFacts.K412Alternating

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Sym

open CFSG.RankThree.PartTwo.KFacts.K412 (eSix card_eSix)

private theorem s16c1G_not_isCyclic_eSix : ¬ IsCyclic ↥eSix := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥eSix)
  rw [card_eSix] at hg
  have h3 : g ^ 3 = 1 :=
    Subtype.ext (CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 3) (g : Equiv.Perm (Fin 6)) g.2)
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at hdvd
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by norm_num)

theorem s16c1G_exists_noncyclic_three_of_isSym_six {X : Type} [Group X] (h : IsSym X 6) :
    ∃ E : Subgroup X, IsPGroup 3 E ∧ ¬ IsCyclic E := by
  obtain ⟨e⟩ := h
  have hE9 : IsPGroup 3 ↥eSix := IsPGroup.of_card (n := 2) (by rw [card_eSix]; norm_num)
  exact ⟨eSix.map e.symm.toMonoidHom, hE9.map e.symm.toMonoidHom,
    SpLift.not_isCyclic_map e.symm.toMonoidHom e.symm.injective s16c1G_not_isCyclic_eSix⟩

end Sym

section Result

variable {G : Type} [Group G] [Finite G]

private theorem s16c1G_quadF2_one {W : Type*} [CommGroup W] {Q : W → ZMod 2} (hQ : IsQuadF2 Q) :
    Q 1 = 0 := by
  have h := hQ.1 1 1 1
  simp only [polarQ, mul_one] at h
  generalize Q 1 = a at h ⊢
  revert a
  decide

@[expose] def R16_41_fin (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L →
      (∃ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q ∧ QuadInvariant Q (lBar V₀ V hV L)) ∧
      ∀ Q : Vtil V₀ V hV → ZMod 2, IsMinusQuadF2 Q → QuadInvariant Q (lBar V₀ V hV L) →
        (∀ w : Vtil V₀ V hV, w ≠ 1 → Q w = 0 → IsE16A5 ↥(ptCent (lBar V₀ V hV L) w)) ∧
        ∀ w : Vtil V₀ V hV, Q w ≠ 0 → IsSym ↥(ptCent (lBar V₀ V hV L) w) 6

theorem r16_41_of_fin (D : Data G) (h61 : UC6.R6_1 D) (h : R16_41_fin D) : R16_41 D := by
  intro V₀ V L hV hS hc
  obtain ⟨hex, hall⟩ := h V₀ V L hV hS hc
  refine ⟨hex, fun Q hQ hQinv => ?_⟩
  obtain ⟨hE, hSym⟩ := hall Q hQ hQinv
  refine ⟨hE, fun w hw => ⟨hSym w hw, fun x hx => ?_⟩⟩
  have hH125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := hH125.pairFacts
  have hcase : V₀ = ⊥ ∨ InCalV0 D.M V₀ V := by
    rcases hH125.1 with ⟨-, h0⟩ | ⟨h0, -⟩
    · exact Or.inl h0
    · exact Or.inr h0
  have h4 : Nat.card V₀ ≤ 4 := by
    have hV₀2 : IsPGroup 2 V₀ := fun g =>
      ⟨1, Subtype.ext (by simpa using hP.elemAbelian₀.2 (g : G) g.2)⟩
    rw [card_eq_two_pow_mSub hV₀2]
    calc 2 ^ mSub V₀ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hS.setting.hyp16.small
      _ = 4 := by norm_num
  have h3 : 3 ∈ D.sig := by
    rw [hc.2.2.1]
    exact Set.mem_singleton 3
  have hx0 : x.val ∉ V₀ := by
    intro h0
    have h1 : mkTil V₀ V hV x = 1 := (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2 h0
    apply hw
    rw [← hx, h1]
    exact s16c1G_quadF2_one hQ.1.1
  obtain ⟨E, hEp, hEc⟩ := s16c1G_exists_noncyclic_three_of_isSym_six (hSym w hw)
  have hle : E.map (ptCent (lBar V₀ V hV L) w).subtype ≤
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV x) := by
    rintro _ ⟨c, -, rfl⟩
    obtain ⟨hcL, hcw⟩ := Subgroup.mem_inf.1 c.2
    exact Subgroup.mem_inf.2 ⟨barSub_mono V₀ V hV hS.setting.hyp151.le hcL, by rw [hx]; exact hcw⟩
  exact centralizer_le_of_noncyclic_bar D h61 Nat.prime_three (by norm_num) h3 hV hP hcase
    h4 x hx0 hle (hEp.map _)
    (SpLift.not_isCyclic_map _ (Subgroup.subtype_injective _) hEc)

theorem r16_41_fin_of_kit (D : Data G) (hkitC : OmegaKitC) (hkitF : OmegaKitF) :
    R16_41_fin D := by
  intro V₀ V L hV hS hc
  have hF := hkitF (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  have hC := hkitC (Vtil V₀ V hV) (lBar V₀ V hV L) hc.2.1
  refine ⟨hF.1, fun Q hQ hQi => ⟨fun w hw hQw => hF.2.1 w hw ((hC.1 Q hQ hQi w hw).1 hQw),
    fun w hw => ?_⟩⟩
  have hw1 : w ≠ 1 := fun h => hw (h ▸ s16c1G_quadF2_one hQ.1.1)
  exact hF.2.2 w hw1 fun h960 => hw ((hC.1 Q hQ hQi w hw1).2 h960)

theorem r16_41_of (D : Data G) (h61 : UC6.R6_1 D) (hkitC : OmegaKitC) (hkitF : OmegaKitF) :
    R16_41 D :=
  r16_41_of_fin D h61 (r16_41_fin_of_kit D hkitC hkitF)

end Result

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
