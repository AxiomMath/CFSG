module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NAlphaPrime
public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOuterPair
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSp projSU)
open CFSG.Blueprint.Chevalley CFSG.LieType.Ree
open Hering88N
open Matrix
open scoped MatrixGroups

theorem two_pow_odd_zmod_five {f : ℕ} (hf : Odd f) :
    ((2 ^ f : ℕ) : ZMod 5) = 2 ∨ ((2 ^ f : ℕ) : ZMod 5) = 3 := by
  obtain ⟨j, rfl⟩ := hf
  push_cast
  rw [pow_succ, pow_mul]
  have h4 : (2 : ZMod 5) ^ 2 = -1 := by decide
  rw [h4]
  rcases neg_one_pow_eq_or (ZMod 5) j with h | h
  · left
    rw [h, one_mul]
  · right
    rw [h]
    decide

theorem five_not_dvd_gl2 {f : ℕ} (hf : Odd f) :
    ¬ 5 ∣ ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 2 - 2 ^ f) := by
  have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have hq2 : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
  intro h
  have h' := (ZMod.natCast_eq_zero_iff _ 5).mpr h
  push_cast [Nat.cast_sub hq1, Nat.cast_sub hq2] at h'
  rcases two_pow_odd_zmod_five hf with h2 | h2
  · rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    rw [h2] at h'
    revert h'
    decide
  · rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    rw [h2] at h'
    revert h'
    decide

theorem five_not_dvd_su3 {f : ℕ} (hf : Odd f) :
    ¬ 5 ∣ (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
  have hq1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  intro h
  have h' := (ZMod.natCast_eq_zero_iff _ 5).mpr h
  push_cast [Nat.cast_sub hq1] at h'
  rcases two_pow_odd_zmod_five hf with h2 | h2
  · rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    rw [h2] at h'
    revert h'
    decide
  · rw [Nat.cast_pow, Nat.cast_ofNat] at h2
    rw [h2] at h'
    revert h'
    decide

theorem five_not_dvd_card_sl2 {F : Type} [Field F] [Finite F] {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : Odd f) : ¬ 5 ∣ Nat.card SL(2, F) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcF : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hGL : Nat.card (GL (Fin 2) F) = ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 2 - 2 ^ f) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hcF]
    simp
  have hdvd : Nat.card SL(2, F) ∣ Nat.card (GL (Fin 2) F) :=
    Subgroup.card_dvd_of_injective _ Matrix.SpecialLinearGroup.toGL_injective
  intro h5
  exact five_not_dvd_gl2 hf (hGL ▸ h5.trans hdvd)

@[expose] def SWFacts {G : Type} [Group G] [Finite G] (W : Subgroup G) : Prop :=
  ((∃ s : W ⧸ aschbacherSolvableCore 3 W, (∃ k : ℕ, s ^ 2 ^ k = 1) ∧ s ^ 4 ≠ 1) ∨
      5 ∣ Nat.card (W ⧸ aschbacherSolvableCore 3 W)) ∧
    (Nat.card (W ⧸ aschbacherSolvableCore 3 W) = 6048 ∨
      Nat.card (W ⧸ aschbacherSolvableCore 3 W) ≤ 720 ∨
      (17971200 ≤ Nat.card (W ⧸ aschbacherSolvableCore 3 W) ∧
        Nat.card (W ⧸ aschbacherSolvableCore 3 W) ≤ 35942400))

section XSide


theorem sWFacts_of_gTwo {G : Type} [Group G] [Finite G] {W M : Subgroup G} {a : G} (hWM : W ≤ M)
    (hW_img : imageModTheta M W =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M))
    (hG2 : IsoGTwoEven (barCentralizer (Subgroup.zpowers a) M) 1) : SWFacts W := by
  refine ⟨Or.inl (exists_order_eight_quot_of_isoGTwoEven hWM hW_img hG2 le_rfl), Or.inl ?_⟩
  rw [card_quot_theta_eq_of_isSimpleGroup hWM hW_img
    (isSimpleGroup_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2),
    card_inSubgroup_perfectResidual_of_isoGTwoEven_one hG2]

theorem sWFacts_of_sp4 {G : Type} [Group G] [Finite G] {W M : Subgroup G} {a : G} (hWM : W ≤ M)
    (hW_img : imageModTheta M W =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M))
    (ι : barCentralizer (Subgroup.zpowers a) M ≃* projSp 2 (GaloisField 2 1)) : SWFacts W := by
  obtain ⟨hS, h5⟩ := sp4two_residual ι
  have hN := card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS
  have h720 : Nat.card (barCentralizer (Subgroup.zpowers a) M) = 720 := by
    rw [Nat.card_congr ι.toEquiv]
    exact Item812Res2.card_projSp_two_one
  have hle := Subgroup.card_le_of_le
    (Item87Proof.residual_le (barCentralizer (Subgroup.zpowers a) M))
  unfold SWFacts
  rw [hN]
  exact ⟨Or.inr h5, Or.inr (Or.inl (hle.trans h720.le))⟩

theorem sWFacts_of_reeGamma_zero {G : Type} [Group G] [Finite G] {W M : Subgroup G} {a : G}
    (hWM : W ≤ M)
    (hW_img : imageModTheta M W =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M))
    {k' : Type} [Field k'] [Finite k'] [CharP k' ReeTag.F4.prime] (hk2 : Nat.card k' = 2)
    (φ : barCentralizer (Subgroup.zpowers a) M ≃* ReeTag.F4.reeGamma k' 0) : SWFacts W := by
  have hS := isSimpleGroup_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
  have hN := card_quot_theta_eq_of_isSimpleGroup hWM hW_img hS
  obtain ⟨hge, hle⟩ := card_inSubgroup_perfectResidual_of_reeGamma_zero hk2 φ
  have hC : Nat.card (barCentralizer (Subgroup.zpowers a) M) = 35942400 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_congr (ReeTag.reeFixedEquivReeGamma k' 0).symm.toEquiv]
    exact (card_commutator_reeFixed_zero hk2).1
  have hdvd : Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M)) ∣
      35942400 := hC ▸ Subgroup.card_dvd_of_le (Item87Proof.residual_le _)
  unfold SWFacts
  rw [hN]
  refine ⟨Or.inr ?_, Or.inr (Or.inr ⟨hge, hle⟩)⟩
  set N := Nat.card (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M))
  obtain ⟨i, hi⟩ := hdvd
  have hi3 : i < 3 := by
    by_contra h3
    push Not at h3
    have : N * 3 ≤ N * i := Nat.mul_le_mul_left N h3
    omega
  interval_cases i
  · omega
  · have hN1 : N = 35942400 := by omega
    rw [hN1]
    norm_num
  · have hN2 : N = 17971200 := by omega
    rw [hN2]
    norm_num

theorem sWFacts_of_isGammaIndex {G : Type} [Group G] [Finite G] {A M : Subgroup G} {a v : G}
    (hv : IsGammaIndex A M v 1) (hUn : ¬ IsUnitaryTwo (M ⧸ aschbacherSolvableCore 3 M) 3)
    (ha3 : a ^ 3 = 1)
    (hk : KFacts.InducesStdKind M a .field ∨ KFacts.InducesStdKind M a .graphField)
    (hG2 : Sec8PairGTwo M a 1) :
    SWFacts (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G))) := by
  classical
  obtain ⟨-, -, -, hcases⟩ := Item87Proof.isGammaIndex_cases hv
  have haN : a ∈ Subgroup.normalizer (M : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have haout : Sec4.InducesOuterTheta a M := by
    rcases hk with h' | h'
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta M h' (by decide)
  have hWM : inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G)) ≤ M :=
    (Item87Proof.residual_le _).trans inf_le_left
  have hW_img : imageModTheta M
      (inSubgroup perfectResidual (M ⊓ Subgroup.centralizer ({a} : Set G))) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) M) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  rcases hcases with ⟨hRee, -⟩ | ⟨htype, -⟩
  ·
    obtain ⟨k₀, hk₀, hkp, ⟨e₀⟩⟩ := hRee
    have hRT : CFSG.Blueprint.ReeTitsModel (M ⧸ aschbacherSolvableCore 3 M) .twistedF4 2
        (2 * k₀ + 1) :=
      CFSG.SectionRank.reeTitsModel_of_mulEquiv e₀ (Sec4.Census.bridgeExceptional46.reeF4 k₀ hk₀)
    obtain ⟨-, a', ha'1, hka, Kf, _, _, _, hKf, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hRT
    obtain ⟨b', k', _, _, _, hk', hb', ⟨φ⟩⟩ :=
      Item812Res2.exists_barCentralizer_mulEquiv_reeGamma_index ha'1 hKf e ha3 haout
    obtain rfl : b' = 0 := by omega
    exact sWFacts_of_reeGamma_zero hWM hW_img (by simpa using hk') φ
  · rcases htype with hD | ⟨q, hq2, hqe, hGq⟩ | hU | hSU | hSp
    · exact sWFacts_of_gTwo hWM hW_img (hG2 (Or.inl hD))
    · exact sWFacts_of_gTwo hWM hW_img
        (hG2 (Or.inr (Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hGq)))
    · exact (hUn (Or.inl (by simpa using hU))).elim
    · exact (hUn (Or.inr (by simpa using hSU))).elim
    · obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero ha3 haout hSp
      exact sWFacts_of_sp4 hWM hW_img ι

theorem xside_facts_of_unitary (h84 : Pair84A) {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X : Subgroup G}
    (h : Sec8Pair G A c L a b X 1) (hU : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) :
    SWFacts (sec8J X a) := by
  have ha3 : a ^ 3 = 1 := (Hering88C.pair_commute_pow_three h).2 a h.a_mem
  have hk := h84 G A c L a b X 1 h
  have haN : a ∈ Subgroup.normalizer (X : Set G) :=
    hk.elim (fun h' => h'.mem_normalizer) (fun h' => h'.mem_normalizer)
  have hWM : sec8J X a ≤ X := (Item87Proof.residual_le _).trans inf_le_left
  have hW_img : imageModTheta X (sec8J X a) =
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers a) X) :=
    KFacts.imageModTheta_perfectResidual_centralizer_eq haN ⟨1, by simpa using ha3⟩
  rcases h.centralizer_of_unitary ⟨3, hU⟩ with hG2 | hSp
  · exact sWFacts_of_gTwo hWM hW_img hG2
  · obtain ⟨ι⟩ := hSp
    exact sWFacts_of_sp4 hWM hW_img ι

theorem lside_facts {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    {a b : G} {X : Subgroup G} (h : Sec8Pair G A c L a b X 1)
    (hUn : ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3) : SWFacts (sec8I L a) := by
  have ha3 : a ^ 3 = 1 := (Hering88C.pair_commute_pow_three h).2 a h.a_mem
  have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) := by
    simp only [sec8I, hUn, ↓reduceIte]
  rw [hIdef]
  exact sWFacts_of_isGammaIndex h.isGammaIndex hUn ha3 h.inducesStdKind h.gTwo

end XSide

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
