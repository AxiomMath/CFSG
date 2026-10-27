module

public import CFSG.RankThree.GF2n.Stroth80.Sec37CommStmt
import CFSG.LargeExtraspecial.S4TwoD
import CFSG.LargeExtraspecial.S4TwoPSL
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
import CFSG.Sporadic.Mathieu.M22
import CFSG.Sporadic.Mathieu.M24
public import CFSG.Assembly.GL83LieDefs
public import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tim37

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LargeExtraspecial.S4

theorem pCore_two_eq_bot_of_normal {X : Type} [Group X]
    (hO2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥) (N : Subgroup X) [N.Normal] :
    CFSG.pCore 2 N = ⊥ := by
  have h := CFSG.ABGLocalTools.map_pCore_le_of_injective_of_normal (p := 2) N.subtype
    N.subtype_injective (by rw [Subgroup.range_subtype]; infer_instance)
  have h0 : CFSG.pCore 2 X = ⊥ := hO2 _ CFSG.pCore_normal CFSG.pCore_isPGroup
  rw [h0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h
  exact h

noncomputable def mulEquivQuotientPCore {N : Type*} [Group N] (hP : CFSG.pCore 2 N = ⊥) :
    N ≃* N ⧸ CFSG.pCore 2 N :=
  MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.pCore 2 N))
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hP],
      QuotientGroup.mk'_surjective _⟩

theorem exists_mulEquiv_Form2Q {X : Type} [Group X] {L : Subgroup X}
    (hP : CFSG.pCore 2 (Subgroup.normalClosure (L : Set X)) = ⊥) :
    ∃ φ : Subgroup.normalClosure (L : Set X) ≃* Form2Q X L,
      (L.subgroupOf (Subgroup.normalClosure (L : Set X))).map φ.toMonoidHom = Form2L X L :=
  ⟨mulEquivQuotientPCore hP, rfl⟩

theorem card_map_mk_of_odd {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : IsElemAbelian 2 T) (Z : Subgroup K) [Z.Normal] (hZodd : Odd (Nat.card Z)) :
    Nat.card (T.map (QuotientGroup.mk' Z)) = Nat.card T := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : T => (⟨QuotientGroup.mk' Z t, Subgroup.mem_map_of_mem _ t.2⟩ :
      T.map (QuotientGroup.mk' Z))) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : QuotientGroup.mk' Z (a : K) = QuotientGroup.mk' Z (b : K) :=
      congrArg Subtype.val hab
    have h2 : (a : K)⁻¹ * b ∈ Z := QuotientGroup.eq.mp h1
    have h3 : (a : K)⁻¹ * b ∈ T := T.mul_mem (T.inv_mem a.2) b.2
    exact Subtype.ext (inv_mul_eq_one.mp (eq_one_of_mem_of_odd_card hT hZodd h3 h2))
  · rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

theorem eleven_dvd_card_of_isSporadic
    {G : Type} [Group G]
    (h : CFSG.Blueprint.NativeSporadic.IsSporadic G .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M24) : 11 ∣ Nat.card G := by
  rcases h with h | h | h
  · obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := h
    have h22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
      CFSG.Sporadic.Mathieu.card_M22
    rw [Nat.card_congr e.toEquiv, h22]
    norm_num
  · obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) := h
    have h23 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 :=
      CFSG.Sporadic.Schreier.m23_card
    rw [Nat.card_congr e.toEquiv, h23]
    norm_num
  · obtain ⟨e⟩ : Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
    have h24 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
      CFSG.Sporadic.Mathieu.card_M24
    rw [Nat.card_congr e.toEquiv, h24]
    norm_num

theorem dichotomy_of_stdPair
    (hA : OddCentralLiftStatement) (hB : NormalLiftStatement)
    {X : Type} [Group X] [Finite X] {L : Subgroup X} (hL : IsWC L)
    (hwc : ∀ x : X, conjSubgroup x L ≤ Subgroup.normalizer (L : Set X) → conjSubgroup x L = L)
    (h16 : 16 ≤ Nat.card L) {N : Subgroup X} [N.Normal] (hLN : L ≤ N)
    {K : Type} [Group K] [Finite K] (φ : N ≃* K) {T : Subgroup K}
    (hφ : (L.subgroupOf N).map φ.toMonoidHom = T) (Zc : Subgroup K) [Zc.Normal]
    (hZ : Zc ≤ Subgroup.center K) (hodd : Odd (Nat.card Zc))
    (hstd : StdPair (K ⧸ Zc) (T.map (QuotientGroup.mk' Zc))) :
    ConjTwoTransitive X L ∨
      (∀ x : X, conjSubgroup x L ⊓ Subgroup.normalizer (L : Set X) ≠ ⊥) ∨
      (Nat.card L = 16 ∧ 11 ∣ Nat.card N) := by
  have hTcard : Nat.card T = Nat.card L := by
    rw [← hφ, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv
  have hTel : IsElemAbelian 2 T := by
    rw [← hφ]
    exact (hL.1.subgroupOf N).map φ.toMonoidHom
  have hT'card : Nat.card (T.map (QuotientGroup.mk' Zc)) = Nat.card L := by
    rw [card_map_mk_of_odd hTel Zc hodd, hTcard]
  obtain ⟨hA1, hA2⟩ := hA K Zc hZ hodd T hTel.isPGroup
  obtain ⟨hB1, hB2⟩ := hB X N L hLN hL.1.isPGroup hwc
  have hleft : ConjTwoTransitive (K ⧸ Zc) (T.map (QuotientGroup.mk' Zc)) →
      ConjTwoTransitive X L := fun h2 => by
    refine hB1 (conjTwoTransitive_of_mulEquiv φ ?_)
    rw [hφ]
    exact hA1 h2
  have hmid : (∀ x : K ⧸ Zc, conjSubgroup x (T.map (QuotientGroup.mk' Zc)) ⊓
      Subgroup.normalizer ((T.map (QuotientGroup.mk' Zc) : Subgroup (K ⧸ Zc)) :
        Set (K ⧸ Zc)) ≠ ⊥) →
      ∀ x : X, conjSubgroup x L ⊓ Subgroup.normalizer (L : Set X) ≠ ⊥ := fun hmeet => by
    refine hB2 (meet_of_mulEquiv φ ?_)
    rw [hφ]
    exact hA2 hmeet
  have hsporadic : (CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Zc) .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Zc) .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic (K ⧸ Zc) .M24) →
      Nat.card L = 16 ∧ 11 ∣ Nat.card N := fun hM => by
    refine ⟨hT'card.symm.trans (hstd.card_sporadic hM), ?_⟩
    rw [Nat.card_congr φ.toEquiv, Subgroup.card_eq_card_quotient_mul_card_subgroup Zc]
    exact Dvd.dvd.mul_right (eleven_dvd_card_of_isSporadic hM) _
  rcases hstd.listGroup with ⟨m, s, hm, hs, hmod⟩ | ⟨s, hs, hmod⟩ | ⟨s, hso, hs, hmod⟩ |
      ⟨k, hk6, hk9, ⟨eA⟩⟩ | hM | hM | hM
  · rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      exact Or.inl (hleft (hstd.of_psl2 hmod).2.2.1)
    · obtain ⟨-, K', hF, hfin, hK', ⟨e⟩⟩ := hmod
      refine Or.inr (Or.inl (hmid ?_))
      obtain ⟨-, hTe⟩ := hstd.of_psl hm3 K' hK' e
      rcases hTe with ⟨c, hc0, hc⟩ | ⟨a, ha0, ha⟩
      · refine meet_of_mulEquiv e ?_
        rw [hc]
        exact (pslTransvectionMeetInput m K' hm3).1 c hc0
      · refine meet_of_mulEquiv e ?_
        rw [ha]
        exact (pslTransvectionMeetInput m K' hm3).2 a ha0
  · exact Or.inl (hleft (hstd.of_psu3 hs hmod).2.2.1)
  · exact Or.inl (hleft (hstd.of_sz hso hs hmod).2.2.1)
  · exfalso
    have hTk := hstd.card_alternating hk6 hk9 ⟨eA⟩
    rw [hT'card] at hTk
    split_ifs at hTk <;> omega
  · exact Or.inr (Or.inr (hsporadic (Or.inl hM)))
  · exact Or.inr (Or.inr (hsporadic (Or.inr (Or.inl hM))))
  · exact Or.inr (Or.inr (hsporadic (Or.inr (Or.inr hM))))

theorem form2Dichotomy_of_lifts
    (hA : OddCentralLiftStatement) (hB : NormalLiftStatement) :
    Form2DichotomyStatement := by
  intro hF2 X _ _ L hL hO2 hwc h16
  have hP := pCore_two_eq_bot_of_normal hO2 (Subgroup.normalClosure (L : Set X))
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_Form2Q hP
  have hTcard : Nat.card (Form2L X L) = Nat.card L := by
    rw [← hφ, Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalClosure).toEquiv
  rcases hF2 X L hL with ⟨hle, -⟩ | ⟨-, -, hodd, -, hstd⟩
  · omega
  · exact dichotomy_of_stdPair hA hB hL hwc h16 Subgroup.le_normalClosure φ hφ _ le_rfl hodd hstd

end CFSG.RankThree.GF2n.Stroth80.Tim37
