module

public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetProved
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.Background.A3Structure36AList
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.Quasithin.Background.A3FactsA134
import CFSG.Adapters.StatedPSLTwoSeven

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def B42FamilyType (X : Type) [Group X] : Prop :=
  B42TypeU3Even X ∨ B42TypeSz X ∨ B42TypeTrialityD4 X ∨ B42TypeReeF4 X ∨ B42TypeL2Even X ∨
    B42TypeL32 X ∨ B42TypeL3Even X ∨ B42TypeSp4Even X ∨ B42TypeG2Even X ∨ B42TypeU33 X ∨
    B42TypeL42 X ∨ B42TypeL52 X ∨ B42TypeAlt5 X ∨ B42TypeAlt6 X ∨ B42TypeHatA6 X ∨
    B42TypeAlt7 X

namespace B42FamilyType

variable {X : Type} [Group X]

theorem of_u3Even (h : B42TypeU3Even X) : B42FamilyType X := Or.inl h

theorem of_sz (h : B42TypeSz X) : B42FamilyType X := Or.inr <| Or.inl h

theorem of_trialityD4 (h : B42TypeTrialityD4 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inl h

theorem of_reeF4 (h : B42TypeReeF4 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_l2Even (h : B42TypeL2Even X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_l32 (h : B42TypeL32 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_l3Even (h : B42TypeL3Even X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_sp4Even (h : B42TypeSp4Even X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_g2Even (h : B42TypeG2Even X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_u33 (h : B42TypeU33 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl h

theorem of_l42 (h : B42TypeL42 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl h

theorem of_l52 (h : B42TypeL52 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inl h

theorem of_alt5 (h : B42TypeAlt5 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_alt6 (h : B42TypeAlt6 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_hatA6 (h : B42TypeHatA6 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h

theorem of_alt7 (h : B42TypeAlt7 X) : B42FamilyType X :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h

end B42FamilyType

namespace B42Dispatch

theorem statedClassicalModel_psl_three_two_of_psl_two_seven {S : Type} [Group S]
    (h : StatedClassicalModel S .PSL 2 7 1) : StatedClassicalModel S .PSL 3 2 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_psl_three_two_of_psl_two_seven h

section Ambient

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem sqtkGroup_of_le {G L : Subgroup Ω} (hS : SQTKGroup ↥G) (hLG : L ≤ G) :
    SQTKGroup ↥L := by
  refine ⟨fun p hp hp2 => ?_,
    (hS.2.subgroup (L.subgroupOf G)).of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG).symm⟩
  exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (Subgroup.inclusion hLG)
    (Subgroup.inclusion_injective hLG)).trans (hS.1 p hp hp2)

theorem a23List_center_quotient
    {G L : Subgroup Ω} (hS : SQTKGroup ↥G) (hLG : L ≤ G) (hq : CFSG.IsQuasisimple ↥L) :
    A23List (↥L ⧸ Subgroup.center ↥L) := by
  let e₀ : ↥(L.subgroupOf G) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  let e : (↥L ⧸ Subgroup.center ↥L) ≃*
      (↥(L.subgroupOf G) ⧸ Subgroup.center ↥(L.subgroupOf G)) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥(L.subgroupOf G)) e₀.symm
      (Subgroup.map_center_eq e₀.symm)
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2.1
  have : IsSimpleGroup (↥(L.subgroupOf G) ⧸ Subgroup.center ↥(L.subgroupOf G)) :=
    e.symm.isSimpleGroup
  have hnonab : ∃ a b : ↥(L.subgroupOf G) ⧸ Subgroup.center ↥(L.subgroupOf G),
      a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  exact A36A.a23List_of_mulEquiv e
    (a23SQTKListFact ↥G hS (L.subgroupOf G) _ inferInstance hnonab)

end Ambient

section Center

variable {X : Type} [Group X] [Finite X]

theorem eq_bot_of_isPGroup_two_of_odd {H : Subgroup X} (h2 : IsPGroup 2 ↥H)
    (hodd : Odd (Nat.card ↥H)) : H = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact Subgroup.eq_bot_of_card_eq H (by rw [hk, pow_zero])
  · rw [hk] at hodd
    exact absurd ((Nat.even_pow' hk0.ne').2 even_two) (Nat.not_even_iff_odd.2 hodd)

theorem center_eq_bot_of_a134 (hq : CFSG.IsQuasisimple X)
    (hodd : Odd (Nat.card (Subgroup.center X))) (h : A134TypesCentral X) :
    Subgroup.center X = ⊥ :=
  eq_bot_of_isPGroup_two_of_odd (mult2Fact X hq h) hodd

theorem center_eq_bot_of_linear_four_five
    (hS : SQTKGroup X) (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    {n : ℕ} (hn : n = 4 ∨ n = 5) (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 1) :
    Subgroup.center X = ⊥ := by
  rcases catalogStepFact X hq hS hodd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exact (Vol2Native.false_of_linear_four_five hq h3 hn h).elim

theorem center_eq_bot_of_psu_three_three
    (hS : SQTKGroup X) (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (h : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 3 1) : Subgroup.center X = ⊥ := by
  rcases catalogStepFact X hq hS hodd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have : Group.IsPerfect X := hq.1
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have : Fintype F := Fintype.ofFinite F
    have : CharP F 3 := charP_of_card_eq_prime_pow (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hF]
      ring)
    have hsplit : ∀ q : ℕ, q = 3 → ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU 3 q F),
        Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
        ∃ s : StatedSU 3 q F →* E, ∀ g, π (s g) = g := by
      rintro q rfl E _ _ π hπ hC hodd'
      obtain ⟨⟨s, hs, -⟩, -⟩ :=
        CFSG.SectionRank.OddCover.prime_classical_three_central_odd_extension_splitting
          Nat.prime_three (by norm_num) (Or.inr ⟨rfl, by rw [hF, pow_one], rfl⟩) π hπ hC hodd'
      exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
    obtain ⟨hdvd, -⟩ := Ch1.triple_cover_unitary (p := 3) (f := 1) h3 hF e
      (hsplit (3 ^ 1) (pow_one 3))
    norm_num at hdvd

theorem center_eq_bot_of_g2
    (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X))) {f : ℕ}
    (h : ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 2 f) : Subgroup.center X = ⊥ := by
  have : Group.IsPerfect X := hq.1
  have h0 := CFSG.SectionRank.g2_even_perfect_odd_cover_trivial h
    (QuotientGroup.mk' (Subgroup.center X)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le (by rw [QuotientGroup.ker_mk']; exact hodd)
  rwa [QuotientGroup.ker_mk'] at h0

end Center

section Dispatch

variable {X : Type} [Group X] [Finite X]

theorem b42FamilyType_of_charTwoOrAlt
    (hS : SQTKGroup X) (hq : CFSG.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hD : Bridge.SQTKCharTwoOrAltNative (X ⧸ Subgroup.center X))
    (h7 : Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 7)) →
      Subgroup.center X = ⊥) :
    B42FamilyType X := by
  have halt5 : ∀ e : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 5), B42FamilyType X := by
    intro e
    have hm := Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ ⟨e⟩
    exact .of_alt5 ⟨center_eq_bot_of_a134 hq hodd (Or.inl ⟨2, hm⟩), ⟨e⟩, hm⟩
  have halt6 : ∀ e : (X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6), B42FamilyType X := by
    intro e
    rcases catalogStepFact X hq hS hodd with h1 | h3
    · exact .of_alt6 ⟨Subgroup.eq_bot_of_card_eq _ h1, ⟨e⟩⟩
    · exact .of_hatA6 ⟨hq, h3, ⟨e⟩⟩
  have hl42 : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 4 2 1 →
      Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 8)) → B42FamilyType X :=
    fun hm he => .of_l42
      ⟨center_eq_bot_of_linear_four_five hS hq hodd (Or.inl rfl) hm, hm, he⟩
  have hl32 : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL 3 2 1 → B42FamilyType X :=
    fun hm => .of_l32 ⟨center_eq_bot_of_a134 hq hodd (Or.inr <| Or.inr <| Or.inr
      ⟨7, 1, Nat.prime_seven, by norm_num, le_rfl, by norm_num,
        A3Facts.statedPSL_two_seven_of_three_two hm⟩), hm⟩
  rcases hD with ⟨n, h5, h8, ⟨e⟩⟩ | h251 | h271 | h232 | h331 | (⟨f, hf⟩ | hTits) |
    ⟨n, hn, hLn⟩
  · obtain rfl | rfl | rfl | rfl : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    · exact halt5 e
    · exact halt6 e
    · exact .of_alt7 ⟨h7 ⟨e⟩, ⟨e⟩⟩
    · exact hl42 (Ch1.statedClassicalModel_psl_four_two_of_alternating_eight _ ⟨e⟩) ⟨e⟩
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h251
    obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
      (Or.inr (by rw [hK, pow_one]))
    exact halt5 (e.trans e₅)
  · exact hl32 (statedClassicalModel_psl_three_two_of_psl_two_seven h271)
  · obtain ⟨e⟩ := Vol2Native.alternating_six_of_psl_two_nine h232
    exact halt6 e
  · exact .of_u33 ⟨center_eq_bot_of_psu_three_three hS hq hodd h331, h331⟩
  · rcases hf with ⟨hf2, h⟩ | ⟨hf1, h⟩ | ⟨hf2, h⟩ | ⟨hf2, h⟩ | ⟨hf2, h⟩ | ⟨hf1, h⟩ |
      ⟨hfo, hf3, h⟩ | ⟨hfo, hf3, h⟩
    · rcases Nat.lt_or_ge f 3 with hf3 | hf3
      · obtain rfl : f = 2 := by omega
        obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
        obtain ⟨e₅⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
          (Or.inl (by rw [hK]; norm_num))
        exact halt5 (e.trans e₅)
      · exact .of_l2Even ⟨center_eq_bot_of_a134 hq hodd (Or.inl ⟨f, h⟩), f, hf3, h⟩
    · rcases Nat.lt_or_ge f 2 with hf2 | hf2
      · obtain rfl : f = 1 := by omega
        exact hl32 h
      · exact .of_l3Even ⟨f, hf2, h⟩
    · exact .of_u3Even ⟨f, hf2, h⟩
    · exact .of_sp4Even
        ⟨(CFSG.SectionRank.EvenCover.even_symplectic_odd_cover_catalog_step hq hodd h).1, f, hf2,
          h⟩
    · exact .of_g2Even ⟨center_eq_bot_of_g2 hq hodd h, f, hf2, h⟩
    · exact .of_trialityD4 ⟨f, hf1, h⟩
    · exact .of_reeF4 (Or.inl ⟨f, hfo, hf3, h⟩)
    · exact .of_sz ⟨f, hfo, hf3, h⟩
  · exact .of_reeF4 (Or.inr hTits)
  · rcases hn with rfl | rfl
    · exact hl42 hLn (CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
        (Or.inl ⟨by decide, hLn⟩))
    · exact .of_l52 ⟨center_eq_bot_of_linear_four_five hS hq hodd (Or.inr rfl) hLn, hLn⟩

end Dispatch

end B42Dispatch

open B42Dispatch in
theorem b42FamilyType_of_offender
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L A : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (hA : IsFFStarOffender G A) :
    B42FamilyType ↥L := by
  obtain ⟨hSG, hLeq, hq, hirr⟩ := hHyp
  have hLG : L ≤ G := by
    rw [hLeq]
    exact quasithinGenFitting_le G
  have hGN : G ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    rw [hLeq]
    exact le_normalizer_quasithinGenFitting G
  have hW : ∀ v : V, v * v = 1 := fun v => by
    rw [← pow_two]
    exact hV v
  have hodd := Setup.Family.odd_card_center_of_irreducible hW (Bridge.TypeList.irr_of_isIrrSec hirr)
  have hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have h := hA.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at h
  obtain ⟨hD, h7⟩ := Bridge.asB42DichotomyNat_proved V hW L hq hirr
    (a23List_center_quotient hSG hLG hq) A (hA.1.trans hGN) hA.2.1 hA.2.2.1 hoff
  exact b42FamilyType_of_charTwoOrAlt (sqtkGroup_of_le hSG hLG) hq hodd hD h7

theorem asB42_of_families
    (hU3 : AsB42U3Even) (hSz : AsB42Sz) (hD4 : AsB42TrialityD4) (hF4 : AsB42ReeF4)
    (hL2 : AsB42L2Even) (hL32 : AsB42L32) (hL3 : AsB42L3Even) (hSp4 : AsB42Sp4Even)
    (hG2 : AsB42G2Even) (hU33 : AsB42U33) (hL42 : AsB42L42) (hL52 : AsB42L52)
    (hA5 : AsB42Alt5) (hA6 : AsB42Alt6) (hHA6 : AsB42HatA6) (hA7 : AsB42Alt7) : AsB42 := by
  intro V _ _ hV G L hHyp A hA
  rcases b42FamilyType_of_offender hV hHyp hA with h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h
  · exact (hU3 V hV G L hHyp h A hA).elim
  · exact (hSz V hV G L hHyp h A hA).elim
  · exact (hD4 V hV G L hHyp h A hA).elim
  · exact (hF4 V hV G L hHyp h A hA).elim
  · exact hL2 V hV G L hHyp h A hA
  · exact hL32 V hV G L hHyp h A hA
  · exact hL3 V hV G L hHyp h A hA
  · exact hSp4 V hV G L hHyp h A hA
  · exact hG2 V hV G L hHyp h A hA
  · exact hU33 V hV G L hHyp h A hA
  · exact hL42 V hV G L hHyp h A hA
  · exact hL52 V hV G L hHyp h A hA
  · exact hA5 V hV G L hHyp h A hA
  · exact hA6 V hV G L hHyp h A hA
  · exact hHA6 V hV G L hHyp h A hA
  · exact hA7 V hV G L hHyp h A hA

end CFSG.Quasithin
