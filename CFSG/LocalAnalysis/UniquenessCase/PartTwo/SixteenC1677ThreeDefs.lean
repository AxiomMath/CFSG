module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677Glue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Std
public import CFSG.LocalAnalysis.RankThreeTheoremC.StrongEmbeddingCase
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure S168e3Std (D : Data G) : Prop where
  hx : DataExt D
  h3 : CFSG.Open.evenRank G = 3
  hSg : UC6S846.SigmaStd D
  h61 : UC6.R6_1 D
  h127 : R127 D
  h1214 : F12.R1214 D
  h638 : UC6.R6_38 D
  h1110 : R1110Core D
  h63 : UC6.R6_3 D
  h126 : R126 D
  h1211 : R1211_1 D
  h111 : W3Thm111 G
  h6161ii : W3Lem616_1ii G
  h77 : F07.R77Eq D
  h1219 : ∀ V₀ V : Subgroup G, Hyp125 D V₀ V → D.sig = D.sig1
  h119 : F11.R119 D
  hSigThree : SigmaThree D

theorem S168e3Std.sig_eq_three_of_mem {D : Data G} (h : S168e3Std D) (h3 : 3 ∈ D.sig) :
    D.sig = {3} :=
  Set.eq_singleton_iff_unique_mem.2 ⟨h3, fun _ hp =>
    CFSG.LocalAnalysis.RankThreeTheoremC.eq_three_of_three_mem_sigmaA h.h3
      (h.hSigThree h.h3 h3) (h.hSigThree h.h3 hp)⟩

theorem S168e3Std.h1217 {D : Data G} (h : S168e3Std D) : R1217 D :=
  r1217_of_twelve_seventeen D h.hx h.h61 h.h127 h.h1214

theorem S168e3Std.pRank_eq_three {D : Data G} (h : S168e3Std D) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p D.M = 3 := by
  have hle : CFSG.Open.pRank p D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p (D.sig_prime p hp).1
      (D.sig_prime p hp).2 D.M D.maxLocal.1
  have h3 := h.hx.three_le p hp
  have h4 := h.h3
  omega

structure S168e3Ctx (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) : Prop where
  std : S168e3Std D
  setting : Setting16 D V₀ V L
  ne : barSub V₀ V hV L ≠ ⊥
  conc : Conc4_136 D V₀ V hV L

theorem S168e3Ctx.m_le_stabTil {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) : D.M ≤ stabTil V₀ V :=
  le_stabTil c.setting.hyp16.hyp125.pairFacts.le_normalizer
    c.setting.hyp16.hyp125.pairFacts.le_normalizer₀

@[expose] noncomputable def Final168F (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  Concl167F D V₀ V hV L ∨ Concl168 D V₀ V hV L

@[expose] noncomputable def Choice168F (D : Data G) (V₀ V : Subgroup G)
    (hV : IsElemAbelian 2 V) : Prop :=
  ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧ barSub V₀ V hV L' ≠ ⊥ ∧
    Conc4_136 D V₀ V hV L' ∧ Final168F D V₀ V hV L'

theorem Choice168F.of_final {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (h : Final168F D V₀ V hV L) : Choice168F D V₀ V hV :=
  ⟨L, c.setting, c.ne, c.conc, h⟩

theorem r16_8F_of_choice {D : Data G}
    (h : ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Setting16 D V₀ V L →
      barSub V₀ V hV L ≠ ⊥ → Conc4_136 D V₀ V hV L → Choice168F D V₀ V hV) : R16_8F D := by
  intro V₀ V L hV hS hne hc hall
  obtain ⟨L', h1, h2, h3, h4 | h4⟩ := h V₀ V L hV hS hne hc
  · exact absurd h4 (hall L' h1 h2 h3)
  · exact ⟨L', h1, h2, h3, h4⟩

@[expose] noncomputable def Case163_8F (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  (∃ (X : Type) (_ : Group X), IsL3 X 1 ∧
      Nonempty (↥(fstarBar D.M V₀ V hV) ≃* (X × X))) ∧
    NatTensor (fstarBar D.M V₀ V hV) (wTil V₀ V hV L) ⊥ 3 1 ∧ s15 D.M V₀ V hV L = 1 ∧
    D.sig = {7}

@[expose] noncomputable def Concl163F (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  Concl162 D V₀ V hV L ∨ Case163_1 D V₀ V hV L ∨ Case163_2 D V₀ V hV L ∨ Case163_3 D V₀ V hV L ∨
    Case163_4 D V₀ V hV L ∨ Case163_5 D V₀ V hV L ∨ Case163_6 D V₀ V hV L ∨
    Case163_7 D V₀ V hV L ∨ Case163_8F D V₀ V hV L ∨ Case163_9 D V₀ V hV L ∨
    Case163_10 V₀ V hV L ∨ Case163_11 V₀ V hV L ∨ Case163_12 D V₀ V hV L

@[expose] def R16_3FE (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V),
    Setting16 D V₀ V L → barSub V₀ V hV L ≠ ⊥ →
    Conc4_136 D V₀ V hV L →
    ∃ L' : Subgroup G, Setting16 D V₀ V L' ∧
      barSub V₀ V hV L' ≠ ⊥ ∧ Conc4_136 D V₀ V hV L' ∧
      Concl163F D V₀ V hV L'

theorem case163_8F_of_case163_8 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Case163_8 D V₀ V hV L) : Case163_8F D V₀ V hV L := by
  have hwT := wTil_eq_top_of_case163_2 hconc h.2.2.1
  have h7 : Case167_7 D V₀ V hV L := by
    refine ⟨h.1, ?_, h.2.2.2⟩
    have := h.2.1
    rw [hwT] at this
    exact this
  have h7F := case167_7F_of_case167_7 D hS.hyp151 hne h7
  refine ⟨h7F.1, ?_, h.2.2.1, h.2.2.2⟩
  rw [hwT]
  exact h7F.2.1

theorem concl163F_of_concl163 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Setting16 D V₀ V L) (hne : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (h : Concl163 D V₀ V hV L) : Concl163F D V₀ V hV L := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (case163_8F_of_case163_8 hS hne hconc h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h)))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr h)))))))))))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
