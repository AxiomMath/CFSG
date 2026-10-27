module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DCin
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62DLine
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P51bK
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Six
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sigma3Main
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PSing
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Arc
public import CFSG.LieType.SteinbergBRTwoRankBound
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathA3Sub3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathShortMap
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.Quasithin.Background.C1Basic
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PEdge
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6LemD

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem lemmaD_four (F : FanTree Γ G) (h40 : Fan40 F) (h36 : Fan36 F) {l d : V}
    (hl5 : valence Γ l = 5) (hdist : Γ.dist l d = 4) {w : G} (hl : w ∈ Cinv G l)
    (hd : w ∈ Cinv G d) : False := by
  obtain ⟨P, hP0, hP4⟩ := IsTree.exists_arc F.isTree 4 l d hdist
  obtain ⟨ℓ, hℓ⟩ := exists_line_of_arc F P (by norm_num)
  have e0 : ℓ.vert 0 = l := by simpa [hP0] using hℓ 0 (by norm_num)
  have e4 : ℓ.vert ((4 : ℕ) : ℤ) = d := by rw [hℓ 4 le_rfl, hP4]
  have hs : ¬ LineSingLe Γ G ℓ 3 := by
    rintro ⟨k, a', hk1, hk3, h | h⟩
    · exact h40 k hk1 (by omega) ⟨ℓ.arc a' k, h⟩
    · exact h40 k hk1 (by omega) (hasRightSingular_of_left hk1 _ h)
  have hexc : ¬ ((4 : ℕ) = 4 ∧ LineSingLe Γ G ℓ 4 ∧ valence Γ (ℓ.vert 0) = 3 ∧
      valence Γ (ℓ.vert (0 + ((4 : ℕ) : ℤ))) = 3) := fun h => by
    have := h.2.2.1
    rw [e0] at this
    omega
  have hloc := fan51b_loc F h40 h36 ℓ 0 4 (by norm_num) hs hexc
  rw [zero_add, e4, e0] at hloc
  set L : Subgroup G := Subgroup.closure ((nbrStab Γ G l : Set G) ∪ nbrStab Γ G d) with hL
  have hKl := cinv_mem_nbrStab F hl
  obtain ⟨a, ha⟩ := F.exists_adj l
  have hcomm : ∀ g ∈ L, g * w = w * g := by
    intro g hg
    have : L ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [hL, Subgroup.closure_le]
      rintro g (hg | hg)
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hl.2.2.2 g (F.nbrStab_le_stabilizer l hg)).symm
      · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact (hd.2.2.2 g (F.nbrStab_le_stabilizer d hg)).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (this hg)
  have hU : ∀ u ∈ Subgroup.zpowers w, u • l = l ∧ u • a = a := by
    have hle : Subgroup.zpowers w ≤ MulAction.stabilizer G l ⊓ MulAction.stabilizer G a :=
      Subgroup.zpowers_le.2 (F.nbrStab_le_edge l ha hKl)
    intro u hu
    exact ⟨MulAction.mem_stabilizer_iff.1 (hle hu).1, MulAction.mem_stabilizer_iff.1 (hle hu).2⟩
  have hbot := F.eq_bot_of_locTrans L ha hU (le_normalizer_zpowers hcomm) (hloc l) (hloc a)
  exact hl.1 (Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_zpowers w))

end P62

section Main

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem lemmaD (F : FanTree Γ G) : LemmaD F := by
  intro h40 l d hld hl5 _ hdist w hl hd
  rcases hdist with h2 | h4
  · exact P62.lemmaD_two F hld h2 hl hd
  · exact P62.lemmaD_four F h40 (fan_3_6 F.localFacts (fan_3_2_main F sigma3Aut)) hl5 h4 hl hd

end Main

end CFSG.Quasithin.Fan86
