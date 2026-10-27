module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3S
import CFSG.RankThree.PartTwo.Sec17.Item17Res3ProofMeet
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec17.Item17Res7ProofL3Quot

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16

@[expose] noncomputable def Item1717OneJ2Clause : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G) (h : Sec17Y1 G A c L Y₀ Y₁ S p P),
    omegaA A = {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    letI := kerAO2_normal h.le_normalizer_y0
    (∃ T : Sylow 2 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)),
        Nonempty (↥(imgY0 A Y₀ (S ⊓ Y₀)) ≃*
          ↥(T : Subgroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))))) ∧
      ∃ (a : G) (ha : a ∈ A) (b : G) (hb : b ∈ A) (d : G),
        Subgroup.closure {a, b} = A ⊓ L ∧ d ∈ A ∧ d ≠ 1 ∧ IsThreeCentralIn L d ∧
        imgY0 A Y₀ (S ⊓ Y₀) =
          oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) ⊔ oTwoCY0 A Y₀ (alphaY0 A Y₀ b hb) ⊔
            imgY0 A Y₀ (S ⊓ Y₀ ⊓ Subgroup.centralizer {d})

namespace Proof17Res7

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G} {c : G}

theorem le_sup_cQuot_of_j2
    (hJ : KS1717J2Inner)
    {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (h142 : Concl142 A (lB A))
    (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hAnorm : ∀ V : Subgroup G, V ≤ L → A ⊓ L ≤ Subgroup.normalizer (V : Set G) →
      A ≤ Subgroup.normalizer (V : Set G))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G))
    (hB9 : Nat.card (Proof17Res6.kimg Y₀ (A ⊓ L)) = 9)
    (hJ2 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := by
  have hs := h.toSec17Std
  obtain ⟨⟨f⟩, -⟩ := hs.j2_local hJ2
  obtain ⟨e₀⟩ := Proof17Res3.nonempty_quotient_pCore_two_equiv hs.le_y0 hY
  set e := e₀.trans f with he
  obtain ⟨-, -, -, hJ2z⟩ := Sec13.sporadicModels131
  exact Proof17Res6.le_sup_cQuot_of_inner h h142 (Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY)
    hAnorm hSM (Proof17Res6.center_eq_bot_of_equiv' e hJ2z)
    (Proof17Res6.actQ_le_range_of h hSM fun Q hQ3 hQN => hJ _ ⟨e⟩ _ hB9 Q hQ3 hQN)

end Proof17Res7

theorem item1717OneL3J2_of
    (hA : KS17L3AutCent) (hT : KS17L3TwoCent) (hJ : KS1717J2Inner) (hJC : Item1717OneJ2Clause)
    (h1715 : Item1715) (h135 : Item135) (h142 : Concl142S14) (h166 : Item166S17)
    (hbot : Item145BotS17) (h168 : Item168S17) (h9 : CardInfNineS17) (h138 : Item138N) :
    Item1717OneL3J2 := by
  intro G _ _ A c L Y₀ Y₁ S p P h hΩ htypes
  have hs := h.toSec17Std
  have := kerAO2_normal h.le_normalizer_y0
  have hSG := Proof1712.mem_qStar_top h (h166 G A c L Y₀ hs) (hbot G A c L Y₀ hs)
    (h168 G A c L Y₀ hs)
  have hSM := hs.qStar_le S hSG
  have h142' := h142 G A c L hs.toSec14Std
  have h9' := h9 G A c L Y₀ hs
  have hAnorm := Proof17Res6.le_normalizer_of_inf hs h9'
  have hB9 := Proof17Res6.card_kimg_inf hs h9'
  rcases htypes with hL3 | hJ2
  · obtain ⟨hY, q, hq, hq3, h91, h98, hiso⟩ :=
      Proof17Res7.exists_l3Pic h1715 h135 h138 h hΩ hL3
    obtain ⟨h1, a, ha, haL, ha1, heq⟩ := Proof17Res7.item1717One_of_l3 hA hT h h142'
      (Proof17Res6.exists_mem_L_mk_eq hs.le_y0 hY) hAnorm hSM hB9 hq3 hiso h91 h98
    obtain ⟨q', hq', -, hiso'⟩ := hL3
    exact ⟨h1, Or.inl ⟨Or.inl ⟨q', 1, hq', le_rfl, hiso'⟩, a, ha, haL, ha1, heq⟩⟩
  · have hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
      rcases h1715 G A c L Y₀ hs with ⟨-, hY, -, -⟩ | ⟨-, -, -, -, hT⟩
      · exact hY
      · exfalso
        have h3 := hT.1
        rw [hΩ, Set.ncard_singleton] at h3
        omega
    refine ⟨le_antisymm (Proof17Res7.le_sup_cQuot_of_j2 hJ h h142' hY hAnorm hSM hB9 hJ2)
      (sup_le inf_le_left inf_le_left), Or.inr (Or.inr ⟨hJ2, hJC G A c L Y₀ Y₁ S p P h hΩ hJ2⟩)⟩

end CFSG.RankThree.PartTwo.Sec17
