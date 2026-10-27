module

public import CFSG.RankThree.PartTwo.Sec13.Item135
public import CFSG.RankThree.PartTwo.Sec13.Item131a
public import CFSG.RankThree.PartTwo.Sec13.Item135SimpleReduce
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofTypes
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCore44
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofCenter
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Mathieu

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item135ReduceCentral : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → HypT A → c ∈ L → ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L) →
      CFSG.pCore 2 L = ⊥ ∧ CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 ∧
      IsQuasisimple (L ⧸ CFSG.oddCore L) ∧
      ((∃ q : ℕ, q % 2 = 1 ∧ Sec4.IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) q) ∨
        Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)))

namespace ResProof

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem sectionFourHyp_of_sec13Data (hD : Sec13Data G A c L) : SectionFourHyp L := by
  have hst := hD.toPartTwoStanding
  have hCtop : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
    intro hCt
    have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
      have hg : g ∈ Subgroup.centralizer ({c} : Set G) := hCt ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    rcases hst.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hcZ
      exact hD.ne_one hcZ
    · obtain ⟨a, b, hab⟩ := hst.nonabelian
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  have hLtop : L ≠ ⊤ := fun hLt => hCtop (top_le_iff.mp (hLt ▸ hD.le_centralizer))
  exact hst.toTheoremFourHyp.sectionFourHyp hLtop

omit [Finite G] in
theorem not_dvd_of_lt_card {n : ℕ} (hn : 5616 < n) :
    ∀ m : ℕ, m = 60 ∨ m = 120 ∨ m = 360 ∨ m = 5616 → ¬ n ∣ m := by
  intro m hm hdvd
  have hm0 : 0 < m := by rcases hm with rfl | rfl | rfl | rfl <;> norm_num
  have := Nat.le_of_dvd hm0 hdvd
  rcases hm with rfl | rfl | rfl | rfl <;> omega

theorem reduce_of_not_mem (h131a : Item131a) (h44 : Sec4.Item4_4)
    (hK : KS135TwoRank) (hspor : SporadicModels131) (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (hnq : ¬ IsQuasisimple (L ⧸ CFSG.pCore 2 L)) :
    CFSG.pCore 2 L = ⊥ ∧ CFSG.Open.pRank 2 (⊤ : Subgroup L) ≤ 2 ∧
      IsQuasisimple (L ⧸ CFSG.oddCore L) ∧
      ((∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
          Sec4.IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7))) := by
  have hLc := hD.mem_thetaComponentsAt
  have hperf : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hbar : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  obtain ⟨htype, hZbar, D, hDL, hDe, hD9⟩ := types_of_not_mem h131a hspor hD hcL
  obtain ⟨E, hE3, hE9⟩ := exists_exponent_three_card_nine_of_le hDL hDe hD9
  have hsimp : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) :=
    isSimpleGroup_of_isQuasisimple_center_eq_bot hbar hZbar
  have hL4 := sectionFourHyp_of_sec13Data hD
  have hcard : ∀ m : ℕ, m = 60 ∨ m = 120 ∨ m = 360 ∨ m = 5616 →
      ¬ Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ m := by
    rcases htype with ⟨p, e, hp, he, hL⟩ | hA7 | hM22 | hM12 | hJ2
    · obtain ⟨-, -, hbig, -⟩ := typeFacts135_isoLThreePi he hbar hL
      exact not_dvd_of_lt_card (by omega)
    · obtain ⟨φ⟩ := hA7
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
      intro m hm
      rcases hm with rfl | rfl | rfl | rfl <;> decide
    · obtain ⟨φ⟩ := hM22
      rw [Nat.card_congr φ.toEquiv, Sec4.Census.card_m22_eq]
      exact not_dvd_of_lt_card (by norm_num)
    · obtain ⟨φ⟩ := hM12
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
      exact not_dvd_of_lt_card (by norm_num)
    · obtain ⟨φ⟩ := hJ2
      rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2]
      exact not_dvd_of_lt_card (by norm_num)
  obtain ⟨hO2, hm, hO⟩ := reduce44_core h44 hL4 hE3 hE9 hcard hnq
  refine ⟨hO2, hm, hO, ?_⟩
  have hbad := fun htype' => three_le_pRank_of_types (X := L) hK hZbar hO htype'
  rcases htype with ⟨p, e, hp, he, hL⟩ | hA7 | hM22 | hM12 | hJ2
  · by_cases hp2 : p = 2
    · subst hp2
      have := hbad (Or.inr (Or.inr (Or.inr ⟨e, he, hL⟩)))
      omega
    · exact Or.inl ⟨p, e, hp, hp2, he, hL⟩
  · exact Or.inr hA7
  · have := hbad (Or.inr (Or.inr (Or.inl hM22)))
    omega
  · have := hbad (Or.inl hM12)
    omega
  · have := hbad (Or.inr (Or.inl hJ2))
    omega

end ResProof

open ResProof

theorem item135Reduce_of (h131a : Item131a) (h44 : Sec4.Item4_4)
    (hK : KS135TwoRank) (hspor : SporadicModels131) (hC : Item135ReduceCentral) :
    Item135Reduce := by
  intro G _ _ A c L hD hST hnq
  by_cases hcL : c ∈ L
  · have hT : HypT A := by
      rcases hST with hS | hT
      · exact absurd hcL (not_mem_of_hypS hD hS)
      · exact hT
    obtain ⟨hO2, hm, hO, hSL | hAZ⟩ := hC G A c L hD hT hcL hnq
    · exact ⟨hO2, hm, hO, Or.inr (Or.inl hSL)⟩
    · exact ⟨hO2, hm, hO, Or.inr (Or.inr (Or.inr hAZ))⟩
  · obtain ⟨hO2, hm, hO, hL | hA7⟩ := reduce_of_not_mem h131a h44 hK hspor hD hcL hnq
    · exact ⟨hO2, hm, hO, Or.inl hL⟩
    · exact ⟨hO2, hm, hO, Or.inr (Or.inr (Or.inl hA7))⟩

end CFSG.RankThree.PartTwo.Sec13
