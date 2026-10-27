module

public import CFSG.Quasithin.EmptyFaithful.SBd8Flag
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Blocks.BrauerInduction
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeOrderSylowColumn
public import CFSG.CharacterTheory.TwoRankLowerBound.BrauerCharacterCriterion
public import CFSG.CharacterTheory.TwoRankLowerBound.NormalComplementCharacterSpace
public import CFSG.ClassicalGroups
public import CFSG.Fischer.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B69Core
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F1Weak
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Sixteen
public import CFSG.Quasithin.Background.FFC7G
public import CFSG.Quasithin.Background.FFC8A
public import CFSG.Quasithin.Background.InternalSecB56B
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Quasithin.EmptyFaithful.SBd8Trio
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M22
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import CFSG.Walter.J1
public import Certificates.Kernel.SporSch.J4S.NoCP

public section

namespace CFSG.Quasithin

namespace SBd8

namespace L5

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.SBd8.Flag

section Path

@[expose] def adj (j k : ℕ) : Prop :=
  (j = 1 ∧ k = 3) ∨ (j = 3 ∧ k = 1) ∨ (j = 2 ∧ k = 3) ∨ (j = 3 ∧ k = 2) ∨ (j = 2 ∧ k = 4) ∨
    (j = 4 ∧ k = 2)

instance (j k : ℕ) : Decidable (adj j k) := by unfold adj; infer_instance

theorem path_aut_aux : ∀ a ∈ Finset.Icc 1 4, ∀ b ∈ Finset.Icc 1 4, ∀ c ∈ Finset.Icc 1 4,
    ∀ d ∈ Finset.Icc 1 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → adj a c → adj c b →
    adj b d → ¬ adj a b → ¬ adj a d → ¬ adj c d →
    ((b = 2 ∧ c = 3) ∨ (b = 3 ∧ c = 2)) ∧ ((a = 1 ∧ d = 4) ∨ (a = 4 ∧ d = 1)) := by
  decide

theorem path_aut {s : ℕ → ℕ} (hs : ∀ j, 1 ≤ j → j ≤ 4 → 1 ≤ s j ∧ s j ≤ 4)
    (hinj : ∀ j k, 1 ≤ j → j ≤ 4 → 1 ≤ k → k ≤ 4 → s j = s k → j = k)
    (hadj : ∀ j k, 1 ≤ j → j ≤ 4 → 1 ≤ k → k ≤ 4 → (adj (s j) (s k) ↔ adj j k)) :
    ((s 2 = 2 ∧ s 3 = 3) ∨ (s 2 = 3 ∧ s 3 = 2)) ∧ ((s 1 = 1 ∧ s 4 = 4) ∨ (s 1 = 4 ∧ s 4 = 1)) := by
  have mem : ∀ j, 1 ≤ j → j ≤ 4 → s j ∈ Finset.Icc 1 4 := fun j hj hj4 =>
    Finset.mem_Icc.2 (hs j hj hj4)
  have ne : ∀ j k, 1 ≤ j → j ≤ 4 → 1 ≤ k → k ≤ 4 → j ≠ k → s j ≠ s k := fun j k hj hj4 hk hk4 hjk h =>
    hjk (hinj j k hj hj4 hk hk4 h)
  have pos : ∀ j k, 1 ≤ j → j ≤ 4 → 1 ≤ k → k ≤ 4 → adj j k → adj (s j) (s k) :=
    fun j k hj hj4 hk hk4 h => (hadj j k hj hj4 hk hk4).2 h
  have neg : ∀ j k, 1 ≤ j → j ≤ 4 → 1 ≤ k → k ≤ 4 → ¬ adj j k → ¬ adj (s j) (s k) :=
    fun j k hj hj4 hk hk4 h h' => h ((hadj j k hj hj4 hk hk4).1 h')
  exact path_aut_aux (s 1) (mem 1 le_rfl (by norm_num)) (s 2) (mem 2 (by norm_num) (by norm_num))
    (s 3) (mem 3 (by norm_num) (by norm_num)) (s 4) (mem 4 (by norm_num) le_rfl)
    (ne 1 2 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (ne 1 3 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (ne 1 4 le_rfl (by norm_num) (by norm_num) le_rfl (by norm_num))
    (ne 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (ne 2 4 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num))
    (ne 3 4 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num))
    (pos 1 3 le_rfl (by norm_num) (by norm_num) (by norm_num) (by decide))
    (pos 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide))
    (pos 2 4 (by norm_num) (by norm_num) (by norm_num) le_rfl (by decide))
    (neg 1 2 le_rfl (by norm_num) (by norm_num) (by norm_num) (by decide))
    (neg 1 4 le_rfl (by norm_num) (by norm_num) le_rfl (by decide))
    (neg 3 4 (by norm_num) (by norm_num) (by norm_num) le_rfl (by decide))

end Path

section Solvable

local macro "hno_tac" : tactic =>
  `(tactic| (intro c hc; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega))

theorem solvable_one_three : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({1, 3} : Set ℕ)) :=
  isSolvable_flagStabilizer_of_small (by norm_num) fun a m h ha hb hno => by
    have h1 := hno 1 (by simp)
    have h3 := hno 3 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega

theorem solvable_two_three : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({2, 3} : Set ℕ)) :=
  isSolvable_flagStabilizer_of_small (by norm_num) fun a m h ha hb hno => by
    have h1 := hno 2 (by simp)
    have h3 := hno 3 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega

theorem solvable_two_four : Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({2, 4} : Set ℕ)) :=
  isSolvable_flagStabilizer_of_small (by norm_num) fun a m h ha hb hno => by
    have h1 := hno 2 (by simp)
    have h3 := hno 4 (by simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    omega

theorem not_solvable_one_one : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({1, 1} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 1) (m := 4) (by norm_num) (by norm_num)
    (Or.inr (by simp)) (Or.inl (by norm_num)) (by hno_tac)

theorem not_solvable_one_two : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({1, 2} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 2) (m := 3) (by norm_num) (by norm_num)
    (Or.inr (by simp)) (Or.inl (by norm_num)) (by hno_tac)

theorem not_solvable_one_four : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({1, 4} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 1) (m := 3) (by norm_num) (by norm_num)
    (Or.inr (by simp)) (Or.inr (by simp)) (by hno_tac)

theorem not_solvable_two_two : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({2, 2} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 2) (m := 3) (by norm_num) (by norm_num)
    (Or.inr (by simp)) (Or.inl (by norm_num)) (by hno_tac)

theorem not_solvable_three_three : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({3, 3} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 0) (m := 3) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inr (by simp)) (by hno_tac)

theorem not_solvable_three_four : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({3, 4} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 0) (m := 3) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inr (by simp)) (by hno_tac)

theorem not_solvable_four_four : ¬ Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({4, 4} : Set ℕ)) :=
  not_isSolvable_flagStabilizer_of_big (a := 0) (m := 4) (by norm_num) (by norm_num)
    (Or.inl rfl) (Or.inr (by simp)) (by hno_tac)

theorem isSolvable_pair_iff {j k : ℕ} (hj : 1 ≤ j) (hj4 : j ≤ 4) (hk : 1 ≤ k) (hk4 : k ≤ 4) :
    Group.IsSolvable ↥(flagStabilizer 5 (ZMod 2) ({j, k} : Set ℕ)) ↔ adj j k := by
  interval_cases j <;> interval_cases k
  · exact iff_of_false not_solvable_one_one (by decide)
  · exact iff_of_false not_solvable_one_two (by decide)
  · exact iff_of_true solvable_one_three (by decide)
  · exact iff_of_false not_solvable_one_four (by decide)
  · rw [Set.pair_comm]; exact iff_of_false not_solvable_one_two (by decide)
  · exact iff_of_false not_solvable_two_two (by decide)
  · exact iff_of_true solvable_two_three (by decide)
  · exact iff_of_true solvable_two_four (by decide)
  · rw [Set.pair_comm]; exact iff_of_true solvable_one_three (by decide)
  · rw [Set.pair_comm]; exact iff_of_true solvable_two_three (by decide)
  · exact iff_of_false not_solvable_three_three (by decide)
  · exact iff_of_false not_solvable_three_four (by decide)
  · rw [Set.pair_comm]; exact iff_of_false not_solvable_one_four (by decide)
  · rw [Set.pair_comm]; exact iff_of_true solvable_two_four (by decide)
  · rw [Set.pair_comm]; exact iff_of_false not_solvable_three_four (by decide)
  · exact iff_of_false not_solvable_four_four (by decide)

end Solvable

section Action

open CFSG.LocalAnalysis.ComponentInitial

theorem sigma_pairs {α : MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hα : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2)) :
    ∃ σ : ℕ → ℕ,
      (∀ j, 1 ≤ j → j < 5 → 1 ≤ σ j ∧ σ j < 5 ∧
        (flagStabilizer 5 (ZMod 2) {j}).map α.toMonoidHom = flagStabilizer 5 (ZMod 2) {σ j}) ∧
      ((σ 2 = 2 ∧ σ 3 = 3) ∨ (σ 2 = 3 ∧ σ 3 = 2)) ∧ ((σ 1 = 1 ∧ σ 4 = 4) ∨ (σ 1 = 4 ∧ σ 4 = 1)) := by
  obtain ⟨σ, hσ⟩ := exists_sigma (Nat.card_zmod 2) hα
  refine ⟨σ, hσ, path_aut (s := σ) (fun j hj hj4 => ?_) (fun j k hj hj4 hk hk4 h => ?_)
    (fun j k hj hj4 hk hk4 => ?_)⟩
  · have := hσ j hj (by omega)
    omega
  · exact sigma_injOn hσ hj (by omega) hk (by omega) h
  · have h1 := hσ j hj (by omega)
    have h2 := hσ k hk (by omega)
    rw [← isSolvable_pair_iff (by omega) (by omega) (by omega) (by omega),
      ← isSolvable_pair_iff hj hj4 hk hk4, ← map_flagStabilizer_pair hσ hj (by omega) hk (by omega)]
    exact isSolvable_map_iff _ α

theorem map_pair_two_three {α : MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hα : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2)) :
    (flagStabilizer 5 (ZMod 2) ({2, 3} : Set ℕ)).map α.toMonoidHom =
      flagStabilizer 5 (ZMod 2) ({2, 3} : Set ℕ) := by
  obtain ⟨σ, hσ, h23, -⟩ := sigma_pairs hα
  rw [map_flagStabilizer_pair hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rcases h23 with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · rw [h2, h3]
  · rw [h2, h3, Set.pair_comm]

theorem map_pair_one_four {α : MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (hα : (unitriangular 5 (ZMod 2)).map α.toMonoidHom = unitriangular 5 (ZMod 2)) :
    (flagStabilizer 5 (ZMod 2) ({1, 4} : Set ℕ)).map α.toMonoidHom =
      flagStabilizer 5 (ZMod 2) ({1, 4} : Set ℕ) := by
  obtain ⟨σ, hσ, -, h14⟩ := sigma_pairs hα
  rw [map_flagStabilizer_pair hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rcases h14 with ⟨h1, h4⟩ | ⟨h1, h4⟩
  · rw [h1, h4]
  · rw [h1, h4, Set.pair_comm]

end Action

end L5

end SBd8

end CFSG.Quasithin
