module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofCenter
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofOrder
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofNine
public import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofHe
public import CFSG.RankThree.PartTwo.Sec4.Census.SporadicTwoCoverJ3
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Triality
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
import CFSG.LieType.Simplicity.Classical
import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

namespace Item21Early2Proof

section M22

open Equiv

@[expose] def m22α : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def m22β : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22α_mem : m22α ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem m22β_mem : m22β ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m22Word : List Char → Perm (Fin 22)
  | [] => 1
  | c :: w => (if c = 'a' then m22α else if c = 'b' then m22β else m22β⁻¹) * m22Word w

theorem m22Word_mem : ∀ w, m22Word w ∈ NativeSporadic.M22
  | [] => Subgroup.one_mem _
  | c :: w => by
    unfold m22Word
    refine Subgroup.mul_mem _ ?_ (m22Word_mem w)
    split_ifs
    · exact m22α_mem
    · exact m22β_mem
    · exact Subgroup.inv_mem _ m22β_mem

@[expose] def m22X₁ : Perm (Fin 22) :=
  swap 0 2 * swap 1 3 * swap 5 6 * swap 7 19 * swap 9 13 * swap 10 14 * swap 12 17 * swap 20 21

@[expose] def m22X₂ : Perm (Fin 22) :=
  swap 0 19 * swap 1 20 * swap 2 7 * swap 3 21 * swap 5 17 * swap 6 12 * swap 9 10 * swap 13 14

@[expose] def m22X₃ : Perm (Fin 22) :=
  swap 0 17 * swap 1 14 * swap 2 12 * swap 3 10 * swap 5 19 * swap 6 7 * swap 9 21 * swap 13 20

@[expose] def m22X₄ : Perm (Fin 22) :=
  swap 0 13 * swap 1 5 * swap 2 9 * swap 3 6 * swap 7 10 * swap 12 21 * swap 14 19 * swap 17 20

theorem m22X₁_eq : m22X₁ = m22β * m22β := by
  decide +kernel

theorem m22X₂_eq :
    m22X₂ = (m22Word "ababaBaBa".toList)⁻¹ * m22X₁ * m22Word "ababaBaBa".toList := by
  decide +kernel

theorem m22X₃_eq :
    m22X₃ = (m22Word "ababaBaBab".toList)⁻¹ * m22X₁ * m22Word "ababaBaBab".toList := by
  decide +kernel

theorem m22X₄_eq : m22X₄ =
    (m22Word "abaBBabaBabbaBaB".toList)⁻¹ * m22X₁ * m22Word "abaBBabaBabbaBaB".toList := by
  decide +kernel

@[expose] def m22Xs : Fin 4 → Perm (Fin 22) := ![m22X₁, m22X₂, m22X₃, m22X₄]

theorem m22_conj_mem (w : List Char) :
    (m22Word w)⁻¹ * m22X₁ * m22Word w ∈ NativeSporadic.M22 := by
  have h1 : m22X₁ ∈ NativeSporadic.M22 := by
    rw [m22X₁_eq]
    exact Subgroup.mul_mem _ m22β_mem m22β_mem
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (m22Word_mem w)) h1)
    (m22Word_mem w)

theorem m22Xs_mem : ∀ i, m22Xs i ∈ NativeSporadic.M22 := by
  intro i
  fin_cases i
  · change m22X₁ ∈ NativeSporadic.M22
    rw [m22X₁_eq]
    exact Subgroup.mul_mem _ m22β_mem m22β_mem
  · change m22X₂ ∈ NativeSporadic.M22
    rw [m22X₂_eq]
    exact m22_conj_mem _
  · change m22X₃ ∈ NativeSporadic.M22
    rw [m22X₃_eq]
    exact m22_conj_mem _
  · change m22X₄ ∈ NativeSporadic.M22
    rw [m22X₄_eq]
    exact m22_conj_mem _

theorem m22Xs_sq : ∀ i, m22Xs i * m22Xs i = 1 := by
  decide +kernel

theorem m22Xs_comm : ∀ i j, m22Xs i * m22Xs j = m22Xs j * m22Xs i := by
  decide +kernel

theorem m22Xs_ker : ∀ a : Fin 4 → Fin 2, a ≠ 0 →
    (List.ofFn fun i => m22Xs i ^ (a i : ℕ)).prod ≠ 1 := by
  decide +kernel

theorem four_le_pRank_M22 : 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup NativeSporadic.M22) := by
  let u : Fin 4 → NativeSporadic.M22 := fun i => ⟨m22Xs i, m22Xs_mem i⟩
  obtain ⟨E, hE, hc⟩ := elemAbelian_of_commuting_involutions u
    (fun i => Subtype.ext (m22Xs_sq i)) (fun i j => Subtype.ext (m22Xs_comm i j))
    (fun a ha h => m22Xs_ker a ha (by
      have h' := congrArg NativeSporadic.M22.subtype h
      rwa [map_list_prod, List.map_ofFn, map_one] at h'))
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc

end M22

theorem four_le_pRank_of_e16Datum {Y : Type*} [Group Y] [Finite Y] {a₁ a₂ a₃ a₄ n : Y}
    (h : Sec4.Census.SporadicTwoCover.E16Datum a₁ a₂ a₃ a₄ n) :
    4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Y) := by
  let u : Fin 4 → Y := ![a₁, a₂, a₃, a₄]
  have hsq : ∀ i, u i * u i = 1 := by
    intro i
    fin_cases i
    · exact (sq a₁).symm.trans h.sq
    · exact (sq a₂).symm.trans h.sq₂
    · exact (sq a₃).symm.trans h.sq₃
    · exact (sq a₄).symm.trans h.sq₄
  have hc : ∀ i j, Commute (u i) (u j) := by
    intro i j
    fin_cases i <;> fin_cases j
    all_goals first
      | exact Commute.refl _
      | exact h.comm₁₂ | exact h.comm₁₃ | exact h.comm₁₄
      | exact h.comm₂₃ | exact h.comm₂₄ | exact h.comm₃₄
      | exact h.comm₁₂.symm | exact h.comm₁₃.symm | exact h.comm₁₄.symm
      | exact h.comm₂₃.symm | exact h.comm₂₄.symm | exact h.comm₃₄.symm
  obtain ⟨E, hE, hcard⟩ := elemAbelian_of_commuting_involutions u hsq (fun i j => (hc i j).eq)
    (fun a ha hprod => h.prod_ne_one a ha (by
      rw [Sec4.Census.SporadicTwoCover.e16Prod]
      simpa [List.ofFn_succ, u, mul_assoc] using hprod))
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top hE hcard

theorem four_le_pRank_J3 :
    4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup NativeSporadic.J3) := by
  obtain ⟨a₁, a₂, a₃, a₄, n, h⟩ := Sec4.Census.SporadicTwoCover.j3_e16Datum
  exact four_le_pRank_of_e16Datum (Y := NativeSporadic.J3) h

theorem card_center_SL3_le (n : ℕ) : Nat.card (Subgroup.center (SL3 n)) ≤ 3 := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (0 : Fin 3)).toEquiv]
  simpa using card_rootsOfUnity (R := GaloisField 2 n) (Fintype.card (Fin 3))

theorem card_center_congr {X S : Type*} [Group X] [Group S] (e : X ≃* S) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center S) := by
  rw [← map_center_eq e, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]

variable {X : Type} [Group X] [Finite X]

theorem center_three_of_isBar211
    (h : IsBar211 X)
    (h3 : 3 ∣ Nat.card (Subgroup.center X)) : Nat.card (Subgroup.center X) = 3 ∧
      4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
  have hbot : Subgroup.center X ≠ ⊥ := by
    intro hZ
    rw [hZ, Subgroup.card_bot] at h3
    norm_num at h3
  unfold IsBar211 at h
  rcases h with h | h | h | h | h | h | h | h | h |
      ⟨n, hn, he, h | h | hG | hD | h | h⟩ | h | ⟨n, hn, hno, h⟩ | h | h |
      h | h | h
  ·
    obtain ⟨hc, ⟨e⟩⟩ := h
    refine ⟨hc, ?_⟩
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact four_le_pRank_M22
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.M22) e center_nativeM22_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.M23) e center_nativeM23_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.HS) e center_nativeHS_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.M24) e center_nativeM24_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.He) e center_nativeHe_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.J2) e center_nativeJ2_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.Ru) e center_nativeRu_eq_bot)
      hbot
  · obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.J4) e center_nativeJ4_eq_bot)
      hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSL_three_eq_bot hn he)) hbot
  ·
    obtain ⟨e⟩ := h
    have hle : Nat.card (Subgroup.center X) ≤ 3 := (card_center_congr e).trans_le
      (card_center_SL3_le n)
    have hpos : 0 < Nat.card (Subgroup.center X) := Nat.card_pos
    have hc : Nat.card (Subgroup.center X) = 3 := by
      obtain ⟨k, hk⟩ := h3
      rcases k with _ | _ | k
      · omega
      · omega
      · rw [hk] at hle
        nlinarith
    refine ⟨hc, ?_⟩
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    obtain ⟨f⟩ := nonempty_quot_SL3 n
    have : Finite (projSL 3 (GaloisField 2 n)) :=
      Finite.of_equiv _ ((quotCenterCongr e).trans f).toEquiv
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2n := Sec17.HeadProof.two_mul_le_pRank_projSL_three (K := GaloisField 2 n) (p := 2)
      (GaloisField.card 2 n (by omega))
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2n
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) ((quotCenterCongr e).trans f)]
    omega
  ·
    exact absurd (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hG).1 hbot
  ·
    exact absurd (CFSG.QuasithinUnique.Setup.X6.even_triality_model_two_extensions hD).1 hbot
  ·
    obtain ⟨e⟩ := h
    have hn2 : 2 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSp_two_eq_bot hn2)) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSU_four_eq_bot (by omega))) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e Sec4.Item434SmallTwoOther.U54.center_U54) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv e (center_projSU_four_eq_bot (by omega))) hbot
  ·
    obtain ⟨e⟩ := h
    exact absurd (center_eq_bot_of_mulEquiv (S := NativeSporadic.J3) e center_nativeJ3_eq_bot)
      hbot
  ·
    obtain ⟨hc, ⟨e⟩⟩ := h
    refine ⟨hc, ?_⟩
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
    exact four_le_pRank_J3
  ·
    have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 4 2 1 h).2
    refine absurd (center_eq_bot_of_isSimpleGroup_of_not_prime ?_) hbot
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
      show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 by decide]
    norm_num
  ·
    have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 5 2 1 h).2
    refine absurd (center_eq_bot_of_isSimpleGroup_of_not_prime ?_) hbot
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl,
      show CFSG.Open.ordA (5 - 1) (2 ^ 1) = 9999360 by decide]
    norm_num
  ·
    have : IsSimpleGroup X :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 3 2 1 h
    refine absurd (center_eq_bot_of_isSimpleGroup_of_not_prime ?_) hbot
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl,
      show CFSG.Open.ordBC 3 (2 ^ 1) = 2 ^ 9 * 2835 by decide]
    norm_num

end Item21Early2Proof

open Item21EarlyProof Item21Early2Proof

@[expose] def Item213CenterRankEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → CFSG.pCore 2 L = ⊥ →
      3 ∣ Nat.card (Subgroup.center (lBar L)) →
      Even (Nat.card (aschbacherSolvableCore 3 L)) → 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L)

theorem item213CenterRank_of
    (h211 : Item211) (hEven : Item213CenterRankEven) : Item213CenterRank := by
  intro G _ _ A E U c L hpair hO2 h3Z
  by_cases hθ : Even (Nat.card (aschbacherSolvableCore 3 L))
  · exact hEven G A E U c L hpair hO2 h3Z hθ
  · have hX : IsBar211 (lBar L) := isBar211_of_case211 (h211 G A E U c L hpair)
    obtain ⟨hZ3, h4⟩ := center_three_of_isBar211 hX h3Z
    set T := aschbacherSolvableCore 3 L with hT
    have hTodd : ¬ 2 ∣ Nat.card T := fun h => hθ (even_iff_two_dvd.mpr h)
    have hK : Nat.card (centerPre T) = Nat.card T * Nat.card (Subgroup.center (lBar L)) :=
      QuotientGroup.card_preimage_mk T _
    rw [hZ3] at hK
    have hK2 : ¬ 2 ∣ Nat.card (centerPre T) := by
      rw [hK]
      intro h
      rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
      · exact hTodd h
      · norm_num at h
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← CFSG.SectionRank.pRank_quotient_eq (centerPre T) hK2,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (centerPreEquiv T)]
    exact h4

theorem item213Center_of_rankEven
    (h211 : Item211) (hEven : Item213CenterRankEven) : Item213Center :=
  item213Center_of h211 ks213Order ks213Nine (item213CenterRank_of h211 hEven)

end CFSG.RankThree.PartTwo.Sec21
