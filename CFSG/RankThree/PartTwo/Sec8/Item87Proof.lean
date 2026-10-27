module

public import CFSG.RankThree.PartTwo.KFacts.K71Coprime
public import CFSG.RankThree.PartTwo.Sec8.Item812ProofFinal
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)


@[expose] def KF87Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (m : ℕ), 1 ≤ m →
    IsGammaType (L ⧸ aschbacherSolvableCore 3 L) m → x ^ 3 = 1 →
    (KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) →
      inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L) = ⊥ ∨
        IsQuasisimple (inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers x) L))

@[expose] def KF87Link : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → sec8I L a ≠ ⊥ → sec8J X a ≠ ⊥ →
      ¬ ⁅sec8I L a, sec8J X a⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))

@[expose] def Pair87Unitary : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 →
      sec8J X a ≠ ⊥ ∧ ∀ Y ∈ thetaComponentsAt 3 a, sec8J X a ≤ Y → sec8I L a ≤ Y

@[expose] def Pair87Trivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ¬ IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 → sec8I L a = ⊥ → sec8J X a = ⊥ →
      (thetaComponentsAt 3 a).Nonempty

namespace Item87Proof

variable {G : Type} [Group G] [Finite G]

theorem residual_centralizer_cases (hC : KF87Cent) {L : Subgroup G} {e x : G}
    (hL : L ∈ thetaComponentsAt 3 e) {m : ℕ} (hm : 1 ≤ m)
    (htype : IsGammaType (L ⧸ aschbacherSolvableCore 3 L) m) (hx3 : x ^ 3 = 1)
    (hk : KFacts.InducesStdKind L x .field ∨ KFacts.InducesStdKind L x .graphField) :
    inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) = ⊥ ∨
      inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) ∈
        thetaComponentsIn (Subgroup.centralizer {e} ⊓ Subgroup.centralizer {x}) := by
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := by
    rcases hk with h | h
    · exact h.mem_normalizer
    · exact h.mem_normalizer
  have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq hxN ⟨1, by simpa using hx3⟩
  have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ L :=
    (residual_le _).trans inf_le_left
  rcases hC G L x m hm htype hx3 hk with h0 | hq
  · left
    rw [← himg] at h0
    exact eq_bot_of_imageModTheta_eq_bot hKL (isPerfect_residual _) h0
  · right
    rw [← himg] at hq
    exact mem_thetaComponentsIn_residual hL (isQuasisimple_quot_of_imageModTheta hKL hq)

end Item87Proof

theorem item87_of (h48 : Sec4.Item4_8) (h84 : Pair84A) (hC : KF87Cent) (hLk : KF87Link)
    (hU : Pair87Unitary) (hT : Pair87Trivial) : Item87 := by
  intro G _ _ A c L a b X n h
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAel := h.mem_partTwoF.1
  have hAn : ∃ k : ℕ, 3 ≤ k ∧ Nat.card A = 3 ^ k := ⟨4, by norm_num, by rw [h.card_eq]; norm_num⟩
  obtain ⟨hbA, hb1, hn, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have ha3 : a ^ 3 = 1 := hAel.2 a h.a_mem
  have hX : X ∈ thetaComponentsAt 3 b := h.pairRel.2.2.1
  obtain ⟨d, m, hdm⟩ := h.mem_pairOmega.2.2.2.2.2
  obtain ⟨-, -, hm, -⟩ := Item87Proof.isGammaIndex_cases hdm
  have hJ := Item87Proof.residual_centralizer_cases hC hX hm
    (Item87Proof.isGammaType_of_isGammaIndex hdm) ha3 (h84 G A c L a b X n h)
  have hJdef : sec8J X a = inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) :=
    rfl
  have hJY : sec8J X a ∈ thetaComponentsIn
      (Subgroup.centralizer {b} ⊓ Subgroup.centralizer {a}) →
      ∃ Y ∈ thetaComponentsAt 3 a, sec8J X a ≤ Y := fun hJm =>
    Item87Proof.exists_mem_thetaComponentsAt_of_mem_inf h48 hG hAel hAn h.a_mem hbA h.a_ne_one
      hb1 (by rwa [inf_comm] at hJm)
  by_cases hUn : IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3
  · obtain ⟨hJne, hIY⟩ := hU G A c L a b X n h hUn
    obtain ⟨Y, hY, hJY'⟩ := hJY (hJ.resolve_left hJne)
    exact ⟨Y, hY, sup_le (hIY Y hY hJY') hJY'⟩
  · have hIdef : sec8I L a = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({a} : Set G)) :=
      by simp only [sec8I, hUn, ↓reduceIte]
    have hI := Item87Proof.residual_centralizer_cases hC h.mem_thetaComponentsAt hn
      (Item87Proof.isGammaType_of_isGammaIndex h.isGammaIndex) ha3 h.inducesStdKind
    have hIY : sec8I L a ∈ thetaComponentsIn
        (Subgroup.centralizer {c} ⊓ Subgroup.centralizer {a}) →
        ∃ Y ∈ thetaComponentsAt 3 a, sec8I L a ≤ Y := fun hIm =>
      Item87Proof.exists_mem_thetaComponentsAt_of_mem_inf h48 hG hAel hAn h.a_mem h.mem_A
        h.a_ne_one h.ne_one (by rwa [inf_comm] at hIm)
    rw [← hIdef] at hI
    rw [← hJdef] at hJ
    rcases hI with hI0 | hIm <;> rcases hJ with hJ0 | hJm
    · obtain ⟨Y, hY⟩ := hT G A c L a b X n h hUn hI0 hJ0
      exact ⟨Y, hY, by rw [hI0, hJ0, sup_bot_eq]; exact bot_le⟩
    · obtain ⟨Y, hY, hJY'⟩ := hJY hJm
      exact ⟨Y, hY, by rw [hI0, bot_sup_eq]; exact hJY'⟩
    · obtain ⟨Y, hY, hIY'⟩ := hIY hIm
      exact ⟨Y, hY, by rw [hJ0, sup_bot_eq]; exact hIY'⟩
    · obtain ⟨Y₁, hY₁, hIY₁⟩ := hIY hIm
      obtain ⟨Y₂, hY₂, hJY₂⟩ := hJY hJm
      have hne := hLk G A c L a b X n h hUn (Item87Proof.ne_bot_of_mem_thetaComponentsIn hIm)
        (Item87Proof.ne_bot_of_mem_thetaComponentsIn hJm)
      have heq := Item87Proof.eq_of_not_commutator_le hY₁ hY₂ hIY₁ hJY₂ hne
      exact ⟨Y₁, hY₁, sup_le hIY₁ (heq ▸ hJY₂)⟩

end CFSG.RankThree.PartTwo.Sec8
