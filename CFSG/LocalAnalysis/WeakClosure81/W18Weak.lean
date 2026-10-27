module

public import CFSG.Quasithin.Background.E3Weak
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem MBarGT.mono {M V₀ V : Subgroup G} {m n : ℕ} (h : MBarGT M V₀ V n) (hmn : m ≤ n) :
    MBarGT M V₀ V m := by
  unfold MBarGT at h ⊢
  have hp : 2 ^ (m + 1) ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ⟨fun x hx h1 h2 => le_trans (Nat.mul_le_mul_right _ hp) (h.1 x hx h1 h2),
    fun h3 => le_trans (Nat.mul_le_mul_right _ hp) (h.2 h3)⟩

theorem MBarGT.two_pow_le_card {M V₀ V : Subgroup G} {n : ℕ} (h : MBarGT M V₀ V n) :
    2 ^ (n + 1) ≤ Nat.card V := by
  classical
  by_cases hex : ∃ m ∈ M, ¬ CentralizesMod V₀ V m ∧ CentralizesMod V₀ V (m * m)
  · obtain ⟨m, hm, h1, h2⟩ := hex
    have h3 := h.1 m hm h1 h2
    have hpos : 0 < Nat.card (centMod V₀ V m) := by
      haveI : Nonempty (centMod V₀ V m) := ⟨⟨1, V.one_mem, by simp⟩⟩
      exact Nat.card_pos
    calc 2 ^ (n + 1) ≤ 2 ^ (n + 1) * Nat.card (centMod V₀ V m) :=
          Nat.le_mul_of_pos_right _ hpos
      _ ≤ Nat.card V := h3
  · have hprem : ∀ m ∈ M, CentralizesMod V₀ V (m * m) → CentralizesMod V₀ V m := by
      intro m hm h2
      by_contra h1
      exact hex ⟨m, hm, h1, h2⟩
    have h3 := h.2 hprem
    calc 2 ^ (n + 1) ≤ 2 ^ (n + 1) * Nat.card V₀ := Nat.le_mul_of_pos_right _ Nat.card_pos
      _ ≤ Nat.card V := h3

private theorem exists_relIndex_two_of_mem {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (h4 : 4 ≤ Nat.card E) {x : G} (hx : x ∈ E) :
    ∃ B : Subgroup G, B ≤ E ∧ B.relIndex E = 2 ∧ x ∈ B := by
  have hP : IsPGroup 2 E := hE.isPGroup
  have hx2 : x ^ 2 = 1 := hE.2 x hx
  have hcard : Nat.card (Subgroup.zpowers x) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx2)
  have hlt : Subgroup.zpowers x < E := by
    refine lt_of_le_of_ne ?_ ?_
    · rwa [Subgroup.zpowers_le]
    · intro hEq
      rw [hEq] at hcard
      omega
  obtain ⟨B, hxB, hBE, hBm⟩ := s15_Glue_exists_hyperplane hP hlt
  exact ⟨B, hBE, by rw [E3.relIndex_eq_two_pow hP B, hBm, pow_one],
    hxB (Subgroup.mem_zpowers x)⟩

private theorem conjSubgroup_le_wClos_one {V T : Subgroup G} (hV : IsElemAbelian 2 V)
    (h4 : 4 ≤ Nat.card V) {g : G} (hg : conjSubgroup V g ≤ T) :
    conjSubgroup V g ≤ E3.wClos V 1 T := by
  intro x hx
  have hEel : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  have hEcard : 4 ≤ Nat.card (conjSubgroup V g) := by
    rw [E3.card_conjSubgroup]
    exact h4
  obtain ⟨B, hBE, hBrel, hxB⟩ := exists_relIndex_two_of_mem hEel hEcard hx
  have hmem : B ∈ E3.gammaSet V 1 T := by
    refine ⟨hBE.trans hg, g, hBE, ?_⟩
    show E3.mQuot (conjSubgroup V g) B = 1
    unfold E3.mQuot
    rw [hBrel]
    exact padicValNat_self
  exact E3.le_wClos hmem hxB

theorem normalizer_wClos_one_le {V T : Subgroup G} (hV : IsElemAbelian 2 V) (h4 : 4 ≤ Nat.card V) :
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (E3.wClos V 0 T : Set G) := by
  intro n hn
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hn ⊢
  have hconj_one_le : ∀ A ∈ E3.gammaSet V 0 T, A ≤ conjSubgroup (E3.wClos V 0 T) n⁻¹ := by
    intro A hA
    have hAle : A ≤ E3.wClos V 1 T := by
      obtain ⟨g, hAg, hm⟩ := hA.2
      have hP : IsPGroup 2 (conjSubgroup V g) :=
        (E3.isElemAbelian_conjSubgroup hV g).isPGroup
      have hAeq : A = conjSubgroup V g := (E3.mQuot_eq_zero_iff hP hAg).1 hm
      rw [hAeq]
      exact conjSubgroup_le_wClos_one hV h4 (hAeq ▸ hA.1)
    have hAnT : conjSubgroup A n ≤ T := by
      calc conjSubgroup A n ≤ conjSubgroup (E3.wClos V 1 T) n :=
            E3.conjSubgroup_mono_left n hAle
        _ = E3.wClos V 1 T := hn
        _ ≤ T := E3.wClos_le 1 T
    exact (E3.conjSubgroup_le_iff_le_inv n).1
      (E3.le_wClos ⟨hAnT, E3.gammaMember_conj n hA.2⟩)
  have hW0_le : E3.wClos V 0 T ≤ conjSubgroup (E3.wClos V 0 T) n⁻¹ :=
    E3.wClos_le_of_forall hconj_one_le
  have heq : E3.wClos V 0 T = conjSubgroup (E3.wClos V 0 T) n⁻¹ :=
    Subgroup.eq_of_le_of_card_ge hW0_le (by rw [E3.card_conjSubgroup])
  have hconj := congrArg (fun X : Subgroup G => conjSubgroup X n) heq
  rw [hconj, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

end CFSG.LocalAnalysis.WeakClosure81

end
