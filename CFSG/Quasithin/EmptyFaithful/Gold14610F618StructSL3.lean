module

import CFSG.Models.PGLSimple
import CFSG.Adapters.StatedQuasisimple
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructIso

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace Gold14610

namespace Struct

theorem statedScalars_subgroupOf_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) :
    (CFSG.Assembly.LowTwoRank.StatedScalars ι K).subgroupOf H ≤ Subgroup.center H :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _

theorem isSimpleGroup_statedProj_statedSL_three {p : ℕ} (hp : p.Prime) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p) : IsSimpleGroup (StatedProj (StatedSL 3 K)) :=
  CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem isQuasisimple_statedSL_three {p : ℕ} (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p) : CFSG.IsQuasisimple ↥(StatedSL 3 K) :=
  CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le le_rfl K

theorem isSimpleGroup_statedProj_statedSU_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = p ^ 2) :
    IsSimpleGroup (StatedProj (StatedSU 3 p K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p 1
    (by rw [pow_one]; exact hK) 3 le_rfl (by simp; omega)
  have key : ∀ q : ℕ, q = p ^ 1 → IsSimpleGroup (StatedProj (StatedSU 3 q K)) := by
    intro q hq
    subst hq
    exact this
  exact key p (pow_one p).symm

theorem isQuasisimple_statedSU_three {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) : CFSG.IsQuasisimple ↥(StatedSU 3 p K) :=
  CFSG.Open.StatedAPI.isQuasisimple_statedSU_three_of_prime hp hp3 K hK

variable {D : Type} [Group D]

theorem isSimple_or_isQuasisimple_of_isSLEps3 {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5) {W : Type}
    [Group W] (h : F6.IsSLEps3 p W) : IsSimpleGroup W ∨ CFSG.IsQuasisimple W := by
  obtain ⟨hp, K, _, _, hK⟩ := h
  have hp3 : 3 ≤ p := by omega
  have qs : ∀ {A : Type} [Group A], CFSG.IsQuasisimple A → W ≃* A → CFSG.IsQuasisimple W :=
    fun hA e => (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr
      (openIsQuasisimple_of_mulEquiv e.symm
        ((CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mp hA))
  rcases hK with ⟨h1, hK, hW⟩ | ⟨h3, hK, hW⟩
  · rcases hW with hW | hW
    · obtain ⟨e⟩ := hW
      exact Or.inr (qs (isQuasisimple_statedSL_three hp K hK) e)
    · obtain ⟨e⟩ := hW
      have := isSimpleGroup_statedProj_statedSL_three hp K hK
      exact Or.inl e.isSimpleGroup
  · rcases hW with hW | hW
    · obtain ⟨e⟩ := hW
      exact Or.inr (qs (isQuasisimple_statedSU_three hp hp3 K hK) e)
    · obtain ⟨e⟩ := hW
      have := isSimpleGroup_statedProj_statedSU_three hp hp3 K hK
      exact Or.inl e.isSimpleGroup

theorem F618Core_of_isSLEps3 {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5) {W : Type} [Group W]
    (h : F6.IsSLEps3 p W) : F618Core W :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hp8, h⟩))))))

theorem idx2Data_of_isSLEps3 {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5) (h : F6.IsSLEps3 p D) :
    Idx2Data D := by
  rcases isSimple_or_isQuasisimple_of_isSLEps3 hp8 h with hs | hq
  · exact idx2Data_of_simple hs (F618Core_of_isSLEps3 hp8 h)
  · exact idx2Data_of_quasisimple hq (F618Core_of_isSLEps3 hp8 h)

theorem exists_index_two_sub_isSLEps3 {p : ℕ} (h : F6.IsSLEps3GraphExt p D) :
    ∃ Kq : Subgroup D, Kq.index = 2 ∧ F6.IsSLEps3 p ↥Kq := by
  have quot : ∀ {G : Type} [Group G] (H : Subgroup G), ↥H ⧸ (⊥ : Subgroup G).subgroupOf H ≃* ↥H :=
    fun H => (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot
  obtain ⟨hp, F, _, _, h1 | h3⟩ := h
  · obtain ⟨hmod, hF, hext | hext⟩ := h1
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      exact ⟨M, hidx, hp, F, inferInstance, inferInstance,
        Or.inl ⟨hmod, hF, Or.inl ⟨e.trans (quot _)⟩⟩⟩
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      exact ⟨M, hidx, hp, F, inferInstance, inferInstance, Or.inl ⟨hmod, hF, Or.inr ⟨e⟩⟩⟩
  · obtain ⟨hmod, hF, hext | hext⟩ := h3
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      exact ⟨M, hidx, hp, F, inferInstance, inferInstance,
        Or.inr ⟨hmod, hF, Or.inl ⟨e.trans (quot _)⟩⟩⟩
    · obtain ⟨M, e, t, g, hidx, -, -⟩ := hext
      exact ⟨M, hidx, hp, F, inferInstance, inferInstance, Or.inr ⟨hmod, hF, Or.inr ⟨e⟩⟩⟩

theorem idx2Data_of_isSLEps3GraphExt {p : ℕ} (hp8 : p % 8 = 3 ∨ p % 8 = 5)
    (h : F6.IsSLEps3GraphExt p D) : Idx2Data D := by
  obtain ⟨Kq, hidx, hKq⟩ := exists_index_two_sub_isSLEps3 h
  exact idx2Data_of_index_two hidx (F618Core_of_isSLEps3 hp8 hKq)
    (isSimple_or_isQuasisimple_of_isSLEps3 hp8 hKq)

end Struct

end Gold14610

end CFSG.Quasithin
