module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringOF

open CFSG.Open

theorem isElemAbelian_closure {M : Type*} [Group M] {S : Set M}
    (hS : S.Pairwise Commute) (h3 : ∀ s ∈ S, s ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.closure S) := by
  have hcomm := Subgroup.isMulCommutative_closure hS
  refine ⟨hcomm, fun z hz => ?_⟩
  induction hz using Subgroup.closure_induction with
  | mem s hs => exact h3 s hs
  | one => exact one_pow 3
  | mul x y hx hy hx3 hy3 =>
    have hc : Commute x y := congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
    rw [hc.mul_pow, hx3, hy3, one_mul]
  | inv x hx hx3 =>
    rw [inv_pow, hx3, inv_one]

theorem exists_elemAbelian_of_commute {K : Type*} [Group K] [Finite K] {x y : K}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hy : y ∉ Subgroup.zpowers x) :
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ 9 ≤ Nat.card E := by
  have hpair : ({x, y} : Set K).Pairwise Commute := by
    intro a ha b hb hab
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hxy
    · exact hxy.symm
    · exact absurd rfl hab
  have hE := isElemAbelian_closure hpair (by
    intro s hs
    rcases hs with rfl | rfl
    · exact hx3
    · exact hy3)
  refine ⟨Subgroup.closure {x, y}, hE, ?_⟩
  have hP : IsPGroup 3 (Subgroup.closure ({x, y} : Set K)) :=
    fun z => ⟨1, Subtype.ext (by simpa using hE.2 z.1 z.2)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxE : Subgroup.zpowers x ≤ Subgroup.closure ({x, y} : Set K) :=
    (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (by simp))
  have hyE : y ∈ Subgroup.closure ({x, y} : Set K) := Subgroup.subset_closure (by simp)
  have hlt : Nat.card (Subgroup.zpowers x) < Nat.card (Subgroup.closure ({x, y} : Set K)) := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hxE) fun h => hy ?_
    have := Subgroup.eq_of_le_of_card_ge hxE h.ge
    rw [this]
    exact hyE
  rw [Nat.card_zpowers, hxo, hk] at hlt
  have hk2 : 2 ≤ k := by
    by_contra hk2
    push Not at hk2
    interval_cases k <;> simp at hlt
  rw [hk]
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

theorem exists_elemAbelian_gt_nine {K M : Type*} [Group K] [Group M] [Finite M]
    (hZ : Subgroup.center K = ⊥) (ι : K →* M) (hι : Function.Injective ι) {g : M}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hcomm : ∀ k, ι k * g = g * ι k) {E : Subgroup K}
    (hE : IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E) :
    ∃ F : Subgroup M, IsElemAbelian 3 F ∧ 9 < Nat.card F := by
  have hE' : IsElemAbelian 3 (E.map ι) := by
    refine ⟨?_, ?_⟩
    · refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      change a.1 * b.1 = b.1 * a.1
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg ι (congrArg Subtype.val (hE.1.is_comm.comm (⟨a', ha'⟩ : E) ⟨b', hb'⟩))
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.2 a ha, map_one]
  set S : Set M := (E.map ι : Set M) ∪ {g} with hS
  have hpair : S.Pairwise Commute := by
    intro a ha b hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact congrArg Subtype.val (hE'.1.is_comm.comm (⟨a, ha⟩ : E.map ι) ⟨b, hb⟩)
    · rw [Set.mem_singleton_iff] at hb
      obtain ⟨k, -, rfl⟩ := ha
      rw [hb]
      exact hcomm k
    · rw [Set.mem_singleton_iff] at ha
      obtain ⟨k, -, rfl⟩ := hb
      rw [ha]
      exact (hcomm k).symm
    · rw [Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hab
  have hF := isElemAbelian_closure hpair (by
    rintro s (hs | hs)
    · exact hE'.2 s hs
    · rw [Set.mem_singleton_iff] at hs
      rw [hs]
      exact hg3)
  refine ⟨Subgroup.closure S, hF, ?_⟩
  have hEF : E.map ι ≤ Subgroup.closure S := by
    intro z hz
    exact Subgroup.subset_closure (Or.inl hz)
  have hgF : g ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  have hgE : g ∉ E.map ι := by
    rintro ⟨k₀, hk₀, hg⟩
    apply hg1
    have hk0 : k₀ ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply hι
      rw [map_mul, map_mul, hg]
      exact hcomm k
    rw [hZ, Subgroup.mem_bot] at hk0
    rw [← hg, hk0, map_one]
  have hcardE : Nat.card (E.map ι) = Nat.card E :=
    Subgroup.card_map_of_injective hι
  have hdvd : Nat.card (E.map ι) ∣ Nat.card (Subgroup.closure S) := Subgroup.card_dvd_of_le hEF
  have hne : Nat.card (E.map ι) ≠ Nat.card (Subgroup.closure S) := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge hEF h.ge
    exact hgE (this ▸ hgF)
  obtain ⟨m, hm⟩ := hdvd
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (by rw [hm, mul_one])
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : Nat.card (Subgroup.closure S) = 0 := by rw [hm, mul_zero]
    exact Nat.card_pos.ne' this
  rw [hm, hcardE]
  have h2 : 2 ≤ m := by omega
  nlinarith

end CFSG.RankThree.PartTwo.Sec4.HeringOF
