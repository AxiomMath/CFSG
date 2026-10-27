module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16e_d5_natCard_multiplicative (α : Type*) :
    Nat.card (Multiplicative α) = Nat.card α :=
  Nat.card_congr Multiplicative.ofAdd.symm

private theorem s16e_d5_card_of_isElemAbelianOfRank {p n : ℕ} {X : Type*} [Group X]
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, s16e_d5_natCard_multiplicative, Nat.card_fun, Nat.card_fin,
    Nat.card_zmod]

private theorem s16e_d5_center_ne_top {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Subgroup.center Q ≠ ⊤ := by
  intro h
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨p, q, hpq⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact hpq (QuotientGroup.eq.mpr (h ▸ Subgroup.mem_top _))

private theorem s16e_d5_not_comm_of_quasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ (∀ a b : Q, a * b = b * a) := by
  intro hc
  refine s16e_d5_center_ne_top hQ ?_
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_center_iff]
  intro y
  exact (hc x y).symm

theorem s16e_d5_extract {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)}
    {t : MulAut W} {L : Subgroup (MulAut W)} (hL : IsElemAbelianOfRank 3 2 ↥L)
    (hrk : rk ↥(commSub ⊤ L) = 8) (h : Conc4_136W A t L) :
    ∀ x ∈ L, x ≠ 1 → rk ↥(commSub ⊤ (Subgroup.zpowers x)) = 6 := by
  have hcardL : Nat.card ↥L = 9 := by
    have h9 := s16e_d5_card_of_isElemAbelianOfRank hL
    norm_num at h9
    exact h9
  have hcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    obtain ⟨e⟩ := hL
    intro x hx y hy
    have h : (⟨x, hx⟩ : ↥L) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
      e.injective (by
        simp only [map_mul]
        exact mul_comm _ _)
    exact congrArg Subtype.val h
  intro x hx hx1
  unfold Conc4_136W at h
  obtain ⟨-, -, hcases⟩ := h
  rcases hcases with h133 | hcomp2 | hcompL | h135
  · obtain ⟨p, -, -, -, -, hcases7⟩ := h133
    rcases hcases7 with h1 | h2 | h3 | h4 | h5 | h6 | h7
    · have hc1 := h1.1.2
      omega
    · have hc2 := h2.1.2
      omega
    · have hc3 := h3.2
      omega
    · exact h4.2.2.1 x hx hx1
    · have hc5 := h5.1.2
      omega
    · obtain ⟨r, m, hpm, hr2, hel, hrk6, -⟩ := h6
      have hpr : p ^ r = 9 := by
        have := s16e_d5_card_of_isElemAbelianOfRank hel
        omega
      rcases hpm with ⟨hp3, hm2⟩ | ⟨hp7, -⟩
      · rw [hp3] at hpr
        rw [hm2] at hrk6
        have hr : r = 2 := by
          have h : 3 ^ r = 3 ^ 2 := by
            rw [hpr]
            norm_num
          exact Nat.pow_right_injective (show 2 ≤ 3 by norm_num) h
        rw [hr] at hrk6
        norm_num at hrk6
        omega
      · rw [hp7] at hpr
        have h7 : (7 : ℕ) ^ 2 ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
        norm_num at h7
        omega
    · have hc7 := h7.2.1
      omega
  · obtain ⟨K, hK, g, -, -, hLK, -⟩ := hcomp2
    have hKi : IsComponentOf K A := hK
    have hKL : K ≤ L := by rw [hLK]; exact le_sup_left
    have hcommK : ∀ a b : ↥K, a * b = b * a := fun a b =>
      Subtype.ext (hcomm a.1 (hKL a.2) b.1 (hKL b.2))
    exact absurd hcommK (s16e_d5_not_comm_of_quasisimple hKi.2.2)
  · obtain ⟨hLc, -⟩ := hcompL
    have hcommL : ∀ a b : ↥L, a * b = b * a := fun a b =>
      Subtype.ext (hcomm a.1 a.2 b.1 b.2)
    exact absurd hcommL (s16e_d5_not_comm_of_quasisimple hLc.2.2)
  · obtain ⟨-, -, hLc, -⟩ := h135
    have hcommL : ∀ a b : ↥L, a * b = b * a := fun a b =>
      Subtype.ext (hcomm a.1 a.2 b.1 b.2)
    exact absurd hcommL (s16e_d5_not_comm_of_quasisimple hLc.2.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
