module

public import CFSG.RankThree.PartOne.SP4GA.Frame
public import CFSG.RankThree.PartOne.SP4GA.Unique

public section

namespace CFSG.RankThree.PartOne.SP4GA

variable {G : Type} [Group G] [Finite G] {p e : ℕ} {c : G} {E L P Q : Subgroup G} {x y : G}

namespace Frame7

variable (F : Frame7 p e c E L P Q x y)

include F

omit [Finite G] in
theorem Q_abelian : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
  have hyx : y * x = x * y := F.setup.xy.symm
  intro q hq q' hq'
  rw [F.Q_eq] at hq hq'
  obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_sup hyx hq
  obtain ⟨i', j', rfl⟩ := exists_zpow_mul_of_sup hyx hq'
  rw [comb_mul hyx, comb_mul hyx, add_comm i, add_comm j]

omit [Finite G] in
theorem Q_le_P : Q ≤ P := by
  obtain ⟨f, -, hPf⟩ := F.P_gen
  rw [hPf]
  exact le_sup_left

theorem conj_mem_Q {n : G} (hn : n ∈ Subgroup.normalizer (P : Set G)) {q : G} (hq : q ∈ Q) :
    n * q * n⁻¹ ∈ Q := by
  have hM : Q.map (MulAut.conj n).toMonoidHom = Q := by
    obtain ⟨f, hfP, hPf⟩ := F.P_gen
    refine eq_of_abelian_card_le F.setup.hp F.setup.hp2 (by have := F.two_le; omega)
      F.P_pgroup F.Q_norm hfP hPf F.Q_eq F.setup.xy F.disj F.x_ord F.y_ord F.x_norm F.y_norm
      F.setup.c_mem F.c_not_mem F.c_pow F.cx F.cy ?_ ?_ ?_
    · rintro _ ⟨q', hq', rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hn q').1 (F.Q_le_P hq')
    · rintro _ ⟨q₁, hq₁, rfl⟩ _ ⟨q₂, hq₂, rfl⟩
      have h := F.Q_abelian q₁ hq₁ q₂ hq₂
      show n * q₁ * n⁻¹ * (n * q₂ * n⁻¹) = n * q₂ * n⁻¹ * (n * q₁ * n⁻¹)
      calc n * q₁ * n⁻¹ * (n * q₂ * n⁻¹) = n * (q₁ * q₂) * n⁻¹ := by group
        _ = n * (q₂ * q₁) * n⁻¹ := by rw [h]
        _ = n * q₂ * n⁻¹ * (n * q₁ * n⁻¹) := by group
    · exact (Subgroup.card_map_of_injective (MulAut.conj n).injective).ge
  have : n * q * n⁻¹ ∈ Q.map (MulAut.conj n).toMonoidHom := ⟨q, hq, by simp [MulAut.conj_apply]⟩
  rwa [hM] at this

theorem coords {n : G} (hn : n ∈ Subgroup.normalizer (P : Set G)) :
    ∃ a a' b₁ b₂ : ℤ, n * x * n⁻¹ = x ^ a * y ^ a' ∧ n * y * n⁻¹ = x ^ b₁ * y ^ b₂ := by
  have hyx : y * x = x * y := F.setup.xy.symm
  have hxQ : x ∈ Q := by
    rw [F.Q_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hyQ : y ∈ Q := by
    rw [F.Q_eq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have h1 : n * x * n⁻¹ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x := by
    rw [← F.Q_eq]
    exact F.conj_mem_Q hn hxQ
  have h2 : n * y * n⁻¹ ∈ Subgroup.zpowers y ⊔ Subgroup.zpowers x := by
    rw [← F.Q_eq]
    exact F.conj_mem_Q hn hyQ
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_sup hyx h1
  obtain ⟨i', j', hij'⟩ := exists_zpow_mul_of_sup hyx h2
  refine ⟨j, i, j', i', ?_, ?_⟩
  · rw [hij]
    exact (Commute.zpow_zpow (show Commute y x from hyx) i j).eq
  · rw [hij']
    exact (Commute.zpow_zpow (show Commute y x from hyx) i' j').eq

end Frame7

end CFSG.RankThree.PartOne.SP4GA
