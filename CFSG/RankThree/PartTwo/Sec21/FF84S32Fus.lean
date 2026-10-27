module

public import CFSG.RankThree.PartTwo.Sec21.FF84S32Syl
public import CFSG.RankThree.PartTwo.Sec21.FF84S3B

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21

section Main
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem c_notin_O3 (h : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ∉ O3 (Cen (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact B_central_notin_Oup 3 (Cen (b₁ * b₂)) B (S2_B_sylow h)
    (fun x hx y hy => (comm_of_mem_B h hx hy).eq) (c_mem_B h)
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.1 hg) (c_ne_one h)

theorem S2_Sylow_H (h : FF84Sec3 b L B b₁ b₂) :
    IsSylowOf 3 (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2)) (O3 (Cen (b₁ * b₂))) ∧
      b₁ * b₂ ∉ O3 (Cen (b₁ * b₂)) := by
  have hc := c_notin_O3 h
  refine ⟨?_, hc⟩
  rw [P_eq_inf h hc]
  exact isSylowOf_inf_of_normal (S2_B_sylow h) (O3_le _) (fun g hg => mem_Nor_O3 hg)

theorem card_P (h : FF84Sec3 b L B b₁ b₂) :
    Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) : Subgroup G) = 9 := by
  have hc := c_notin_O3 h
  rw [P_eq_inf h hc]
  have h27 : Nat.card ↥(B ⊓ O3 (Cen (b₁ * b₂))) ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ O3 (Cen (b₁ * b₂)) ≤ B)
    rw [P_cardB h] at this
    norm_num
    exact this
  have hne : Nat.card ↥(B ⊓ O3 (Cen (b₁ * b₂))) ≠ 27 := by
    intro h27'
    have heq : B ⊓ O3 (Cen (b₁ * b₂)) = B :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h27', P_cardB h])
    have hcB : b₁ * b₂ ∈ B ⊓ O3 (Cen (b₁ * b₂)) := by rw [heq]; exact c_mem_B h
    exact hc hcB.2
  have hge := card_P_ge h
  rw [P_eq_inf h hc] at hge
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h27
  rw [hk'] at hge ⊢
  interval_cases k
  · norm_num at hge
  · norm_num at hge
  · norm_num
  · exact absurd (hk'.trans (by norm_num)) hne

theorem P_inter_six (h : FF84Sec3 b L B b₁ b₂) {x : G}
    (hx : x ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2))
    (h6 : x ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G)) : x = b ∨ x = b⁻¹ := by
  obtain ⟨i, j, hij⟩ := exists_coord_P h hx
  obtain ⟨a, c, d, hxa, hcase⟩ := six_coord h6
  have := (ceq h).1 (hij.symm.trans hxa)
  have hb : a = 1 ∧ c = 0 ∧ d = 0 ∨ a = -1 ∧ c = 0 ∧ d = 0 := by omega
  rcases hb with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · left; simp [hxa]
  · right; simp [hxa]

theorem S2_N_P_le (h : FF84Sec3 b L B b₁ b₂) :
    Nor (Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2)) ≤ Nor (Subgroup.zpowers b) := by
  intro n hn
  have hbP : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hnb : n * b * n⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers (b₁ * b₂ ^ 2) :=
    (Subgroup.mem_normalizer_iff.1 hn b).1 hbP
  have hB : n * b * n⁻¹ ∈ B := P_le_B h hnb
  have h6 := fusion_mem h hB
  exact mem_nor_zpowers_of_conj (by
    rcases P_inter_six h hnb h6 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1)

theorem S2_not_conj (h : FF84Sec3 b L B b₁ b₂) :
    ¬ ∃ g ∈ O3 (Cen (b₁ * b₂)), conjBy g (Subgroup.zpowers (b₁ * b₂ ^ 2)) = Subgroup.zpowers b := by
  rintro ⟨g, -, hg⟩
  have hdg : g * (b₁ * b₂ ^ 2) * g⁻¹ ∈ Subgroup.zpowers b := by
    rw [← hg]
    exact ⟨_, Subgroup.mem_zpowers _, rfl⟩
  have hd1 : g * (b₁ * b₂ ^ 2) * g⁻¹ ≠ 1 := by
    intro h1
    apply d_ne_one h
    calc b₁ * b₂ ^ 2 = g⁻¹ * (g * (b₁ * b₂ ^ 2) * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hbm : b ∈ Subgroup.zpowers (g * (b₁ * b₂ ^ 2) * g⁻¹) :=
    mem_zpowers_of_mem_zpowers_ne_one hdg (pow3_of_mem_B h (mem_B_b h)) (b_ne_one' h) hd1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hbm
  have hk' : g⁻¹ * b * g = (b₁ * b₂ ^ 2) ^ k := by
    rw [← hk, conj_zpow]; group
  have hB : g⁻¹ * b * g⁻¹⁻¹ ∈ B := by
    rw [inv_inv, hk']
    exact Subgroup.zpow_mem _ (d_mem_B h) _
  have h6 := fusion_mem h hB
  obtain ⟨a, c, d, hxa, hcase⟩ := six_coord h6
  rw [inv_inv, hk', zpow_d h] at hxa
  have := (ceq h).1 hxa
  omega

end Main

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
