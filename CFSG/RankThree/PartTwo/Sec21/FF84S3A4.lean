module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3A3
public import CFSG.RankThree.PartTwo.Sec21.FF84S3A4K

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.GLTheoremA.CatB

abbrev K5 : Subgroup P8 := a8Kb.map (alternatingGroup (Fin 8)).subtype

theorem K5_le_A8 : K5 ≤ A8s := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

theorem K5_le_cent : K5 ≤ Subgroup.centralizer ({m₁ * m₂} : Set P8) := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (comm_of_mem_a8Kb x hx)

theorem K5_card : Nat.card K5 = 60 := by
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), a8Kb_card]

theorem K5_simple : IsSimpleGroup K5 := by
  haveI := a8Kb_simple
  exact MulEquiv.isSimpleGroup (Subgroup.equivMapOfInjective a8Kb _
    (Subgroup.subtype_injective _)).symm

theorem K5_fix_low (x : A8) (hx : x ∈ a8Kb) (w : Fin 8) (hw : w.val < 3) :
    (x : P8) w = w := by
  obtain ⟨h0, h1, h2⟩ := (mem_a8Kb_iff x).1 hx
  rcases (fin8_lt3 w).1 hw with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

theorem cent_preserves_low (g : P8) (hg : g * (m₁ * m₂) = (m₁ * m₂) * g) (z : Fin 8)
    (hz : z.val < 3) : (g z).val < 3 := by
  have key : ∀ w : Fin 8, 3 ≤ w.val → (m₁ * m₂) w = w := by decide +kernel
  have key2 : ∀ w : Fin 8, w.val < 3 → (m₁ * m₂) w ≠ w := by decide +kernel
  by_contra hcon
  push Not at hcon
  have h1 : m₁ (m₂ (g z)) = g z := by
    have := key _ hcon
    rwa [Equiv.Perm.mul_apply] at this
  have h := congrArg (fun p : P8 => p z) hg
  simp only [Equiv.Perm.mul_apply] at h
  have h2 : g (m₁ (m₂ z)) = g z := by
    rw [h]
    exact h1
  have h3 : m₁ (m₂ z) = z := g.injective h2
  exact key2 z hz (by rw [Equiv.Perm.mul_apply]; exact h3)

theorem K5_normal_cent (g : P8) (hg : g * (m₁ * m₂) = (m₁ * m₂) * g) (y : P8) (hy : y ∈ K5) :
    g * y * g⁻¹ ∈ K5 := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  have hg' : g⁻¹ * (m₁ * m₂) = (m₁ * m₂) * g⁻¹ := Commute.inv_left_iff.2 hg
  have hmem : g * (x : P8) * g⁻¹ ∈ alternatingGroup (Fin 8) :=
    (inferInstance : (alternatingGroup (Fin 8)).Normal).conj_mem _ x.2 g
  refine Subgroup.mem_map.2 ⟨⟨g * (x : P8) * g⁻¹, hmem⟩, (mem_a8Kb_iff _).2 ?_, rfl⟩
  have hfix : ∀ z : Fin 8, z.val < 3 → (g * (x : P8) * g⁻¹) z = z := by
    intro z hz
    have hw := cent_preserves_low g⁻¹ hg' z hz
    simp only [Equiv.Perm.mul_apply]
    rw [K5_fix_low x hx _ hw]
    simp
  exact ⟨hfix 0 (by decide), hfix 1 (by decide), hfix 2 (by decide)⟩

theorem formPerm_345_alt : (List.formPerm [3, 4, 5] : P8) ∈ alternatingGroup (Fin 8) := by
  have hd3 : (List.formPerm [3, 4, 5] : P8).IsThreeCycle :=
    card_support_eq_three_iff.mp (by decide +kernel)
  exact Equiv.Perm.mem_alternatingGroup.2 hd3.sign

theorem formPerm_34567_alt : (List.formPerm [3, 4, 5, 6, 7] : P8) ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide +kernel)

theorem formPerm_345_mem_K5 : (List.formPerm [3, 4, 5] : P8) ∈ K5 :=
  Subgroup.mem_map.2 ⟨⟨_, formPerm_345_alt⟩, (mem_a8Kb_iff _).2 ⟨by decide, by decide, by decide⟩, rfl⟩

theorem formPerm_34567_mem_K5 : (List.formPerm [3, 4, 5, 6, 7] : P8) ∈ K5 :=
  Subgroup.mem_map.2 ⟨⟨_, formPerm_34567_alt⟩, (mem_a8Kb_iff _).2 ⟨by decide, by decide, by decide⟩, rfl⟩

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem centralizer_K5_cc (g : P8)
    (h1 : g * (List.formPerm [3, 4, 5] : P8) = (List.formPerm [3, 4, 5] : P8) * g)
    (h2 : g * (List.formPerm [3, 4, 5, 6, 7] : P8) = (List.formPerm [3, 4, 5, 6, 7] : P8) * g)
    (h3 : g * (m₁ * m₂) = (m₁ * m₂) * g) :
    g = 1 ∨ g = m₁ * m₂ ∨ g = (m₁ * m₂) ^ 2 :=
  S3A4K.key g h1 h2 h3

theorem orderOf_cc : orderOf (m₁ * m₂) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem orderOf_cc_sq : orderOf ((m₁ * m₂) ^ 2) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem A6_O3'_centralizer_c (Y N : Subgroup P8)
    (hY₁ : Subgroup.centralizer ({m₁ * m₂} : Set P8) ⊓ A8s ≤ Y)
    (hY₂ : Y ≤ Subgroup.centralizer ({m₁ * m₂} : Set P8)) (hN : N ≤ Y)
    (hNn : (N.subgroupOf Y).Normal) (h3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  have hKY : K5 ≤ Y := le_trans (le_inf K5_le_cent K5_le_A8) hY₁
  have hNK : ∀ m ∈ N, ∀ k ∈ Y, k * m * k⁻¹ ∈ N := by
    intro m hm k hk
    have h := hNn.conj_mem ⟨m, hN hm⟩ (Subgroup.mem_subgroupOf.2 hm) ⟨k, hk⟩
    have h' := Subgroup.mem_subgroupOf.1 h
    exact h'
  haveI := K5_simple
  have hNK5 : ∀ m ∈ N, m ∈ K5 → m = 1 := by
    have hnorm : (N.subgroupOf K5).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := hNK _ hn _ (hKY g.2)
      simpa using h
    rcases K5_simple.eq_bot_or_eq_top_of_normal (N.subgroupOf K5) with hb | ht
    · intro m hm hmK
      have hmem : (⟨m, hmK⟩ : K5) ∈ N.subgroupOf K5 := Subgroup.mem_subgroupOf.2 hm
      rw [hb, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    · exfalso
      have hle : K5 ≤ N := by
        intro k hk
        have hmem : (⟨k, hk⟩ : K5) ∈ N.subgroupOf K5 := by rw [ht]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 hmem
      have hdvd : Nat.card K5 ∣ Nat.card N := Subgroup.card_dvd_of_le hle
      rw [K5_card] at hdvd
      exact h3 (dvd_trans (by norm_num) hdvd)
  have hcomm : ∀ n ∈ N, ∀ k ∈ K5, n * k = k * n := by
    intro n hn k hk
    have hnY : n ∈ Y := hN hn
    have hnC : n * (m₁ * m₂) = (m₁ * m₂) * n := Subgroup.mem_centralizer_singleton_iff.1 (hY₂ hnY)
    have h1 : n * k * n⁻¹ ∈ K5 := K5_normal_cent n hnC k hk
    have hu1 : n * k * n⁻¹ * k⁻¹ ∈ K5 := K5.mul_mem h1 (K5.inv_mem hk)
    have hk' : k * n⁻¹ * k⁻¹ ∈ N := hNK _ (N.inv_mem hn) k (hKY hk)
    have hu2 : n * k * n⁻¹ * k⁻¹ ∈ N := by
      have : n * k * n⁻¹ * k⁻¹ = n * (k * n⁻¹ * k⁻¹) := by group
      rw [this]
      exact N.mul_mem hn hk'
    have hu := hNK5 _ hu2 hu1
    calc n * k = (n * k * n⁻¹ * k⁻¹) * (k * n) := by group
      _ = k * n := by rw [hu, one_mul]
  have hone : ∀ n ∈ N, n = 1 := by
    intro n hn
    have hnC : n * (m₁ * m₂) = (m₁ * m₂) * n :=
      Subgroup.mem_centralizer_singleton_iff.1 (hY₂ (hN hn))
    rcases centralizer_K5_cc n (hcomm n hn _ formPerm_345_mem_K5)
      (hcomm n hn _ formPerm_34567_mem_K5) hnC with h | h | h
    · exact h
    · exfalso
      apply h3
      have h' := Subgroup.orderOf_dvd_natCard N hn
      rw [h, orderOf_cc] at h'
      exact h'
    · exfalso
      apply h3
      have h' := Subgroup.orderOf_dvd_natCard N hn
      rw [h, orderOf_cc_sq] at h'
      exact h'
  exact eq_bot_iff.2 fun n hn => Subgroup.mem_bot.2 (hone n hn)

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
