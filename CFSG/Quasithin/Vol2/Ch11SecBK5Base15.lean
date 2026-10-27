module

public import CFSG.Quasithin.Vol2.Ch11SecBK5Base14
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base13

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat CFSG.Quasithin.Vol2.Ch11.G2Q8
open Matrix
open scoped Pointwise

variable {K : Type} [Field K] [CharP K 2]


theorem flagStab_one_or_two [Finite K] (hK : 4 ≤ Nat.card K) {B : Subgroup (GL (Fin 6) K)}
    (hBG : ∀ b ∈ B, IsScalG2 b) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 6) K)) * (u0Six K : Set (GL (Fin 6) K)) =
      (u0Six K : Set (GL (Fin 6) K)) * B) :
    B ≤ Tri.flagStab 6 1 K ∨ B ≤ Tri.flagStab 6 2 K := by
  have := finite_cayleyGroup (F := K)
  have hUp : IsPGroup 2 ((U0 K).map g2Six) := isPGroup_U0.map _
  rcases Tri.exists_normal_or_le_normalizer hBab hBodd hUp hBU with ⟨O, hO1, hOU, hON⟩ | hN
  · obtain ⟨h, h1, h5, hBh⟩ := stab_of_normal_g2 hBG hO1 hOU hON
    have key : ∀ m, stabQ (stdF K h) ≤ stabQ (stdF K m) → B ≤ Tri.flagStab 6 m K := by
      intro m H b hb
      obtain ⟨c, g, hc, hbg⟩ := hBG b hb
      rw [mem_flagStab_iff_of_isScalG2 hc hbg]
      exact H ((mem_flagStab_iff_of_isScalG2 hc hbg).mp (hBh hb))
    rcases stabQ_le_one_or_two (K := K) h1 h5 with H | H
    · exact Or.inl (key 1 H)
    · exact Or.inr (key 2 H)
  · right
    refine Tri.le_of_commute (E := (longRoot K).map g2Six)
      ((Subgroup.map_mono longRoot_le_U0).trans hN) ?_ ?_ ?_ hBodd ?_
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, longRoot_comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, longRoot_mul_self a ha, map_one]
    · rw [Subgroup.card_map_of_injective g2Six_injective, card_longRoot]
      exact hK
    · rintro _ ⟨e, ⟨s, rfl⟩, rfl⟩ he1 b hb heb
      have hs : s ≠ 0 := by
        rintro rfl
        exact he1 (by rw [tL_zero', map_one])
      obtain ⟨c, g, hc, hbg⟩ := hBG b hb
      rw [mem_flagStab_iff_of_isScalG2 hc hbg]
      have h1 := commute_of_smul hc hbg heb
      refine mem_stabQ_two_of_comm_tL hs (g2Six_injective ?_)
      rw [map_mul, map_mul]
      exact h1.symm

theorem flagStab_one_and_two [Finite K] (hK : 4 ≤ Nat.card K) {B : Subgroup (GL (Fin 6) K)}
    (hBG : ∀ b ∈ B, IsScalG2 b) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 6) K)) * (u0Six K : Set (GL (Fin 6) K)) =
      (u0Six K : Set (GL (Fin 6) K)) * B) :
    B ≤ Tri.flagStab 6 1 K ⊓ Tri.flagStab 6 2 K := by
  have hUh : ∀ h, (U0 K).map g2Six ≤ Tri.flagStab 6 h K := fun h => by
    rintro _ ⟨u, hu, rfl⟩
    exact g2Six_mem_flagStab_iff.mpr (U0_le_stabQ h hu)
  rcases flagStab_one_or_two hK hBG hBab hBodd hBU with h1 | h2
  · have h3 : B ≤ Tri.flagStab 6 3 K := fun b hb => by
      obtain ⟨c, g, hc, hbg⟩ := hBG b hb
      rw [mem_flagStab_iff_of_isScalG2 hc hbg]
      exact stabQ_one_le_three ((mem_flagStab_iff_of_isScalG2 hc hbg).mp (h1 hb))
    have hQ := sup_le h3 (hUh 3)
    have hmap := Tri.map_le_borGL_three hK (Tri.topHom (by norm_num : 3 ≤ 6) hQ) le_sup_left
      le_sup_right (map_topHom_three_g2 hQ le_sup_right) hBab hBodd hBU
    intro b hb
    have hbQ : b ∈ B ⊔ (U0 K).map g2Six := le_sup_left (b := (U0 K).map g2Six) hb
    have hb' := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
    rw [Tri.mem_borGL] at hb'
    have h3b := Tri.mem_flagStab.mp (h3 hb)
    have key : ∀ m, m ≤ 3 → b ∈ Tri.flagStab 6 m K := fun m hm =>
      Tri.mem_flagStab.mpr fun i j hj hi => by
        by_cases hi3 : (i : ℕ) < 3
        · exact hb' ⟨i, hi3⟩ ⟨j, by omega⟩ (Fin.lt_def.mpr (by simp only; omega))
        · exact h3b i j (by omega) (by omega)
    exact ⟨key 1 (by norm_num), key 2 (by norm_num)⟩
  · have hQ := sup_le h2 (hUh 2)
    have hmap := Tri.map_le_borGL_two hK (Tri.topHom (by norm_num : 2 ≤ 6) hQ) le_sup_left
      le_sup_right (map_topHom_two_g2 hQ le_sup_right) hBab hBodd hBU
    intro b hb
    have hbQ : b ∈ B ⊔ (U0 K).map g2Six := le_sup_left (b := (U0 K).map g2Six) hb
    have hb' := hmap ⟨⟨b, hbQ⟩, hb, rfl⟩
    rw [Tri.mem_borGL_two] at hb'
    have h2b := Tri.mem_flagStab.mp (h2 hb)
    refine ⟨Tri.mem_flagStab.mpr fun i j hj hi => ?_, h2 hb⟩
    by_cases hi1 : (i : ℕ) = 1
    · have hi : i = 1 := Fin.ext hi1
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hi hj0
      exact hb'
    · exact h2b i j (by omega) (by omega)

theorem triangular_g2 [Finite K] (hK : 4 ≤ Nat.card K) {B : Subgroup (GL (Fin 6) K)}
    (hBG : ∀ b ∈ B, IsScalG2 b) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 6) K)) * (u0Six K : Set (GL (Fin 6) K)) =
      (u0Six K : Set (GL (Fin 6) K)) * B) :
    B ≤ Tri.borGL 6 K := by
  intro b hb
  obtain ⟨hb1, hb2⟩ := flagStab_one_and_two hK hBG hBab hBodd hBU hb
  obtain ⟨c, g, hc, hbg⟩ := hBG b hb
  have hg1 := (mem_flagStab_iff_of_isScalG2 hc hbg).mp hb1
  have hg2 := (mem_flagStab_iff_of_isScalG2 hc hbg).mp hb2
  have hg : ∀ h, 1 ≤ h → h ≤ 5 → g ∈ stabQ (stdF K h) := by
    intro h h1 h5
    interval_cases h
    · exact hg1
    · exact hg2
    · exact stabQ_one_le_three hg1
    · exact stabQ_le_perp (h := 2) (by norm_num) hg2
    · exact stabQ_le_perp (h := 1) (by norm_num) hg1
  rw [Tri.mem_borGL]
  intro i j hij
  have hij' := Fin.lt_def.mp hij
  have hj : (j : ℕ) + 1 ≤ 5 := by
    have := i.2
    omega
  have := (mem_flagStab_iff_of_isScalG2 hc hbg).mpr (hg (j + 1) (by omega) hj)
  exact Tri.mem_flagStab.mp this i j (by omega) (by omega)

theorem pow_card_sub_one_of_g2 [Finite K] (hK : 4 ≤ Nat.card K) {B : Subgroup (GL (Fin 6) K)}
    (hBG : ∀ b ∈ B, IsScalG2 b) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B))
    (hBU : (B : Set (GL (Fin 6) K)) * (u0Six K : Set (GL (Fin 6) K)) =
      (u0Six K : Set (GL (Fin 6) K)) * B) {b : GL (Fin 6) K} (hb : b ∈ B) :
    b ^ (Nat.card K - 1) = 1 :=
  Tri.pow_card_sub_one_eq_one (triangular_g2 hK hBG hBab hBodd hBU hb)
    (Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb))

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
