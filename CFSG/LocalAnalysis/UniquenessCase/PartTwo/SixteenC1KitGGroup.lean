module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGFin
public import CFSG.LargeExtraspecial.O62Span

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

theorem s16c1g_closure_pair {G : Type*} [Group G] [Finite G] [DecidableEq G] {a b : G}
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hba2 : b ≠ a ^ 2) :
    IsPGroup 3 (Subgroup.closure ({a, b} : Set G)) ∧
      ¬ IsCyclic (Subgroup.closure ({a, b} : Set G)) := by
  let E := Subgroup.closure ({a, b} : Set G)
  have haE : a ∈ E := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E := Subgroup.subset_closure (by simp)
  have hpair : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy hxy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy
  haveI : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x :=
    fun x hx y hy => setLike_mul_comm hx hy
  have h3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact ha3
      · exact hb3
    | one => simp
    | mul x y hxE hyE ihx ihy =>
      have hc : Commute x y := hcommE x hxE y hyE
      rw [Commute.mul_pow hc 3, ihx, ihy, one_mul]
    | inv x hxE ihx => rw [inv_pow, ihx, inv_one]
  refine ⟨?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    exact h3 g.1 g.2
  · intro hcyc
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      exact h3 g.1 g.2
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
    have hle : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hmem : ∀ x ∈ E, x = 1 ∨ x = g.1 ∨ x = g.1 ^ 2 := by
      intro x hx
      have hxzp : (⟨x, hx⟩ : E) ∈ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top _
      rw [mem_zpowers_iff_mem_range_orderOf] at hxzp
      obtain ⟨n, hnmem, hneq⟩ := Finset.mem_image.mp hxzp
      have hn3 : n < 3 := lt_of_lt_of_le (Finset.mem_range.mp hnmem) hle
      interval_cases n
      · left
        have h' : (⟨x, hx⟩ : E) = 1 := by rw [← hneq, pow_zero]
        exact congrArg Subtype.val h'
      · right; left
        have h' : (⟨x, hx⟩ : E) = g := by rw [← hneq, pow_one]
        exact congrArg Subtype.val h'
      · right; right
        have h' : (⟨x, hx⟩ : E) = g ^ 2 := by rw [← hneq]
        simpa using congrArg Subtype.val h'
    rcases hmem a haE with ha1' | ha_g | ha_g2
    · exact ha1 ha1'
    · rcases hmem b hbE with hb1' | hb_g | hb_g2
      · exact hb1 hb1'
      · exact hba (by rw [hb_g, ← ha_g])
      · exact hba2 (by rw [hb_g2, ← ha_g])
    · have hgeq : g.1 = a ^ 2 := by
        have hg3G : g.1 ^ 3 = 1 := by
          have := h3 g.1 g.2
          simpa using this
        have h1 : (g.1 ^ 2) ^ 2 = g.1 := by
          rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add, hg3G, one_mul, pow_one]
        exact ((congrArg (fun t => t ^ 2) ha_g2).trans h1).symm
      rcases hmem b hbE with hb1' | hb_g | hb_g2
      · exact hb1 hb1'
      · exact hba2 (by rw [hb_g, hgeq])
      · have h' : g.1 ^ 2 = a := by
          have h1 : (a ^ 2) ^ 2 = a := by
            rw [← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_add, ha3, one_mul, pow_one]
          exact (congrArg (fun t => t ^ 2) hgeq).trans h1
        exact hba (by rw [hb_g2, h'])

private theorem s16c1g_okWord_omega {e : List ℕ} (hok : s16c1b_okWord e = true) :
    wordProd e ∈ Ω₀ true := by
  rw [s16c1b_okWord, Bool.and_eq_true] at hok
  exact (wordProd_mem_omegaGroup_iff (fun n hn => List.all_eq_true.mp hok.1 n hn)).mpr
    (Nat.even_iff.mpr (beq_iff_eq.mp hok.2))

private theorem s16c1g_cube_of_code {w : List ℕ}
    (h : mul (wordC w) (mul (wordC w) (wordC w)) = one) : wordProd w ^ 3 = 1 := by
  have hc : Coded (wordProd w * (wordProd w * wordProd w))
      (mul (wordC w) (mul (wordC w) (wordC w))) :=
    (coded_wordProd w).mul ((coded_wordProd w).mul (coded_wordProd w))
  rw [h] at hc
  calc wordProd w ^ 3 = wordProd w * (wordProd w * wordProd w) := pow_three _
    _ = 1 := (hc.eq_iff coded_one).mpr rfl

@[expose] noncomputable def s16c1g_E (p : List ℕ × List ℕ) :
    Subgroup (V₀ ≃ₗ[ZMod 2] V₀) :=
  Subgroup.closure {wordProd p.1, wordProd p.2}

theorem s16c1g_goodE_spec {p : List ℕ × List ℕ} (hp : s16c1g_goodE p = true) :
    wordProd p.1 ∈ Ω₀ true ∧ wordProd p.2 ∈ Ω₀ true ∧ wordProd p.1 ^ 3 = 1 ∧
      wordProd p.2 ^ 3 = 1 ∧ wordProd p.1 * wordProd p.2 = wordProd p.2 * wordProd p.1 ∧
      wordProd p.1 ≠ 1 ∧ wordProd p.2 ≠ 1 ∧ wordProd p.2 ≠ wordProd p.1 ∧
      wordProd p.2 ≠ wordProd p.1 ^ 2 := by
  simp only [s16c1g_goodE, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hok1, hok2⟩, hc1⟩, hc2⟩, hn1⟩, hn2⟩, hcomm⟩, hne⟩, hne2⟩ := hp
  refine ⟨s16c1g_okWord_omega hok1, s16c1g_okWord_omega hok2, s16c1g_cube_of_code hc1,
    s16c1g_cube_of_code hc2, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : Coded (wordProd p.1 * wordProd p.2) (mul (wordC p.1) (wordC p.2)) :=
      (coded_wordProd p.1).mul (coded_wordProd p.2)
    have h2 : Coded (wordProd p.2 * wordProd p.1) (mul (wordC p.2) (wordC p.1)) :=
      (coded_wordProd p.2).mul (coded_wordProd p.1)
    exact (h1.eq_iff h2).mpr hcomm
  · exact fun h => hn1 (((coded_wordProd p.1).eq_iff coded_one).mp h)
  · exact fun h => hn2 (((coded_wordProd p.2).eq_iff coded_one).mp h)
  · exact fun h => hne (((coded_wordProd p.2).eq_iff (coded_wordProd p.1)).mp h)
  · intro h
    have h2 : Coded (wordProd p.1 ^ 2) (mul (wordC p.1) (wordC p.1)) := by
      simpa [pow_two] using (coded_wordProd p.1).mul (coded_wordProd p.1)
    exact hne2 (((coded_wordProd p.2).eq_iff h2).mp h)

theorem s16c1g_E_spec {p : List ℕ × List ℕ} (hp : s16c1g_goodE p = true) :
    s16c1g_E p ≤ Ω₀ true ∧ IsPGroup 3 (s16c1g_E p) ∧ ¬ IsCyclic (s16c1g_E p) := by
  classical
  obtain ⟨hΩ1, hΩ2, h1, h2, hcomm, hn1, hn2, hne, hne2⟩ := s16c1g_goodE_spec hp
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  obtain ⟨hpg, hnc⟩ := s16c1g_closure_pair h1 h2 hcomm hn1 hn2 hne hne2
  refine ⟨?_, hpg, hnc⟩
  rw [s16c1g_E, Subgroup.closure_le]
  rintro x hx
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact hΩ1
  · exact hΩ2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
