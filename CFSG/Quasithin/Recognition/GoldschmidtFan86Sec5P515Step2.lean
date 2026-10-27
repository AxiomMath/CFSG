module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Step
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P515Claim

public section

namespace CFSG.Quasithin.Fan86

namespace P515

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P514

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem lab_mem_nbrStab (F : FanTree Γ G) {T : Track Γ G} {z : G} {a r : ℤ} (C : Ctx F T z a r)
    (hr0 : 0 ≤ r) {j : ℤ} (hj : 0 ≤ j) (hjr : 2 * j ≤ r) :
    lab T z j ∈ nbrStab Γ G (T.line.vert (a + 1)) := by
  have h1 : lab T z j • T.line.vert a = T.line.vert a :=
    (C.fix j a).2 ⟨by omega, by omega⟩
  have h2 : lab T z j • T.line.vert (a + 2) = T.line.vert (a + 2) :=
    (C.fix j (a + 2)).2 ⟨by omega, by omega⟩
  have ha : Γ.Adj (T.line.vert (a + 1)) (T.line.vert a) := (T.line.adj a).symm
  have hb : Γ.Adj (T.line.vert (a + 1)) (T.line.vert (a + 2)) := by
    have := T.line.adj (a + 1)
    rwa [show a + 1 + 1 = a + 2 by ring] at this
  have hab : T.line.vert a ≠ T.line.vert (a + 2) := T.line.nb a
  exact F.fix_two_nbrs ha hb hab h1 h2

theorem step (F : FanTree Γ G) (h40 : Fan40 F) {T : Track Γ G} {z : G} {a r : ℤ}
    (C : Ctx F T z a r) (hr0 : 0 ≤ r) {m : ℤ} (hm : 0 ≤ m) (hr : 2 * m + 4 ≤ r)
    (hQ : Q T z a m) : Q T z a (m + 1) := by
  intro μ l hαμ hμl hlα
  set α := T.line.vert (a + 1) with hα
  have hv3μ : valence Γ μ = 3 := valence_adj_three F C.val hαμ
  have hl5 : valence Γ l = 5 := valence_adj_five F hv3μ hμl
  have hl : ∃ g : G, g • α = l := conj_of_valence F C.val hl5
  obtain ⟨l', hset, hαl', hll'⟩ := exists_third_neighbor hv3μ hαμ.symm hμl hlα.symm
  have e3 : a + 1 + 2 * m + 3 = a + 2 + 2 * (m + 1) := by ring
  have e2 : a + 1 + 2 * m + 2 = a + 1 + 2 * (m + 1) := by ring
  have e4 : a + 1 + 2 * m + 4 = a + 1 + 2 * (m + 2) := by ring
  have hp32 : Γ.Adj (T.line.vert (a + 2 + 2 * (m + 1))) (T.line.vert (a + 1 + 2 * (m + 1))) := by
    have := (T.line.adj (a + 1 + 2 * (m + 1))).symm
    rwa [show a + 1 + 2 * (m + 1) + 1 = a + 2 + 2 * (m + 1) by ring] at this
  have hp34 : Γ.Adj (T.line.vert (a + 2 + 2 * (m + 1))) (T.line.vert (a + 1 + 2 * (m + 2))) := by
    have := T.line.adj (a + 2 + 2 * (m + 1))
    rwa [show a + 2 + 2 * (m + 1) + 1 = a + 1 + 2 * (m + 2) by ring] at this
  have n24 : T.line.vert (a + 1 + 2 * (m + 1)) ≠ T.line.vert (a + 1 + 2 * (m + 2)) := by
    have := T.line.nb (a + 1 + 2 * (m + 1))
    rwa [show a + 1 + 2 * (m + 1) + 2 = a + 1 + 2 * (m + 2) by ring] at this
  obtain ⟨ξ, hset3, n2ξ, n4ξ⟩ := exists_third_neighbor (v3 F C (m + 1)) hp32 hp34 n24
  have hp3ξ : Γ.Adj (T.line.vert (a + 2 + 2 * (m + 1))) ξ := by
    have : ξ ∈ Γ.neighborSet (T.line.vert (a + 2 + 2 * (m + 1))) := by rw [hset3]; simp
    exact this
  have el1 := lab_eq_Lb C (m + 1)
  have el2 := lab_eq_Lb C (m + 2)
  obtain ⟨hprod, -, -, -⟩ := three_labels F C.cinv C.val (v3 F C (m + 1)) C.f2 hp32 hp34 hp3ξ
    n24 n2ξ n4ξ
  rw [← el1, ← el2] at hprod
  have hξlab : Lb z α ξ = (lab T z (m + 1) * lab T z (m + 2))⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  have hw1 := lab_mem_nbrStab F C hr0 (j := m + 1) (by omega) (by omega)
  have hw2 := lab_mem_nbrStab F C hr0 (j := m + 2) (by omega) (by omega)
  have hfix : ∀ g, g ∈ nbrStab Γ G α → g • α = α := fun g hg =>
    MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer α hg)
  have hzl := hQ μ l hαμ hμl hlα
  have c0 : ∀ k : G, k • T.line.vert (a + 1 + 2 * m) = T.line.vert (a + 1 + 2 * m) →
      k • T.line.vert (a + 1 + 2 * (m + 1)) = T.line.vert (a + 1 + 2 * (m + 1)) →
      ∀ t : ℤ, (t = 1 ∨ t = 2) →
      Lb z α (k • T.line.vert (a + 1 + 2 * (m + t))) • l = l →
      Lb z α l • T.line.vert (a + 1 + 2 * (m + 1)) = T.line.vert (a + 1 + 2 * (m + 1)) :=
    fun k hk0 hk2 t ht hxi => claim F C m t ht hk0 hk2 hl hzl hxi
  rcases P73.swap_or_fix F hset hll' hlα.symm hαl' (hfix _ hw1) (mem_nbrStab.1 hw1 μ hαμ) with
    ⟨s1, -⟩ | ⟨s1, s1'⟩
  ·
    refine c0 1 (one_smul _ _) (one_smul _ _) 1 (Or.inl rfl) ?_
    rw [one_smul, ← el1]
    exact s1
  rcases P73.swap_or_fix F hset hll' hlα.symm hαl' (hfix _ hw2) (mem_nbrStab.1 hw2 μ hαμ) with
    ⟨s2, -⟩ | ⟨s2, s2'⟩
  ·
    refine c0 1 (one_smul _ _) (one_smul _ _) 2 (Or.inr rfl) ?_
    rw [one_smul, ← el2]
    exact s2
  ·
    obtain ⟨h, hh0, hh2, hh3, hh4⟩ := exists_swapper F h40 T.line (a + 1 + 2 * m)
      (by rw [e3]; exact v3 F C (m + 1)) (by rw [e3]; exact hp3ξ)
      (by rw [e2]; exact fun h => n2ξ h.symm) (by rw [e4]; exact fun h => n4ξ h.symm)
    rw [e2] at hh2
    rw [e4] at hh4
    refine c0 h hh0 hh2 2 (Or.inr rfl) ?_
    rw [hh4, hξlab]
    have : (lab T z (m + 1) * lab T z (m + 2)) • l = l := by
      rw [mul_smul, s2, s1']
    exact (inv_smul_eq_iff.2 this.symm)

end P515

end CFSG.Quasithin.Fan86
