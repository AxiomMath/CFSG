module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35AtFin1

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.T1

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin
  CFSG.Quasithin.F53.Stellmacher.S35.At

@[expose] def stepF (T X : Finset (Perm (Fin 5))) : Finset (Perm (Fin 5)) :=
  X ∪ X.biUnion fun x => T.image fun t => x * t

@[expose] def ballF (T : Finset (Perm (Fin 5))) : ℕ → Finset (Perm (Fin 5))
  | 0 => {1}
  | n + 1 => stepF T (ballF T n)

@[expose] def ptF : Finset (Perm (Fin 5)) := Finset.univ.filter fun x => x 4 = 4

set_option maxRecDepth 100000 in
theorem ptF_le_ballF : ∀ x ∈ ptF, x ∉ S5SylF → ptF ⊆ ballF {swap 0 2, swap 1 3, x} 8 := by
  decide +kernel

theorem ptStab_le_of_That_le {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    {K : Subgroup (Perm (Fin 5))} (hT : That D ≤ K) (hK : K ≤ ptStab (fixPt D))
    (hnD : ¬ K ≤ D) : ptStab (fixPt D) ≤ K := by
  obtain ⟨g, rfl, hTg, -, hp⟩ := std_data hD
  rw [hp] at hK ⊢
  obtain ⟨x, hxK, hxD⟩ := Set.not_subset.mp hnD
  have hx4 : (g⁻¹ * x * g) 4 = 4 := by
    have h := mem_ptStab.mp (hK hxK)
    simp only [Perm.mul_apply]
    rw [h]
    simp
  have hxS : g⁻¹ * x * g ∉ S5SylF := by
    intro h
    exact hxD (mem_cj.mpr ((mem_S5Syl_iff _).mpr h))
  have hsub := ptF_le_ballF (g⁻¹ * x * g) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx4⟩) hxS
  intro y hy
  have hy4 : (g⁻¹ * y * g) 4 = 4 := by
    have h := mem_ptStab.mp hy
    simp only [Perm.mul_apply]
    rw [h]
    simp
  have hmem := hsub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy4⟩)
  have key : ∀ n, ∀ z ∈ ballF {swap 0 2, swap 1 3, g⁻¹ * x * g} n, g * z * g⁻¹ ∈ K := by
    intro n
    induction n with
    | zero =>
      intro z hz
      simp only [ballF, Finset.mem_singleton] at hz
      rw [hz]
      simp
    | succ n ih =>
      intro z hz
      simp only [ballF, stepF, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hz
      rcases hz with hz | ⟨a, ha, t, ht, rfl⟩
      · exact ih z hz
      · have h1 := ih a ha
        have h2 : g * t * g⁻¹ ∈ K := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at ht
          rcases ht with rfl | rfl | rfl
          · refine hT ?_
            rw [hTg]
            have h0 : (swap 0 2 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
            exact mem_cj.mpr (by simpa [mul_assoc] using h0)
          · refine hT ?_
            rw [hTg]
            have h0 : (swap 1 3 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
            exact mem_cj.mpr (by simpa [mul_assoc] using h0)
          · simpa [mul_assoc] using hxK
        have := K.mul_mem h1 h2
        simpa [mul_assoc] using this
  have := key 8 _ hmem
  simpa [mul_assoc] using this

theorem exists_act_ep_ne {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {x y : Fin 5}
    (hxy : x ≠ y) : ∃ g ∈ D, orth.act g (ep x y) ≠ ep x y := by
  by_contra h
  push Not at h
  have hP : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD]; norm_num)
  have := (card_le_four_of_fix hP hxy h).1
  omega

end CFSG.Quasithin.F53.Stellmacher.S35.T1
