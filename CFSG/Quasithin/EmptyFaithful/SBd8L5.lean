module

public import CFSG.Quasithin.EmptyFaithful.SBd8L5Pair
public import CFSG.Quasithin.EmptyFaithful.SBd8FlagNine

public section

namespace CFSG.Quasithin

namespace SBd8

namespace L5

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Quasithin.SBd8.Flag

section Std

local macro "hno_tac" : tactic =>
  `(tactic| (intro c hc; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega))

variable {A : Subgroup (MulAut (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))}
  {K : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}

theorem false_two_three (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({2, 3} : Set ℕ)) : False := by
  refine d.not_nine ?_
  rw [hK]
  exact nine_dvd_card_flagStabilizer (a := 0) (b := 3) (by norm_num) (by norm_num) (by norm_num)
    (by simp) (by simp)

theorem false_one_three (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({1, 3} : Set ℕ)) : False := by
  refine d.not_nine ?_
  rw [hK]
  exact nine_dvd_card_flagStabilizer (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)
    (by simp) (by simp)

theorem false_two_four (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({2, 4} : Set ℕ)) : False := by
  refine d.not_nine ?_
  rw [hK]
  exact nine_dvd_card_flagStabilizer (a := 0) (b := 2) (by norm_num) (by norm_num) (by norm_num)
    (by simp) (by simp)

theorem false_one_four (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({1, 4} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 1) (m := 3) (by norm_num) (by norm_num) (Or.inr (by simp))
    (Or.inr (by simp)) (by hno_tac)

theorem false_one_two (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({1, 2} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 2) (m := 3) (by norm_num) (by norm_num) (Or.inr (by simp))
    (Or.inl (by norm_num)) (by hno_tac)

theorem false_three_four (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({3, 4} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 0) (m := 3) (by norm_num) (by norm_num) (Or.inl rfl)
    (Or.inr (by simp)) (by hno_tac)

theorem false_one (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({1} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 1) (m := 4) (by norm_num) (by norm_num) (Or.inr (by simp))
    (Or.inl (by norm_num)) (by hno_tac)

theorem false_two (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({2} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 2) (m := 3) (by norm_num) (by norm_num) (Or.inr (by simp))
    (Or.inl (by norm_num)) (by hno_tac)

theorem false_three (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({3} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 0) (m := 3) (by norm_num) (by norm_num) (Or.inl rfl)
    (Or.inr (by simp)) (by hno_tac)

theorem false_four (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) ({4} : Set ℕ)) : False :=
  false_of_bigBlock d.Y_solv hK (a := 0) (m := 4) (by norm_num) (by norm_num) (Or.inl rfl)
    (Or.inr (by simp)) (by hno_tac)

theorem false_empty (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) (hK : K = flagStabilizer 5 (ZMod 2) (∅ : Set ℕ)) : False :=
  d.K_ne (by rw [hK, flagStabilizer_empty])

theorem false_of_stdData (d : OvgData (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) A
    (unitriangular 5 (ZMod 2)) K) : False := by
  obtain ⟨I, hI, hK⟩ := exists_cuts d
  have hmem : ∀ c ∈ I, c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := fun c hc => by
    have := hI c hc
    omega
  have hst23 : ∀ α ∈ A, (flagStabilizer 5 (ZMod 2) ({2, 3} : Set ℕ)).map α.toMonoidHom =
      flagStabilizer 5 (ZMod 2) ({2, 3} : Set ℕ) := fun α hα => map_pair_two_three (d.A_U α hα)
  have hst14 : ∀ α ∈ A, (flagStabilizer 5 (ZMod 2) ({1, 4} : Set ℕ)).map α.toMonoidHom =
      flagStabilizer 5 (ZMod 2) ({1, 4} : Set ℕ) := fun α hα => map_pair_one_four (d.A_U α hα)
  have hc23 : IsCuts 5 ({2, 3} : Set ℕ) := fun i hi => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  have hc14 : IsCuts 5 ({1, 4} : Set ℕ) := fun i hi => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
    omega
  by_cases h23 : 2 ∈ I ∧ 3 ∈ I
  · have hIeq : I = {2, 3} := eq_of_stable d hI hc23 hK ⟨2, by simp⟩
      (fun c hc => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl
        exacts [h23.1, h23.2]) hst23
    rw [hIeq] at hK
    exact false_two_three d hK
  by_cases h14 : 1 ∈ I ∧ 4 ∈ I
  · have hIeq : I = {1, 4} := eq_of_stable d hI hc14 hK ⟨1, by simp⟩
      (fun c hc => by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        rcases hc with rfl | rfl
        exacts [h14.1, h14.2]) hst14
    rw [hIeq] at hK
    exact false_one_four d hK
  have ext4 : ∀ {J : Set ℕ}, (∀ c, c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 → (c ∈ I ↔ c ∈ J)) →
      (∀ c ∈ J, c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4) → I = J := fun {J} h1 h2 =>
    Set.ext fun c => ⟨fun hc => (h1 c (hmem c hc)).1 hc, fun hc => (h1 c (h2 c hc)).2 hc⟩
  by_cases h1 : 1 ∈ I <;> by_cases h2 : 2 ∈ I <;> by_cases h3 : 3 ∈ I <;> by_cases h4 : 4 ∈ I
  · exact absurd ⟨h2, h3⟩ h23
  · exact absurd ⟨h2, h3⟩ h23
  · exact absurd ⟨h1, h4⟩ h14
  ·
    have hIeq : I = {1, 2} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_one_two d hK
  · exact absurd ⟨h1, h4⟩ h14
  ·
    have hIeq : I = {1, 3} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_one_three d hK
  · exact absurd ⟨h1, h4⟩ h14
  ·
    have hIeq : I = {1} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_one d hK
  · exact absurd ⟨h2, h3⟩ h23
  · exact absurd ⟨h2, h3⟩ h23
  ·
    have hIeq : I = {2, 4} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_two_four d hK
  ·
    have hIeq : I = {2} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_two d hK
  ·
    have hIeq : I = {3, 4} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_three_four d hK
  ·
    have hIeq : I = {3} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_three d hK
  ·
    have hIeq : I = {4} := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp only [Set.mem_singleton_iff] at hc; omega)
    rw [hIeq] at hK
    exact false_four d hK
  ·
    have hIeq : I = ∅ := ext4 (fun c hc => by rcases hc with rfl | rfl | rfl | rfl <;> simp [*])
      (fun c hc => by simp at hc)
    rw [hIeq] at hK
    exact false_empty d hK

end Std

end L5

variable {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {U K : Subgroup X}

theorem famL5 (d : OvgData X A U K)
    (e : X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))) : False := by
  obtain ⟨ψ, hd⟩ := Flag.exists_stdData (n := 5) (by norm_num) d
    (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm)
  exact L5.false_of_stdData hd

end SBd8

end CFSG.Quasithin
