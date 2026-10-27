module

public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType.QTwo



variable {G : Type} [Group G] [Finite G]

theorem qTwoFrontQ_no_klein {S : Subgroup G} (hS : Nat.card S = 6) {A B : G} (hA : A ∈ S)
    (hB : B ∈ S) (hA2 : A * A = 1) (hB2 : B * B = 1) (hAB : A * B = B * A) (hA1 : A ≠ 1)
    (hB1 : B ≠ 1) (hne : A ≠ B) : False := by
  set T : Subgroup G := Subgroup.closure ({A, B} : Set G) with hT
  have hTS : T ≤ S := (Subgroup.closure_le _).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact hA
    · exact hB)
  have hAT : A ∈ T := Subgroup.subset_closure (by simp)
  have hBT : B ∈ T := Subgroup.subset_closure (by simp)
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have h1 : T ≤ Subgroup.centralizer ({A, B} : Set G) := (Subgroup.closure_le _).mpr (by
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hz with rfl | rfl <;> rcases hh with rfl | rfl
      · rfl
      · exact hAB.symm
      · exact hAB
      · rfl)
    have hxc := Subgroup.mem_centralizer_iff.mp (h1 hx)
    have h2 : T ≤ Subgroup.centralizer ({x} : Set G) := (Subgroup.closure_le _).mpr (by
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rcases hz with rfl | rfl
      · exact (hxc _ (by simp)).symm
      · exact (hxc _ (by simp)).symm)
    have := Subgroup.mem_centralizer_iff.mp (h2 hy) x (by simp)
    exact this
  have hsq : ∀ x ∈ T, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hA2
      · exact hB2
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy := hcomm x hx y hy
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x hx ih =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ih, inv_one]
  have hp : IsPGroup 2 T := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hsq g.1 g.2
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hdvd : Nat.card T ∣ 6 := by
    rw [← hS]; exact Subgroup.card_dvd_of_le hTS
  have h3 : 3 ≤ Nat.card T := by
    let f : Fin 3 → T := ![⟨1, T.one_mem⟩, ⟨A, hAT⟩, ⟨B, hBT⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
        | rfl
        | (exfalso
           simp [f] at hij
           first
           | exact hA1 hij | exact hA1 hij.symm | exact hB1 hij | exact hB1 hij.symm
           | exact hne hij | exact hne hij.symm)
    simpa using Nat.card_le_card_of_injective f hf
  rw [hn] at hdvd h3
  have hn1 : n ≤ 1 := by
    by_contra h
    have h4 : 4 ∣ 2 ^ n := by
      have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
      simpa using this
    have := h4.trans hdvd
    omega
  interval_cases n <;> omega

end CFSG.StandardType.QTwo

end
