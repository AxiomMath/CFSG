module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam

public section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Gen

variable {D : Type} [Group D]

theorem range_conj_le_K' (A : LieAmalgamExt D) (hsup : A.P1 ⊔ A.P2 = ⊤) :
    (MulAut.conj : D →* MulAut D).range ≤ A.K := by
  have hN1 : A.P1.map (MulAut.conj : D →* MulAut D) ≤ A.N1 := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨A.inn_le ⟨p, rfl⟩, fun x => ?_⟩
    rw [MulAut.conj_apply]
    constructor
    · intro hx
      exact A.P1.mul_mem (A.P1.mul_mem hp hx) (A.P1.inv_mem hp)
    · intro hx
      have := A.P1.mul_mem (A.P1.mul_mem (A.P1.inv_mem hp) hx) hp
      simpa [mul_assoc] using this
  have hN2 : A.P2.map (MulAut.conj : D →* MulAut D) ≤ A.N2 := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨A.inn_le ⟨p, rfl⟩, fun x => ?_⟩
    rw [MulAut.conj_apply]
    constructor
    · intro hx
      exact A.P2.mul_mem (A.P2.mul_mem hp hx) (A.P2.inv_mem hp)
    · intro hx
      have := A.P2.mul_mem (A.P2.mul_mem (A.P2.inv_mem hp) hx) hp
      simpa [mul_assoc] using this
  have h : (⊤ : Subgroup D).map (MulAut.conj : D →* MulAut D) ≤ A.K := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le (hN1.trans A.N1_le_K) (hN2.trans A.N2_le_K)
  rintro _ ⟨d, rfl⟩
  exact h ⟨d, Subgroup.mem_top d, rfl⟩

end Gen

section Main

variable {X : Type} [Group X] [Finite X] {n : ℕ} (R : RankTwoSystem X n)

omit [Finite X] in
theorem P₁_sup_P₂ : R.P₁ ⊔ R.P₂ = ⊤ := by
  by_contra hne
  have hB : R.B ≤ R.P₁ ⊔ R.P₂ := (B_le_P R true).trans le_sup_left
  rcases over_of_ne_top R hB hne with h | h
  · exact not_le_P R false (le_sup_right.trans h)
  · exact not_le_P R true (le_sup_left.trans h)

theorem generation_of_rankTwo [IsSimpleGroup X] (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D]
    (e : X ≃* D) (A : LieAmalgamExt D) : A.P1 ⊔ A.P2 = ⊤ := by
  obtain ⟨e', -, hP | hP⟩ := exists_iso_of_yam R hU e A
  · rw [hP.1, hP.2, ← Subgroup.map_sup, P₁_sup_P₂ R]
    exact Subgroup.map_top_of_surjective _ e'.surjective
  · rw [hP.1, hP.2, ← Subgroup.map_sup, sup_comm, P₁_sup_P₂ R]
    exact Subgroup.map_top_of_surjective _ e'.surjective

theorem range_conj_le_of_rankTwo [IsSimpleGroup X] (hU : IsSylowTwoOf R.U ⊤) {D : Type} [Group D]
    (e : X ≃* D) (A : LieAmalgamExt D) : (MulAut.conj : D →* MulAut D).range ≤ A.K :=
  range_conj_le_K' A (generation_of_rankTwo R hU e A)

end Main

end CFSG.Quasithin.H13.F431.BN
