module

public import CFSG.Quasithin.H13.A6S13820AutL2a
public import CFSG.Quasithin.H13.A6S13820AutG2a
public import CFSG.Quasithin.H13.A6S13820AutL3b
public import CFSG.Quasithin.H13.A6S13820AutT

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open CFSG.RankThree.PartOne.KCRootAxis (slFieldAut slFieldAut_apply exists_conj_mul_slFieldAut
  slEquivPSL)
open CFSG.QuasithinUnique (IsSylowTwoOf)

namespace Aut20

variable {F : Type} [Field F]

theorem slFieldAut_mem_U20 (σ : F ≃+* F) {u : SpecialLinearGroup (Fin 2) F}
    (hu : u ∈ unitriangular 2 F) : slFieldAut F σ u ∈ unitriangular 2 F := by
  obtain ⟨hlow, hdiag⟩ := mem_unitriangular.1 hu
  refine mem_unitriangular.2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [slFieldAut_apply, hlow i j hij, map_zero]
  · rw [slFieldAut_apply, hdiag i, map_one]

theorem autBorelL2U20 [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {C : Subgroup (SpecialLinearGroup (Fin 2) F)} {α : MulAut (SpecialLinearGroup (Fin 2) F)}
    (h : BorelAut13820 (unitriangular 2 F) C α) : (∃ g, α = MulAut.conj g) ∨ n = 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨-, -, -, hCn, hidx, -, hαS, hcomm⟩ := h
  obtain ⟨M, σ, hα⟩ := exists_conj_mul_slFieldAut α
  have hαU : ∀ x ∈ unitriangular 2 F, α x ∈ unitriangular 2 F := fun x hx => by
    rw [← hαS]
    exact ⟨x, hx, rfl⟩
  have hMU : ∀ x ∈ unitriangular 2 F, M * x * M⁻¹ ∈ unitriangular 2 F := by
    intro x hx
    have e : M * x * M⁻¹ = α ((slFieldAut F σ)⁻¹ x) := by
      rw [hα, MulAut.mul_apply, MulAut.apply_inv_self, MulAut.conj_apply]
    rw [e]
    exact hαU _ (inv_apply_mem20 _ (fun y hy => slFieldAut_mem_U20 σ hy) hx)
  have hMB := mem_upperTriangular_of_mem_normalizer2_20 (mem_normalizer_of_conj_le20 hMU)
  have hσ : ∀ t : Fˣ, σ ((t : F) ^ 3) = (t : F) ^ 3 := by
    intro t
    have hmem := mem_normalizer_of_upper2_20 (diag2_20_mem_upperTriangular (F := F) t)
    have h1 := hcomm _ (pow_three_mem20 hCn hidx hmem)
    rw [diag2_20_pow, hα, MulAut.mul_apply, MulAut.conj_apply, slFieldAut_diag2_20] at h1
    have hc := comm_mem_unitriangular2_20 hMB
      (diag2_20_mem_upperTriangular (Units.map σ.toRingHom.toMonoidHom (t ^ 3)))
    have hmem3 := mem_normalizer_of_upper2_20 (diag2_20_mem_upperTriangular (F := F) (t ^ 3))
    have h2 := mem_of_conj_mem20 hmem3 hc h1
    rw [diag2_20_inv, diag2_20_mul] at h2
    have h3 := congrArg Units.val (eq_one_of_diag2_mem20 h2)
    rw [Units.val_mul, Units.val_one, Units.coe_map, Units.val_pow_eq_pow_val] at h3
    have h4 : ((t ^ 3 : Fˣ) : F) = σ ((t : F) ^ 3) := by
      have := congrArg (fun z => ((t ^ 3 : Fˣ) : F) * z) h3
      simp only [mul_one, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        one_mul] at this
      rw [← this]
      simp
    rw [← h4, Units.val_pow_eq_pow_val]
  rcases sigma_eq_one_of_fix_cubes20 hn hF σ hσ with rfl | h2
  · left
    rw [map_one, mul_one] at hα
    exact ⟨M, hα⟩
  · exact Or.inr h2

theorem autBorelL2_20 [Finite F] [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {S C : Subgroup (SpecialLinearGroup (Fin 2) F)} {α : MulAut (SpecialLinearGroup (Fin 2) F)}
    (h : BorelAut13820 S C α) : (∃ g, α = MulAut.conj g) ∨ n = 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨x, hx⟩ := exists_map_conj_eq20 h.1 (isSylowTwoOf_U2_20 (F := F))
  have h' := borelAut_mulEquiv20 (MulAut.conj x) h
  rw [hx] at h'
  rcases autBorelL2U20 hn hF h' with hi | h2
  · exact Or.inl ((inner_congr_iff20 (MulAut.conj x) α).1 hi)
  · exact Or.inr h2

end Aut20

theorem autBorel13820L2_holds : AutBorel13820L2 := by
  intro Q _ _ n hq hZ hn hL S C α h
  classical
  have hquot := Aut20.borelAut_quot20 hZ h
  obtain ⟨-, F, _, _, hcard, ⟨e⟩⟩ := hL
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  have : Fintype F := Fintype.ofFinite F
  let ψ : (Q ⧸ Subgroup.center Q) ≃* SpecialLinearGroup (Fin 2) F :=
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).trans
      (slEquivPSL F).symm
  rcases Aut20.autBorelL2_20 hn hcard (Aut20.borelAut_mulEquiv20 ψ hquot) with hi | h2
  · left
    have : Group.IsPerfect Q := hq.1
    obtain ⟨g, hg⟩ := (Aut20.inner_congr_iff20 ψ _).1 hi
    exact Aut20.inner_of_quot20 hg
  · exact Or.inr h2

end CFSG.Quasithin.H13.A6
