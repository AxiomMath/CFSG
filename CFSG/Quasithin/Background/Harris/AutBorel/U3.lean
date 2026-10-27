module

public import CFSG.Quasithin.Background.Harris.AutBorel.U3Core
public import CFSG.Quasithin.Background.Harris.AutBorel.FieldNine
public import CFSG.Quasithin.H13.A6S13820AutT

public section

namespace CFSG.Quasithin.Background.Harris.AutBorel

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {f : ℕ} {K : Type} [Field K]

theorem autBorel_hypPSU_sylow (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {S C : Subgroup (hypPSU h 1 1)} {α : MulAut (hypPSU h 1 1)}
    (hB : H13.A6.BorelAut13820 S C α) : (∃ g, α = MulAut.conj g) ∨ f = 3 := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨P₀, hP₀⟩, -, -⟩ :=
    unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
  have hidx : ¬ 2 ∣ S.index := by
    have h2 := hB.1.2.2
    rwa [show (S.subgroupOf ⊤).index = S.relIndex ⊤ from rfl, Subgroup.relIndex_top_right] at h2
  set P : Sylow 2 (hypPSU h 1 1) := hB.1.2.1.toSylow hidx with hP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (hypPSU h 1 1) P P₀
  have hmem : ∀ x, x ∈ hypProjUnitriangular h 1 1 ↔ g⁻¹ * x * g ∈ S := by
    intro x
    have h1 : (P₀ : Subgroup (hypPSU h 1 1)) =
        MulAut.conj g • (P : Subgroup (hypPSU h 1 1)) := by
      rw [← hg]
      rfl
    rw [← hP₀, h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply]
    rfl
  have hSe : S.map (MulAut.conj g).toMonoidHom = hypProjUnitriangular h 1 1 := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [hmem]
      simpa [MulAut.conj_apply, mul_assoc] using hs
    · intro hx
      refine ⟨g⁻¹ * x * g, (hmem x).mp hx, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have h' := H13.A6.Aut20.borelAut_mulEquiv20 (MulAut.conj g) hB
  rw [hSe] at h'
  have hcard : Nat.card K = 2 ^ (2 * f) := h.card
  rcases autBorel_hypPSU h hf (fun σ hσ => sigma_eq_one_of_fix_pow_nine hf hcard σ hσ) h' with
    hi | h3
  · exact Or.inl ((H13.A6.Aut20.inner_congr_iff20 (MulAut.conj g) α).1 hi)
  · exact Or.inr h3

theorem autBorel13820U3_holds : H13.A6.AutBorel13820U3 := by
  intro Q _ _ n hq hZ hn hU S C α h
  have hquot := H13.A6.Aut20.borelAut_quot20 hZ h
  obtain ⟨⟨hp, hf1, -⟩, L, _, _, hL, ⟨e₀⟩⟩ := hU
  have hL' : UnitaryFieldData 2 n L := ⟨hp, hf1, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) hL'
  let ψ : (Q ⧸ Subgroup.center Q) ≃* hypPSU hL' 1 1 :=
    e₀.trans (hypPSUEquivStatedProj hL' hR (by norm_num)).symm
  have : Finite (hypPSU hL' 1 1) := Finite.of_equiv _ ψ.toEquiv
  rcases autBorel_hypPSU_sylow hL' hn (H13.A6.Aut20.borelAut_mulEquiv20 ψ hquot) with hi | h3
  · left
    have : Group.IsPerfect Q := hq.1
    obtain ⟨g, hg⟩ := (H13.A6.Aut20.inner_congr_iff20 ψ _).1 hi
    exact H13.A6.Aut20.inner_of_quot20 hg
  · exact Or.inr h3

end CFSG.Quasithin.Background.Harris.AutBorel
