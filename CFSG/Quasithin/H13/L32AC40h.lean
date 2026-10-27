module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour

public section

namespace CFSG.Quasithin.H13.L32A.C.A5Mod

open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.SL2Modules CFSG.GorensteinWalter
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

variable {k : Type*} [Field k] [Fintype k] [Fintype (ℙ k (Fin 2 → k))]
  [DecidableEq (ℙ k (Fin 2 → k))]

theorem card_fix_upperRootGroup_le (hk : Fintype.card k = 4) :
    Nat.card {w : ↥(evenWeight (ℙ k (Fin 2 → k))) // ∀ g ∈ upperRootGroup k,
      SL2Modules.permAct (MulAction.toPerm g) (w : ℙ k (Fin 2 → k) → ZMod 2) = w} ≤ 2 := by
  classical
  set L₀ := psl2AffinePoint k 0 with hL₀
  have hL₀ne : L₀ ≠ psl2ProjectiveInfinity k := psl2AffinePoint_ne_infinity 0
  have hconst : ∀ w : ↥(evenWeight (ℙ k (Fin 2 → k))), (∀ g ∈ upperRootGroup k,
      SL2Modules.permAct (MulAction.toPerm g) (w : ℙ k (Fin 2 → k) → ZMod 2) = w) →
      ∀ L, L ≠ psl2ProjectiveInfinity k →
        (w : ℙ k (Fin 2 → k) → ZMod 2) L = (w : ℙ k (Fin 2 → k) → ZMod 2) L₀ := by
    intro w hw L hL
    obtain ⟨t, ht, -⟩ := rootGroup_regular L₀ L hL₀ne hL
    have hg : uElt t ∈ upperRootGroup k := (mem_upperRootGroup_iff _).mpr ⟨t, rfl⟩
    have h1 := congrFun (hw _ hg) L
    simp only [SL2Modules.permAct, MulAction.toPerm_symm_apply] at h1
    have hL0 : (uElt t)⁻¹ • L = L₀ := by rw [← ht]; exact inv_smul_smul _ _
    rw [hL0] at h1
    exact h1.symm
  have hinf : ∀ w : ↥(evenWeight (ℙ k (Fin 2 → k))), (∀ g ∈ upperRootGroup k,
      SL2Modules.permAct (MulAction.toPerm g) (w : ℙ k (Fin 2 → k) → ZMod 2) = w) →
      (w : ℙ k (Fin 2 → k) → ZMod 2) (psl2ProjectiveInfinity k) = 0 := by
    intro w hw
    have hsum : ∑ i, (w : ℙ k (Fin 2 → k) → ZMod 2) i = 0 := w.2
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (psl2ProjectiveInfinity k))] at hsum
    have h2 : ∑ i ∈ Finset.univ.erase (psl2ProjectiveInfinity k),
        (w : ℙ k (Fin 2 → k) → ZMod 2) i = ∑ _i ∈ Finset.univ.erase (psl2ProjectiveInfinity k),
          (w : ℙ k (Fin 2 → k) → ZMod 2) L₀ :=
      Finset.sum_congr rfl fun i hi => hconst w hw i (Finset.ne_of_mem_erase hi)
    have hcard : (Finset.univ.erase (psl2ProjectiveInfinity k)).card = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_projectiveLine, hk]
    rw [h2, Finset.sum_const, hcard] at hsum
    have h4 : (4 : ℕ) • (w : ℙ k (Fin 2 → k) → ZMod 2) L₀ = 0 := by
      rw [nsmul_eq_mul, show ((4 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
    simpa [h4] using hsum
  let f : {w : ↥(evenWeight (ℙ k (Fin 2 → k))) // ∀ g ∈ upperRootGroup k,
      SL2Modules.permAct (MulAction.toPerm g) (w : ℙ k (Fin 2 → k) → ZMod 2) = w} → ZMod 2 :=
    fun w => (w.1 : ℙ k (Fin 2 → k) → ZMod 2) L₀
  have hf : Function.Injective f := by
    intro w₁ w₂ h
    apply Subtype.ext
    apply Subtype.ext
    funext L
    by_cases hL : L = psl2ProjectiveInfinity k
    · rw [hL, hinf w₁.1 w₁.2, hinf w₂.1 w₂.2]
    · rw [hconst w₁.1 w₁.2 L hL, hconst w₂.1 w₂.2 L hL]
      exact h
  calc Nat.card _ ≤ Nat.card (ZMod 2) := Nat.card_le_card_of_injective f hf
    _ = 2 := Nat.card_zmod 2

theorem card_fix_le_two (hk : Fintype.card k = 4) (hcard : Nat.card SL(2, k) = 60)
    {P : Subgroup SL(2, k)} (hP : Nat.card P = 4) :
    Nat.card {w : ↥(evenWeight (ℙ k (Fin 2 → k))) // ∀ g ∈ P,
      SL2Modules.permAct (MulAction.toPerm g) (w : ℙ k (Fin 2 → k) → ZMod 2) = w} ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h60 : (Nat.card SL(2, k)).factorization 2 = 2 := by
    rw [hcard, Nat.factorization_def _ Nat.prime_two,
      show (60 : ℕ) = 2 ^ 2 * 15 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hU : Nat.card (upperRootGroup k) = 4 := by
    have hset : ((upperRootGroup k : Subgroup SL(2, k)) : Set SL(2, k)) = Set.range uElt := by
      ext g
      exact mem_upperRootGroup_iff g |>.trans (by
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨t, rfl⟩
        · rintro ⟨t, rfl⟩
          exact ⟨t, rfl⟩)
    have h1 : Nat.card (upperRootGroup k) = Nat.card (Set.range (uElt : k → SL(2, k))) := by
      rw [← hset]
      rfl
    rw [h1, Nat.card_range_of_injective uElt_injective, Nat.card_eq_fintype_card, hk]
  let SU : Sylow 2 SL(2, k) := Sylow.ofCard (upperRootGroup k) (by rw [hU, h60]; norm_num)
  let SP : Sylow 2 SL(2, k) := Sylow.ofCard P (by rw [hP, h60]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, k) SU SP
  have hPg : ∀ p ∈ P, g⁻¹ * p * g ∈ upperRootGroup k := by
    intro p hp
    have hp' : p ∈ ((g • SU : Sylow 2 SL(2, k)) : Subgroup SL(2, k)) := by rw [hg]; exact hp
    rw [Sylow.coe_subgroup_smul] at hp'
    obtain ⟨u, hu, hup⟩ := Subgroup.mem_smul_pointwise_iff_exists p _ _ |>.mp hp'
    have hu' : u ∈ upperRootGroup k := hu
    rw [← hup]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hu'
  let F : {w : ↥(evenWeight (ℙ k (Fin 2 → k))) // ∀ p ∈ P,
      SL2Modules.permAct (MulAction.toPerm p) (w : ℙ k (Fin 2 → k) → ZMod 2) = w} →
      {w : ↥(evenWeight (ℙ k (Fin 2 → k))) // ∀ u ∈ upperRootGroup k,
      SL2Modules.permAct (MulAction.toPerm u) (w : ℙ k (Fin 2 → k) → ZMod 2) = w} := fun w =>
    ⟨⟨SL2Modules.permAct (MulAction.toPerm g⁻¹) (w.1 : ℙ k (Fin 2 → k) → ZMod 2),
      permAct_mem_evenWeight _ w.1.2⟩, fun u hu => by
        have hgu : g * u * g⁻¹ ∈ P := by
          have := (hg ▸ (Sylow.coe_subgroup_smul (g := g) (P := SU)) : _)
          have hmem : g * u * g⁻¹ ∈ ((g • SU : Sylow 2 SL(2, k)) : Subgroup SL(2, k)) := by
            rw [Sylow.coe_subgroup_smul]
            exact ⟨u, hu, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
          rwa [hg] at hmem
        have h1 := w.2 _ hgu
        funext L
        have h2 := congrFun h1 (g • L)
        simp only [SL2Modules.permAct, MulAction.toPerm_symm_apply] at h2 ⊢
        have e : (g * u * g⁻¹)⁻¹ • g • L = g⁻¹⁻¹ • u⁻¹ • L := by
          rw [smul_smul, smul_smul]
          congr 1
          group
        rw [e] at h2
        rw [h2, inv_inv]⟩
  have hF : Function.Injective F := by
    intro w₁ w₂ h
    have h1 := congrArg (fun z => ((z.1 : ↥(evenWeight (ℙ k (Fin 2 → k)))) :
      ℙ k (Fin 2 → k) → ZMod 2)) h
    apply Subtype.ext
    apply Subtype.ext
    funext L
    have h2 := congrFun h1 (g⁻¹ • L)
    simpa [F, SL2Modules.permAct] using h2
  exact (Nat.card_le_card_of_injective F hF).trans (card_fix_upperRootGroup_le hk)

end CFSG.Quasithin.H13.L32A.C.A5Mod
