module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18ModU4OuterClsWedge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open CFSG.SeitzReduction.F4Pilot (omIsoGroup statedOmega_le_omIsoGroup)
open CFSG.QuasithinUnique.Setup.Family (card_range_displacement)
open scoped commutatorElement Pointwise Matrix

private theorem adjWedge_base_ne_zero {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  intro hb
  have hring : ringChar F = 2 := (ringChar.eq F 2)
  obtain ⟨s, hs⟩ := FiniteField.isSquare_of_char_two hring c
  apply hirr s
  rw [hb, zero_mul, add_zero, hs, pow_two]
  exact CharTwo.add_self_eq_zero (s * s)

theorem four_mul_le_rkIdx_adjAct {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {g : ↥(omIsoGroup (StatedQuadMinus 3 F b c))} (hg : g * g = 1) (hg1 : g ≠ 1) :
    4 * n ≤ rkIdx (fixV (Subgroup.zpowers (adjAct F b c g))) := by
  classical
  have hb : b ≠ 0 := adjWedge_base_ne_zero hirr
  let t : MulAut (Multiplicative ↥(adjOmega6 F b)) := adjAct F b c g
  let M : Matrix Om6Idx Om6Idx F := ((g : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)
  have hM : M * M = 1 := by
    have := congrArg (fun h : ↥(omIsoGroup (StatedQuadMinus 3 F b c)) =>
      ((h : GL Om6Idx F) : Matrix Om6Idx Om6Idx F)) hg
    simpa [M] using this
  have hx_ex : ∃ x : Om6Idx → F, M *ᵥ x ≠ x := by
    by_contra h
    push Not at h
    apply hg1
    have hM1 : M = 1 := by
      ext i j
      have h2 := congrFun (h (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
      simpa [Pi.single_apply, Matrix.one_apply] using h2
    apply Subtype.ext
    apply Units.ext
    ext i j
    simpa [M] using congrFun (congrFun hM1 i) j
  obtain ⟨x, hx⟩ := hx_ex
  let I := Multiplicative ↥(adjOmega6 F b)
  haveI : Finite I := by
    dsimp [I]
    infer_instance
  haveI : Fact (∀ s : I, s * s = 1) := ⟨fun s => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_one]
    ext i j
    exact CharTwo.add_self_eq_zero _⟩
  let Ψ : (Om6Idx → F) → I := fun w => t (adjWedge b x w) * (adjWedge b x w)⁻¹
  let K : Submodule F (Om6Idx → F) := Submodule.span F {x, M *ᵥ x - x}
  have hfiber : ∀ w w' : Om6Idx → F, Ψ w = Ψ w' → w - w' ∈ K := by
    intro w w' hww'
    have hA : adjWedge b x (w - w') = adjWedge b x w * (adjWedge b x w')⁻¹ := by
      have h := adjWedge_add_right b x (w - w') w'
      rw [sub_add_cancel] at h
      rw [h, mul_assoc, mul_inv_cancel, mul_one]
    have hfix : t (adjWedge b x (w - w')) = adjWedge b x (w - w') := by
      rw [hA]
      apply Multiplicative.toAdd.injective
      have h0 := congrArg Multiplicative.toAdd hww'
      simp only [Ψ, toAdd_mul, toAdd_inv] at h0
      rw [map_mul, map_inv]
      simp only [toAdd_mul, toAdd_inv]
      have h0' : Multiplicative.toAdd (t (adjWedge b x w)) -
          Multiplicative.toAdd (adjWedge b x w) =
          Multiplicative.toAdd (t (adjWedge b x w')) -
            Multiplicative.toAdd (adjWedge b x w') := by
        simpa only [sub_eq_add_neg] using h0
      simpa only [sub_eq_add_neg] using sub_eq_sub_iff_sub_eq_sub.mp h0'
    have hW : adjWedge b (M *ᵥ x) (M *ᵥ (w - w')) = adjWedge b x (w - w') := by
      have h := adjAct_adjWedge hb g x (w - w')
      exact h.symm.trans hfix
    have hmat : ((Multiplicative.toAdd (adjWedge b (M *ᵥ x) (M *ᵥ (w - w'))) :
        ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F) =
        ((Multiplicative.toAdd (adjWedge b x (w - w')) : ↥(adjOmega6 F b)) :
          Matrix Om6Idx Om6Idx F) := by
      exact congrArg (fun z : I =>
        ((Multiplicative.toAdd z : ↥(adjOmega6 F b)) : Matrix Om6Idx Om6Idx F)) hW
    rw [toAdd_adjWedge hb, toAdd_adjWedge hb] at hmat
    rw [adjPolar_mulVec g x (w - w')] at hmat
    exact mem_span_of_wedge_mulVec_eq hM hx (sub_left_injective hmat)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hx
    rw [h0, Matrix.mulVec_zero]
  have hli : LinearIndependent F ![x, M *ᵥ x - x] := by
    rw [LinearIndependent.pair_iff' hx0]
    intro a ha
    have h1 : M *ᵥ x = a • x + x := by
      rw [ha]
      exact (sub_add_cancel _ _).symm
    have hMx : M *ᵥ x = (a + 1) • x := by
      rw [h1, add_smul, one_smul]
    have hsq : (a + 1) * (a + 1) = 1 := by
      have h2 : x = ((a + 1) * (a + 1)) • x := by
        calc x = M *ᵥ (M *ᵥ x) := by rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
          _ = M *ᵥ ((a + 1) • x) := by rw [hMx]
          _ = (a + 1) • (M *ᵥ x) := by rw [Matrix.mulVec_smul]
          _ = (a + 1) • ((a + 1) • x) := by rw [hMx]
          _ = ((a + 1) * (a + 1)) • x := by rw [smul_smul]
      have h3 : ((a + 1) * (a + 1) - 1) • x = 0 := by
        rw [sub_smul, one_smul, h2.symm, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right hx0)
    have ha0 : a = 0 := by
      have h4 : (a + 1) * (a + 1) = a * a + 1 := by
        calc (a + 1) * (a + 1) = a * a + a * 1 + 1 * a + 1 * 1 := by ring
          _ = a * a + a + a + 1 := by ring
          _ = a * a + (a + a) + 1 := by ring
          _ = a * a + 0 + 1 := by rw [CharTwo.add_self_eq_zero]
          _ = a * a + 1 := by ring
      have h5 : a * a + 1 = 1 := by rwa [h4] at hsq
      have h6 : a * a + 1 = 0 + 1 := by simpa using h5
      exact mul_self_eq_zero.mp (add_right_cancel h6)
    rw [ha0, zero_smul] at ha
    exact hx (sub_eq_zero.mp ha.symm)
  have hKfin : Module.finrank F K = 2 := by
    have hrange : Set.range ![x, M *ᵥ x - x] = {x, M *ᵥ x - x} := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    have h := finrank_span_eq_card hli
    rw [hrange] at h
    simpa [K] using h
  have hKcard : Nat.card K = (Nat.card F) ^ 2 := by
    haveI : Module.Finite F K := Module.finite_of_finrank_pos (by omega)
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), hKfin]
  have hsubset : Set.range Ψ ⊆ Set.range (fun v : I => t v * v⁻¹) := by
    rintro y ⟨w, rfl⟩
    exact ⟨adjWedge b x w, rfl⟩
  have hrange_le : Nat.card (Set.range Ψ) ≤ 2 ^ disp t := by
    have h := Nat.card_le_card_of_injective (Set.inclusion hsubset)
      (Set.inclusion_injective hsubset)
    rw [card_range_displacement t] at h
    exact h
  let σ : Set.range Ψ → (Om6Idx → F) := fun y => Classical.choose y.2
  have hσ : ∀ y : Set.range Ψ, Ψ (σ y) = y.1 := fun y => Classical.choose_spec y.2
  let f : Set.range Ψ × K → (Om6Idx → F) := fun p => σ p.1 + (p.2 : Om6Idx → F)
  have hf : Function.Surjective f := by
    intro v
    let y : Set.range Ψ := ⟨Ψ v, ⟨v, rfl⟩⟩
    refine ⟨(y, ⟨v - σ y, ?_⟩), ?_⟩
    · exact hfiber v (σ y) (by simpa using (hσ y).symm)
    · show σ y + (v - σ y) = v
      abel
  have hVle : Nat.card (Om6Idx → F) ≤ Nat.card (Set.range Ψ) * Nat.card K := by
    haveI : Finite (Set.range Ψ × K) := inferInstance
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective f hf
  have hVcard : Nat.card (Om6Idx → F) = (Nat.card F) ^ 6 := by
    rw [Nat.card_fun]
    congr 1
    simp only [Om6Idx, Nat.card_sum, Nat.card_fin]
  have hpow : (2 : ℕ) ^ (6 * n) ≤ 2 ^ (disp t + 2 * n) := by
    calc 2 ^ (6 * n) = (Nat.card F) ^ 6 := by
          rw [hF, ← pow_mul, Nat.mul_comm n 6]
      _ = Nat.card (Om6Idx → F) := hVcard.symm
      _ ≤ Nat.card (Set.range Ψ) * Nat.card K := hVle
      _ ≤ 2 ^ disp t * (Nat.card F) ^ 2 := by
          rw [hKcard]
          exact Nat.mul_le_mul_right _ hrange_le
      _ = 2 ^ disp t * 2 ^ (2 * n) := by
          rw [hF, ← pow_mul, Nat.mul_comm n 2]
      _ = 2 ^ (disp t + 2 * n) := by rw [pow_add]
  have h6 : 6 * n ≤ disp t + 2 * n :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
  have h4 : 4 * n ≤ disp t := by omega
  rw [Thm14_5.rkIdx_fixV_zpowers_eq_disp]
  exact h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
