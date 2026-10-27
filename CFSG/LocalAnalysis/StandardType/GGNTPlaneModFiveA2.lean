module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

open scoped Matrix

private def xRep : X3 := ![0, 0, 0, 1, 0, 0]

private theorem xRep_eq_reps : xRep = reps 3 := rfl

private def compH : Fin 3 → Fin Tag.E6.rank → ℤ
  | 0 => ![0, 0, 0, -1, 1, 1]
  | 1 => ![0, 1, 0, 0, 0, 0]
  | 2 => ![1, 0, 1, -1, 0, 0]

private def pRoot : Fin 3 → Fin Tag.E6.rank → ℤ
  | 0 => ![0, 0, 0, 0, 0, 1]
  | 1 => ![0, 1, 0, 0, 0, 0]
  | 2 => ![0, 0, 1, 0, 0, 0]

private def qRoot : Fin 3 → Fin Tag.E6.rank → ℤ
  | 0 => ![0, 0, 0, 0, 1, 0]
  | 1 => ![1, 1, 2, 3, 2, 1]
  | 2 => ![1, 0, 0, 0, 0, 0]

private def pairEnum (p q : Fin Tag.E6.rank → ℤ) : Fin 6 → Fin Tag.E6.rank → ℤ :=
  ![p, -p, q, -q, p + q, -(p + q)]

private def psiPair (p q : Fin Tag.E6.rank → ℤ) : Finset (Fin Tag.E6.rank → ℤ) :=
  Finset.univ.image (pairEnum p q)

private def psi (j : Fin 3) : Finset (Fin Tag.E6.rank → ℤ) := psiPair (pRoot j) (qRoot j)

open scoped CFSG.Decide.Bounded

private theorem psi_subset :
    ∀ (j : Fin 3) (γ : Fin Tag.E6.rank → ℤ), γ ∈ psi j →
      γ ∈ e6RootList ∧ pairVec xRep γ = 0 := by
  decide +kernel

private theorem dot_eq_zero_of_mem_psi_of_ne :
    ∀ (j l : Fin 3), l ≠ j → ∀ γ : Fin Tag.E6.rank → ℤ, γ ∈ psi j → compH l ⬝ᵥ γ = 0 := by
  decide +kernel

private theorem dot_ne_zero_of_mem_psi :
    ∀ (j : Fin 3) (γ : Fin Tag.E6.rank → ℤ), γ ∈ psi j → compH j ⬝ᵥ γ ≠ 0 := by
  decide +kernel

private theorem dot_ne_zero_of_mem_kerRoots :
    ∀ α : Fin Tag.E6.rank → ℤ, α ∈ e6RootList → pairVec xRep α = 0 →
      compH 0 ⬝ᵥ α ≠ 0 ∨ compH 1 ⬝ᵥ α ≠ 0 ∨ compH 2 ⬝ᵥ α ≠ 0 := by
  decide +kernel

private theorem dot_eq_zero_of_ne_of_dot_ne_zero :
    ∀ (j : Fin 3) (α : Fin Tag.E6.rank → ℤ), α ∈ e6RootList → pairVec xRep α = 0 →
      compH j ⬝ᵥ α ≠ 0 → ∀ l : Fin 3, l ≠ j → compH l ⬝ᵥ α = 0 := by
  decide +kernel

private theorem mem_psi_of_dot_ne_zero :
    ∀ (j : Fin 3) (α : Fin Tag.E6.rank → ℤ), α ∈ e6RootList → pairVec xRep α = 0 →
      compH j ⬝ᵥ α ≠ 0 → α ∈ psi j := by
  decide +kernel

private theorem pairEnum_inj (j : Fin 3) :
    ∀ a b : Fin 6, pairEnum (pRoot j) (qRoot j) a = pairEnum (pRoot j) (qRoot j) b → a = b := by
  fin_cases j <;> decide +kernel

private theorem pRoot_mem_psi (j : Fin 3) : pRoot j ∈ psi j := by
  refine Finset.mem_image.mpr ⟨0, Finset.mem_univ 0, ?_⟩
  rfl

private theorem sum_psi_eq (j : Fin 3) (f : (Fin Tag.E6.rank → ℤ) → ZMod 5) :
    ∑ γ ∈ psi j, f γ =
      f (pRoot j) + f (-pRoot j) + f (qRoot j) + f (-qRoot j) +
        f (pRoot j + qRoot j) + f (-(pRoot j + qRoot j)) := by
  rw [show psi j = Finset.univ.image (pairEnum (pRoot j) (qRoot j)) from rfl,
    Finset.sum_image (fun a _ b _ h => pairEnum_inj j a b h), Fin.sum_univ_six]
  rfl

private theorem sum_sq_psi (j : Fin 3) (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) :
    ∑ γ ∈ psi j, (μ γ) ^ 2 =
      2 * ((μ (pRoot j)) ^ 2 + (μ (qRoot j)) ^ 2 + (μ (pRoot j + qRoot j)) ^ 2) := by
  rw [sum_psi_eq]
  simp only [map_neg]
  ring

private theorem quadratic_eq_zero :
    ∀ P Q : ZMod 5, 2 * (P ^ 2 + Q ^ 2 + (P + Q) ^ 2) = 0 → P = 0 ∧ Q = 0 := by
  decide +kernel

private theorem zmod5_two_two_two : (2 * 2 * 2 : ZMod 5) = 3 := by decide

private theorem zmod5_eight_mul_two : (8 : ZMod 5) * 2 = 1 := by decide

private theorem zmod5_three_mul_two : (3 : ZMod 5) * 2 = 1 := by decide

private theorem kerReflVec_smul_mem_psi_aux {r : WeylGroup Tag.E6} (hr : r ∈ kerReflVec xRep) :
    ∀ (j : Fin 3) (γ : Fin Tag.E6.rank → ℤ), γ ∈ psi j → r • γ ∈ psi j ∧ r⁻¹ • γ ∈ psi j := by
  rw [kerReflVec] at hr
  refine Subgroup.closure_induction (p := fun r _ => ∀ (j : Fin 3) (γ : Fin Tag.E6.rank → ℤ),
    γ ∈ psi j → r • γ ∈ psi j ∧ r⁻¹ • γ ∈ psi j) ?_ ?_ ?_ ?_ hr
  · rintro r ⟨w, i, hmem, rfl⟩
    intro j γ hγ
    obtain ⟨hγlist, hγ0⟩ := psi_subset j γ hγ
    have hγroot : IsRoot Tag.E6 γ := (isRoot_iff_mem_e6RootList γ).2 hγlist
    have hγj : compH j ⬝ᵥ γ ≠ 0 := dot_ne_zero_of_mem_psi j γ hγ
    have hγl : ∀ l : Fin 3, l ≠ j → compH l ⬝ᵥ γ = 0 :=
      fun l hl => dot_eq_zero_of_mem_psi_of_ne j l hl γ hγ
    have hβroot : IsRoot Tag.E6 (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) := hmem.1
    have hβ0 : pairVec xRep (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 := hmem.2
    have hβlist : w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∈ e6RootList :=
      (isRoot_iff_mem_e6RootList _).1 hβroot
    have hrγroot : IsRoot Tag.E6 ((w * simple Tag.E6 i * w⁻¹) • γ) := IsRoot.smul hγroot _
    have hrγ0 : pairVec xRep ((w * simple Tag.E6 i * w⁻¹) • γ) = 0 := by
      rw [conj_simple_smul, pairVec_sub, pairVec_zsmul, hγ0, hβ0]
      simp
    have hrγlist : (w * simple Tag.E6 i * w⁻¹) • γ ∈ e6RootList :=
      (isRoot_iff_mem_e6RootList _).1 hrγroot
    have hrinv : (w * simple Tag.E6 i * w⁻¹)⁻¹ = w * simple Tag.E6 i * w⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, CoxeterSystem.inv_simple, mul_assoc]
    have hmain : (w * simple Tag.E6 i * w⁻¹) • γ ∈ psi j := by
      by_cases hjβ : compH j ⬝ᵥ (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ≠ 0
      · have hzero : ∀ l : Fin 3, l ≠ j →
            compH l ⬝ᵥ ((w * simple Tag.E6 i * w⁻¹) • γ) = 0 := by
          intro l hl
          rw [conj_simple_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hγl l hl,
            dot_eq_zero_of_ne_of_dot_ne_zero j _ hβlist hβ0 hjβ l hl, mul_zero, sub_zero]
        have hcov := dot_ne_zero_of_mem_kerRoots _ hrγlist hrγ0
        have hnj : compH j ⬝ᵥ ((w * simple Tag.E6 i * w⁻¹) • γ) ≠ 0 := by
          rcases hcov with h | h | h
          · by_cases hj : j = 0
            · simpa [hj] using h
            · exact absurd (hzero 0 (Ne.symm hj)) h
          · by_cases hj : j = 1
            · simpa [hj] using h
            · exact absurd (hzero 1 (Ne.symm hj)) h
          · by_cases hj : j = 2
            · simpa [hj] using h
            · exact absurd (hzero 2 (Ne.symm hj)) h
        exact mem_psi_of_dot_ne_zero j _ hrγlist hrγ0 hnj
      · have hjβ0 : compH j ⬝ᵥ (w • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 :=
          not_not.mp hjβ
        have heq : compH j ⬝ᵥ ((w * simple Tag.E6 i * w⁻¹) • γ) = compH j ⬝ᵥ γ := by
          rw [conj_simple_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul, hjβ0, mul_zero,
            sub_zero]
        exact mem_psi_of_dot_ne_zero j _ hrγlist hrγ0 (by rw [heq]; exact hγj)
    refine ⟨hmain, ?_⟩
    rwa [hrinv]
  · intro j γ hγ
    exact ⟨by simpa using hγ, by simpa using hγ⟩
  · intro r s _ _ hr' hs' j γ hγ
    refine ⟨?_, ?_⟩
    · rw [mul_smul]
      exact (hr' j (s • γ) (hs' j γ hγ).1).1
    · rw [mul_inv_rev, mul_smul]
      exact (hs' j (r⁻¹ • γ) (hr' j γ hγ).2).2
  · intro r _ hr' j γ hγ
    exact ⟨(hr' j γ hγ).2, by simpa only [inv_inv] using (hr' j γ hγ).1⟩

private theorem kerReflVec_smul_mem_psi {r : WeylGroup Tag.E6} (hr : r ∈ kerReflVec xRep)
    (j : Fin 3) {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ psi j) : r • γ ∈ psi j :=
  (kerReflVec_smul_mem_psi_aux hr j γ hγ).1

private def u0List : List (Fin Tag.E6.rank) :=
  [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨1, by decide⟩,
   ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩]

private def u0 : WeylGroup Tag.E6 := (u0List.map (simple Tag.E6)).prod

private theorem applyWord_u0List : applyWord u0List xRep = xRep := by
  decide +kernel

private def vecWord (l : List (Fin Tag.E6.rank)) (v : Fin Tag.E6.rank → ℤ) :
    Fin Tag.E6.rank → ℤ :=
  l.foldr (fun i w => reflect Tag.E6 i w) v

private theorem prod_simple_smul_eq_vecWord (l : List (Fin Tag.E6.rank))
    (v : Fin Tag.E6.rank → ℤ) :
    (l.map (simple Tag.E6)).prod • v = vecWord l v := by
  induction l with
  | nil => simp [vecWord]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, mul_smul, ih, simple_smul]
    rfl

private theorem vecWord_u0List : vecWord u0List (pRoot 0) = pRoot 1 := by
  decide +kernel

private theorem u0_smul_xRep : u0 • xRep = xRep := by
  show (u0List.map (simple Tag.E6)).prod • xRep = xRep
  rw [← applyWord_eq_prod_smul, applyWord_u0List]

private theorem u0_smul_pRoot : u0 • pRoot 0 = pRoot 1 := by
  show (u0List.map (simple Tag.E6)).prod • pRoot 0 = pRoot 1
  rw [prod_simple_smul_eq_vecWord, vecWord_u0List]

private theorem u0_mem_stabVec : u0 ∈ stabVec xRep := by
  show u0 ∈ MulAction.stabilizer (WeylGroup Tag.E6) xRep
  rw [MulAction.mem_stabilizer_iff]
  exact u0_smul_xRep

private theorem not_mem_kerReflVec_u0 : u0 ∉ kerReflVec xRep := by
  intro hu
  have hmem : pRoot 1 ∈ psi 0 := by
    have h := kerReflVec_smul_mem_psi hu 0 (pRoot_mem_psi 0)
    rwa [u0_smul_pRoot] at h
  have hne : compH 0 ⬝ᵥ pRoot 1 ≠ 0 := dot_ne_zero_of_mem_psi 0 (pRoot 1) hmem
  have hzero : compH 0 ⬝ᵥ pRoot 1 = 0 := by decide +kernel
  exact hne hzero

private theorem index_kerReflVec_subgroupOf :
    ((kerReflVec xRep).subgroupOf (stabVec xRep)).index = 3 := by
  have ht : TableVec xRep := by
    rw [xRep_eq_reps]
    exact tableVec_rep 3
  rcases ht with hEq | ⟨-, hidx⟩
  · exfalso
    exact not_mem_kerReflVec_u0 (by rw [hEq]; exact u0_mem_stabVec)
  · exact hidx

private theorem normal_subgroupOf_kerReflVec :
    ((kerReflVec xRep).subgroupOf (stabVec xRep)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (kerReflVec_le_stabVec xRep)]
  intro h k hh hk
  have hk' : k • xRep = xRep := MulAction.mem_stabilizer_iff.mp hk
  have hkmap : kerReflVec xRep = (kerReflVec xRep).map (MulAut.conj k).toMonoidHom := by
    rw [← kerReflVec_smul k xRep, hk']
  rw [hkmap]
  exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩

private theorem pow_three_mem_kerReflVec
    {w : WeylGroup Tag.E6} (hw : w ∈ stabVec xRep) :
    w ^ 3 ∈ kerReflVec xRep := by
  haveI : ((kerReflVec xRep).subgroupOf (stabVec xRep)).Normal := normal_subgroupOf_kerReflVec
  have hpow : (⟨w, hw⟩ : stabVec xRep) ^ ((kerReflVec xRep).subgroupOf (stabVec xRep)).index ∈
      (kerReflVec xRep).subgroupOf (stabVec xRep) :=
    Subgroup.pow_index_mem _ _
  rw [index_kerReflVec_subgroupOf] at hpow
  rw [Subgroup.mem_subgroupOf] at hpow
  simpa using hpow

private theorem mu_pow_three {μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5} {w : WeylGroup Tag.E6}
    (hμ : ∀ v, μ (w • v) = 2 * μ v) (v : Fin Tag.E6.rank → ℤ) :
    μ ((w ^ 3) • v) = 3 * μ v := by
  rw [pow_three, mul_smul, mul_smul, hμ, hμ, hμ]
  have hc : (2 * 2 * 2 : ZMod 5) = 3 := zmod5_two_two_two
  calc 2 * (2 * (2 * μ v)) = (2 * 2 * 2) * μ v := by ring
    _ = 3 * μ v := by rw [hc]

private theorem sum_sq_eq_zero
    {μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5} {w : WeylGroup Tag.E6}
    (hw : w ∈ stabVec xRep) (hμ : ∀ v, μ (w • v) = 2 * μ v) (j : Fin 3) :
    ∑ γ ∈ psi j, (μ γ) ^ 2 = 0 := by
  have h3 : w ^ 3 ∈ kerReflVec xRep := pow_three_mem_kerReflVec hw
  have h3inv : (w ^ 3)⁻¹ ∈ kerReflVec xRep := (kerReflVec xRep).inv_mem h3
  have hbij : ∑ γ ∈ psi j, (μ ((w ^ 3) • γ)) ^ 2 = ∑ γ ∈ psi j, (μ γ) ^ 2 := by
    refine Finset.sum_nbij' (fun γ => (w ^ 3) • γ) (fun γ => (w ^ 3)⁻¹ • γ) ?_ ?_ ?_ ?_ ?_
    · exact fun γ hγ => kerReflVec_smul_mem_psi h3 j hγ
    · exact fun γ hγ => kerReflVec_smul_mem_psi h3inv j hγ
    · exact fun γ _ => inv_smul_smul (w ^ 3) γ
    · exact fun γ _ => smul_inv_smul (w ^ 3) γ
    · exact fun γ _ => rfl
  have hstep : ∑ γ ∈ psi j, (μ ((w ^ 3) • γ)) ^ 2 = ∑ γ ∈ psi j, (3 * μ γ) ^ 2 := by
    exact Finset.sum_congr rfl fun γ _ => by rw [mu_pow_three hμ γ]
  have h9 : ∑ γ ∈ psi j, (3 * μ γ) ^ 2 = 9 * ∑ γ ∈ psi j, (μ γ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun γ _ => by ring
  have hS : ∑ γ ∈ psi j, (μ γ) ^ 2 = 9 * ∑ γ ∈ psi j, (μ γ) ^ 2 :=
    calc ∑ γ ∈ psi j, (μ γ) ^ 2
        = ∑ γ ∈ psi j, (μ ((w ^ 3) • γ)) ^ 2 := hbij.symm
      _ = ∑ γ ∈ psi j, (3 * μ γ) ^ 2 := hstep
      _ = 9 * ∑ γ ∈ psi j, (μ γ) ^ 2 := h9
  have h8 : (8 : ZMod 5) * (∑ γ ∈ psi j, (μ γ) ^ 2) = 0 := by
    have h8eq : (8 : ZMod 5) * (∑ γ ∈ psi j, (μ γ) ^ 2) =
        9 * (∑ γ ∈ psi j, (μ γ) ^ 2) - (∑ γ ∈ psi j, (μ γ) ^ 2) := by ring
    rw [h8eq, ← hS, sub_self]
  calc ∑ γ ∈ psi j, (μ γ) ^ 2
      = ((8 : ZMod 5) * 2) * (∑ γ ∈ psi j, (μ γ) ^ 2) := by
          rw [zmod5_eight_mul_two, one_mul]
    _ = (8 : ZMod 5) * (∑ γ ∈ psi j, (μ γ) ^ 2) * 2 := by ring
    _ = 0 := by rw [h8, zero_mul]

private def eRoot (i : Fin 6) : Fin Tag.E6.rank → ℤ := Pi.single i 1

theorem modFive_eq_zero_of_mem_stabVec_rep_three
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5)
    {w : WeylGroup Tag.E6} (hw : w ∈ stabVec (reps 3))
    (hμ : ∀ v, μ (w • v) = 2 * μ v) : μ = 0 := by
  have hpq : ∀ j : Fin 3, μ (pRoot j) = 0 ∧ μ (qRoot j) = 0 := by
    intro j
    have h := sum_sq_eq_zero hw hμ j
    rw [sum_sq_psi j μ, map_add] at h
    exact quadratic_eq_zero (μ (pRoot j)) (μ (qRoot j)) h
  have he0 : μ (eRoot 0) = 0 := by
    rw [show eRoot 0 = qRoot 2 from by decide +kernel]
    exact (hpq 2).2
  have he1 : μ (eRoot 1) = 0 := by
    rw [show eRoot 1 = pRoot 1 from by decide +kernel]
    exact (hpq 1).1
  have he2 : μ (eRoot 2) = 0 := by
    rw [show eRoot 2 = pRoot 2 from by decide +kernel]
    exact (hpq 2).1
  have he4 : μ (eRoot 4) = 0 := by
    rw [show eRoot 4 = qRoot 0 from by decide +kernel]
    exact (hpq 0).2
  have he5 : μ (eRoot 5) = 0 := by
    rw [show eRoot 5 = pRoot 0 from by decide +kernel]
    exact (hpq 0).1
  have hq1 : qRoot 1 = eRoot 0 + eRoot 1 + (2 : ℤ) • eRoot 2 + (3 : ℤ) • eRoot 3 +
      (2 : ℤ) • eRoot 4 + eRoot 5 := by
    decide +kernel
  have he3 : μ (eRoot 3) = 0 := by
    have h := (hpq 1).2
    rw [hq1, map_add, map_add, map_add, map_add, map_add, map_zsmul, map_zsmul, map_zsmul,
      he0, he1, he2, he4, he5] at h
    have h' : (3 : ℤ) • μ (eRoot 3) = 0 := by
      have h2 := h
      rw [smul_zero] at h2
      simp only [zero_add, add_zero] at h2
      exact h2
    have h3 : (3 : ZMod 5) * μ (eRoot 3) = 0 := by
      rw [zsmul_eq_mul] at h'
      simpa using h'
    calc μ (eRoot 3) = ((3 : ZMod 5) * 2) * μ (eRoot 3) := by
          rw [zmod5_three_mul_two, one_mul]
      _ = (3 : ZMod 5) * μ (eRoot 3) * 2 := by ring
      _ = 0 := by rw [h3, zero_mul]
  have hsingle : ∀ i : Fin Tag.E6.rank, μ (Pi.single i 1) = 0 := by
    intro i
    fin_cases i
    · show μ (eRoot 0) = 0
      exact he0
    · show μ (eRoot 1) = 0
      exact he1
    · show μ (eRoot 2) = 0
      exact he2
    · show μ (eRoot 3) = 0
      exact he3
    · show μ (eRoot 4) = 0
      exact he4
    · show μ (eRoot 5) = 0
      exact he5
  refine AddMonoidHom.ext fun v => ?_
  rw [pi_eq_sum v, map_sum μ]
  exact Finset.sum_eq_zero fun i _ => by
    rw [map_zsmul, hsingle i]
    exact smul_zero (v i)

private theorem ncard_isRoot_eq_72 :
    Set.ncard {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} = 72 := by
  have hset : {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} = {α | α ∈ e6RootList} := by
    ext α
    simp [isRoot_iff_mem_e6RootList]
  have hset' : {α : Fin Tag.E6.rank → ℤ | α ∈ e6RootList} = ↑e6RootList.toFinset := by
    ext α
    simp
  rw [hset, hset', Set.ncard_coe_finset]
  decide +kernel

theorem modFive_eq_zero_of_ncard_kerRoots_eq_eighteen
    {x : X3} (hx : (kerRoots x).ncard = 18)
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w : WeylGroup Tag.E6} (hw : w ∈ stabVec x)
    (hμ : ∀ v, μ (w • v) = 2 * μ v) : μ = 0 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    have h72 : (kerRoots (0 : X3)).ncard = 72 := by
      have hk : kerRoots (0 : X3) = {α : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 α} := by
        ext α
        simp [kerRoots, pairVec]
      rw [hk, ncard_isRoot_eq_72]
    rw [h72] at hx
    norm_num at hx
  obtain ⟨k, g, hkx⟩ := exists_smul_reps x hx0
  have hk : k = 3 := by
    have h1 : (kerRoots (reps k)).ncard = 18 := by
      rw [← ncard_kerRoots_smul g (reps k), ← hkx]
      exact hx
    rw [ncard_kerRoots_reps] at h1
    fin_cases k <;> first | rfl | (norm_num [repKerCard] at h1)
  have hkx3 : x = g • reps 3 := by
    rw [hk] at hkx
    exact hkx
  have hwx : w ∈ stabVec (g • reps 3) := by
    rw [← hkx3]
    exact hw
  have hwx' : w ∈ (stabVec (reps 3)).map (MulAut.conj g).toMonoidHom := by
    have h := hwx
    rw [stabVec_smul g (reps 3)] at h
    exact h
  obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.mp hwx'
  have hveq' : (MulAut.conj g) v = w := hveq
  have hgv : g * v = w * g := by
    have h := congrArg (fun t => t * g) hveq'
    rw [MulAut.conj_apply] at h
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  let μ' : (Fin Tag.E6.rank → ℤ) →+ ZMod 5 :=
    { toFun := fun u => μ (g • u)
      map_zero' := by simp
      map_add' := fun a b => by simp [smul_add, map_add] }
  have hμ' : ∀ u, μ' (v • u) = 2 * μ' u := by
    intro u
    change μ (g • (v • u)) = 2 * μ (g • u)
    rw [smul_smul, hgv, mul_smul, hμ]
  have hμ0 : μ' = 0 := modFive_eq_zero_of_mem_stabVec_rep_three μ' hv hμ'
  refine AddMonoidHom.ext fun u => ?_
  have h : μ' (g⁻¹ • u) = 0 := by rw [hμ0]; rfl
  simpa [μ', smul_inv_smul] using h

theorem modFive_eq_zero_of_ncard_rootCharKernel_eq_eighteen
    {L : Type} [Field L] (a : Fin Tag.E6.rank → Lˣ)
    (ha3 : ∀ i, a i ^ 3 = 1) (h18 : (rootCharKernel a).ncard = 18)
    (μ : (Fin Tag.E6.rank → ℤ) →+ ZMod 5) {w : WeylGroup Tag.E6}
    (hw : w ∈ rootCharStabilizerSubgroup a) (hμ : ∀ v, μ (w • v) = 2 * μ v) : μ = 0 := by
  have ha1 : a ≠ 1 := by
    rintro rfl
    have hk : rootCharKernel (1 : Fin Tag.E6.rank → Lˣ) = {α | IsRoot Tag.E6 α} := by
      ext α
      simp [rootCharKernel, rootChar]
    rw [hk, ncard_isRoot_eq_72] at h18
    norm_num at h18
  obtain ⟨x, hx0, hxchar⟩ := exists_vec_of_cube_roots a ha3 ha1
  have hx : (kerRoots x).ncard = 18 := by
    rwa [← rootCharKernel_eq_kerRoots hxchar]
  have hw' : w ∈ stabVec x := by
    rwa [← rootCharStabilizerSubgroup_eq_stabVec hxchar]
  exact modFive_eq_zero_of_ncard_kerRoots_eq_eighteen hx μ hw' hμ

end CFSG.StandardType.NTPlane

end
