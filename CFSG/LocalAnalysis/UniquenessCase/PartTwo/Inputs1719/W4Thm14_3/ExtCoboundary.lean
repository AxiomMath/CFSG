module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtTensor
public import CFSG.CGT.Timmesfeld75.L2Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

section Coboundary
variable {F : Type} [Field F] [Fintype F] [CharP F 2] {E : Type} [Field E] [Algebra F E]
  [CharP E 2]

private theorem tmatE_uElt_col_top (J : Finset ℕ) (t : F) (x : J → Fin 2) :
    tmatE E (fun i : J => (i : ℕ)) (uElt t) x (fun _ => 1) =
      algebraMap F E t ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) := by
  unfold tmatE aexp
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [twistMat_uElt]
  rcases fin2_cases (x i) with h | h <;> simp [h]

private theorem aexp_add_aexp_one_sub (J : Finset ℕ) (x : J → Fin 2) :
    aexp (fun i : J => (i : ℕ)) x + aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) =
      ∑ i ∈ J, 2 ^ i := by
  rw [aexp, aexp, ← Finset.sum_add_distrib, Finset.univ_eq_attach]
  rw [← Finset.sum_attach J (fun i => 2 ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : (x i : ℕ) + ((1 - x i : Fin 2) : ℕ) = 1 := by
    rcases fin2_cases (x i) with h | h <;> simp [h]
  rw [← add_mul, hx, one_mul]

private theorem aexp_one (J : Finset ℕ) :
    aexp (fun i : J => (i : ℕ)) (fun _ => 1) = ∑ i ∈ J, 2 ^ i := by
  rw [aexp, Finset.univ_eq_attach]
  rw [← Finset.sum_attach J (fun i => 2 ^ i)]
  simp

private theorem utriElt_eq_uElt (s : F) : CFSG.CGT.Timmesfeld75.utriElt s = uElt s := rfl

theorem frobTensor_uElt_apply_single_top (J : Finset ℕ) (t : F) (κ : E) (x : J → Fin 2) :
    frobTensor F E J (uElt t) (Pi.single (fun _ => 1) κ) x =
      algebraMap F E t ^ aexp (fun i : J => (i : ℕ)) (fun i => 1 - x i) * κ := by
  rw [frobTensor, tensorRep_apply, Finset.sum_eq_single (fun _ => 1)]
  · rw [Pi.single_eq_same, tmatE_uElt_col_top, mul_comm]
  · intro y _ hy
    rw [Pi.single_eq_of_ne hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uElt_cocycle_eq_steinberg {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (c' : SL(2, F) → (Finset.range n → Fin 2) → E)
    (hc' : ∀ g h, c' (g * h) = c' g + frobTensor F E (Finset.range n) g (c' h))
    (heq : ∀ (z : Fˣ) (t : F),
      c' (uElt ((z : F) ^ 2 * t)) = frobTensor F E (Finset.range n) (dElt z) (c' (uElt t))) :
    ∃ v : (Finset.range n → Fin 2) → E,
      ∀ t : F, c' (uElt t) = frobTensor F E (Finset.range n) (uElt t) v - v := by
  classical
  let J := Finset.range n
  let e : J → ℕ := fun i => (i : ℕ)
  have he_inj : Function.Injective e := fun i j h => Subtype.ext h
  have he_lt : ∀ i, e i < n := fun i => Finset.mem_range.mp i.2
  have hsum : ∑ i ∈ J, 2 ^ i = 2 ^ n - 1 := by
    rw [Nat.geomSum_eq (le_refl 2)]
    simp
  have hone : c' 1 = 0 := frobTensor_cocycle_one_eq_zero (Finset.range n) c' hc'
  let κ : (J → Fin 2) → E := c' (uElt 1)
  have hmono : ∀ (t : F), t ≠ 0 → ∀ x : J → Fin 2,
      c' (uElt t) x = algebraMap F E t ^ aexp e (fun i => 1 - x i) * κ x := by
    intro t ht x
    obtain ⟨z, hz⟩ : ∃ z : Fˣ, (z : F) = t ^ (2 ^ (n - 1)) :=
      ⟨Units.mk0 _ (pow_ne_zero _ ht), rfl⟩
    have hz2 : (z : F) ^ 2 = t := by
      rw [hz, ← pow_mul]
      have h2n : 2 ^ (n - 1) * 2 = 2 ^ n := by
        rw [← pow_succ, Nat.sub_add_cancel hn]
      rw [h2n, ← hF, FiniteField.pow_card]
    have h := heq z 1
    rw [mul_one, hz2] at h
    rw [h, frobTensor_dElt_apply]
    have hzpow : (z : F) ^ (∑ i ∈ J, 2 ^ i) = 1 := by
      rw [hsum, ← hF, FiniteField.pow_card_sub_one_eq_one (z : F) z.ne_zero]
    have hAm : (algebraMap F E (z : F)) ^ (∑ i ∈ J, 2 ^ i) = 1 := by
      rw [← map_pow, hzpow, map_one]
    have hprod : (algebraMap F E (z : F)) ^ aexp e x *
        (algebraMap F E (z : F)) ^ aexp e (fun i => 1 - x i) = 1 := by
      rw [← pow_add, aexp_add_aexp_one_sub, hAm]
    have hinv : ((algebraMap F E (z : F)) ^ aexp e x)⁻¹ =
        (algebraMap F E (z : F)) ^ aexp e (fun i => 1 - x i) :=
      inv_eq_of_mul_eq_one_right hprod
    have hA2 : (algebraMap F E (z : F)) ^ 2 = algebraMap F E t := by
      rw [← map_pow, hz2]
    calc algebraMap F E (z : F) ^ aexp e (fun i => 1 - x i) *
          ((algebraMap F E (z : F)) ^ aexp e x)⁻¹ * κ x
        = algebraMap F E (z : F) ^ aexp e (fun i => 1 - x i) *
          algebraMap F E (z : F) ^ aexp e (fun i => 1 - x i) * κ x := by rw [hinv]
      _ = (algebraMap F E (z : F)) ^ (aexp e (fun i => 1 - x i) +
            aexp e (fun i => 1 - x i)) * κ x := by rw [← pow_add]
      _ = ((algebraMap F E (z : F)) ^ 2) ^ aexp e (fun i => 1 - x i) * κ x := by
          rw [← two_mul, pow_mul]
      _ = algebraMap F E t ^ aexp e (fun i => 1 - x i) * κ x := by rw [hA2]
  have hf0 : ∀ t : F, c' (uElt t) (fun _ => 0) =
      (algebraMap F E t) ^ (∑ i ∈ J, 2 ^ i) * κ (fun _ => 0) := by
    intro t
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      rw [uElt_zero, hone]
      have hm : 0 < ∑ i ∈ J, 2 ^ i := by
        refine Finset.sum_pos (fun i _ => by positivity) ?_
        exact ⟨0, by simp [J]; omega⟩
      simp only [Pi.zero_apply, map_zero, zero_pow hm.ne', zero_mul]
    · rw [hmono t ht (fun _ => 0)]
      simp only [Pi.zero_apply, sub_zero]
      rw [aexp_one J]
  have hpoly : ∀ s : F, ∑ y : J → Fin 2,
      (if y = (fun _ => 1) then κ (fun _ => 1) else κ (fun _ => 0) - κ y) *
        (algebraMap F E s) ^ aexp e y = 0 := by
    intro s
    have hcoc := congrFun (hc' (uElt s) (uElt 1)) (fun _ => 0)
    simp only [Pi.add_apply] at hcoc
    rw [← uElt_add, hf0 (s + 1), hf0 s, frobTensor_uElt_apply_zero] at hcoc
    have hExp : (algebraMap F E (s + 1)) ^ (∑ i ∈ J, 2 ^ i) =
        ∑ y : J → Fin 2, (algebraMap F E s) ^ aexp e y *
          1 ^ aexp e (fun i => 1 - y i) := by
      rw [map_add, map_one]
      simpa only [aexp] using CFSG.FrobeniusMonomials.add_pow_aexp J (algebraMap F E s) 1
    rw [hExp, ← aexp_one J] at hcoc
    simp only [one_pow, mul_one] at hcoc
    rw [Finset.sum_mul] at hcoc
    have hEq : ∑ y : J → Fin 2, (κ (fun _ => 0) - κ y) * (algebraMap F E s) ^ aexp e y =
        κ (fun _ => 0) * (algebraMap F E s) ^ aexp e (fun _ => 1) := by
      calc ∑ y : J → Fin 2, (κ (fun _ => 0) - κ y) * (algebraMap F E s) ^ aexp e y
          = ∑ y : J → Fin 2, ((algebraMap F E s) ^ aexp e y * κ (fun _ => 0) -
              (algebraMap F E s) ^ aexp e y * κ y) := by
            refine Finset.sum_congr rfl fun y _ => by ring
        _ = (∑ y : J → Fin 2, (algebraMap F E s) ^ aexp e y * κ (fun _ => 0)) -
              ∑ y : J → Fin 2, (algebraMap F E s) ^ aexp e y * κ y :=
            Finset.sum_sub_distrib _ _
        _ = (algebraMap F E s) ^ aexp e (fun _ => 1) * κ (fun _ => 0) +
              ∑ y : J → Fin 2, (algebraMap F E s) ^ aexp e y * κ y -
              ∑ y : J → Fin 2, (algebraMap F E s) ^ aexp e y * κ y := by rw [hcoc]
        _ = κ (fun _ => 0) * (algebraMap F E s) ^ aexp e (fun _ => 1) := by
            rw [mul_comm]
            abel
    have hsplit : ∑ y : J → Fin 2,
        (if y = (fun _ => 1) then κ (fun _ => 1) else κ (fun _ => 0) - κ y) *
          (algebraMap F E s) ^ aexp e y
        = (∑ y : J → Fin 2, (κ (fun _ => 0) - κ y) * (algebraMap F E s) ^ aexp e y) -
          κ (fun _ => 0) * (algebraMap F E s) ^ aexp e (fun _ => 1) := by
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (fun _ => 1))]
      rw [← Finset.sum_erase_add Finset.univ (fun y => (κ (fun _ => 0) - κ y) *
        (algebraMap F E s) ^ aexp e y) (Finset.mem_univ (fun _ => 1))]
      rw [if_pos rfl]
      have hcongr : ∑ y ∈ Finset.univ.erase (fun _ => 1),
          (if y = (fun _ => 1) then κ (fun _ => 1) else κ (fun _ => 0) - κ y) *
            (algebraMap F E s) ^ aexp e y
          = ∑ y ∈ Finset.univ.erase (fun _ => 1),
            (κ (fun _ => 0) - κ y) * (algebraMap F E s) ^ aexp e y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [if_neg (Finset.ne_of_mem_erase hy)]
      rw [hcongr]
      have h2 : κ (fun _ => 1) * (algebraMap F E s) ^ aexp e (fun _ => 1) +
          κ (fun _ => 1) * (algebraMap F E s) ^ aexp e (fun _ => 1) = 0 :=
        CharTwo.add_self_eq_zero _
      linear_combination h2
    rw [hsplit, hEq, sub_self]
  have hcoef := eq_zero_of_sum_pow_eq_zero (a := aexp e) (ha := aexp_injective e he_inj)
    (hlt := fun y => by rw [hF]; exact aexp_lt e he_inj he_lt y)
    (c := fun y => if y = (fun _ => 1) then κ (fun _ => 1) else κ (fun _ => 0) - κ y) hpoly
  have hctop : κ (fun _ => 1) = 0 := by
    simpa using hcoef (fun _ => 1)
  have hcy : ∀ y : J → Fin 2, y ≠ (fun _ => 1) → κ y = κ (fun _ => 0) := by
    intro y hy
    have h := hcoef y
    rw [if_neg hy, sub_eq_zero] at h
    exact h.symm
  refine ⟨Pi.single (fun _ => 1) (κ (fun _ => 0)), fun t => ?_⟩
  funext x
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    rw [uElt_zero, hone]
    simp
  · rw [hmono t ht x]
    simp only [Pi.sub_apply]
    rw [frobTensor_uElt_apply_single_top]
    by_cases hx : x = (fun _ => 1)
    · subst hx
      rw [hctop, Pi.single_eq_same]
      simp [aexp]
    · rw [hcy x hx, Pi.single_eq_of_ne hx, sub_zero]

theorem frobTensor_cocycle_coboundary {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n) (hJ : 2 ≤ J.card) (c : SL(2, F) → (J → Fin 2) → E)
    (hc : ∀ g h, c (g * h) = c g + frobTensor F E J g (c h)) :
    ∃ v, ∀ g, c g = frobTensor F E J g v - v := by
  obtain ⟨c', v₀, hc₀, hc', heq⟩ := exists_torus_equivariant J c hc
  have hres : ∃ v : (J → Fin 2) → E, ∀ t : F,
      c' (uElt t) = frobTensor F E J (uElt t) v - v := by
    rcases eq_or_ne J (Finset.range n) with hJ' | hJ'
    · subst hJ'
      exact uElt_cocycle_eq_steinberg (by omega) hF c' hc' heq
    · refine ⟨0, fun t => ?_⟩
      rw [uElt_cocycle_eq_zero_of_not_steinberg hF hJn hJ hJ' c' hc' heq t]
      simp
  obtain ⟨vU, hvU⟩ := hres
  let μ : SL(2, F) →* AddMonoid.End ((J → Fin 2) → E) := frobMu (F := F) (E := E) J
  have hZ : c' ∈ Z1A μ := by
    intro g h
    exact hc' g h
  have hH : ∀ h ∈ CFSG.CGT.Timmesfeld75.utri F, c' h = μ h vU - vU := by
    intro h hh
    obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.1 hh
    rw [utriElt_eq_uElt]
    exact hvU s
  have h2 : ∀ m : (J → Fin 2) → E, m + m = 0 := fun m => by
    funext x
    exact CharTwo.add_self_eq_zero (m x)
  have hodd : Odd (CFSG.CGT.Timmesfeld75.utri F).index :=
    CFSG.CGT.Timmesfeld75.odd_index_utri
  obtain ⟨V, hV⟩ := mem_B1A_of_restrict (μ := μ) h2 hodd hZ hH
  have hVg : ∀ g, c' g = frobTensor F E J g V - V := by
    intro g
    have := congrFun hV g
    rw [coboundaryA_apply] at this
    exact this.symm
  refine ⟨V + v₀, fun g => ?_⟩
  rw [hc₀ g, hVg g, map_add]
  abel

end Coboundary

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
