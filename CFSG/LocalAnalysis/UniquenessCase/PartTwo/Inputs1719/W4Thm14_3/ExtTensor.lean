module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.ExtTorus
public import CFSG.Timmesfeld.Bridge.RootStructR2HigmanIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.FrobeniusMonomials
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

private theorem image_rotate_ne_self {n : ℕ} (hn : 1 ≤ n) {J : Finset ℕ} (hJne : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (hJst : J ≠ Finset.range n) :
    J.image (fun i => (i + n - 1) % n) ≠ J := by
  intro h
  have hfun : (fun i => (i + n - 1) % n) = fun i => (i + (n - 1)) % n := by
    funext i
    congr 1
    omega
  rw [hfun] at h
  have hgcd : Nat.gcd n (n - 1) = 1 :=
    (Nat.coprime_self_sub_right (m := 1) hn).mpr (Nat.coprime_one_right n)
  have hle := CFSG.Timmesfeld.Bridge.Higman.le_card_mul_gcd_of_shift (n := n) (d := n - 1)
    (by omega) hJne hJn h
  rw [hgcd, mul_one] at hle
  have hsub : J ⊆ Finset.range n := fun i hi => Finset.mem_range.mpr (hJn i hi)
  have hcard : J.card = n := by
    refine le_antisymm ?_ hle
    calc J.card ≤ (Finset.range n).card := Finset.card_le_card hsub
      _ = n := Finset.card_range n
  exact hJst (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range, hcard]))

private theorem mem_of_aexp_eq_two_pow {J : Finset ℕ} {j : ℕ} {x : J → Fin 2}
    (hx : aexp (fun i : J => (i : ℕ)) x = 2 ^ j) : j ∈ J := by
  classical
  set S : Finset ℕ := (Finset.univ.filter (fun i : J => x i = 1)).image (fun i : J => (i : ℕ))
    with hSdef
  have hS : aexp (fun i : J => (i : ℕ)) x = ∑ i ∈ S, 2 ^ i := by
    rw [hSdef]
    exact aexp_eq_sum_support (fun i : J => (i : ℕ)) Subtype.val_injective x
  have h2 : ∑ i ∈ S, 2 ^ i = ∑ i ∈ ({j} : Finset ℕ), 2 ^ i := by
    rw [← hS, hx]
    simp
  have hSeq : S = {j} := by
    have hinj := Finset.equivBitIndices.symm.injective (a₁ := S) (a₂ := {j})
    exact hinj (by simpa only [Finset.equivBitIndices_symm_apply] using h2)
  have hSsub : S ⊆ J := by
    intro k hk
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hk
    exact i.2
  rw [hSeq] at hSsub
  exact hSsub (Finset.mem_singleton_self j)

private theorem exists_aexp_eq_two_pow {n : ℕ} {J : Finset ℕ} {j : ℕ}
    (hj : j ∈ J.image (fun i => (i + n - 1) % n)) :
    ∃ y : (J.image (fun i => (i + n - 1) % n)) → Fin 2,
      aexp (fun i : (J.image (fun i => (i + n - 1) % n)) => (i : ℕ)) y = 2 ^ j := by
  classical
  refine ⟨Pi.single ⟨j, hj⟩ 1, ?_⟩
  unfold aexp
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro b _ hb
    have hb' : b ≠ ⟨j, hj⟩ := hb
    have hzero : Pi.single (M := fun _ => Fin 2) ⟨j, hj⟩ (1 : Fin 2) b = 0 :=
      Pi.single_eq_of_ne hb' 1
    rw [hzero]
    simp
  · simp

section Tensor
variable {F : Type} [Field F] [Fintype F] [CharP F 2] {E : Type} [Field E] [Algebra F E]
  [CharP E 2]
theorem frobTensor_uElt_apply_zero (J : Finset ℕ) (s : F) (v : (J → Fin 2) → E) :
    frobTensor F E J (uElt s) v (fun _ => 0) =
      ∑ x : J → Fin 2, algebraMap F E s ^ aexp (fun i : J => (i : ℕ)) x * v x := by
  rw [frobTensor, tensorRep_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tmatE_uElt_base_row]

theorem uElt_cocycle_eq_zero_of_not_steinberg {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {J : Finset ℕ} (hJn : ∀ i ∈ J, i < n) (hJ : 2 ≤ J.card)
    (hJst : J ≠ Finset.range n) (c' : SL(2, F) → (J → Fin 2) → E)
    (hc' : ∀ g h, c' (g * h) = c' g + frobTensor F E J g (c' h))
    (heq : ∀ (z : Fˣ) (t : F),
      c' (uElt ((z : F) ^ 2 * t)) = frobTensor F E J (dElt z) (c' (uElt t)))
    (t : F) : c' (uElt t) = 0 := by
  classical
  let rot : ℕ → ℕ := fun i => (i + n - 1) % n
  let Jrot : Finset ℕ := J.image rot
  let r : ℕ := ∑ i ∈ Jrot, 2 ^ i
  let A : (J → Fin 2) → ℕ := aexp (fun i : J => (i : ℕ))
  let B : (Jrot → Fin 2) → ℕ := aexp (fun i : Jrot => (i : ℕ))
  let κ : (J → Fin 2) → E := fun x => c' (uElt 1) x
  have hJne : J.Nonempty := Finset.card_pos.mp (by omega)
  have hn1 : 1 ≤ n := by
    obtain ⟨j, hj⟩ := hJne
    have := hJn j hj
    omega
  have hRmem : ∀ i ∈ Jrot, i < n := by
    intro i hi
    simp only [Jrot, Finset.mem_image] at hi
    obtain ⟨j, -, rfl⟩ := hi
    exact Nat.mod_lt _ (by omega)
  have hcardR : Jrot.card = J.card := by
    simp only [Jrot]
    exact Finset.card_image_of_injOn (rotate_injOn hJn)
  have hAinj : Function.Injective A := aexp_injective _ Subtype.val_injective
  have hBinj : Function.Injective B := aexp_injective _ Subtype.val_injective
  have hr_lt : r < 2 ^ n := by
    exact Nat.geomSum_lt le_rfl hRmem
  have hc1 : c' 1 = 0 := frobTensor_cocycle_one_eq_zero J c' hc'
  have hbase : ∀ u : F,
      c' (uElt u) (fun _ => 0) = κ (fun _ => 0) * (algebraMap F E u) ^ r := by
    intro u
    have h := cocycle_uElt_base (F := F) (E := E) (n := n) hF hJne hJn c' hc' heq u
    simpa [κ, r, Jrot, rot] using h
  have hcoord : ∀ s : F, c' (uElt (s + 1)) (fun _ => 0)
      = c' (uElt s) (fun _ => 0)
        + ∑ x : J → Fin 2, κ x * (algebraMap F E s) ^ A x := by
    intro s
    have h := hc' (uElt s) (uElt 1)
    rw [← uElt_add] at h
    have h2 := congrFun h (fun _ => 0)
    simp only [Pi.add_apply] at h2
    rw [frobTensor_uElt_apply_zero] at h2
    rw [h2]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [κ, A]
    rw [mul_comm]
  have hExp : ∀ s : F, (algebraMap F E (s + 1)) ^ r
      = ∑ y : Jrot → Fin 2, (algebraMap F E s) ^ B y := by
    intro s
    have h := add_pow_aexp (R := F) Jrot s 1
    have h' : (s + 1) ^ r = ∑ y : Jrot → Fin 2, s ^ B y := by
      simpa [r, B, aexp] using h
    calc (algebraMap F E (s + 1)) ^ r
        = algebraMap F E ((s + 1) ^ r) := (map_pow _ _ _).symm
      _ = algebraMap F E (∑ y : Jrot → Fin 2, s ^ B y) := by rw [h']
      _ = ∑ y : Jrot → Fin 2, (algebraMap F E s) ^ B y := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun y _ => map_pow _ _ _
  have hC : ∀ s : F, (∑ y : Jrot → Fin 2, κ (fun _ => 0) * (algebraMap F E s) ^ B y)
      + ((∑ x : J → Fin 2, κ x * (algebraMap F E s) ^ A x)
          + κ (fun _ => 0) * (algebraMap F E s) ^ r) = 0 := by
    intro s
    have h1 : κ (fun _ => 0) * (algebraMap F E (s + 1)) ^ r =
        κ (fun _ => 0) * (algebraMap F E s) ^ r
          + ∑ x : J → Fin 2, κ x * (algebraMap F E s) ^ A x := by
      rw [← hbase (s + 1), hcoord s, hbase s]
    have h2 : (∑ y : Jrot → Fin 2, κ (fun _ => 0) * (algebraMap F E s) ^ B y)
        = κ (fun _ => 0) * (algebraMap F E (s + 1)) ^ r := by
      rw [hExp s, Finset.mul_sum]
    rw [h2, h1]
    rw [add_comm (κ (fun _ => 0) * (algebraMap F E s) ^ r)
      (∑ x : J → Fin 2, κ x * (algebraMap F E s) ^ A x)]
    exact CharTwo.add_self_eq_zero _
  have hexists : ∃ E₀ : ℕ, (∃ y : Jrot → Fin 2, B y = E₀)
      ∧ (∀ x : J → Fin 2, A x ≠ E₀) ∧ E₀ ≠ r := by
    by_contra hcon
    push Not at hcon
    have hRsubJ : Jrot ⊆ J := by
      intro j hj
      obtain ⟨y, hy⟩ := exists_aexp_eq_two_pow (n := n) hj
      have hlt : 2 ^ j < r := by
        have hpos : 0 < ∑ i ∈ Jrot.erase j, 2 ^ i := by
          apply Finset.sum_pos
          · intro i _; positivity
          · rw [← Finset.card_pos, Finset.card_erase_of_mem hj]
            have hcard2 : 2 ≤ Jrot.card := by rw [hcardR]; exact hJ
            omega
        have hEq : r = 2 ^ j + ∑ i ∈ Jrot.erase j, 2 ^ i :=
          (Finset.add_sum_erase Jrot (fun i => 2 ^ i) hj).symm
        omega
      have hx : ∃ x : J → Fin 2, A x = 2 ^ j := by
        by_contra hx
        push Not at hx
        exact (ne_of_lt hlt) (hcon (2 ^ j) ⟨y, hy⟩ hx)
      obtain ⟨x, hx⟩ := hx
      exact mem_of_aexp_eq_two_pow hx
    have hRJ : Jrot = J := by
      refine Finset.eq_of_subset_of_card_le hRsubJ ?_
      rw [hcardR]
    exact image_rotate_ne_self hn1 hJne hJn hJst (by simpa [Jrot] using hRJ)
  let ι : Type := (Jrot → Fin 2) ⊕ ((J → Fin 2) ⊕ Unit)
  let ex : ι → ℕ := fun i => match i with
    | Sum.inl y => B y
    | Sum.inr (Sum.inl x) => A x
    | Sum.inr (Sum.inr _) => r
  let cf : ι → E := fun i => match i with
    | Sum.inl _ => κ (fun _ => 0)
    | Sum.inr (Sum.inl x) => κ x
    | Sum.inr (Sum.inr _) => κ (fun _ => 0)
  have hsumC : ∀ s : F, ∑ i : ι, cf i * (algebraMap F E s) ^ ex i = 0 := by
    intro s
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique, ex, cf]
    exact hC s
  have hcoeff : ∀ m : ℕ,
      ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => ex i = m), cf i = 0 := by
    intro m
    refine sum_filter_eq_zero_of_forall_eval (F := F) (E := E)
      (Finset.univ : Finset ι) ex cf ?_ ?_ m
    · intro i _
      rcases i with y | (x | u)
      · rw [hF]; exact aexp_lt _ Subtype.val_injective (fun i => hRmem i i.2) y
      · rw [hF]; exact aexp_lt _ Subtype.val_injective (fun i => hJn i i.2) x
      · rw [hF]; exact hr_lt
    · intro s
      simpa using hsumC s
  obtain ⟨E₀, ⟨y₀, hy₀⟩, hE₀U, hE₀r⟩ := hexists
  have hκ0 : κ (fun _ => 0) = 0 := by
    have hcoef := hcoeff E₀
    have hfilter : (Finset.univ : Finset ι).filter (fun i => ex i = E₀) = {Sum.inl y₀} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hi
        rcases i with y | (x | u)
        · simp only [ex] at hi
          exact congrArg Sum.inl (hBinj (by rw [hi, hy₀]))
        · simp only [ex] at hi
          exact absurd hi (hE₀U x)
        · simp only [ex] at hi
          exact absurd hi.symm hE₀r
      · intro hi
        subst hi
        simp only [ex]
        exact hy₀
    rw [hfilter, Finset.sum_singleton] at hcoef
    simpa only [cf] using hcoef
  have hκ : ∀ x : J → Fin 2, κ x = 0 := by
    intro x
    have hC' : ∀ s : F, ∑ z : J → Fin 2, κ z * (algebraMap F E s) ^ A z = 0 := by
      intro s
      have h := hC s
      simpa [hκ0] using h
    have hlt : ∀ i : J → Fin 2, A i < Fintype.card F := by
      intro i
      rw [hF]
      exact aexp_lt _ Subtype.val_injective (fun j => hJn j j.2) i
    exact eq_zero_of_sum_pow_eq_zero (a := A) hAinj hlt κ hC' x
  have h1 : c' (uElt 1) = 0 := funext hκ
  by_cases ht : t = 0
  · subst ht
    rw [uElt_zero]
    exact hc1
  · obtain ⟨z, hz⟩ : ∃ z : Fˣ, (z : F) ^ 2 = t := by
      refine ⟨Units.mk0 (t ^ (2 ^ (n - 1))) (pow_ne_zero _ ht), ?_⟩
      rw [Units.val_mk0, ← pow_mul]
      have h2 : 2 ^ (n - 1) * 2 = 2 ^ n := by
        rw [← pow_succ]
        congr 1
        omega
      rw [h2, ← hF]
      exact FiniteField.pow_card t
    rw [← hz, ← mul_one ((z : F) ^ 2), heq z 1, h1, map_zero]
end Tensor

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
