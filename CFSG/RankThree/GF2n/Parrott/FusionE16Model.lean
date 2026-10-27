module

public import CFSG.RankThree.GF2n.Parrott.FusionE16Defs
public import CFSG.RankThree.GF2n.Parrott.QA45ElementaryAbelian
public import CFSG.Sporadic.Co2Smith.GlC0JankoA
public import CFSG.Literature.Janko67ModelSub
public import CFSG.GroupTheory.CommuteOfSqEqOne
public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.GroupTheory.CardSupInf
public import CFSG.LargeExtraspecial.Types
public import CFSG.RankThree.GF2n.Parrott.FusionE16ModelPack

public section

namespace CFSG.RankThree.GF2n.Parrott.FusionE16

open CFSG CFSG.Open CFSG.Literature.Janko67
open CFSG.Sporadic.Co2Smith (x45P)
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices (quaternionLift quaternionLift_a
  quaternionLift_xa)
open scoped Pointwise
open CFSG.KS.PCnt (pkw)
open CFSG.Permutation.FinPack64 (pk_mul eq_of_pk conj_of sq_of pow_four_of)
open CFSG.RankThree.GF2n.Parrott.Pack45 (h45 pk_one pk_t pk_u pk_a1 pk_b1 pk_a2 pk_b2 pk_s1 pk_s2
  pk_a1i pk_b1i)
open CFSG.RankThree.GF2n.Parrott.FusionE16.Pack (cjK cjK_other conj_table_sound)

private def modelUPerm : Fin 4 → Equiv.Perm (Fin 45)
  | 0 => t
  | 1 => alpha1 * alpha2
  | 2 => beta1 * beta2
  | 3 => u

private def q0code (p : Fin 5 → Fin 2) : ℕ :=
  (p 0 : ℕ) + 2 * (p 1 : ℕ) + 4 * (p 2 : ℕ) + 8 * (p 3 : ℕ) + 16 * (p 4 : ℕ)

private def q0Perm (p : Fin 5 → Fin 2) : Equiv.Perm (Fin 45) :=
  alpha1 ^ (p 0 : ℕ) * beta1 ^ (p 1 : ℕ) * alpha2 ^ (p 2 : ℕ) * beta2 ^ (p 3 : ℕ) *
    t ^ (p 4 : ℕ)

private def s0Perm (p : Fin 4 → Fin 2) : Equiv.Perm (Fin 45) :=
  t ^ (p 0 : ℕ) * u ^ (p 1 : ℕ) * (alpha1 * alpha2) ^ (p 2 : ℕ) * (beta1 * beta2) ^ (p 3 : ℕ)

private def q8Perm : QuaternionGroup 2 →* Equiv.Perm (Fin 45) :=
  quaternionLift (pow_four_of h45 pk_one pk_a1 (by decide +kernel) : alpha1 ^ 4 = 1)
    (conj_of h45 pk_b1 pk_a1 pk_a1i (by decide +kernel) : beta1 * alpha1 * beta1⁻¹ = alpha1⁻¹)
    (sq_of h45 pk_b1 pk_a1 (by decide +kernel) : beta1 ^ 2 = alpha1 ^ 2)

private def conjPerm (p : Fin 5 → Fin 2) : Equiv.Perm (Fin 45) :=
  match q0code p with
  | 10 => sigma1 * sigma1 * sigma2 * sigma2
  | 26 => beta1 * sigma1 * sigma1 * sigma2 * sigma2
  | 6 => sigma1 * sigma1
  | 22 => beta1 * sigma1 * sigma1
  | 14 => beta1 * sigma1 * sigma1 * sigma2
  | 30 => sigma1 * sigma1 * sigma2
  | 9 => sigma2 * sigma2
  | 25 => beta1 * sigma2 * sigma2
  | 21 => beta1
  | 13 => beta1 * sigma2
  | 29 => sigma2
  | 11 => beta1 * sigma1 * sigma2 * sigma2
  | 27 => sigma1 * sigma2 * sigma2
  | 7 => beta1 * sigma1
  | 23 => sigma1
  | 15 => sigma1 * sigma2
  | 31 => beta1 * sigma1 * sigma2
  | _ => 1

private theorem q8Perm_normal_form :
    ∀ q : QuaternionGroup 2,
      ∃ i j m : Fin 2, q8Perm q = t ^ (m : ℕ) * alpha1 ^ (i : ℕ) * beta1 ^ (j : ℕ) := by
  decide +kernel

private theorem pk_conjPerm (p : Fin 5 → Fin 2) : pkw 6 (conjPerm p) = cjK (q0code p) := by
  unfold conjPerm
  split
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_s1 pk_s1) pk_s2) pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_b1 pk_s1) pk_s1) pk_s2) pk_s2).trans
      (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 pk_s1 pk_s1).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 pk_b1 pk_s1) pk_s1).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_b1 pk_s1) pk_s1) pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 pk_s1 pk_s1) pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 pk_s2 pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 pk_b1 pk_s2) pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact pk_b1.trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 pk_b1 pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact pk_s2.trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 (pk_mul h45 pk_b1 pk_s1) pk_s2) pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 pk_s1 pk_s2) pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 pk_b1 pk_s1).trans (by decide +kernel)
  next h =>
    rw [h]
    exact pk_s1.trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 pk_s1 pk_s2).trans (by decide +kernel)
  next h =>
    rw [h]
    exact (pk_mul h45 (pk_mul h45 pk_b1 pk_s1) pk_s2).trans (by decide +kernel)
  next =>
    rw [cjK_other _ ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›]
    exact pk_one

private theorem conj_table_perm :
    ∀ p : Fin 5 → Fin 2, q0Perm p * q0Perm p = 1 → q0Perm p ≠ t → q0Perm p ≠ 1 →
      conjPerm p * q0Perm p * (conjPerm p)⁻¹ = alpha1 * alpha2 := by
  intro p h2 ht h1
  exact conj_table_sound p (pk_conjPerm p) h2 ht h1

section


private def modelU : Fin 4 → C0
  | 0 => tC
  | 1 => a1C * a2C
  | 2 => b1C * b2C
  | 3 => uC

private def toPerm : C0 →* Equiv.Perm (Fin 45) where
  toFun x := x.val.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl

private theorem toPerm_injective : Function.Injective toPerm := by
  intro x y h
  exact Subtype.ext (Subtype.ext h)

private theorem toPerm_tC : toPerm tC = t := rfl

private theorem toPerm_uC : toPerm uC = u := rfl

private theorem toPerm_a1C : toPerm a1C = alpha1 := rfl

private theorem toPerm_b1C : toPerm b1C = beta1 := rfl

private theorem toPerm_a2C : toPerm a2C = alpha2 := rfl

private theorem toPerm_b2C : toPerm b2C = beta2 := rfl

private theorem toPerm_s1C : toPerm s1C = sigma1 := rfl

private theorem toPerm_s2C : toPerm s2C = sigma2 := rfl

private def rhoC : C0 := s1C * s2C

private def q0C (p : Fin 5 → Fin 2) : C0 :=
  a1C ^ (p 0 : ℕ) * b1C ^ (p 1 : ℕ) * a2C ^ (p 2 : ℕ) * b2C ^ (p 3 : ℕ) * tC ^ (p 4 : ℕ)

private def s0C (p : Fin 4 → Fin 2) : C0 :=
  tC ^ (p 0 : ℕ) * uC ^ (p 1 : ℕ) * (a1C * a2C) ^ (p 2 : ℕ) * (b1C * b2C) ^ (p 3 : ℕ)

private def conjC (p : Fin 5 → Fin 2) : C0 :=
  match q0code p with
  | 10 => s1C * s1C * s2C * s2C
  | 26 => b1C * s1C * s1C * s2C * s2C
  | 6 => s1C * s1C
  | 22 => b1C * s1C * s1C
  | 14 => b1C * s1C * s1C * s2C
  | 30 => s1C * s1C * s2C
  | 9 => s2C * s2C
  | 25 => b1C * s2C * s2C
  | 21 => b1C
  | 13 => b1C * s2C
  | 29 => s2C
  | 11 => b1C * s1C * s2C * s2C
  | 27 => s1C * s2C * s2C
  | 7 => b1C * s1C
  | 23 => s1C
  | 15 => s1C * s2C
  | 31 => b1C * s1C * s2C
  | _ => 1

private theorem modelU_val (i : Fin 4) : toPerm (modelU i) = modelUPerm i := by
  fin_cases i <;> rfl

private theorem q0C_val (p : Fin 5 → Fin 2) : toPerm (q0C p) = q0Perm p := by
  simp [q0C, q0Perm, toPerm_tC, toPerm_a1C, toPerm_b1C, toPerm_a2C, toPerm_b2C, map_mul,
    map_pow]

private theorem s0C_val (p : Fin 4 → Fin 2) : toPerm (s0C p) = s0Perm p := by
  simp [s0C, s0Perm, toPerm_tC, toPerm_uC, toPerm_a1C, toPerm_a2C, toPerm_b1C, toPerm_b2C,
    map_mul, map_pow]

private theorem conjC_val (p : Fin 5 → Fin 2) : toPerm (conjC p) = conjPerm p := by
  unfold conjC conjPerm
  split <;> rfl

private theorem modelU_mem_S0 (i : Fin 4) : modelU i ∈ S0 := by
  fin_cases i
  · show tC ∈ S0
    rw [S0]
    exact Subgroup.subset_closure (by simp)
  · show a1C * a2C ∈ S0
    rw [S0]
    exact Subgroup.subset_closure (by simp)
  · show b1C * b2C ∈ S0
    rw [S0]
    exact Subgroup.subset_closure (by simp)
  · show uC ∈ S0
    rw [S0]
    exact Subgroup.subset_closure (by simp)

private theorem modelU_sq (i : Fin 4) : modelU i * modelU i = 1 :=
  mul_self_eq_one_of_mem_S0 (modelU_mem_S0 i)

private theorem modelU_pow_two (i : Fin 4) : modelU i ^ 2 = 1 := by
  rw [pow_two]
  exact modelU_sq i

private theorem modelU_commute (i j : Fin 4) : Commute (modelU i) (modelU j) := by
  rw [commute_iff_eq]
  exact CFSG.commute_of_sq_eq_one (by rw [pow_two]; exact modelU_sq i)
    (by rw [pow_two]; exact modelU_sq j)
    (by
      rw [pow_two]
      exact mul_self_eq_one_of_mem_S0 (S0.mul_mem (modelU_mem_S0 i) (modelU_mem_S0 j)))

private theorem modelU_mem_P0 (i : Fin 4) : modelU i ∈ P0 := by
  fin_cases i
  · show tC ∈ P0
    have h : tC = a1C * a1C := by
      apply Subtype.ext
      apply Subtype.ext
      show t = alpha1 * alpha1
      exact alpha1_sq.symm
    rw [h, P0]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · show a1C * a2C ∈ P0
    rw [P0]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · show b1C * b2C ∈ P0
    rw [P0]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · show uC ∈ P0
    rw [P0]
    exact Subgroup.subset_closure (by simp)

private theorem modelQ_val (c : Fin 4 → Fin 2) :
    toPerm (List.ofFn fun i => modelU i ^ (c i : ℕ)).prod =
      (List.ofFn fun i => modelUPerm i ^ (c i : ℕ)).prod := by
  rw [map_list_prod, List.map_ofFn]
  have hlist : List.ofFn (⇑toPerm ∘ fun i => modelU i ^ (c i : ℕ)) =
      List.ofFn fun i => modelUPerm i ^ (c i : ℕ) := by
    rw [List.ofFn_inj]
    funext i
    show toPerm (modelU i ^ (c i : ℕ)) = modelUPerm i ^ (c i : ℕ)
    rw [map_pow]
    congr 1
    exact modelU_val i
  rw [hlist]

private theorem modelQ_ne_one (c : Fin 4 → Fin 2) (hc : c ≠ 0) :
    (List.ofFn fun i => modelU i ^ (c i : ℕ)).prod ≠ 1 := by
  intro h
  have hperm : (List.ofFn fun i => modelUPerm i ^ (c i : ℕ)).prod = 1 := by
    rw [← modelQ_val c, h, map_one]
  exact (by decide +kernel :
    ∀ c : Fin 4 → Fin 2, c ≠ 0 →
      (List.ofFn fun i => modelUPerm i ^ (c i : ℕ)).prod ≠ 1) c hc hperm

private theorem modelU_act_a :
    a1C * modelU 0 * a1C⁻¹ = modelU 0 ∧ a1C * modelU 1 * a1C⁻¹ = modelU 1 ∧
      a1C * modelU 2 * a1C⁻¹ = modelU 0 * modelU 2 ∧
      a1C * modelU 3 * a1C⁻¹ = modelU 0 * modelU 1 * modelU 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Subtype.ext
    show alpha1 * t * alpha1⁻¹ = t
    exact conj_of h45 pk_a1 pk_t pk_t (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show alpha1 * (alpha1 * alpha2) * alpha1⁻¹ = alpha1 * alpha2
    exact conj_of h45 pk_a1 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_a1 pk_a2) (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show alpha1 * (beta1 * beta2) * alpha1⁻¹ = t * (beta1 * beta2)
    exact conj_of h45 pk_a1 (pk_mul h45 pk_b1 pk_b2) (pk_mul h45 pk_t (pk_mul h45 pk_b1 pk_b2))
      (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show alpha1 * u * alpha1⁻¹ = t * (alpha1 * alpha2) * u
    exact conj_of h45 pk_a1 pk_u (pk_mul h45 (pk_mul h45 pk_t (pk_mul h45 pk_a1 pk_a2)) pk_u)
      (by decide +kernel)

private theorem modelU_act_b :
    b1C * modelU 0 * b1C⁻¹ = modelU 0 ∧
      b1C * modelU 1 * b1C⁻¹ = modelU 0 * modelU 1 ∧
      b1C * modelU 2 * b1C⁻¹ = modelU 2 ∧
      b1C * modelU 3 * b1C⁻¹ = modelU 0 * modelU 2 * modelU 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Subtype.ext
    show beta1 * t * beta1⁻¹ = t
    exact conj_of h45 pk_b1 pk_t pk_t (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show beta1 * (alpha1 * alpha2) * beta1⁻¹ = t * (alpha1 * alpha2)
    exact conj_of h45 pk_b1 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_t (pk_mul h45 pk_a1 pk_a2))
      (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show beta1 * (beta1 * beta2) * beta1⁻¹ = beta1 * beta2
    exact conj_of h45 pk_b1 (pk_mul h45 pk_b1 pk_b2) (pk_mul h45 pk_b1 pk_b2) (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show beta1 * u * beta1⁻¹ = t * (beta1 * beta2) * u
    exact conj_of h45 pk_b1 pk_u (pk_mul h45 (pk_mul h45 pk_t (pk_mul h45 pk_b1 pk_b2)) pk_u)
      (by decide +kernel)

private theorem modelU_act_ρ :
    rhoC * modelU 0 * rhoC⁻¹ = modelU 0 ∧ rhoC * modelU 1 * rhoC⁻¹ = modelU 2 ∧
      rhoC * modelU 2 * rhoC⁻¹ = modelU 1 * modelU 2 ∧
      rhoC * modelU 3 * rhoC⁻¹ = modelU 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Subtype.ext; apply Subtype.ext
    show (sigma1 * sigma2) * t * (sigma1 * sigma2)⁻¹ = t
    exact conj_of h45 (pk_mul h45 pk_s1 pk_s2) pk_t pk_t (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show (sigma1 * sigma2) * (alpha1 * alpha2) * (sigma1 * sigma2)⁻¹ = beta1 * beta2
    exact conj_of h45 (pk_mul h45 pk_s1 pk_s2) (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_b1 pk_b2)
      (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show (sigma1 * sigma2) * (beta1 * beta2) * (sigma1 * sigma2)⁻¹ =
      (alpha1 * alpha2) * (beta1 * beta2)
    exact conj_of h45 (pk_mul h45 pk_s1 pk_s2) (pk_mul h45 pk_b1 pk_b2)
      (pk_mul h45 (pk_mul h45 pk_a1 pk_a2) (pk_mul h45 pk_b1 pk_b2)) (by decide +kernel)
  · apply Subtype.ext; apply Subtype.ext
    show (sigma1 * sigma2) * u * (sigma1 * sigma2)⁻¹ = u
    exact conj_of h45 (pk_mul h45 pk_s1 pk_s2) pk_u pk_u (by decide +kernel)

private theorem card_C0 : Nat.card C0 = 576 := qp45_card_centralizer_t

private theorem hPsyl_P0 : ∃ R : Sylow 2 C0, (R : Subgroup C0) = P0 := by
  have hfac : (Nat.card C0).factorization 2 = 6 := by
    rw [card_C0]
    norm_num [Nat.factorization]
  have hcard : Nat.card P0 = 2 ^ (Nat.card C0).factorization 2 := by
    rw [card_P0, hfac]
    norm_num
  exact ⟨Sylow.ofCard P0 hcard, Sylow.coe_ofCard P0 hcard⟩

private def K8 : Subgroup C0 := Subgroup.closure {a1C, b1C}

private theorem a1C_pow_four : a1C ^ 4 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  show alpha1 ^ 4 = 1
  exact pow_four_of h45 pk_one pk_a1 (by decide +kernel)

private theorem b1C_conj_a1C : b1C * a1C * b1C⁻¹ = a1C⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  show beta1 * alpha1 * beta1⁻¹ = alpha1⁻¹
  exact conj_of h45 pk_b1 pk_a1 pk_a1i (by decide +kernel)

private theorem b1C_sq_eq_a1C_sq : b1C ^ 2 = a1C ^ 2 := by
  apply Subtype.ext
  apply Subtype.ext
  show beta1 ^ 2 = alpha1 ^ 2
  exact sq_of h45 pk_b1 pk_a1 (by decide +kernel)

private noncomputable def q8Lift : QuaternionGroup 2 →* C0 :=
  quaternionLift a1C_pow_four b1C_conj_a1C b1C_sq_eq_a1C_sq

private theorem q8Lift_a (k : ZMod 4) : q8Lift (.a k) = a1C ^ k.val := by
  rw [q8Lift, quaternionLift_a]

private theorem q8Lift_xa (k : ZMod 4) : q8Lift (.xa k) = b1C * a1C ^ k.val := by
  rw [q8Lift, quaternionLift_xa]

private theorem q8Lift_val (q : QuaternionGroup 2) : toPerm (q8Lift q) = q8Perm q := by
  rcases q with r | r
  · rw [q8Lift_a, q8Perm, quaternionLift_a, map_pow]
    rfl
  · rw [q8Lift_xa, q8Perm, quaternionLift_xa, map_mul, map_pow]
    rfl

private theorem q8Lift_normal_form (q : QuaternionGroup 2) :
    ∃ i j m : Fin 2, q8Lift q = tC ^ (m : ℕ) * a1C ^ (i : ℕ) * b1C ^ (j : ℕ) := by
  obtain ⟨i, j, m, h⟩ := q8Perm_normal_form q
  refine ⟨i, j, m, ?_⟩
  apply toPerm_injective
  rw [q8Lift_val, h, map_mul, map_mul, map_pow, map_pow, map_pow]
  rfl

private theorem range_q8Lift : q8Lift.range = K8 := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    rcases q with r | r
    · rw [q8Lift_a]
      exact K8.pow_mem (Subgroup.subset_closure (by simp)) _
    · rw [q8Lift_xa]
      exact K8.mul_mem (Subgroup.subset_closure (by simp))
        (K8.pow_mem (Subgroup.subset_closure (by simp)) _)
  · rw [K8, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine ⟨.a 1, ?_⟩
      rw [q8Lift_a]
      show a1C ^ 1 = a1C
      simp
    · refine ⟨.xa 0, ?_⟩
      rw [q8Lift_xa]
      show b1C * a1C ^ 0 = b1C
      simp

private theorem K8_normal_form {k : C0} (hk : k ∈ K8) :
    ∃ i j m : Fin 2, k = tC ^ (m : ℕ) * a1C ^ (i : ℕ) * b1C ^ (j : ℕ) := by
  have hk' : k ∈ q8Lift.range := by rw [range_q8Lift]; exact hk
  obtain ⟨q, rfl⟩ := hk'
  exact q8Lift_normal_form q

private theorem K8_le_normalizer_S0 : K8 ≤ Subgroup.normalizer (S0 : Set C0) := by
  rw [K8, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact pCore_C0_le_normalizer_S0
      (by rw [pCore_C0_eq]; exact Subgroup.subset_closure (by simp))
  · exact pCore_C0_le_normalizer_S0
      (by rw [pCore_C0_eq]; exact Subgroup.subset_closure (by simp))

private theorem P0_eq_sup_S0_K8 : P0 = S0 ⊔ K8 := by
  apply le_antisymm
  · rw [P0, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (modelU_mem_S0 3)
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    · have ha2 : a2C = (a1C * a2C) * a1C⁻¹ := by
        apply Subtype.ext
        apply Subtype.ext
        show alpha2 = (alpha1 * alpha2) * alpha1⁻¹
        exact eq_of_pk h45 pk_a2 (pk_mul h45 (pk_mul h45 pk_a1 pk_a2) pk_a1i) (by decide +kernel)
      rw [ha2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (modelU_mem_S0 1))
        (Subgroup.mem_sup_right (K8.inv_mem (Subgroup.subset_closure (by simp))))
    · have hb2 : b2C = (b1C * b2C) * b1C⁻¹ := by
        apply Subtype.ext
        apply Subtype.ext
        show beta2 = (beta1 * beta2) * beta1⁻¹
        exact eq_of_pk h45 pk_b2 (pk_mul h45 (pk_mul h45 pk_b1 pk_b2) pk_b1i) (by decide +kernel)
      rw [hb2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (modelU_mem_S0 2))
        (Subgroup.mem_sup_right (K8.inv_mem (Subgroup.subset_closure (by simp))))
  · refine sup_le S0_le_P0 ?_
    rw [K8, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [P0]; exact Subgroup.subset_closure (by simp)
    · rw [P0]; exact Subgroup.subset_closure (by simp)

private theorem closure_range_modelU_eq_S0 : Subgroup.closure (Set.range modelU) = S0 := by
  have hrange : Set.range modelU = ({tC, uC, a1C * a2C, b1C * b2C} : Set C0) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [modelU]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [hrange]
  rfl

private theorem P0_coset_decomposition (p : C0) (hp : p ∈ P0) :
    ∃ s ∈ S0, ∃ k ∈ K8, p = s * k := by
  have hp1 : p ∈ (S0 ⊔ K8 : Subgroup C0) := by
    rw [← P0_eq_sup_S0_K8]
    exact hp
  have hcoe : (↑(S0 ⊔ K8) : Set C0) = (S0 : Set C0) * (K8 : Set C0) :=
    Subgroup.coe_mul_of_right_le_normalizer_left S0 K8 K8_le_normalizer_S0
  change p ∈ (↑(S0 ⊔ K8) : Set C0) at hp1
  rw [hcoe] at hp1
  obtain ⟨s, hs, k, hk, rfl⟩ := hp1
  exact ⟨s, hs, k, hk, rfl⟩

private theorem hPcos_C0 :
    ∀ p ∈ P0, ∃ s ∈ Subgroup.closure (Set.range modelU), ∃ i j : Fin 2,
      p = s * a1C ^ (i : ℕ) * b1C ^ (j : ℕ) := by
  intro p hp
  obtain ⟨s, hs, k, hk, rfl⟩ := P0_coset_decomposition p hp
  obtain ⟨i, j, m, hk'⟩ := K8_normal_form hk
  refine ⟨s * tC ^ (m : ℕ), ?_, i, j, ?_⟩
  · rw [closure_range_modelU_eq_S0]
    exact S0.mul_mem hs (S0.pow_mem (modelU_mem_S0 0) m)
  · rw [hk']
    group

private theorem hunique_S0 (E : Subgroup C0) (hE : E ≤ P0)
    (hEel : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = 16) :
    E = Subgroup.closure (Set.range modelU) := by
  have h2 : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    simpa [pow_two] using hEel.2 a ha
  rw [eq_S0_of_le_P0 hE hcard h2, closure_range_modelU_eq_S0]

private theorem hCS_C0 (g : C0)
    (hg : ∀ s ∈ Subgroup.closure (Set.range modelU), g * s = s * g) :
    g ∈ Subgroup.closure (Set.range modelU) := by
  rw [closure_range_modelU_eq_S0]
  have hg' : g ∈ Subgroup.centralizer (S0 : Set C0) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← closure_range_modelU_eq_S0] at hs
    exact (hg s hs).symm
  have hgi : iotaC g ∈ Subgroup.centralizer (sQA45 : Set ↥QA45.originalSubgroup) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [← map_S0_iotaC] at hs
    obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
    have h := Subgroup.mem_centralizer_iff.mp hg' s0 hs0
    calc iotaC s0 * iotaC g = iotaC (s0 * g) := by rw [map_mul]
      _ = iotaC (g * s0) := by rw [h]
      _ = iotaC g * iotaC s0 := by rw [map_mul]
  rw [centralizer_sQA45] at hgi
  have hmem : iotaC g ∈ S0.map iotaC := by
    rw [map_S0_iotaC]
    exact hgi
  obtain ⟨s0, hs0, hsg⟩ := Subgroup.mem_map.mp hmem
  have hsg' : s0 = g := iotaC_injective hsg
  simpa [hsg'] using hs0

private theorem orderOf_tC : orderOf tC = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf tC = orderOf (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup) :=
    Subgroup.orderOf_mk (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup) tC.2
  rw [h1, Subgroup.orderOf_mk]
  exact orderOf_eq_prime t_sq t_ne_one

private theorem a1C_not_mem_S0 : a1C ∉ S0 := by
  intro h
  rw [mem_S0_iff] at h
  obtain ⟨p, hp⟩ := h
  change a1C = s0C p at hp
  have hp' : alpha1 = s0Perm p := by
    have := congrArg toPerm hp
    rwa [toPerm_a1C, s0C_val] at this
  exact (by decide +kernel : ∀ q : Fin 4 → Fin 2, alpha1 ≠ s0Perm q) p hp'

private theorem b1C_not_mem_S0 : b1C ∉ S0 := by
  intro h
  rw [mem_S0_iff] at h
  obtain ⟨p, hp⟩ := h
  change b1C = s0C p at hp
  have hp' : beta1 = s0Perm p := by
    have := congrArg toPerm hp
    rwa [toPerm_b1C, s0C_val] at this
  exact (by decide +kernel : ∀ q : Fin 4 → Fin 2, beta1 ≠ s0Perm q) p hp'

private theorem a1C_mul_b1C_not_mem_S0 : a1C * b1C ∉ S0 := by
  intro h
  rw [mem_S0_iff] at h
  obtain ⟨p, hp⟩ := h
  change a1C * b1C = s0C p at hp
  have hp' : alpha1 * beta1 = s0Perm p := by
    have := congrArg toPerm hp
    rwa [map_mul, toPerm_a1C, toPerm_b1C, s0C_val] at this
  exact (by decide +kernel : ∀ q : Fin 4 → Fin 2, alpha1 * beta1 ≠ s0Perm q) p hp'

private theorem exists_conj_a1a2 (j : C0) (hj : j ∈ CFSG.pCore 2 C0)
    (hj2 : orderOf j = 2) (hjt : j ≠ tC) :
    ∃ c : C0, c * j * c⁻¹ = a1C * a2C := by
  rw [mem_pCore_C0_iff] at hj
  obtain ⟨p, rfl⟩ := hj
  change orderOf (q0C p) = 2 at hj2
  change q0C p ≠ tC at hjt
  change ∃ c : C0, c * q0C p * c⁻¹ = a1C * a2C
  have hj2' : q0C p * q0C p = 1 := by
    have h := pow_orderOf_eq_one (q0C p)
    rw [hj2] at h
    simpa [sq] using h
  have h2 : q0Perm p * q0Perm p = 1 := by
    have := congrArg toPerm hj2'
    rwa [map_mul, q0C_val, map_one] at this
  have h1 : q0Perm p ≠ 1 := by
    intro h
    have hq : q0C p = 1 := toPerm_injective (by rw [q0C_val, h, map_one])
    rw [hq, orderOf_one] at hj2
    omega
  have ht : q0Perm p ≠ t := by
    intro h
    apply hjt
    exact toPerm_injective (by rw [q0C_val, h]; rfl)
  refine ⟨conjC p, ?_⟩
  apply toPerm_injective
  rw [map_mul, map_mul, map_inv, conjC_val, q0C_val, map_mul]
  exact conj_table_perm p h2 ht h1

end

theorem exists_modelE16Config :
    ∃ cfg : E16Config ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)),
      (cfg.u 0 : ↥QP45.originalSubgroup) = x45P ∧
      (∀ z ∈ Subgroup.center ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)),
        z = 1 ∨ z = cfg.u 0) ∧
      (∀ j ∈ CFSG.pCore 2 ↥(Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)),
        orderOf j = 2 → j ≠ cfg.u 0 → ∃ c, c * j * c⁻¹ = cfg.u 1) := by
  have hX : Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) = C0 := by
    have hx : x45P = (⟨t, t_mem_Q⟩ : ↥QP45.originalSubgroup) := Subtype.ext rfl
    rw [hx]
  rw [hX]
  refine ⟨{
    u := modelU
    a := a1C
    b₁ := b1C
    ρ := rhoC
    P := P0
    hsq := modelU_pow_two
    hcomm := modelU_commute
    hker := modelQ_ne_one
    act_a := modelU_act_a
    act_b := modelU_act_b
    act_ρ := modelU_act_ρ
    hSP := modelU_mem_P0
    haP := by rw [P0]; exact Subgroup.subset_closure (by simp)
    hbP := by rw [P0]; exact Subgroup.subset_closure (by simp)
    hPsyl := hPsyl_P0
    hPcos := hPcos_C0
    hunique := hunique_S0
    hCS := hCS_C0 }, ?_, ?_, ?_⟩
  · exact Subtype.ext rfl
  · intro z hz
    rw [center_C0] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [← zpow_mod_orderOf, orderOf_tC] at hk
    have hk' : tC ^ (k % 2) = z := by simpa using hk
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← hk', h, zpow_zero]
    · right
      change z = tC
      rw [← hk', h, zpow_one]
  · intro j hj hj2 hjt
    exact exists_conj_a1a2 j hj hj2 hjt

end CFSG.RankThree.GF2n.Parrott.FusionE16
