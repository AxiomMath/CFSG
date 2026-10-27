module

public import CFSG.Quasithin.Vol2.Ch10SecKRSc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag C10P4F

section Theta

variable {H : Type*} [Group H]

@[expose] def theta (X : Subgroup H) : Subgroup H :=
  Subgroup.closure {x | x ∈ X ∧ x ^ 3 = 1}

theorem theta_le (X : Subgroup H) : theta X ≤ X :=
  (Subgroup.closure_le X).mpr fun _ hx => hx.1

theorem mem_theta {X : Subgroup H} {x : H} (hx : x ∈ X) (h3 : x ^ 3 = 1) : x ∈ theta X :=
  Subgroup.subset_closure ⟨hx, h3⟩

theorem theta_mono {X Y : Subgroup H} (h : X ≤ Y) : theta X ≤ theta Y :=
  Subgroup.closure_mono fun _ hx => ⟨h hx.1, hx.2⟩

theorem map_theta_le {K : Type*} [Group K] (f : H →* K) (X : Subgroup H) :
    (theta X).map f ≤ theta (X.map f) := by
  rw [theta, MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨x, ⟨hx, h3⟩, rfl⟩
  exact ⟨⟨x, hx, rfl⟩, by rw [← map_pow, h3, map_one]⟩

theorem theta_eq_top_of_simple [IsSimpleGroup H] {x : H} (hx : x ≠ 1) (h3 : x ^ 3 = 1) :
    theta (⊤ : Subgroup H) = ⊤ := by
  have hN : (theta (⊤ : Subgroup H)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have key : ∀ y ∈ theta (⊤ : Subgroup H), g * y * g⁻¹ ∈ theta (⊤ : Subgroup H) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        refine mem_theta (Subgroup.mem_top _) ?_
        rw [conj_pow, hz.2, mul_one, mul_inv_cancel]
      | one => simp
      | mul a b _ _ ha hb =>
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ ha hb
      | inv a _ ha =>
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ ha
    exact key n hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (theta (⊤ : Subgroup H)) with h | h
  · exact absurd ((Subgroup.mem_bot).mp (h ▸ mem_theta (Subgroup.mem_top x) h3)) hx
  · exact h

end Theta

section Q1

@[expose] def iota4Mat (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  Matrix.of fun i j => Fin.cases (Fin.cases 1 (fun _ => 0) j)
    (fun i' => Fin.cases 0 (fun j' => A i' j') j) i

theorem iota4Mat_mul (A B : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    iota4Mat (A * B) = iota4Mat A * iota4Mat B := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
    simp [iota4Mat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem det_iota4Mat (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) : (iota4Mat A).det = A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp [iota4Mat]
  rfl

@[expose] def iota4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) →* SL5 where
  toFun A := ⟨iota4Mat A, by rw [det_iota4Mat, A.2]⟩
  map_one' := by
    ext i j
    refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;>
      simp [iota4Mat, Matrix.one_apply, Fin.succ_inj, (Fin.succ_ne_zero _).symm]
  map_mul' A B := Subtype.ext (iota4Mat_mul A B)

theorem iota4_coe (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ((iota4 A : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) = iota4Mat A := rfl

theorem iota4_mem_Q1 (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : iota4 A ∈ Q1 := by
  rw [mem_Q1_iff]
  intro a ha
  obtain ⟨a', rfl⟩ : ∃ a' : Fin 4, a = a'.succ :=
    ⟨a.pred (fun h => by rw [h] at ha; simp at ha), (Fin.succ_pred _ _).symm⟩
  simp [iota4_coe, iota4Mat]

theorem cons_dot_single (r : Fin 4 → ZMod 2) :
    (Fin.cons (0 : ZMod 2) r : Fin 5 → ZMod 2) ⬝ᵥ Pi.single 0 1 = 0 := by
  simp [dotProduct, Fin.sum_univ_succ]

@[expose] def nr : Multiplicative (Fin 4 → ZMod 2) →* SL5 where
  toFun r := trv (Fin.cons 0 (Multiplicative.toAdd r)) (Pi.single 0 1) (cons_dot_single _)
  map_one' := by
    have h : (Fin.cons (0 : ZMod 2) (Multiplicative.toAdd (1 : Multiplicative (Fin 4 → ZMod 2))) :
        Fin 5 → ZMod 2) = 0 := by
      funext k
      refine Fin.cases ?_ (fun k' => ?_) k <;> simp
    simp only [h]
    exact trv_zero _
  map_mul' r s := by
    rw [trv_mul_trv]
    congr 1
    funext k
    refine Fin.cases ?_ (fun k' => ?_) k <;> simp

theorem nr_apply (r : Multiplicative (Fin 4 → ZMod 2)) (a b : Fin 5) :
    ((nr r : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b +
        (if a = 0 then (Fin.cons (0 : ZMod 2) (Multiplicative.toAdd r) : Fin 5 → ZMod 2) b
          else 0) := by
  show ((1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) + vecMulVec (Pi.single (0 : Fin 5) (1 : ZMod 2))
    (Fin.cons (0 : ZMod 2) (Multiplicative.toAdd r) : Fin 5 → ZMod 2) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = _
  rw [Matrix.add_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp

theorem nr_mem_Q1 (r : Multiplicative (Fin 4 → ZMod 2)) : nr r ∈ Q1 := by
  rw [mem_Q1_iff]
  intro a ha
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  simp [nr_apply, ha0, Matrix.one_apply_ne ha0]

theorem exists_iota4_mul_nr {g : SL5} (hg : g ∈ Q1) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) (r : Multiplicative (Fin 4 → ZMod 2)),
      g = iota4 A * nr r := by
  have h00 : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 0 = 1 := by
    have := congrFun (mem_Q1_iff_mulVec.mpr hg) 0
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hcol : ∀ a : Fin 4, (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) a.succ 0 = 0 := fun a =>
    mem_Q1_iff.mp hg a.succ (by simp)
  set A' : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
    (g : Matrix (Fin 5) (Fin 5) (ZMod 2)).submatrix Fin.succ Fin.succ with hA'
  set r : Multiplicative (Fin 4 → ZMod 2) :=
    Multiplicative.ofAdd fun j => (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 j.succ with hr
  have hmat : (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      iota4Mat A' * ((nr r : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
    ext a b
    refine Fin.cases ?_ (fun a' => ?_) a <;> refine Fin.cases ?_ (fun b' => ?_) b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, iota4Mat, nr_apply, h00, hcol, hA', hr,
        Matrix.one_apply, Fin.succ_inj, (Fin.succ_ne_zero _).symm]
  have hdet : A'.det = 1 := by
    have h1 := g.2
    rw [hmat, Matrix.det_mul, det_iota4Mat, (nr r).2, mul_one] at h1
    exact h1
  exact ⟨⟨A', hdet⟩, r, Subtype.ext hmat⟩

@[expose] def rr4 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ⟨!![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1], by decide⟩

theorem rr4_pow : rr4 ^ 3 = 1 := by decide

theorem rr4_ne : rr4 ≠ 1 := by decide

theorem theta_SL4 : theta (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) = ⊤ := by
  have := CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 4 (by norm_num)
  exact theta_eq_top_of_simple rr4_ne rr4_pow

theorem iota4_mem_theta (A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    iota4 A ∈ theta Q1 := by
  have h1 : iota4 A ∈ (theta (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))).map
      iota4 := ⟨A, by rw [theta_SL4]; trivial, rfl⟩
  refine theta_mono ?_ (map_theta_le iota4 ⊤ h1)
  rintro _ ⟨B, -, rfl⟩
  exact iota4_mem_Q1 B

@[expose] def bvec : Fin 4 → Fin 4 → ZMod 2 :=
  ![![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 1, 1], ![0, 0, 1, 0]]

theorem nr_single_eq (j : Fin 4) :
    nr (Multiplicative.ofAdd (Pi.single j 1)) = iota4 rr4 * (nr (Multiplicative.ofAdd (bvec j)) *
      (iota4 rr4 * iota4 rr4) * nr (Multiplicative.ofAdd (bvec j))) := by
  fin_cases j <;> decide

theorem pow_three_conj_inv {H : Type*} [Group H] {n x : H} (hn : n * n = 1) (hx : x ^ 3 = 1) :
    (n * x * n) ^ 3 = 1 := by
  have hn' : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn
  have : n * x * n = n * x * n⁻¹ := by rw [hn']
  rw [this, conj_pow, hx, mul_one, mul_inv_cancel]

theorem nr_mul_self (r : Multiplicative (Fin 4 → ZMod 2)) : nr r * nr r = 1 := by
  rw [← map_mul]
  have : r * r = 1 := by
    apply Multiplicative.toAdd.injective
    funext k
    simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
    exact zmod2_add_self _
  rw [this, map_one]

theorem nr_single_mem_theta (j : Fin 4) : nr (Multiplicative.ofAdd (Pi.single j 1)) ∈ theta Q1 := by
  rw [nr_single_eq, mul_assoc (nr _)]
  refine Subgroup.mul_mem _ (mem_theta (iota4_mem_Q1 _) (by rw [← map_pow, rr4_pow, map_one])) ?_
  rw [← mul_assoc]
  refine mem_theta (Subgroup.mul_mem _ (Subgroup.mul_mem _ (nr_mem_Q1 _)
    (Subgroup.mul_mem _ (iota4_mem_Q1 _) (iota4_mem_Q1 _))) (nr_mem_Q1 _)) ?_
  refine pow_three_conj_inv (nr_mul_self _) ?_
  rw [← map_mul, ← map_pow, show (rr4 * rr4) ^ 3 = 1 by decide, map_one]

theorem nr_mem_theta (r : Multiplicative (Fin 4 → ZMod 2)) : nr r ∈ theta Q1 := by
  have hr : r = Multiplicative.ofAdd (Multiplicative.toAdd r 0 • Pi.single 0 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd r 1 • Pi.single 1 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd r 2 • Pi.single 2 1) *
      Multiplicative.ofAdd (Multiplicative.toAdd r 3 • Pi.single 3 1) := by
    apply Multiplicative.toAdd.injective
    funext k
    fin_cases k <;> simp
  have hc : ∀ (c : ZMod 2) (j : Fin 4), nr (Multiplicative.ofAdd (c • Pi.single j 1)) ∈
      theta Q1 := by
    intro c j
    rcases zmod2_cases c with rfl | rfl
    · rw [zero_smul, ofAdd_zero, map_one]
      exact Subgroup.one_mem _
    · rw [one_smul]
      exact nr_single_mem_theta j
  rw [hr, map_mul, map_mul, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hc _ _) (hc _ _)) (hc _ _))
    (hc _ _)

theorem theta_Q1 : theta Q1 = Q1 := by
  refine le_antisymm (theta_le Q1) fun g hg => ?_
  obtain ⟨A, r, rfl⟩ := exists_iota4_mul_nr hg
  exact Subgroup.mul_mem _ (iota4_mem_theta A) (nr_mem_theta r)

end Q1

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
