module

public import CFSG.RankThree.PartOne.KF1514B.Tns
public import CFSG.RankThree.PartOne.KF1514B.OddMem
public import CFSG.RankThree.PartOne.KF1514B.Sylow
public import CFSG.RankThree.PartOne.KF1514B.Numbers
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailCharTwoSign

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LieType.Universal.Spin

section Action

variable {K : Type} [Field K]

@[expose] def Xmat (v : Vt K) : Matrix (Fin 2) (Fin 2) K :=
  !![v.1 (Sum.inl 0), v.1 (Sum.inl 1); v.1 (Sum.inr 1), v.1 (Sum.inr 0)]

@[expose] def trFun (P Q S : Matrix (Fin 2) (Fin 2) K) (v : Vt K) : Vt K :=
  (Sum.elim ![(P * Xmat v * Q) 0 0, (P * Xmat v * Q) 0 1, v.1 (Sum.inl 2)]
    ![(P * Xmat v * Q) 1 1, (P * Xmat v * Q) 1 0, v.1 (Sum.inr 2)], S.mulVec v.2)

theorem Xmat_add (v w : Vt K) : Xmat (v + w) = Xmat v + Xmat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat]

theorem Xmat_smul (t : K) (v : Vt K) : Xmat (t • v) = t • Xmat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat]

@[expose] def trLin (P Q S : Matrix (Fin 2) (Fin 2) K) : Vt K →ₗ[K] Vt K where
  toFun := trFun P Q S
  map_add' v w := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i <;> fin_cases i <;>
        simp [trFun, Xmat_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
    · simp [trFun, Matrix.mulVec_add]
  map_smul' t v := by
    refine Prod.ext (funext fun c => ?_) ?_
    · rcases c with i | i <;> fin_cases i <;>
        simp [trFun, Xmat_smul]
    · simp [trFun, Matrix.mulVec_smul]

section Comp

variable (P Q S : Matrix (Fin 2) (Fin 2) K) (v : Vt K)

@[simp] theorem trFun_inl0 : (trFun P Q S v).1 (Sum.inl 0) = (P * Xmat v * Q) 0 0 := rfl
@[simp] theorem trFun_inl1 : (trFun P Q S v).1 (Sum.inl 1) = (P * Xmat v * Q) 0 1 := rfl
@[simp] theorem trFun_inl2 : (trFun P Q S v).1 (Sum.inl 2) = v.1 (Sum.inl 2) := rfl
@[simp] theorem trFun_inr0 : (trFun P Q S v).1 (Sum.inr 0) = (P * Xmat v * Q) 1 1 := rfl
@[simp] theorem trFun_inr1 : (trFun P Q S v).1 (Sum.inr 1) = (P * Xmat v * Q) 1 0 := rfl
@[simp] theorem trFun_inr2 : (trFun P Q S v).1 (Sum.inr 2) = v.1 (Sum.inr 2) := rfl
@[simp] theorem trFun_snd : (trFun P Q S v).2 = S.mulVec v.2 := rfl

theorem Xmat_trFun : Xmat (trFun P Q S v) = P * Xmat v * Q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat]

end Comp

theorem trFun_comp (P Q S P' Q' S' : Matrix (Fin 2) (Fin 2) K) (v : Vt K) :
    trFun P Q S (trFun P' Q' S' v) = trFun (P * P') (Q' * Q) (S * S') v := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i <;> fin_cases i <;> simp [Xmat_trFun, Matrix.mul_assoc]
  · rw [trFun_snd, trFun_snd, trFun_snd, Matrix.mulVec_mulVec]

theorem trFun_one (v : Vt K) : trFun 1 1 1 v = v := by
  refine Prod.ext (funext fun c => ?_) ?_
  · rcases c with i | i <;> fin_cases i <;> simp [Xmat]
  · simp

@[expose] noncomputable def trEquiv (g₁ g₂ g₃ : GL (Fin 2) K) : Vt K ≃ₗ[K] Vt K :=
  LinearEquiv.ofLinearMap (trLin (g₁ : Matrix (Fin 2) (Fin 2) K) ((g₂⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) (g₃ : Matrix (Fin 2) (Fin 2) K))
    (trLin ((g₁⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (g₂ : Matrix (Fin 2) (Fin 2) K)
      ((g₃⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (LinearMap.ext fun v => by
      show trFun _ _ _ (trFun _ _ _ v) = v
      rw [trFun_comp]
      simp [trFun_one])
    (LinearMap.ext fun v => by
      show trFun _ _ _ (trFun _ _ _ v) = v
      rw [trFun_comp]
      simp [trFun_one])

theorem trEquiv_apply (g₁ g₂ g₃ : GL (Fin 2) K) (v : Vt K) :
    trEquiv g₁ g₂ g₃ v = trFun (g₁ : Matrix (Fin 2) (Fin 2) K) ((g₂⁻¹ : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K) (g₃ : Matrix (Fin 2) (Fin 2) K) v := rfl

@[expose] noncomputable def trHomGL :
    GL (Fin 2) K × GL (Fin 2) K × GL (Fin 2) K →* (Vt K ≃ₗ[K] Vt K) where
  toFun g := trEquiv g.1 g.2.1 g.2.2
  map_one' := LinearEquiv.ext fun v => by
    rw [trEquiv_apply]
    simpa using trFun_one v
  map_mul' g h := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, trEquiv_apply, trEquiv_apply, trEquiv_apply, trFun_comp]
    simp [_root_.mul_inv_rev, Units.val_mul]

end Action

section Torus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

variable (b c) in
@[expose] noncomputable def torusHom :
    Tns b c × Tns b c × Tns b c →* (Vt K ≃ₗ[K] Vt K) :=
  trHomGL.comp (MonoidHom.prodMap (Tns b c).subtype
    (MonoidHom.prodMap (Tns b c).subtype (Tns b c).subtype))

theorem torusHom_apply (g₁ g₂ g₃ : Tns b c) :
    torusHom b c (g₁, g₂, g₃) = trEquiv (g₁ : GL (Fin 2) K) g₂ g₃ := rfl

theorem torusHom_mem_orth (t : Tns b c × Tns b c × Tns b c) :
    torusHom b c t ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail 3 (minusTailForm K b c)) := by
  obtain ⟨g₁, g₂, g₃⟩ := t
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [torusHom_apply, trEquiv_apply, quadTail_apply, quadTail_apply, quadPlus_apply, quadPlus_apply]
  simp only [Fin.sum_univ_three, trFun_inl0, trFun_inl1, trFun_inl2, trFun_inr0, trFun_inr1,
    trFun_inr2, trFun_snd]
  have hP := det_of_mem_Tns g₁.2
  have hQ : ((((g₂ : GL (Fin 2) K)⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K).det = 1 :=
    det_of_mem_Tns (inv_mem g₂.2)
  set M : Matrix (Fin 2) (Fin 2) K := ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Xmat v *
    ((((g₂ : GL (Fin 2) K)⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det = (Xmat v).det := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, hP, hQ, one_mul, mul_one]
  rw [Matrix.det_fin_two, Matrix.det_fin_two] at hdet
  have hq := isometry_of_mem_Tns g₃.2 v.2
  rw [hq]
  have e00 : Xmat v 0 0 = v.1 (Sum.inl 0) := rfl
  have e01 : Xmat v 0 1 = v.1 (Sum.inl 1) := rfl
  have e10 : Xmat v 1 0 = v.1 (Sum.inr 1) := rfl
  have e11 : Xmat v 1 1 = v.1 (Sum.inr 0) := rfl
  rw [e00, e01, e10, e11] at hdet
  linear_combination hdet + (M 0 1 * M 1 0 - v.1 (Sum.inl 1) * v.1 (Sum.inr 1)) * h2

end Torus

section Inj

variable {K : Type} [Field K]

@[expose] def ofX (X : Matrix (Fin 2) (Fin 2) K) : Vt K :=
  (Sum.elim ![X 0 0, X 0 1, 0] ![X 1 1, X 1 0, 0], 0)

theorem Xmat_ofX (X : Matrix (Fin 2) (Fin 2) K) : Xmat (ofX X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xmat, ofX]

theorem PXQ_eq {P Q S : Matrix (Fin 2) (Fin 2) K} (hv : ∀ v, trFun P Q S v = v)
    (X : Matrix (Fin 2) (Fin 2) K) : P * X * Q = X := by
  have h := hv (ofX X)
  have e := Xmat_ofX X
  have h00 := congrArg (fun w : Vt K => w.1 (Sum.inl 0)) h
  have h01 := congrArg (fun w : Vt K => w.1 (Sum.inl 1)) h
  have h10 := congrArg (fun w : Vt K => w.1 (Sum.inr 1)) h
  have h11 := congrArg (fun w : Vt K => w.1 (Sum.inr 0)) h
  simp only [trFun_inl0, trFun_inl1, trFun_inr0, trFun_inr1, e] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [ofX] using h00
  · simpa [ofX] using h01
  · simpa [ofX] using h10
  · simpa [ofX] using h11

theorem S_eq {P Q S : Matrix (Fin 2) (Fin 2) K} (hv : ∀ v, trFun P Q S v = v) (a : Fin 2 → K) :
    S.mulVec a = a := by
  have h := congrArg (fun w : Vt K => w.2) (hv ((0 : Fin 3 ⊕ Fin 3 → K), a))
  simpa using h

end Inj

section Torus2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem torusHom_injective : Function.Injective (torusHom b c) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨g₁, g₂, g₃⟩ h
  have hv : ∀ v : Vt K, trFun ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((((g₂ : GL (Fin 2) K)⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K)
      ((g₃ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) v = v := fun v => by
    have := congrArg (fun e : Vt K ≃ₗ[K] Vt K => e v) h
    simpa [torusHom_apply, trEquiv_apply] using this
  have hS := S_eq hv
  have h3 : g₃ = 1 := by
    refine Subtype.ext (eq_of_col_eq g₃.2 (one_mem _) ?_ ?_)
    · have := congrFun (hS (Pi.single 0 1)) 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
    · have := congrFun (hS (Pi.single 0 1)) 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hX := PXQ_eq hv
  have h12 : (g₁ : GL (Fin 2) K) = g₂ := by
    have := hX 1
    rw [Matrix.mul_one] at this
    have h' : ((g₁ : GL (Fin 2) K) * ((g₂ : GL (Fin 2) K)⁻¹ : GL (Fin 2) K) : GL (Fin 2) K) = 1 :=
      Units.ext (by simpa using this)
    exact mul_inv_eq_one.1 h'
  have hcomm : ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 1 1 =
      Matrix.single 0 1 1 * ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
    have this := hX (Matrix.single 0 1 1)
    rw [← h12] at this
    have e1 : (((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 1 1 *
        ((((g₁ : GL (Fin 2) K)⁻¹ : GL (Fin 2) K)) : Matrix (Fin 2) (Fin 2) K)) *
        ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * Matrix.single 0 1 1 := by
      rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    rw [← e1, this]
  have h10 : ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    have := congrFun (congrFun hcomm 0) 0
    simpa [Matrix.mul_apply, Matrix.single, Fin.sum_univ_two] using this.symm
  have h1 : g₁ = 1 := by
    obtain ⟨z, hz, hgz⟩ := g₁.2
    have hz2 : z.2 = 0 := by
      have : ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = z.2 := by rw [hgz]; rfl
      rw [← this]; exact h10
    have hz1 : z.1 = 1 := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      simp only [nrm, hz2] at hz
      have : (z.1 - 1) ^ 2 = 0 := by linear_combination hz + (1 - z.1) * h2
      exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    refine Subtype.ext (eq_of_col_eq g₁.2 (one_mem _) ?_ ?_)
    · have : ((g₁ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 = z.1 := by rw [hgz]; rfl
      rw [this, hz1]; rfl
    · rw [h10]; rfl
  have h2 : g₂ = 1 := by
    apply Subtype.ext
    rw [← h12]
    exact congrArg Subtype.val h1
  rw [h1, h2, h3]
  rfl

end Torus2

section Torus3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} [AnisoPair b c]

theorem odd_card_Tns3 : Odd (Nat.card (Tns b c × Tns b c × Tns b c)) := by
  rw [Nat.card_prod, Nat.card_prod, card_Tns]
  have : Odd (Nat.card K + 1) := (even_card_of_charTwo (K := K)).add_one
  exact this.mul (this.mul this)

theorem torusHom_mem_G0 (t : Tns b c × Tns b c × Tns b c) : torusHom b c t ∈ G0 b c :=
  odd_mem_G0 (torusHom_mem_orth t)
    (Odd.of_dvd_nat odd_card_Tns3 ((orderOf_map_dvd _ t).trans (orderOf_dvd_natCard t)))

theorem card_torusHom_range : Nat.card (torusHom b c).range = (Nat.card K + 1) ^ 3 := by
  rw [Nat.card_congr (MonoidHom.ofInjective (torusHom_injective (b := b) (c := c))).toEquiv.symm,
    Nat.card_prod, Nat.card_prod, card_Tns]
  ring

theorem exists_conj_le_torusHom {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hcard : Nat.card ↥(G0 b c) = (Nat.card K) ^ 12 * ((Nat.card K) ^ 4 + 1) *
      (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) * ((Nat.card K) ^ 6 - 1)))
    (hpq : p ∣ Nat.card K + 1) {A : Subgroup (Vt K ≃ₗ[K] Vt K)} (hAG : A ≤ G0 b c)
    (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ h ∈ G0 b c, A.map (MulAut.conj h).toMonoidHom ≤ (torusHom b c).range := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
  have hpr : p ∣ r + 2 := by
    have : Nat.card K + 1 = r + 2 := by omega
    rwa [this] at hpq
  have hrpos : 0 < r + 2 := by omega
  have hG : Nat.card ↥(G0 b c) = (r + 2) ^ 3 * ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) *
      (r ^ 3 * (r ^ 2 + 2 * r + 2) * (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
    rw [hcard, hr]
    exact order_factor_four r
  set Ts : Subgroup (Vt K ≃ₗ[K] Vt K) := (torusHom b c).range with hTs
  have hTsG : Ts ≤ G0 b c := by
    rintro _ ⟨t, rfl⟩
    exact torusHom_mem_G0 t
  set T' : Subgroup ↥(G0 b c) := Ts.subgroupOf (G0 b c) with hT'
  have hT'card : Nat.card T' = (r + 2) ^ 3 := by
    rw [hT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTsG).toEquiv, hTs, card_torusHom_range,
      hr]
  have hindex : T'.index = ((r + 1) ^ 12 * ((r + 1) ^ 4 + 1) *
      (r ^ 3 * (r ^ 2 + 2 * r + 2) * (r ^ 2 + r + 1) * (r ^ 2 + 3 * r + 3))) := by
    have h := T'.card_mul_index
    rw [hT'card, hG] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  have hnd : ¬ p ∣ T'.index := by
    rw [hindex]
    exact not_dvd_cofactor_four Fact.out hp5 hpr
  have hAp : IsPGroup p (A.subgroupOf (G0 b c)) := fun x => ⟨1, by
    have := hA (x : ↥(G0 b c)) (Subgroup.mem_subgroupOf.1 x.2)
    exact Subtype.ext (Subtype.ext (by simpa using this))⟩
  obtain ⟨g, hg⟩ := exists_conj_le_of_not_dvd_index hnd hAp
  refine ⟨(g : Vt K ≃ₗ[K] Vt K), g.2, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  have h1 : (⟨a, hAG ha⟩ : ↥(G0 b c)) ∈ A.subgroupOf (G0 b c) := Subgroup.mem_subgroupOf.2 ha
  have h2 := hg (Subgroup.mem_map_of_mem _ h1)
  rw [hT', Subgroup.mem_subgroupOf] at h2
  simpa [MulAut.conj_apply] using h2

end Torus3

end CFSG.RankThree.PartOne.KF1514B
