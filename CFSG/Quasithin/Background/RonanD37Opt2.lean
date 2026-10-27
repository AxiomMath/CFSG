module

public import CFSG.Quasithin.Background.SmithD37Core
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.RonanD37

open CFSG.Quasithin CFSG.Quasithin.SmithD37
open scoped Matrix

section Model

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F]
  (Mm : MatModel L₁ L₂ F 2)

private def uM (a : F) : Matrix (Fin 2) (Fin 2) F := !![1, a; 0, 1]

private theorem uM_mul (a b : F) : uM a * uM b = uM (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem uM_zero : uM (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uM]

private theorem det_uM (a : F) : (uM a).det = 1 := by
  simp [uM, Matrix.det_fin_two_of]

private theorem uM_conj (a b : F) (X : Matrix (Fin 2) (Fin 2) F) :
    uM a * X * (uM b)ᵀ = !![X 0 0 + a * X 1 0 + b * (X 0 1 + a * X 1 1), X 0 1 + a * X 1 1;
      X 1 0 + b * X 1 1, X 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

private def uGL (a : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  ⟨uM a, uM (-a), by rw [uM_mul, add_neg_cancel, uM_zero], by rw [uM_mul, neg_add_cancel, uM_zero]⟩

private theorem uGL_val (a : F) :
    ((uGL a : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = uM a :=
  rfl

private def co (v : U) : Matrix (Fin 2) (Fin 2) F := Multiplicative.toAdd (Mm.β v)

private theorem co_mul (v w : U) : co Mm (v * w) = co Mm v + co Mm w := by
  simp [co]

private theorem co_inv (v : U) : co Mm v⁻¹ = -co Mm v := by
  simp [co]

private theorem co_one : co Mm 1 = 0 := by
  simp [co]

private theorem co_injective : Function.Injective (co Mm) :=
  fun _ _ h => Mm.β.injective (Multiplicative.toAdd.injective h)

private theorem co_symm (X : Matrix (Fin 2) (Fin 2) F) :
    co Mm (Mm.β.symm (Multiplicative.ofAdd X)) = X := by
  simp [co]

private def HasPar (g : MulAut U) (a b : F) : Prop :=
  ∀ v, co Mm (g v) = uM a * co Mm v * (uM b)ᵀ

variable {Mm}

private theorem hasPar_one : HasPar Mm 1 0 0 := fun v => by
  simp [uM_zero]

private theorem HasPar.mul {g h : MulAut U} {a b a' b' : F} (hg : HasPar Mm g a b)
    (hh : HasPar Mm h a' b') : HasPar Mm (g * h) (a + a') (b + b') := fun v => by
  rw [MulAut.mul_apply, hg (h v), hh v, ← uM_mul, ← uM_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

private theorem HasPar.inv {g : MulAut U} {a b : F} (hg : HasPar Mm g a b) :
    HasPar Mm g⁻¹ (-a) (-b) := fun v => by
  have h := hg (g⁻¹ v)
  rw [MulAut.apply_inv_self] at h
  rw [h]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (uM (-a)), uM_mul, neg_add_cancel, uM_zero, Matrix.one_mul,
    ← Matrix.transpose_mul, uM_mul, neg_add_cancel, uM_zero, Matrix.transpose_one, Matrix.mul_one]

private theorem HasPar.eq {g h : MulAut U} {a b : F} (hg : HasPar Mm g a b)
    (hh : HasPar Mm h a b) : g = h :=
  MulEquiv.ext fun v => co_injective Mm (by rw [hg v, hh v])

private theorem HasPar.par {g : MulAut U} {a b : F} (hg : HasPar Mm g a b) :
    co Mm (g (Mm.β.symm (Multiplicative.ofAdd !![0, 0; 0, 1]))) 0 1 = a ∧
      co Mm (g (Mm.β.symm (Multiplicative.ofAdd !![0, 0; 0, 1]))) 1 0 = b := by
  rw [hg _, co_symm, uM_conj]
  simp

variable (Mm)

private def Bsub : Subgroup (MulAut U) where
  carrier := {g | ∃ a b, HasPar Mm g a b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hg⟩ ⟨a', b', hh⟩
    exact ⟨a + a', b + b', hg.mul hh⟩
  one_mem' := ⟨0, 0, hasPar_one⟩
  inv_mem' := by
    rintro _ ⟨a, b, hg⟩
    exact ⟨-a, -b, hg.inv⟩

private def W₁ : Subgroup U where
  carrier := {v | co Mm v 1 1 = 0}
  mul_mem' := by
    intro v w hv hw
    simp only [Set.mem_setOf_eq, co_mul, Matrix.add_apply] at *
    rw [hv, hw, add_zero]
  one_mem' := by simp [co_one]
  inv_mem' := by
    intro v hv
    simp only [Set.mem_setOf_eq, co_inv, Matrix.neg_apply] at *
    rw [hv, neg_zero]

private theorem exists_hasPar
    (hR₁ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
      ∃ l, Mm.R₁ l = g)
    (hR₂ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
      ∃ k, Mm.R₂ k = g) (a b : F) :
    ∃ g ∈ L₁ ⊔ L₂, HasPar Mm g a b := by
  obtain ⟨l, hl⟩ := hR₁ (uGL a) (det_uM a)
  obtain ⟨k, hk⟩ := hR₂ (uGL b) (det_uM b)
  refine ⟨(l : MulAut U) * (k : MulAut U), Subgroup.mul_mem_sup l.2 k.2, fun v => ?_⟩
  simp only [co, MulAut.mul_apply, Mm.act₁, Mm.act₂, toAdd_ofAdd, hl, hk, uGL_val,
    Matrix.mul_assoc]

variable {Mm}

private theorem mem_fixV_Bsub {v : U} (h01 : co Mm v 0 1 = 0) (h10 : co Mm v 1 0 = 0)
    (h11 : co Mm v 1 1 = 0) : v ∈ fixV (Bsub Mm) := by
  rw [mem_fixV]
  rintro g ⟨a, b, hg⟩
  apply co_injective Mm
  rw [hg v, uM_conj, Matrix.eta_fin_two (co Mm v), h01, h10, h11]
  simp

private theorem entries_of_mem_fixV (hex : ∀ a b : F, ∃ g ∈ L₁ ⊔ L₂, HasPar Mm g a b) {v : U}
    (hv : v ∈ fixV (Bsub Mm)) : co Mm v 0 1 = 0 ∧ co Mm v 1 0 = 0 ∧ co Mm v 1 1 = 0 := by
  obtain ⟨g₁, -, hg₁⟩ := hex 1 0
  obtain ⟨g₂, -, hg₂⟩ := hex 0 1
  have e₁ := hg₁ v
  have e₂ := hg₂ v
  rw [mem_fixV.mp hv g₁ ⟨1, 0, hg₁⟩, uM_conj] at e₁
  rw [mem_fixV.mp hv g₂ ⟨0, 1, hg₂⟩, uM_conj] at e₂
  have a1 := congrFun (congrFun e₁ 0) 0
  have a2 := congrFun (congrFun e₁ 0) 1
  have a3 := congrFun (congrFun e₂ 0) 0
  simp at a1 a2 a3
  exact ⟨a3, a1, a2⟩

end Model

variable {U : Type} [CommGroup U] [Finite U] {L₁ L₂ : Subgroup (MulAut U)}
  {F : Type} [Field F] [Fintype F] [CharP F 2]

theorem exists_opt_two (Mm : MatModel L₁ L₂ F 2)
    (hR₁ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
      ∃ l, Mm.R₁ l = g)
    (hR₂ : ∀ g : Matrix.GeneralLinearGroup (Fin 2) F, (g : Matrix (Fin 2) (Fin 2) F).det = 1 →
      ∃ k, Mm.R₂ k = g)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    ∃ B : Subgroup (MulAut U), B ≤ L₁ ⊔ L₂ ∧ B ≠ ⊥ ∧ IsElemAbelian2 B ∧ commSeries B 3 = ⊥ ∧
      rk B = 2 * n ∧ rkIdx (fixV B) = 3 * n := by
  have hex := exists_hasPar Mm hR₁ hR₂
  have hB : Nat.card (Bsub Mm) = Nat.card F * Nat.card F := by
    rw [← Nat.card_prod]
    refine Nat.card_eq_of_bijective
      (fun g => (co Mm (g.1 (Mm.β.symm (Multiplicative.ofAdd !![0, 0; 0, 1]))) 0 1,
        co Mm (g.1 (Mm.β.symm (Multiplicative.ofAdd !![0, 0; 0, 1]))) 1 0)) ⟨?_, ?_⟩
    · rintro ⟨g, a, b, hg⟩ ⟨h, a', b', hh⟩ hgh
      obtain ⟨h1, h2⟩ := hg.par
      obtain ⟨h1', h2'⟩ := hh.par
      simp only [Prod.mk.injEq] at hgh
      rw [h1, h2, h1', h2'] at hgh
      obtain ⟨rfl, rfl⟩ := hgh
      exact Subtype.ext (hg.eq hh)
    · rintro ⟨a, b⟩
      obtain ⟨g, -, hg⟩ := hex a b
      exact ⟨⟨g, a, b, hg⟩, Prod.ext hg.par.1 hg.par.2⟩
  have hfix : Nat.card (fixV (Bsub Mm)) = Nat.card F := by
    refine Nat.card_eq_of_bijective (fun v => co Mm v.1 0 0) ⟨?_, ?_⟩
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
      have hvw' : co Mm v 0 0 = co Mm w 0 0 := hvw
      obtain ⟨v1, v2, v3⟩ := entries_of_mem_fixV hex hv
      obtain ⟨w1, w2, w3⟩ := entries_of_mem_fixV hex hw
      refine Subtype.ext (co_injective Mm ?_)
      rw [Matrix.eta_fin_two (co Mm v), Matrix.eta_fin_two (co Mm w), hvw', v1, v2, v3, w1, w2,
        w3]
    · intro c
      refine ⟨⟨Mm.β.symm (Multiplicative.ofAdd !![c, 0; 0, 0]), mem_fixV_Bsub ?_ ?_ ?_⟩, ?_⟩ <;>
        simp [co_symm]
  have hU : Nat.card U = Nat.card F ^ 4 := by
    rw [Nat.card_congr (Mm.β.toEquiv.trans Multiplicative.toAdd)]
    change Nat.card (Fin 2 → Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul]
  have hidx : (fixV (Bsub Mm)).index = 2 ^ (3 * n) := by
    have h := (fixV (Bsub Mm)).card_mul_index
    rw [hfix, hU, hF] at h
    have h4 : 2 ^ n * (fixV (Bsub Mm)).index = 2 ^ n * 2 ^ (3 * n) := by
      rw [h, ← pow_mul, ← pow_add]
      congr 1
      ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h4
  refine ⟨Bsub Mm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro g ⟨a, b, hg⟩
    obtain ⟨g', hg'L, hg'⟩ := hex a b
    rwa [hg.eq hg']
  · intro h
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [h, Subgroup.card_bot] at hB
    nlinarith
  · refine ⟨?_, ?_⟩
    · rintro g ⟨a, b, hg⟩ h ⟨a', b', hh⟩
      refine (hg.mul hh).eq ?_
      rw [add_comm a, add_comm b]
      exact hh.mul hg
    · rintro g ⟨a, b, hg⟩
      have h2 := hg.mul hg
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero] at h2
      rw [pow_two]
      exact h2.eq hasPar_one
  ·
    have h1 : commSub ⊤ (Bsub Mm) ≤ W₁ Mm := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, ⟨a, b, hx⟩, w, -, rfl⟩
      show co Mm (x w * w⁻¹) 1 1 = 0
      rw [co_mul, co_inv, hx w, uM_conj]
      simp
    have h2 : commSub (W₁ Mm) (Bsub Mm) ≤ fixV (Bsub Mm) := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, ⟨a, b, hx⟩, w, hw, rfl⟩
      have hw' : co Mm w 1 1 = 0 := hw
      apply mem_fixV_Bsub <;> rw [co_mul, co_inv, hx w, uM_conj] <;> simp [hw']
    have h3 : commSub (fixV (Bsub Mm)) (Bsub Mm) = ⊥ := commSub_eq_bot_iff.mpr le_rfl
    show commSub (commSub (commSub ⊤ (Bsub Mm)) (Bsub Mm)) (Bsub Mm) = ⊥
    exact le_bot_iff.mp (h3 ▸ commSub_mono ((commSub_mono h1 le_rfl).trans h2) le_rfl)
  · show padicValNat 2 (Nat.card (Bsub Mm)) = 2 * n
    rw [hB, hF, ← pow_add, padicValNat.prime_pow, two_mul]
  · show padicValNat 2 (fixV (Bsub Mm)).index = 3 * n
    rw [hidx, padicValNat.prime_pow]

end CFSG.Quasithin.RonanD37
