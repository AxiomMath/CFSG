module

public import CFSG.Quasithin.H13.A6S1372L76Oh1
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (leviSp coe_leviSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent exists_sylow_unipotent)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (tau lam sym2 coe_tau coe_lam
  tau_mem_unipotent lam_mem_unipotent sym2_transpose unitri)
open scoped Pointwise IsMulCommutative Matrix

namespace A6L76Oh

variable {F : Type} [Field F]

@[expose] def spHom : ↥(StatedSp 2 F) →* MulAut (Multiplicative (Fin 2 ⊕ Fin 2 → F)) :=
  glHomG.comp (StatedSp 2 F).subtype

theorem spHom_apply (γ : ↥(StatedSp 2 F)) (m : Multiplicative (Fin 2 ⊕ Fin 2 → F)) :
    Multiplicative.toAdd (spHom γ m) =
      ((γ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
        Multiplicative.toAdd m := rfl

theorem tau_mulVec {C : Matrix (Fin 2) (Fin 2) F} (hC : Cᵀ = C) (v : Fin 2 ⊕ Fin 2 → F) :
    (((tau hC : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      Sum.elim (v ∘ Sum.inl + C *ᵥ (v ∘ Sum.inr)) (v ∘ Sum.inr) := by
  rw [coe_tau, Matrix.fromBlocks_mulVec, Matrix.one_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec, zero_add]

theorem lam_mulVec (a : F) (v : Fin 2 ⊕ Fin 2 → F) :
    (((lam a : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v =
      Sum.elim (unitri a *ᵥ (v ∘ Sum.inl)) ((unitri (-a))ᵀ *ᵥ (v ∘ Sum.inr)) := by
  rw [coe_lam, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero,
    zero_add]

theorem tau_diag_sub (b d : F) (v : Fin 2 ⊕ Fin 2 → F) :
    (((tau (sym2_transpose b 0 d) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v =
      Pi.single (Sum.inl 0) (b * v (Sum.inr 0)) + Pi.single (Sum.inl 1) (d * v (Sum.inr 1)) := by
  rw [tau_mulVec]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [sym2, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail]

theorem lam_sub (a : F) (v : Fin 2 ⊕ Fin 2 → F) :
    (((lam a : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v =
      Pi.single (Sum.inl 0) (a * v (Sum.inl 1)) + Pi.single (Sum.inr 1) (-a * v (Sum.inr 0)) := by
  rw [lam_mulVec]
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [unitri, dotProduct, Fin.sum_univ_two]

theorem unipotent_fix {v : Fin 2 ⊕ Fin 2 → F}
    (hv : ∀ u ∈ unipotent 2 F, ((u : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = v) :
    v (Sum.inl 1) = 0 ∧ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  have h1 := hv _ (tau_mem_unipotent (sym2_transpose 1 0 1))
  have h2 := hv _ (lam_mem_unipotent (1 : F))
  rw [← sub_eq_zero, tau_diag_sub] at h1
  rw [← sub_eq_zero, lam_sub] at h2
  have e1 := congrFun h1 (Sum.inl 0)
  have e2 := congrFun h1 (Sum.inl 1)
  have e3 := congrFun h2 (Sum.inl 0)
  simp at e1 e2 e3
  exact ⟨e3, e1, e2⟩

theorem unipotent_comm [Finite F] (hq : 2 < Nat.card F) {w v : Fin 2 ⊕ Fin 2 → F} (hw : w ≠ 0)
    (hw' : w (Sum.inl 1) = 0 ∧ w (Sum.inr 0) = 0 ∧ w (Sum.inr 1) = 0)
    (hv : ∀ u ∈ unipotent 2 F, ((u : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v = 0 ∨
      ((u : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v - v = w) :
    v (Sum.inl 1) = 0 ∧ v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hw0 : w (Sum.inl 0) ≠ 0 := by
    intro h0
    apply hw
    funext i
    rcases i with i | i <;> fin_cases i
    · exact h0
    · exact hw'.1
    · exact hw'.2.1
    · exact hw'.2.2
  obtain ⟨c, hc0, hc1⟩ : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun c _ => by
      by_cases h : c = 0
      · simp [h]
      · simp [hcon c h]
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h2
    have h3 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
    omega
  have key : ∀ t : F, (Pi.single (Sum.inl 0) t : Fin 2 ⊕ Fin 2 → F) = 0 ∨
      (Pi.single (Sum.inl 0) t : Fin 2 ⊕ Fin 2 → F) = w →
      (Pi.single (Sum.inl 0) (c * t) : Fin 2 ⊕ Fin 2 → F) = 0 ∨
      (Pi.single (Sum.inl 0) (c * t) : Fin 2 ⊕ Fin 2 → F) = w → t = 0 := by
    intro t h1 h2
    by_contra ht
    rcases h1 with h1 | h1
    · exact ht (by simpa using congrFun h1 (Sum.inl 0))
    · rcases h2 with h2 | h2
      · have := congrFun h2 (Sum.inl 0)
        simp only [Pi.single_eq_same, Pi.zero_apply] at this
        exact mul_ne_zero hc0 ht this
      · have e1 := congrFun h1 (Sum.inl 0)
        have e2 := congrFun h2 (Sum.inl 0)
        simp only [Pi.single_eq_same] at e1 e2
        apply hc1
        have : c * t = 1 * t := by rw [one_mul]; exact e2.trans e1.symm
        exact mul_right_cancel₀ ht this
  have hy0 : v (Sum.inr 0) = 0 := by
    have h1 := hv _ (tau_mem_unipotent (sym2_transpose 1 0 0))
    have h2 := hv _ (tau_mem_unipotent (sym2_transpose c 0 0))
    rw [tau_diag_sub, zero_mul, Pi.single_zero, add_zero] at h1 h2
    have := key (v (Sum.inr 0)) (by rwa [one_mul] at h1) h2
    exact this
  have hy1 : v (Sum.inr 1) = 0 := by
    have h1 := hv _ (tau_mem_unipotent (sym2_transpose 0 0 1))
    rw [tau_diag_sub, zero_mul, Pi.single_zero, zero_add, one_mul] at h1
    rcases h1 with h1 | h1
    · simpa using congrFun h1 (Sum.inl 1)
    · exfalso
      apply hw0
      rw [← h1]
      simp
  have hx1 : v (Sum.inl 1) = 0 := by
    have h1 := hv _ (lam_mem_unipotent (1 : F))
    have h2 := hv _ (lam_mem_unipotent c)
    rw [lam_sub, hy0, mul_zero, Pi.single_zero, add_zero] at h1 h2
    exact key (v (Sum.inl 1)) (by rwa [one_mul] at h1) h2
  exact ⟨hx1, hy0, hy1⟩

theorem exists_conj_unipotent [Finite F] [CharP F 2] {P : Subgroup ↥(StatedSp 2 F)}
    (hP : IsPGroup 2 ↥P) (hodd : ¬ 2 ∣ P.index) :
    ∃ g : ↥(StatedSp 2 F), ∀ x ∈ unipotent 2 F, g⁻¹ * x * g ∈ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := F) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥(StatedSp 2 F)) (hP.toSylow hodd) Q
  refine ⟨g, fun x hx => ?_⟩
  rw [← hQ, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    IsPGroup.toSylow_coe] at hx
  exact hx

@[expose] def leviSpMat (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks (Matrix.diagonal ![1, A 0 0]) (Matrix.diagonal ![0, A 0 1])
    (Matrix.diagonal ![0, A 1 0]) (Matrix.diagonal ![1, A 1 1])

theorem leviSpMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    leviSpMat A * leviSpMat B = leviSpMat (A * B) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [leviSpMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.diagonal]

theorem leviSpMat_one : leviSpMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [leviSpMat, Matrix.diagonal]

theorem leviSpMat_symp {A : Matrix (Fin 2) (Fin 2) F} (hA : A.det = 1) :
    (leviSpMat A)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 * leviSpMat A = Matrix.fromBlocks 0 1 (-1) 0 := by
  rw [Matrix.det_fin_two] at hA
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [leviSpMat, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal, Matrix.one_apply] <;>
    first
    | ring1
    | linear_combination hA
    | linear_combination (-1 : F) * hA

@[expose] noncomputable def leviSp1 :
    Matrix.SpecialLinearGroup (Fin 2) F →* ↥(StatedSp 2 F) where
  toFun A := ⟨⟨leviSpMat (A : Matrix (Fin 2) (Fin 2) F),
      leviSpMat ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F),
      by rw [leviSpMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.SpecialLinearGroup.coe_one, leviSpMat_one],
      by rw [leviSpMat_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one, leviSpMat_one]⟩,
    Subgroup.subset_closure (leviSpMat_symp A.2)⟩
  map_one' := Subtype.ext (Units.ext (by
    show leviSpMat ((1 : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, leviSpMat_one]))
  map_mul' A B := Subtype.ext (Units.ext (by
    show leviSpMat ((A * B : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      leviSpMat (A : Matrix (Fin 2) (Fin 2) F) * leviSpMat (B : Matrix (Fin 2) (Fin 2) F)
    rw [leviSpMat_mul, Matrix.SpecialLinearGroup.coe_mul]))

theorem leviSp1_coe (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((leviSp1 A : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = leviSpMat (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem leviSp1_injective : Function.Injective (leviSp1 (F := F)) := by
  intro A B h
  have h1 : leviSpMat (A : Matrix (Fin 2) (Fin 2) F) = leviSpMat (B : Matrix (Fin 2) (Fin 2) F) :=
    congrArg (fun C : ↥(StatedSp 2 F) =>
      ((C : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [leviSpMat, Matrix.diagonal] using congrFun (congrFun h1 (Sum.inl 1)) (Sum.inl 1)
  · simpa [leviSpMat, Matrix.diagonal] using congrFun (congrFun h1 (Sum.inl 1)) (Sum.inr 1)
  · simpa [leviSpMat, Matrix.diagonal] using congrFun (congrFun h1 (Sum.inr 1)) (Sum.inl 1)
  · simpa [leviSpMat, Matrix.diagonal] using congrFun (congrFun h1 (Sum.inr 1)) (Sum.inr 1)

theorem leviSpMat_mulVec {A : Matrix (Fin 2) (Fin 2) F} {x : Fin 2 ⊕ Fin 2 → F}
    (h1 : x (Sum.inl 1) = 0) (h2 : x (Sum.inr 1) = 0) : leviSpMat A *ᵥ x = x := by
  funext i
  rcases i with i | i <;> fin_cases i <;>
    simp [leviSpMat, Matrix.mulVec, dotProduct, Matrix.diagonal, h1, h2]

theorem spHom_fixed {m : Multiplicative (Fin 2 ⊕ Fin 2 → F)} (h : ∀ γ, spHom γ m = m) :
    m = 1 := by
  have hU : ∀ u ∈ unipotent 2 F, ((u : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ Multiplicative.toAdd m =
        Multiplicative.toAdd m := fun u _ => congrArg Multiplicative.toAdd (h u)
  obtain ⟨h1, h2, h3⟩ := unipotent_fix hU
  have hdet : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp
  have h4 := congrArg Multiplicative.toAdd
    (h (leviSp (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)))
  rw [spHom_apply, coe_leviSp] at h4
  have h5 := congrFun h4 (Sum.inl 1)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1] at h5
  apply Multiplicative.toAdd.injective
  funext i
  rcases i with i | i <;> fin_cases i
  · simpa using h5
  · exact h1
  · exact h2
  · exact h3

end A6L76Oh

end CFSG.Quasithin.H13.A6
