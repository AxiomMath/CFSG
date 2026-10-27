module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSSp4Weyl
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank
open Matrix
open scoped Matrix

variable {K : Type} [Field K]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def IsPointUnip (g : StatedSp 2 K) : Prop :=
  (∀ i j : Fin 2 ⊕ Fin 2, j ≠ Sum.inr 0 → i ≠ Sum.inl 0 →
      (spMat g) i j = if i = j then 1 else 0) ∧
    (spMat g) (Sum.inr 0) (Sum.inr 0) = 1

def qMat (α β γ : K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.of fun i j =>
    if i = Sum.inl 0 then
      if j = Sum.inl 0 then 1 else if j = Sum.inl 1 then α else if j = Sum.inr 0 then γ else β
    else if i = Sum.inl 1 then
      if j = Sum.inl 1 then 1 else if j = Sum.inr 0 then β else 0
    else if i = Sum.inr 0 then
      if j = Sum.inr 0 then 1 else 0
    else if j = Sum.inr 0 then -α else if j = Sum.inr 1 then 1 else 0

theorem qMat_zero : qMat (0 : K) 0 0 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp [qMat]

theorem qMat_inl_zero_inr_zero (γ : K) :
    qMat 0 0 γ = pairRootMat K (Sum.inl 0) (Sum.inr 0) γ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat, pairRootMat, rootNil]

theorem qMat_zero_beta_zero (β : K) :
    qMat 0 β 0 = pairRootMat K (Sum.inl 0) (Sum.inr 1) β := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat, pairRootMat, rootNil, lineSign]

theorem qMat_alpha_zero_zero (α : K) :
    qMat α 0 0 = pairRootMat K (Sum.inl 0) (Sum.inl 1) α := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat, pairRootMat, rootNil, lineSign]

theorem spMat_pairRootElt_inl_zero_inr_zero (γ : K) :
    (spMat (pairRootElt (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0) γ)) =
      qMat 0 0 γ := by
  rw [coe_pairRootElt]
  exact (qMat_inl_zero_inr_zero γ).symm

theorem spMat_pairRootElt_inl_zero_inr_one (β : K) :
    (spMat (pairRootElt (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 1) β)) =
      qMat 0 β 0 := by
  rw [coe_pairRootElt]
  exact (qMat_zero_beta_zero β).symm

theorem spMat_pairRootElt_inl_zero_inl_one (α : K) :
    (spMat (pairRootElt ((by simp : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inl 1)) α)) =
      qMat α 0 0 := by
  rw [coe_pairRootElt]
  exact (qMat_alpha_zero_zero α).symm

theorem transpose_mul_J_mul_apply [CharP K 2]
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (u v : Fin 2 ⊕ Fin 2) :
    (Mᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * M) u v =
      ∑ i : Fin 2,
        (M (Sum.inl i) u * M (Sum.inr i) v - M (Sum.inr i) u * M (Sum.inl i) v) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring

theorem eq_qMat_of_isPointUnip [CharP K 2] {g : StatedSp 2 K} (hg : IsPointUnip g) :
    (spMat g) = qMat ((spMat g) (Sum.inl 0) (Sum.inl 1)) ((spMat g) (Sum.inl 0) (Sum.inr 1))
      ((spMat g) (Sum.inl 0) (Sum.inr 0)) := by
  classical
  have hJ : (spMat g)ᵀ * fromBlocks 0 1 (-1) 0 * (spMat g) = fromBlocks 0 1 (-1) 0 :=
    mem_statedSp_iff.mp g.2
  have h10 : (spMat g) (Sum.inl 1) (Sum.inl 0) = 0 := by
    rw [hg.1 (Sum.inl 1) (Sum.inl 0) (by decide) (by decide)]
    simp
  have h20 : (spMat g) (Sum.inr 0) (Sum.inl 0) = 0 := by
    rw [hg.1 (Sum.inr 0) (Sum.inl 0) (by decide) (by decide)]
    simp
  have h30 : (spMat g) (Sum.inr 1) (Sum.inl 0) = 0 := by
    rw [hg.1 (Sum.inr 1) (Sum.inl 0) (by decide) (by decide)]
    simp
  have h11 : (spMat g) (Sum.inl 1) (Sum.inl 1) = 1 := by
    rw [hg.1 (Sum.inl 1) (Sum.inl 1) (by decide) (by decide)]
    simp
  have h21 : (spMat g) (Sum.inr 0) (Sum.inl 1) = 0 := by
    rw [hg.1 (Sum.inr 0) (Sum.inl 1) (by decide) (by decide)]
    simp
  have h31 : (spMat g) (Sum.inr 1) (Sum.inl 1) = 0 := by
    rw [hg.1 (Sum.inr 1) (Sum.inl 1) (by decide) (by decide)]
    simp
  have h13 : (spMat g) (Sum.inl 1) (Sum.inr 1) = 0 := by
    rw [hg.1 (Sum.inl 1) (Sum.inr 1) (by decide) (by decide)]
    simp
  have h23 : (spMat g) (Sum.inr 0) (Sum.inr 1) = 0 := by
    rw [hg.1 (Sum.inr 0) (Sum.inr 1) (by decide) (by decide)]
    simp
  have h33 : (spMat g) (Sum.inr 1) (Sum.inr 1) = 1 := by
    rw [hg.1 (Sum.inr 1) (Sum.inr 1) (by decide) (by decide)]
    simp
  have h22 : (spMat g) (Sum.inr 0) (Sum.inr 0) = 1 := hg.2
  have h00 : (spMat g) (Sum.inl 0) (Sum.inl 0) = 1 := by
    have h := congrFun (congrFun hJ (Sum.inl 0)) (Sum.inr 0)
    rw [transpose_mul_J_mul_apply (K := K) (M := (spMat g)) (u := Sum.inl 0)
      (v := Sum.inr 0)] at h
    simp [Fin.sum_univ_two, h10, h20, h30, h22] at h
    simpa using h
  have hbeta : (spMat g) (Sum.inl 1) (Sum.inr 0) = (spMat g) (Sum.inl 0) (Sum.inr 1) := by
    have h := congrFun (congrFun hJ (Sum.inr 0)) (Sum.inr 1)
    rw [transpose_mul_J_mul_apply (K := K) (M := (spMat g)) (u := Sum.inr 0)
      (v := Sum.inr 1)] at h
    simp [Fin.sum_univ_two, h13, h22, h23, h33] at h
    linear_combination h
  have halpha :
      (spMat g) (Sum.inr 1) (Sum.inr 0) = -((spMat g) (Sum.inl 0) (Sum.inl 1)) := by
    have h := congrFun (congrFun hJ (Sum.inl 1)) (Sum.inr 0)
    rw [transpose_mul_J_mul_apply (K := K) (M := (spMat g)) (u := Sum.inl 1)
      (v := Sum.inr 0)] at h
    simp [Fin.sum_univ_two, h11, h21, h22, h31] at h
    linear_combination h
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat, h10, h20, h30, h11, h21, h31, h13, h23, h33, h22, h00, hbeta, halpha]

theorem qMat_mul [CharP K 2] (α β γ α' β' γ' : K) :
    qMat α β γ * qMat α' β' γ' = qMat (α + α') (β + β') (γ + γ' + α * β' + α' * β) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq] <;> ring

theorem spMat_conj_torusHom (t : Fin 2 → Kˣ) (g : StatedSp 2 K) :
    (spMat (torusHom t * g * (torusHom t)⁻¹)) =
      diagonal (Sum.elim (fun i => (t i : K)) fun i => ((t i : K))⁻¹) * (spMat g) *
        diagonal (Sum.elim (fun i => ((t i : K))⁻¹) fun i => (t i : K)) := by
  have h1 : (spMat (torusHom t)) =
      diagonal (Sum.elim (fun i => (t i : K)) fun i => ((t i : K))⁻¹) := by
    rw [coe_torusHom]
    simp only [← Units.val_inv_eq_inv_val]
  have h2 : (spMat ((torusHom t)⁻¹)) =
      diagonal (Sum.elim (fun i => ((t i : K))⁻¹) fun i => (t i : K)) := by
    rw [← map_inv, coe_torusHom]
    congr 1
    funext x
    rcases x with x | x <;> simp
  rw [TorusQS.spMat_mul, TorusQS.spMat_mul, h1, h2]

theorem spMat_conj_torusHom_const [CharP K 2] (a : Kˣ) (g : StatedSp 2 K) (α β γ : K)
    (h : (spMat g) = qMat α β γ) :
    (spMat (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) =
      qMat α ((a : K) * (a : K) * β) ((a : K) * (a : K) * γ) := by
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  rw [spMat_conj_torusHom, h]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat] <;> (try field_simp [ha0])

theorem spMat_conj_torusHom_inv [CharP K 2] (a : Kˣ) (g : StatedSp 2 K) (α β γ : K)
    (h : (spMat g) = qMat α β γ) :
    (spMat (torusHom ![a, a⁻¹] * g * (torusHom ![a, a⁻¹])⁻¹)) =
      qMat ((a : K) * (a : K) * α) β ((a : K) * (a : K) * γ) := by
  have ha0 : (a : K) ≠ 0 := a.ne_zero
  rw [spMat_conj_torusHom, h]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [qMat] <;> (try field_simp [ha0])

theorem qMat_mul_conj_const [CharP K 2] (a : Kˣ) (α β γ : K) :
    qMat α β γ * qMat α ((a : K) * (a : K) * β) ((a : K) * (a : K) * γ) =
      qMat 0 ((1 + (a : K) * (a : K)) * β) ((1 + (a : K) * (a : K)) * (γ + α * β)) := by
  rw [qMat_mul]
  have h1 : α + α = 0 := CharTwo.add_self_eq_zero α
  have h2 : β + (a : K) * (a : K) * β = (1 + (a : K) * (a : K)) * β := by ring
  have h3 : γ + (a : K) * (a : K) * γ + α * ((a : K) * (a : K) * β) + α * β =
      (1 + (a : K) * (a : K)) * (γ + α * β) := by ring
  rw [h1, h2, h3]

theorem qMat_mul_conj_inv [CharP K 2] (a : Kˣ) (β γ : K) :
    qMat 0 β γ * qMat ((a : K) * (a : K) * 0) β ((a : K) * (a : K) * γ) =
      qMat 0 0 ((1 + (a : K) * (a : K)) * γ) := by
  rw [qMat_mul]
  have h1 : 0 + (a : K) * (a : K) * 0 = 0 := by ring
  have h2 : β + β = 0 := CharTwo.add_self_eq_zero β
  have h3 : γ + (a : K) * (a : K) * γ + 0 * β + ((a : K) * (a : K) * 0) * β =
      (1 + (a : K) * (a : K)) * γ := by ring
  rw [h1, h2, h3]

theorem exists_unit_ne_one_add_mul_ne_zero [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K) :
    ∃ a : Kˣ, a ≠ 1 ∧ (1 : K) + (a : K) * (a : K) ≠ 0 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hne : ζ ≠ 1 := by
    intro h
    have h1 : orderOf ζ = 1 := by rw [h, orderOf_one]
    omega
  refine ⟨ζ, hne, ?_⟩
  intro hzero
  apply hne
  have hsq : (ζ : K) * (ζ : K) = 1 := by
    calc (ζ : K) * (ζ : K) = (ζ : K) * (ζ : K) + 0 := (add_zero _).symm
      _ = (ζ : K) * (ζ : K) + (1 + (ζ : K) * (ζ : K)) := by rw [hzero]
      _ = 1 := by
          rw [add_comm (1 : K) ((ζ : K) * (ζ : K)), ← add_assoc,
            CharTwo.add_self_eq_zero ((ζ : K) * (ζ : K)), zero_add]
  have h1 : (ζ : K) = 1 := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  exact Units.ext h1

theorem eq_one_of_isPointUnip [Finite K] [CharP K 2] (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {g : StatedSp 2 K} (hg : g ∈ X) (hgQ : IsPointUnip g) : g = 1 := by
  classical
  obtain ⟨a, ha1, ha2⟩ := exists_unit_ne_one_add_mul_ne_zero (K := K) hK
  set α : K := (spMat g) (Sum.inl 0) (Sum.inl 1) with hα
  set β : K := (spMat g) (Sum.inl 0) (Sum.inr 1) with hβ
  set γ : K := (spMat g) (Sum.inl 0) (Sum.inr 0) with hγ
  have hshape : (spMat g) = qMat α β γ := by
    rw [hα, hβ, hγ]
    exact eq_qMat_of_isPointUnip hgQ
  have h1X : torusHom ![a, a] ∈ X := hT (torusHom_mem_torus (r := 2) (k := K) ![a, a])
  have h2X : torusHom ![a, a⁻¹] ∈ X :=
    hT (torusHom_mem_torus (r := 2) (k := K) ![a, a⁻¹])
  have hG1X : g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹) ∈ X :=
    X.mul_mem hg (X.mul_mem (X.mul_mem h1X hg) (X.inv_mem h1X))
  have hconj1 : (spMat (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) =
      qMat α ((a : K) * (a : K) * β) ((a : K) * (a : K) * γ) :=
    spMat_conj_torusHom_const a g α β γ hshape
  have hG1 : (spMat (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹))) =
      qMat 0 ((1 + (a : K) * (a : K)) * β) ((1 + (a : K) * (a : K)) * (γ + α * β)) := by
    rw [TorusQS.spMat_mul, hconj1, hshape]
    exact qMat_mul_conj_const a α β γ
  have hG2X : g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹) *
      (torusHom ![a, a⁻¹] * (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) *
        (torusHom ![a, a⁻¹])⁻¹) ∈ X :=
    X.mul_mem hG1X (X.mul_mem (X.mul_mem h2X hG1X) (X.inv_mem h2X))
  have hconj2 : (spMat (torusHom ![a, a⁻¹] *
      (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) * (torusHom ![a, a⁻¹])⁻¹)) =
      qMat ((a : K) * (a : K) * 0) ((1 + (a : K) * (a : K)) * β)
        ((a : K) * (a : K) * ((1 + (a : K) * (a : K)) * (γ + α * β))) :=
    spMat_conj_torusHom_inv a (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) 0 _ _ hG1
  have hG2 : (spMat (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹) *
      (torusHom ![a, a⁻¹] * (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) *
        (torusHom ![a, a⁻¹])⁻¹))) =
      qMat 0 0 ((1 + (a : K) * (a : K)) * ((1 + (a : K) * (a : K)) * (γ + α * β))) := by
    rw [TorusQS.spMat_mul, hconj2, hG1]
    exact qMat_mul_conj_inv a _ _
  have hC : γ + α * β = 0 := by
    have hroot : (1 + (a : K) * (a : K)) * ((1 + (a : K) * (a : K)) * (γ + α * β)) = 0 := by
      refine hX (Sum.inl 0) (Sum.inr 0)
        (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0)
        ((1 + (a : K) * (a : K)) * ((1 + (a : K) * (a : K)) * (γ + α * β))) ?_
      have hEq : g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹) *
          (torusHom ![a, a⁻¹] * (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹)) *
            (torusHom ![a, a⁻¹])⁻¹) =
          pairRootElt (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0)
            ((1 + (a : K) * (a : K)) * ((1 + (a : K) * (a : K)) * (γ + α * β))) := by
        apply statedSp_ext
        rw [hG2, spMat_pairRootElt_inl_zero_inr_zero]
      rw [← hEq]
      exact hG2X
    rcases mul_eq_zero.mp hroot with h | h
    · exact absurd h ha2
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' ha2
      · exact h'
  have hG1' : (spMat (g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹))) =
      qMat 0 ((1 + (a : K) * (a : K)) * β) 0 := by
    rw [hG1, hC, mul_zero]
  have hB : (1 + (a : K) * (a : K)) * β = 0 := by
    refine hX (Sum.inl 0) (Sum.inr 1)
      (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 1)
      ((1 + (a : K) * (a : K)) * β) ?_
    have hEq : g * (torusHom ![a, a] * g * (torusHom ![a, a])⁻¹) =
        pairRootElt (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 1)
          ((1 + (a : K) * (a : K)) * β) := by
      apply statedSp_ext
      rw [hG1', spMat_pairRootElt_inl_zero_inr_one]
    rw [← hEq]
    exact hG1X
  have hβ0 : β = 0 := by
    rcases mul_eq_zero.mp hB with h | h
    · exact absurd h ha2
    · exact h
  have hγ0 : γ = 0 := by
    rw [hβ0, mul_zero, add_zero] at hC
    exact hC
  have hαroot : (spMat g) = qMat α 0 0 := by rw [hshape, hβ0, hγ0]
  have hα0 : α = 0 := by
    refine hX (Sum.inl 0) (Sum.inl 1)
      ((by simp : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inl 1)) α ?_
    have hEq : g = pairRootElt
        ((by simp : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inl 1)) α := by
      apply statedSp_ext
      rw [hαroot, spMat_pairRootElt_inl_zero_inl_one]
    rw [← hEq]
    exact hg
  apply statedSp_ext
  rw [hshape, hα0, hβ0, hγ0, qMat_zero]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
