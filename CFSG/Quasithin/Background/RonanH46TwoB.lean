module

public import CFSG.Quasithin.Background.RonanH46Comm

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44 CFSG.Quasithin.RonanH45
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem twoB_mat22_of_mem (hK : Nat.card K = (2 ^ 1) ^ 2) {X : HMod 1 K}
    (hX : X ∈ commOnR ⊤ (LW hK)) : mat X 2 2 = 0 :=
  mem_Hhyp.1 (commOnR_le_Hhyp hK hX)

private theorem twoB_mem_of_mat22 (hK : Nat.card K = (2 ^ 1) ^ 2) {X : HMod 1 K}
    (hX : mat X 2 2 = 0) : X ∈ commOnR ⊤ (LW hK) :=
  Hhyp_le_commOnR hK (mem_Hhyp.2 hX)

private def twoBCol (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ↥(commOnR ⊤ (LW hK)) →* Multiplicative (Fin 2 → K) where
  toFun u := Multiplicative.ofAdd (![mat (u : HMod 1 K) 0 2, mat (u : HMod 1 K) 1 2] : Fin 2 → K)
  map_one' := by
    try dsimp only
    rw [ofAdd_eq_one]
    funext i
    fin_cases i <;> simp [mat_one]
  map_mul' u v := by
    try dsimp only
    rw [← ofAdd_add]
    congr 1
    funext i
    fin_cases i <;> simp [mat_mul]

private theorem twoBCol_apply (hK : Nat.card K = (2 ^ 1) ^ 2) (u : ↥(commOnR ⊤ (LW hK))) :
    twoBCol hK u =
      Multiplicative.ofAdd (![mat (u : HMod 1 K) 0 2, mat (u : HMod 1 K) 1 2] : Fin 2 → K) :=
  rfl

private theorem twoBCol_surjective (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Function.Surjective (twoBCol hK) := by
  intro y
  have h22 : mat (colH hK (Multiplicative.toAdd y)) 2 2 = 0 := by
    simp [mat_colH, colMat]
  refine ⟨⟨colH hK (Multiplicative.toAdd y), twoB_mem_of_mat22 hK h22⟩, ?_⟩
  rw [twoBCol_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  funext i
  fin_cases i <;> simp [mat_colH, colMat]

private theorem twoBCol_eq_one_iff (hK : Nat.card K = (2 ^ 1) ^ 2)
    (u : ↥(commOnR ⊤ (LW hK))) :
    twoBCol hK u = 1 ↔ (u : HMod 1 K) ∈ blkW 1 K := by
  have h22 : mat (u : HMod 1 K) 2 2 = 0 := twoB_mat22_of_mem hK u.2
  rw [twoBCol_apply, ofAdd_eq_one, mem_blkW]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, h22⟩
  · rintro ⟨h0, h1, -⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1

private theorem twoBCol_compat (hK : Nat.card K = (2 ^ 1) ^ 2) {g₀ : SL(3, K)}
    (hg₀ : g₀ ∈ perfW K) (C : GL (Fin 2) K)
    (hC : (C : Matrix (Fin 2) (Fin 2) K) = blkMat (g₀ : Matrix (Fin 3) (Fin 3) K))
    (u u' : ↥(commOnR ⊤ (LW hK))) (huu : (u' : HMod 1 K) = rho hK g₀ (u : HMod 1 K)) :
    twoBCol hK u' = natHomR 2 K C (twoBCol hK u) := by
  have h22 : mat (u : HMod 1 K) 2 2 = 0 := twoB_mat22_of_mem hK u.2
  have key : ∀ i : Fin 2, mat (rho hK g₀ (u : HMod 1 K)) (Fin.castLE (by decide) i) 2 =
      (blkMat (g₀ : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ![mat (u : HMod 1 K) 0 2, mat (u : HMod 1 K) 1 2]) i := by
    intro i
    rw [rhoW_col hK hg₀ (u : HMod 1 K) i, h22, mul_zero, add_zero]
  apply Multiplicative.toAdd.injective
  rw [twoBCol_apply, twoBCol_apply, natHomR_apply, toAdd_ofAdd, toAdd_ofAdd, hC, huu]
  funext i
  fin_cases i
  · exact key 0
  · exact key 1

theorem part2b (hK : Nat.card K = (2 ^ 1) ^ 2) :
    InducesOnR (LW hK) (commOnR ⊤ (LW hK)) (blkW 1 K) (Multiplicative (Fin 2 → K))
      (natSubR 2 K (StatedSLR 2 K)) := by
  refine ⟨?_, ?_, ?_, twoBCol hK, twoBCol_surjective hK, fun u => twoBCol_eq_one_iff hK u, ?_, ?_⟩
  · intro X hX
    exact twoB_mem_of_mat22 hK (mem_blkW.1 hX).2.2
  · intro g hg u hu
    obtain ⟨g₀, hg₀, rfl⟩ := mem_LW hg
    apply twoB_mem_of_mat22 hK
    rw [rhoW_entry22 hK hg₀]
    exact twoB_mat22_of_mem hK hu
  · intro g hg z hz
    obtain ⟨g₀, hg₀, rfl⟩ := mem_LW hg
    exact (hermBlk_rho le_rfl hK (show g₀ ∈ stabW K from ⟨hg₀.1, hg₀.2.1⟩) hz).1
  · intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := mem_LW hg
    let A : SL(2, K) := ⟨blkMat (g₀ : Matrix (Fin 3) (Fin 3) K), det_blkMat_of_perfW hg₀⟩
    have hmem : Matrix.SpecialLinearGroup.toGL A ∈ StatedSLR 2 K := mem_StatedSLR.2 A.2
    refine ⟨natHomR 2 K (Matrix.SpecialLinearGroup.toGL A),
      Subgroup.mem_map_of_mem (natHomR 2 K) hmem, fun u u' huu =>
        twoBCol_compat hK hg₀ (Matrix.SpecialLinearGroup.toGL A) rfl u u' huu⟩
  · intro γ hγ
    have hγ' : γ ∈ (StatedSLR 2 K).map (natHomR 2 K) := hγ
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.1 hγ'
    have h4 : 4 ≤ Nat.card K := by rw [hK] <;> norm_num
    let A : SL(2, K) := ⟨(B : Matrix (Fin 2) (Fin 2) K), mem_StatedSLR.1 hB⟩
    refine ⟨rho hK (embW A), rho_embW_mem_LW h4 A, fun u u' huu =>
      twoBCol_compat hK (embW_mem_perfW A) B (blkMat_embW A).symm u u' huu⟩

end CFSG.Quasithin.RonanH46
