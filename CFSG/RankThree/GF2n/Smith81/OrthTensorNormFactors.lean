module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormGroup
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormSylow
public import CFSG.RankThree.GF2n.Smith81.OrthTensorNormAct
public import CFSG.RankThree.GF2n.Stroth80.Sec41iii
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple

public section

open scoped Matrix

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Factors

variable {K : Type} [Field K] [Finite K] [CharP K 2]

open CFSG.RankThree.GF2n.Stroth80 in
theorem isSimpleGroup_SL2 (hq : 4 ≤ Nat.card K) : IsSimpleGroup (SL2 K) := by
  haveI := isSimpleGroup_statedSL_two (statedSL_quasisimple_of_card 2 K le_rfl hq)
  exact (MulEquiv.isSimpleGroup_congr
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)).mpr this

theorem actMap_cubeF_injective (i : Fin 3) :
    Function.Injective ((kronSLHom 3 K).comp (MonoidHom.mulSingle (fun _ : Fin 3 => SL2 K) i)) :=
  (kronSLHom_injective 3 K).comp (fun a b h => by
    simpa using congrFun h i)

noncomputable def cubeFEquiv (i : Fin 3) : SL2 K ≃* cubeF 3 K i :=
  MonoidHom.ofInjective (actMap_cubeF_injective i)

theorem isSimpleGroup_cubeF (hq : 4 ≤ Nat.card K) (i : Fin 3) :
    IsSimpleGroup ↥(cubeF 3 K i) := by
  haveI := isSimpleGroup_SL2 hq
  exact (MulEquiv.isSimpleGroup_congr (cubeFEquiv i)).mp this

@[expose] def mkSL (A : Matrix (Fin 2) (Fin 2) K) (h : A.det = 1) : SL2 K := ⟨A, h⟩

@[expose] noncomputable def actSL (i : Fin 3) (A : SL2 K) : Cube 3 K ≃ₗ[K] Cube 3 K :=
  kronSLHom 3 K (Pi.mulSingle i A)

theorem actSL_apply (i : Fin 3) (A : SL2 K) (v : Cube 3 K) :
    actSL i A v = actMap i (A : Matrix (Fin 2) (Fin 2) K) v := by
  show kronSL (Pi.mulSingle i A : Fin 3 → SL2 K) v = _
  rw [kronSL_apply, coe_mulSingle_SL2]
  rfl

theorem actSL_mem (i : Fin 3) (A : SL2 K) : actSL i A ∈ cubeF 3 K i :=
  mem_cubeF.mpr ⟨A, A.2, fun v => actSL_apply i A v⟩

theorem actSL_mul (i : Fin 3) (A B : SL2 K) : actSL i (A * B) = actSL i A * actSL i B := by
  unfold actSL
  rw [← map_mul, Pi.mulSingle_mul]

theorem actSL_injective (i : Fin 3) : Function.Injective (actSL (K := K) i) :=
  fun a b h => by
    have := actMap_cubeF_injective (K := K) i
    exact this h

theorem threeFactors (hq : 4 ≤ Nat.card K) : ThreeFactors (cubeF 3 K) (cubeE 3 K) where
  le := cubeF_le_cubeE
  simple := isSimpleGroup_cubeF hq
  nonab := fun i => by
    let A : SL2 K := uniSL 1
    let B : SL2 K := mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])
    refine ⟨actSL i A, actSL_mem i A, actSL i B, actSL_mem i B, ?_⟩
    rw [← actSL_mul, ← actSL_mul]
    intro h
    have h' := actSL_injective i h
    have h1 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 0) h'
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h1
    simp [A, B, uniSL, uniMat, mkSL, Matrix.mul_apply, Fin.sum_univ_two] at h1

  comm := fun i j hij x hx y hy => by
    obtain ⟨A, -, hA⟩ := mem_cubeF.mp hx
    obtain ⟨B, -, hB⟩ := mem_cubeF.mp hy
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hA, hB, hA, hB]
    exact LinearMap.congr_fun (actMap_comm hij A B) v
  gen := fun e he => by
    obtain ⟨k, hk, hv⟩ := mem_cubeE.mp he
    refine ⟨actSL 0 (mkSL (k 0) (hk 0)), actSL_mem 0 _, actSL 1 (mkSL (k 1) (hk 1)),
      actSL_mem 1 _, actSL 2 (mkSL (k 2) (hk 2)), actSL_mem 2 _, LinearEquiv.ext fun v => ?_⟩
    rw [hv, kronMap_fin3, LinearEquiv.mul_apply, LinearEquiv.mul_apply, actSL_apply, actSL_apply,
      actSL_apply]
    rfl

theorem cubeE_eq_sup (hq : 4 ≤ Nat.card K) :
    cubeE 3 K = cubeF 3 K 0 ⊔ cubeF 3 K 1 ⊔ cubeF 3 K 2 := by
  refine le_antisymm (fun e he => ?_)
    (sup_le (sup_le (cubeF_le_cubeE 0) (cubeF_le_cubeE 1)) (cubeF_le_cubeE 2))
  obtain ⟨a₀, h0, a₁, h1, a₂, h2, rfl⟩ := (threeFactors hq).gen e he
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left h0))
    (Subgroup.mem_sup_left (Subgroup.mem_sup_right h1))) (Subgroup.mem_sup_right h2)
end Factors

end CFSG.RankThree.GF2n.Smith81.OrthTN

end
