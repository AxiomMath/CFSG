module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeDeltaCentBlock
public import CFSG.RankThree.PartOne.KP.Fi22Unitary
public import CFSG.Fischer.Polar.Delta
public import CFSG.Fischer.T46Unitary
public import CFSG.Models
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open Subgroup Matrix CFSG.Open CFSG.Models CFSG.Fischer

private noncomputable def centralScalarSU0 (c : F4ˣ) : SU0 := ⟨scalarGL c, scalarGL_mem c⟩

private theorem centralScalarSU0_mem_center (c : F4ˣ) :
    centralScalarSU0 c ∈ Subgroup.center SU0 := by
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (scalarGL_central c g).symm

private theorem exists_scalarGL_of_mem_center
    {z : SU0} (hz : z ∈ Subgroup.center SU0) :
    ∃ c : F4ˣ, (z : GL (Fin 6) F4) = scalarGL c := by
  rw [CFSG.RankThree.PartOne.center_SU0_eq_scalars] at hz
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, by rw [CFSG.RankThree.PartOne.scalarGL_eq_scalar]; exact hc.symm⟩

private theorem trace_deltaM_ne_zero : Matrix.trace deltaM ≠ 0 := by
  unfold deltaM
  rw [Matrix.trace_diagonal, Fin.sum_univ_six]
  decide

private theorem mul_deltaM_comm_of_piSU_comm
    {g : SU0}
    (h : piSU g * piGU deltaGU = piGU deltaGU * piSU g) :
    ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * deltaM =
      deltaM * ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := by
  let gU : GU0 := Subgroup.inclusion SU0_le_GU0 g
  let uU : GU0 := gU * deltaGU * gU⁻¹ * deltaGU⁻¹
  have hg : Matrix.GeneralLinearGroup.det (g : GL (Fin 6) F4) = 1 := (mem_SU0.1 g.2).1
  have huSU : (uU : GL (Fin 6) F4) ∈ SU0 := mem_SU0.2 ⟨by simp [uU, gU, hg], uU.2⟩
  have hpi : piSU ⟨(uU : GL (Fin 6) F4), huSU⟩ = 1 := by
    show piGU uU = 1
    simp only [uU, map_mul, map_inv]
    change piSU g * piGU deltaGU * (piSU g)⁻¹ * (piGU deltaGU)⁻¹ = 1
    rw [h]
    group
  obtain ⟨c, hc⟩ := exists_scalarGL_of_mem_center
    (z := ⟨(uU : GL (Fin 6) F4), huSU⟩) (by rw [← ker_piSU]; exact hpi)
  have h2 : (g : GL (Fin 6) F4) * deltaGU * (g : GL (Fin 6) F4)⁻¹ = scalarGL c * deltaGU := by
    rw [← hc]
    exact (inv_mul_cancel_right _ _).symm
  have hc1 : c = 1 := by
    have h3 := congrArg (fun x : GL (Fin 6) F4 => Matrix.trace (x : Matrix (Fin 6) (Fin 6) F4)) h2
    simp only [Units.val_mul, scalarGL_val, deltaGU_val, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul, Matrix.trace_units_conj] at h3
    refine Units.ext (mul_right_cancel₀ trace_deltaM_ne_zero ?_)
    rw [Units.val_one, one_mul]
    exact h3.symm
  have h4 : (g : GL (Fin 6) F4) * deltaGU = deltaGU * g := by
    have h5 : (g : GL (Fin 6) F4) * deltaGU * (g : GL (Fin 6) F4)⁻¹ = deltaGU := by
      rw [h2, hc1, show scalarGL 1 = 1 from Units.ext (by simp [scalarGL_val]), one_mul]
    exact mul_inv_eq_iff_eq_mul.1 h5
  have h6 := congrArg Units.val h4
  rwa [Units.val_mul, Units.val_mul, deltaGU_val] at h6

private theorem block_shape_of_comm_deltaM {M : Matrix (Fin 6) (Fin 6) F4}
    (h : M * deltaM = deltaM * M) :
    (∀ i : Fin 5, M i.succ 0 = 0) ∧ ∀ j : Fin 5, M 0 j.succ = 0 := by
  have hω1 : ∀ x : F4, x * F4.ω = x → x = 0 := by decide
  have hω2 : ∀ x : F4, x = F4.ω * x → x = 0 := by decide
  refine ⟨fun i => hω1 _ ?_, fun j => hω2 _ ?_⟩
  · have := congrFun (congrFun h i.succ) 0
    rw [deltaM, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simpa [Fin.succ_ne_zero] using this
  · have := congrFun (congrFun h 0) j.succ
    rw [deltaM, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    simpa [Fin.succ_ne_zero] using this

private noncomputable def blockToSU0 : StatedSU 5 (2 ^ 1) F4 →* SU0 :=
  (deltaCentBlockGL.comp (StatedSU 5 (2 ^ 1) F4).subtype).codRestrict SU0
    (fun A => deltaCentBlockGL_mem_SU0 A.2)

private noncomputable def deltaCentHom :
    StatedSU 5 (2 ^ 1) F4 →* Equiv.Perm (Fin 693) :=
  piSU.comp blockToSU0

private theorem deltaCentHom_injective :
    Function.Injective deltaCentHom := by
  rw [injective_iff_map_eq_one]
  intro A hA
  obtain ⟨c, hc⟩ := exists_scalarGL_of_mem_center (z := blockToSU0 A)
    (by rw [← ker_piSU]; exact hA)
  have h00 := congrArg (fun x : GL (Fin 6) F4 => (x : Matrix (Fin 6) (Fin 6) F4) 0 0) hc
  have hc1 : c = 1 := by
    refine Units.ext ?_
    have h1 : ((blockToSU0 A : SU0) : GL (Fin 6) F4) = deltaCentBlockGL (A : GL (Fin 5) F4) := rfl
    simpa [h1, deltaCentBlockGL_apply_zero_zero, scalarGL_val] using h00.symm
  subst hc1
  refine Subtype.ext (deltaCentBlockGL_injective ?_)
  rw [Subgroup.coe_one, map_one]
  exact hc.trans (Units.ext (by simp [scalarGL_val]))

private theorem inclusion_blockToSU0_val (A : StatedSU 5 (2 ^ 1) F4) :
    ((Subgroup.inclusion SU0_le_GU0 (blockToSU0 A) : GU0) : GL (Fin 6) F4) =
      deltaCentBlockGL (A : GL (Fin 5) F4) := rfl

private theorem range_deltaCentHom :
    deltaCentHom.range = T46 ⊓ centralizer ({piGU deltaGU} : Set (Equiv.Perm (Fin 693))) := by
  ext c
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨?_, mem_centralizer_iff.2 fun h hh => ?_⟩
    · rw [← range_piSU]
      exact ⟨blockToSU0 A, rfl⟩
    · rw [Set.mem_singleton_iff.1 hh]
      change piGU deltaGU * piGU (Subgroup.inclusion SU0_le_GU0 (blockToSU0 A)) =
        piGU (Subgroup.inclusion SU0_le_GU0 (blockToSU0 A)) * piGU deltaGU
      rw [← map_mul, ← map_mul]
      refine congrArg piGU (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, inclusion_blockToSU0_val]
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, deltaGU_val, deltaCentBlockGL_val]
      exact (deltaCentBlockMat_comm_diagonal _ F4.ω).symm
  · rintro ⟨hT, hC⟩
    rw [← range_piSU] at hT
    obtain ⟨g, rfl⟩ := hT
    have hcomm : piSU g * piGU deltaGU = piGU deltaGU * piSU g :=
      (mem_centralizer_iff.1 hC _ rfl).symm
    obtain ⟨h0, h1⟩ := block_shape_of_comm_deltaM (mul_deltaM_comm_of_piSU_comm hcomm)
    obtain ⟨s, A, hA, hgA⟩ := exists_deltaCentBlock_of_block_shape g.2 h0 h1
    refine ⟨⟨A, hA⟩, ?_⟩
    have hs : piSU (centralScalarSU0 s) = 1 := center_le_ker (centralScalarSU0_mem_center s)
    have hb : blockToSU0 ⟨A, hA⟩ = g * centralScalarSU0 s := Subtype.ext hgA.symm
    change piSU (blockToSU0 ⟨A, hA⟩) = piSU g
    rw [hb, map_mul, hs, mul_one]

private theorem deltaCent_scalars_subgroupOf_eq_bot :
    (StatedScalars (Fin 5) F4).subgroupOf (StatedSU 5 (2 ^ 1) F4) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hA
  have hdet : Matrix.GeneralLinearGroup.det (A : GL (Fin 5) F4) = 1 := by
    rw [← deltaCentBlockGL_det]
    exact (mem_SU0.1 (deltaCentBlockGL_mem_SU0 A.2)).1
  rw [← hc, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
  have hc1 : c = 1 := by
    refine Units.ext ?_
    have h5 : (c : F4) ^ 5 = 1 := by simpa using congrArg Units.val hdet
    revert h5
    generalize (c : F4) = x
    revert x
    decide
  subst hc1
  exact Subtype.ext (hc.symm.trans (Units.ext (by simp)))

theorem lieModel_inf_centralizer_piGU_deltaGU :
    LieModel ↥(T46 ⊓ centralizer ({piGU deltaGU} : Set (Equiv.Perm (Fin 693)))) .PSU 5 2 1 := by
  have hadm : StatedLieAdmissible .PSU 5 2 1 := ⟨Nat.prime_two, le_rfl, by omega, fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega⟩
  let e : StatedSU 5 (2 ^ 1) F4 ≃* StatedProj (StatedSU 5 (2 ^ 1) F4) :=
    QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq deltaCent_scalars_subgroupOf_eq_bot.symm)
  refine ⟨hadm, Or.inl ⟨hadm, F4, inferInstance, inferInstance, ?_, ⟨?_⟩⟩⟩
  · rw [Nat.card_eq_fintype_card, F4.card]
    norm_num
  · exact ((MonoidHom.ofInjective deltaCentHom_injective).trans
      (MulEquiv.subgroupCongr range_deltaCentHom)).symm.trans e

end CFSG.GGQ2Prime
