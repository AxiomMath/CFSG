module

public import CFSG.RankThree.PartTwo.CTU6.Nodes

public section

namespace CFSG.RankThree.PartTwo.CTU6

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.RankThree.PartOne.CTP CFSG.LieType.BorelTits
open CFSG.LieType.Steinberg (fixedSubfield mem_fixedSubfield hypHom coe_hypHom hypHom_injective
  hypHom_surjective hypMat)
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.Timmesfeld (tv)
open scoped MatrixGroups

section LongRoots

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

theorem rootGroup_le_range_longRootHom (he : Even n) {γ : Fin (n / 2) → ℤ} {p : Fin n}
    (hp : p ≠ Fin.rev p) (hγ : toStd n γ = 2 • weight n p) :
    rootGroup σ hσ n γ ≤ (longRootHom σ hp).range := by
  unfold rootGroup
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => iSup_le fun hi => iSup_le fun hj =>
      iSup_le fun hji => iSup_le fun hw => ?_
    rw [hγ] at hw
    obtain ⟨rfl, rfl⟩ := eq_of_weight_sub_eq_two_smul hp hw
    exact absurd rfl hji
  · refine iSup_le fun i => iSup_le fun hi => iSup_le fun hw => ?_
    rw [hγ] at hw
    obtain rfl := weight_injective (two_nsmul_injective' hw)
    exact le_rfl
  · refine iSup_le fun i => iSup_le fun k => iSup_le fun hi => iSup_le fun hik =>
      iSup_le fun hk => iSup_le fun hw => ?_
    exact absurd hk (rev_ne_self_of_even he k)

end LongRoots

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem unitaryInvolution_one_eq_neg : unitaryInvolution K 2 f 1 = -1 := by
  rw [map_one, CharTwo.neg_eq]

variable (K f) in
@[expose] noncomputable def lbSU4 :
    SL(2, fixedSubfield K 2 f) →* SU (unitaryInvolution K 2 f) 4 :=
  (lbEmb (unitaryInvolution K 2 f)).comp (hypHom one_ne_zero unitaryInvolution_one_eq_neg)

theorem coe_lbSU4 (A : SL(2, fixedSubfield K 2 f)) :
    (((lbSU4 K f A : SU (unitaryInvolution K 2 f) 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      embMid (hypMat (1 : K) (A : Matrix (Fin 2) (Fin 2) (fixedSubfield K 2 f))) :=
  rfl

theorem lbSU4_injective : Function.Injective (lbSU4 K f) :=
  lbEmb_injective.comp (hypHom_injective one_ne_zero unitaryInvolution_one_eq_neg)

theorem range_lbSU4 : (lbSU4 K f).range = (lbEmb (unitaryInvolution K 2 f)).range := by
  rw [lbSU4, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (hypHom_surjective one_ne_zero unitaryInvolution_one_eq_neg),
    Subgroup.map_top]

variable (K f) in
@[expose] noncomputable def rL : SL(2, fixedSubfield K 2 f) →* SU (unitaryInvolution K 2 f) 6 :=
  (embSU4 (unitaryInvolution K 2 f)).comp (lbSU4 K f)

theorem rL_injective : Function.Injective (rL K f) :=
  (embSU4_injective _).comp lbSU4_injective

theorem mem_traceZero_of_mem_fixedSubfield (c : fixedSubfield K 2 f) :
    (c : K) ∈ traceZero (unitaryInvolution K 2 f) := by
  rw [mem_traceZero, (mem_fixedSubfield).mp c.2, CharTwo.add_self_eq_zero]

theorem mem_fixedSubfield_of_mem_traceZero (c : traceZero (unitaryInvolution K 2 f)) :
    (c : K) ∈ fixedSubfield K 2 f := by
  rw [mem_fixedSubfield]
  have h := (mem_traceZero _).mp c.2
  rw [CharTwo.add_eq_zero] at h
  exact h.symm

@[expose] def toTraceZero (c : fixedSubfield K 2 f) : traceZero (unitaryInvolution K 2 f) :=
  ⟨c, mem_traceZero_of_mem_fixedSubfield c⟩

theorem rL_tv01 (c : fixedSubfield K 2 f) :
    rL K f (tv 0 1 c) = longRootHom (unitaryInvolution K 2 f) (lowIdx_ne_rev k2 k2)
      (Multiplicative.ofAdd (toTraceZero c)) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_longRootHom, toAdd_ofAdd, rL, MonoidHom.comp_apply, coe_embSU4, coe_lbSU4,
    coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, embMid, hypMat, longRootMatrix, toTraceZero, one_apply, Fin.rev, lowIdx]

theorem rL_tv10 (c : fixedSubfield K 2 f) :
    rL K f (tv 1 0 c) = longRootHom (unitaryInvolution K 2 f)
      (rev_ne_rev_rev (lowIdx_ne_rev k2 k2)) (Multiplicative.ofAdd (toTraceZero c)) := by
  refine Subtype.ext (Units.ext ?_)
  rw [coe_longRootHom, toAdd_ofAdd, rL, MonoidHom.comp_apply, coe_embSU4, coe_lbSU4,
    coe_tv (by decide)]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [blockMat_apply, embMid, hypMat, longRootMatrix, toTraceZero, one_apply, Fin.rev, lowIdx]

variable (hK : Nat.card K = (2 ^ f) ^ 2)
include hK

theorem rL_upper_mem (c : fixedSubfield K 2 f) :
    rL K f (tv 0 1 c) ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 6
      (Pi.single k2 1) := by
  rw [rL_tv01]
  exact longRootHom_mem _ _ (toStd_last_even (k := k2) (by decide) ⟨3, rfl⟩).symm _

theorem rL_lower_mem (c : fixedSubfield K 2 f) :
    rL K f (tv 1 0 c) ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 6
      (-Pi.single k2 1) := by
  rw [rL_tv10]
  exact longRootHom_mem _ _ (toStd_neg_last_even (k := k2) (by decide) ⟨3, rfl⟩).symm _

theorem rL_param_upper :
    ∀ g ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 6
      (Pi.single k2 1), ∃ c, rL K f (tv 0 1 c) = g := by
  intro g hg
  obtain ⟨t, rfl⟩ := rootGroup_le_range_longRootHom (unitaryInvolution_involutive hK) ⟨3, rfl⟩
    (lowIdx_ne_rev k2 k2) (toStd_last_even (k := k2) (by decide) ⟨3, rfl⟩) hg
  refine ⟨⟨((Multiplicative.toAdd t : traceZero (unitaryInvolution K 2 f)) : K),
    mem_fixedSubfield_of_mem_traceZero _⟩, ?_⟩
  rw [rL_tv01]
  rfl

theorem rL_param_lower :
    ∀ g ∈ rootGroup (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK) 6
      (-Pi.single k2 1), ∃ c, rL K f (tv 1 0 c) = g := by
  intro g hg
  obtain ⟨t, rfl⟩ := rootGroup_le_range_longRootHom (unitaryInvolution_involutive hK) ⟨3, rfl⟩
    (rev_ne_rev_rev (lowIdx_ne_rev k2 k2))
    (toStd_neg_last_even (k := k2) (by decide) ⟨3, rfl⟩) hg
  refine ⟨⟨((Multiplicative.toAdd t : traceZero (unitaryInvolution K 2 f)) : K),
    mem_fixedSubfield_of_mem_traceZero _⟩, ?_⟩
  rw [rL_tv10]
  rfl

end CFSG.RankThree.PartTwo.CTU6
