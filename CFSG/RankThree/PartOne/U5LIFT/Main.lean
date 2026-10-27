module

public import CFSG.RankThree.PartOne.U5LIFT.Single
public import CFSG.RankThree.PartOne.S12.KFTransfer
public import CFSG.RankThree.PartOne.KF.U4Model

public section

namespace CFSG.RankThree.PartOne.U5LIFT

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec12Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.LSTD

theorem comm_swap_five : ∀ a b c d : Fin 5, a ≠ b → c ≠ d →
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b →
      Equiv.swap a b ≠ Equiv.swap c d → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by decide +kernel

theorem inf_eq_bot_of_centralizes' {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hc : K₁ ≤ Subgroup.centralizer (K₂ : Set G)) (hcen : Subgroup.center ↥K₁ = ⊥) :
    K₁ ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hmem : (⟨x, hx.1⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hc y.2) x hx.2).symm
  rw [hcen, Subgroup.mem_bot] at hmem
  exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)

namespace U5Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}
  {K : Type} [Field K] (C : U5Ctx A c L E f K)

theorem refl_kfAt (R : C.Refl) : KFAt 5 E f R.t := by
  obtain ⟨hqs, hz, hmod⟩ := blk_model C.hU C.hf2 R.hab
  have hK := R.kZero_eq_blkG hqs hz
  have hmodG : StatedClassicalModel ↥(C.blkG R.hab) .PSL 2 2 f :=
    Equivariance.statedClassicalModel_of_mulEquiv (C.blkGEquiv R.hab).symm hmod
  have hzG : Subgroup.center ↥(C.blkG R.hab) = ⊥ :=
    center_eq_bot_of_mulEquiv (C.blkGEquiv R.hab) hz
  refine ⟨?_, ?_, R.inf_centralizer_eq hK, ?_, ?_⟩
  · rintro ⟨f', -, -, hf'⟩
    rw [hK] at hf'
    exact not_psu_three_quotient_of_psl_two hmodG hzG hf'
  · rw [hK]
    exact hmodG
  · rw [hK]
    exact R.autMovedInG_le_blkG
  · obtain ⟨k, hk, hkB, hkt⟩ := R.exists_swap_elt
    exact ⟨k, hk, hK ▸ hkB, hkt⟩

include C in
theorem exists_refl {t : MulAut E} (ht : t ∈ reflectionSet 5 E) (htL : t ∈ torusImage E L) :
    ∃ R : C.Refl, R.t = t := by
  obtain ⟨w, hwL, hwE, rfl⟩ := mem_torusImage_iff.mp htL
  obtain ⟨g, τ, hg, hτ⟩ := C.exists_perm hwL hwE
  subst hg
  let P : C.PermData := ⟨g, τ, hτ, hwE⟩
  obtain ⟨a, b, hab, hτab⟩ := P.exists_swap_of_reflection ht.1
  exact ⟨⟨P, a, b, hab, hτab⟩, rfl⟩

theorem pair_comm (Rs Rt : C.Refl) (hne : Rs.t ≠ Rt.t) (hcomm : Rs.t * Rt.t = Rt.t * Rs.t) :
    kZero 5 E Rs.t ≤ Subgroup.centralizer (kZero 5 E Rt.t : Set G) ∧
      kZero 5 E Rs.t ⊓ kZero 5 E Rt.t = ⊥ := by
  obtain ⟨hqs, hz, -⟩ := blk_model C.hU C.hf2 Rs.hab
  obtain ⟨hqt, hzt, -⟩ := blk_model C.hU C.hf2 Rt.hab
  have hKs := Rs.kZero_eq_blkG hqs hz
  have hKt := Rt.kZero_eq_blkG hqt hzt
  have hts : (Rs.toPermData.mul Rt.toPermData).t = Rs.t * Rt.t := PermData.t_mul _ _
  have htsr : (Rt.toPermData.mul Rs.toPermData).t = Rt.t * Rs.t := PermData.t_mul _ _
  have hperm : Equiv.swap Rs.a Rs.b * Equiv.swap Rt.a Rt.b =
      Equiv.swap Rt.a Rt.b * Equiv.swap Rs.a Rs.b := by
    have h1 := (PermData.t_eq_iff C (Rs.toPermData.mul Rt.toPermData)
      (Rt.toPermData.mul Rs.toPermData)).mp (by rw [hts, htsr]; exact hcomm)
    have h2 : Rs.toPermData.τ * Rt.toPermData.τ = Rt.toPermData.τ * Rs.toPermData.τ := h1
    rwa [Rs.hτ', Rt.hτ'] at h2
  have hne' : Equiv.swap Rs.a Rs.b ≠ Equiv.swap Rt.a Rt.b := by
    intro h'
    apply hne
    refine (PermData.t_eq_iff C Rs.toPermData Rt.toPermData).mpr ?_
    rw [Rs.hτ', Rt.hτ']
    exact h'
  obtain ⟨hac, had, hbc, hbd⟩ := comm_swap_five _ _ _ _ Rs.hab Rt.hab hperm hne'
  have hc : kZero 5 E Rs.t ≤ Subgroup.centralizer (kZero 5 E Rt.t : Set G) := by
    rw [hKs, hKt]
    rintro _ ⟨g1, hg1, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨g2, hg2, rfl⟩
    have hg1' : (g1 : GL (Fin 5) K) ∈ blk C.hU Rs.hab := hg1
    have hg2' : (g2 : GL (Fin 5) K) ∈ blk C.hU Rt.hab := hg2
    have hcm := blk_comm_of_disjoint Rt.hab Rs.hab hac.symm hbc.symm had.symm hbd.symm hg2' hg1'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcm
  refine ⟨hc, inf_eq_bot_of_centralizes' hc ?_⟩
  rw [hKs]
  exact center_eq_bot_of_mulEquiv (C.blkGEquiv Rs.hab) hz

end U5Ctx

end CFSG.RankThree.PartOne.U5LIFT
