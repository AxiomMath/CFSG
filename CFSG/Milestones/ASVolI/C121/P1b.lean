module

public import CFSG.Milestones.ASVolI.C121.P1a
public import CFSG.Milestones.ASVolI.C121.Base
public import CFSG.Milestones.ASVolI.C121.NatPrime

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

theorem burnsideC121_omegaOneCenter_baum {Ω : Type} [Group Ω] [Finite Ω] (P : Subgroup Ω) :
    omegaOneCenterOf (baum P) = omegaOneCenterOf (thompsonJ P) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 fun g hg => ?_
    rw [← (omegaOne_centralizer_thompsonJ P).1]
    refine Subgroup.subset_closure ⟨⟨hg.1.1.1, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩, hg.2⟩
    exact Subgroup.mem_centralizer_iff.1 hg.1.2 j (B6.thompsonJ_le_baum P hj)
  · refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hgΩ : g ∈ omegaOneCenterOf (thompsonJ P) := Subgroup.subset_closure hg
    refine Subgroup.subset_closure ⟨⟨B6.thompsonJ_le_baum P hg.1.1,
      Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩, hg.2⟩
    exact (Subgroup.mem_centralizer_iff.1 hs.2 g hgΩ).symm

theorem burnsideC121_iSup_conj_eq {Ω : Type} [Group Ω] {Y S : Subgroup Ω}
    (hY : ⁅Y, S⁆ = Y) :
    (⨆ l ∈ Y, S.map (MulAut.conj l).toMonoidHom) = Y ⊔ S := by
  apply le_antisymm
  · refine iSup₂_le fun l hl => ?_
    rintro _ ⟨s, hs, rfl⟩
    show l * s * l⁻¹ ∈ Y ⊔ S
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hl)
      (Subgroup.mem_sup_right hs)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left hl))
  · have hS : S ≤ ⨆ l ∈ Y, S.map (MulAut.conj l).toMonoidHom := by
      refine le_trans ?_ (le_iSup₂_of_le (1 : Ω) Y.one_mem le_rfl)
      intro s hs
      exact ⟨s, hs, by simp⟩
    refine sup_le ?_ hS
    calc Y = ⁅Y, S⁆ := hY.symm
      _ ≤ _ := by
        rw [Subgroup.commutator_le]
        intro y hy s hs
        have h1 : y * s * y⁻¹ ∈ ⨆ l ∈ Y, S.map (MulAut.conj l).toMonoidHom := by
          apply le_iSup₂ (f := fun l (_ : l ∈ Y) => S.map (MulAut.conj l).toMonoidHom) y hy
          exact ⟨s, hs, rfl⟩
        have e : ⁅y, s⁆ = (y * s * y⁻¹) * s⁻¹ := by rw [commutatorElement_def]
        rw [e]
        exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hS hs))

namespace burnsideC121_YCtx

variable {Ω : Type} [Group Ω] [Finite Ω] {X R T Y W : Subgroup Ω}
  (c : burnsideC121_YCtx X R T Y W) {n : ℕ} {F : Type} [Field F] [Fintype F]
  (D : burnsideC121_NatD Y W n F)

include c

theorem twoResidual_Y : twoResidual Y = Y := by
  rw [CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper, ← c.hY.perf]

theorem twoResidual_H : twoResidual (burnsideC121_H X T Y) = Y := by
  rw [c.H_eq]
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left
    (sup_le Subgroup.le_normalizer c.P_le_normalizer)
    (B6.isTwoQuotient_of_sup_eq c.P_pGroup (sup_le Subgroup.le_normalizer c.P_le_normalizer)
      (sup_comm _ _))) ?_
  have := C126.A5.twoResidual_mono (le_sup_left : Y ≤ Y ⊔ burnsideC121_P X R T Y)
  rwa [c.twoResidual_Y] at this

theorem charTwo_H : CharTwo (burnsideC121_H X T Y) :=
  C126.A5.charTwo_of_pCore_le c.charTwo (c.Q_le_P.trans c.P_le_H) c.H_le_X

theorem isSubnormal_Y_H : IsSubnormal Y (burnsideC121_H X T Y) :=
  IsSubnormal.step c.Y_le_H
    ((Subgroup.normal_subgroupOf_iff_le_normalizer c.Y_le_H).mpr c.H_le_normalizer)
    (IsSubnormal.refl _)

theorem commutator_S_eq (hJ : ⁅Y, thompsonJ R⁆ = Y) : ⁅Y, baum T⁆ = Y := by
  refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp c.S_le_normalizer) ?_
  calc Y = ⁅Y, thompsonJ R⁆ := hJ.symm
    _ ≤ ⁅Y, baum T⁆ := Subgroup.commutator_mono le_rfl c.thompsonJ_R_le_S

include D

theorem b610 (h610 : B_6_10) (hn : 2 ≤ n) (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧
      omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y)) =
        (⁅W, Y⁆ ⊓ Subgroup.centralizer (thompsonJ (burnsideC121_P X R T Y) : Set Ω)) ⊔
          (omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y)) ⊓
            Subgroup.centralizer (Y : Set Ω)) := by
  obtain ⟨M, hM⟩ := c.minParabolic_H D hYS
  obtain ⟨h2, h3⟩ := burnsideC121_b610 h610 hM c.charTwo_H c.W_red c.isSubnormal_Y_H
    (c.isNaturalL2Prime D hn) (c.commutator_W_thompsonJ_ne_bot D hYS)
  rw [c.baum_P, burnsideC121_iSup_conj_eq (c.commutator_S_eq (c.commutator_thompsonJ_eq D hYS))]
    at h2
  exact ⟨h2, h3 c.twoResidual_Y⟩

theorem isSolvable_Y (hn : n = 1) : Group.IsSolvable ↥Y := by
  have h3 : Nat.card D.α.range = 3 := by
    rw [D.αr]; exact burnsideC121_card_commutator_sl2_two (by rw [D.card, hn]; rfl)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥D.α.range := isCyclic_of_prime_card h3
  have : Group.IsSolvable ↥D.α.range := by
    letI := hcyc.commGroup
    infer_instance
  have hO : Group.IsSolvable ↥((pCoreOf 2 Y).subgroupOf Y) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥((pCoreOf 2 Y).subgroupOf Y) :=
      (pCoreOf_isPGroup 2 Y).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 Y)).symm
    have := hp.isNilpotent
    infer_instance
  exact solvable_of_ker_le_range ((pCoreOf 2 Y).subgroupOf Y).subtype D.α.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, D.αk, Subgroup.range_subtype])

theorem card_H (hn : n = 1) :
    Nat.card (burnsideC121_H X T Y) = 3 * Nat.card (burnsideC121_P X R T Y) := by
  rw [c.H_eq]
  have h1 := C126.A5.card_sup_mul_card_inf_of_le_normalizer c.P_le_normalizer
  have hYP : Y ⊓ burnsideC121_P X R T Y = pCoreOf 2 Y := by
    rw [inf_comm, c.P_inf_Y, c.RY_eq_pCore D hn]
  rw [hYP] at h1
  have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 Y) Y
  rw [inf_eq_left.2 (pCoreOf_le 2 Y), c.relIndex_pCore_three D hn] at h2
  have hpos : 0 < Nat.card ↥(pCoreOf 2 Y) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, ← h2]
  ring

theorem isSolvable_H (hn : n = 1) : Group.IsSolvable ↥(burnsideC121_H X T Y) := by
  rw [c.H_eq]
  exact F1.isSolvable_sup_of_le_normalizer (c.isSolvable_Y D hn)
    (F1.isSolvable_of_isPGroup_two c.P_pGroup) c.P_le_normalizer

theorem pRank_H (hn : n = 1) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (burnsideC121_H X T Y) ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).1 c.P_pGroup
  exact C124.Z3.pRank_le_two_of_card_dvd (a := a) (by rw [c.card_H D hn, ha, mul_comm])

theorem e23 (hn : n = 1) (hYS : ¬ Y ≤ Subgroup.normalizer (baum T : Set Ω)) :
    IsSylowTwoOf (baum T) (Y ⊔ baum T) ∧
      conjClosure (omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y))) Y =
        ⁅W, Y⁆ ⊔ (omegaOneCenterOf (thompsonJ (burnsideC121_P X R T Y)) ⊓
          Subgroup.centralizer (Y : Set Ω)) := by
  obtain ⟨M, hM⟩ := c.minParabolic_H D hYS
  have hJ : ¬ thompsonJ (burnsideC121_P X R T Y) ≤ Subgroup.centralizer (W : Set Ω) := by
    intro h
    apply c.commutator_W_thompsonJ_ne_bot D hYS
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h
  obtain ⟨-, -, h3, -, h5⟩ := E2_3_two_of_isSolvable c.W_elem hM (c.isSolvable_H D hn)
    (c.pRank_H D hn) c.W_red hJ
  rw [c.twoResidual_H, c.baum_P] at h3
  rw [c.twoResidual_H] at h5
  exact ⟨h3, h5⟩

end burnsideC121_YCtx

end CFSG.ASVolI
