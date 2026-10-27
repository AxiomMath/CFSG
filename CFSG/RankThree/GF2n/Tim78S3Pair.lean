module

public import CFSG.RankThree.GF2n.Tim78P210CD

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

structure NCPair (U V : Subgroup G) : Prop where
  setup : Setup210 U V
  exp : ∀ x ∈ U, x ^ 4 = 1
  ncomm : ¬ ∀ a ∈ U, ∀ b ∈ V, a * b = b * a

namespace NCPair

variable {U V : Subgroup G} (P : NCPair U V)
include P

theorem ne : U ≠ V := (P.setup.invol_of_not_comm P.ncomm).1

theorem invol₀ : ∀ x ∈ nrm U V, x * x = 1 := (P.setup.invol_of_not_comm P.ncomm).2.1

theorem invol₁ : ∀ x ∈ nrm V U, x * x = 1 := (P.setup.invol_of_not_comm P.ncomm).2.2

omit [Finite G] in
theorem exp₁ : ∀ x ∈ V, x ^ 4 = 1 := P.setup.exp₁ P.exp

theorem symm : NCPair V U :=
  ⟨P.setup.symm, P.exp₁, fun h => P.ncomm fun a ha b hb => (h b hb a ha).symm⟩

theorem qdata (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) : QData U V U V :=
  P.setup.qdata_full hCen hU P.exp P.ne P.invol₀ P.invol₁

theorem nrm_eq (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    nrm U V = PartTwo.omegaOneSub U :=
  P.setup.nrm_eq_omega hCen hU P.ne P.invol₀ P.invol₁

theorem nrm_eq' (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    nrm V U = PartTwo.omegaOneSub V :=
  P.symm.nrm_eq hCen hU

theorem N_eq (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) :
    nrm U V ⊔ nrm V U = PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := by
  rw [P.nrm_eq hCen hU, P.nrm_eq' hCen hU]

section Facts

variable (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
include hCen hU

theorem comm_N {x y : G} (hx : x ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hy : y ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) : x * y = y * x := by
  rw [← P.N_eq hCen hU] at hx hy
  exact (P.qdata hCen hU).comm_Q hx hy

theorem sq_N {x : G} (hx : x ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) : x * x = 1 := by
  rw [← P.N_eq hCen hU] at hx
  exact (P.qdata hCen hU).sq_Q hx

theorem exists_mul {x : G} (hx : x ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    ∃ a ∈ PartTwo.omegaOneSub U, ∃ b ∈ PartTwo.omegaOneSub V, x = a * b := by
  rw [← P.N_eq hCen hU] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := (P.qdata hCen hU).exists_mul_of_mem_Q hx
  rw [P.nrm_eq hCen hU] at ha
  rw [P.nrm_eq' hCen hU] at hb
  exact ⟨a, ha, b, hb, rfl⟩

theorem le_normalizer :
    U ⊔ V ≤ Subgroup.normalizer
      ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V : Subgroup G) : Set G) := by
  rw [← P.N_eq hCen hU]
  exact (P.qdata hCen hU).R_le_normalizer_Q

theorem normal :
    ((PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V).subgroupOf (U ⊔ V)).Normal := by
  rw [← P.N_eq hCen hU]
  exact (P.qdata hCen hU).normal_Q

theorem comm_mem {y m : G} (hy : y ∈ U) (hm : m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    y * m * y⁻¹ * m⁻¹ ∈ PartTwo.omegaOneSub U := by
  rw [← P.N_eq hCen hU] at hm
  rw [← P.nrm_eq hCen hU]
  exact (P.qdata hCen hU).commutator_mem_F₀ hy hm

theorem cent {y m : G} (hy : y ∈ U) (hyL : y ∉ PartTwo.omegaOneSub U)
    (hm : m ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) (hc : y * m = m * y) :
    m ∈ PartTwo.omegaOneSub U := by
  rw [← P.N_eq hCen hU] at hm
  rw [← P.nrm_eq hCen hU] at hyL ⊢
  exact (P.qdata hCen hU).mem_F_of_commute hy hyL hm hc

theorem mem_U₀_of_mem_N {x : G} (hx : x ∈ U)
    (hxN : x ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) : x ∈ PartTwo.omegaOneSub U := by
  rw [← P.N_eq hCen hU] at hxN
  rw [← P.nrm_eq hCen hU]
  exact (P.qdata hCen hU).mem_F₀_of_mem_Q hx hxN

theorem eq_of_commute {x x' v w : G} (hx : x ∈ U ⊔ V) (hx' : x' ∈ U ⊔ V)
    (hv : v ∈ conjSubgroup x U) (hvN : v ∉ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hw : w ∈ conjSubgroup x' U) (hwN : w ∉ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hvw : v * w * (w * v)⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    conjSubgroup x U = conjSubgroup x' U := by
  rw [← P.N_eq hCen hU] at hvN hwN hvw
  exact (P.qdata hCen hU).eq_of_commute_mod_side QData.isSide_left QData.isSide_left hx hx' hv
    hvN hw hwN hvw

end Facts

end NCPair

end CFSG.RankThree.GF2n.Tim78
