module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.MSPBasic
public import CFSG.Quasithin.MS93.SkHyp

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem Uq_le_centralizer_pCore : Uq M T L ≤ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
  h.Uq_le_Xq.trans ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right)

theorem comm_of_mem_Uq {u x : G} (hu : u ∈ Uq M T L) (hx : x ∈ pCoreOf 2 M) : x * u = u * x :=
  (Subgroup.mem_centralizer_iff.1 (Uq_le_centralizer_pCore h hu) x hx)

theorem Uq_le_L : Uq M T L ≤ L := by
  rw [Uq, Subgroup.commutator_comm]
  exact commutator_le_left_of_le_normalizer ((Z0q_le M T).trans h.le_normalizer)

variable (hVU : Vq M L = Uq M T L)
include hVU

omit [Finite G] h in
theorem comm_mem_Uq {x l : G} (hx : x ∈ pCoreOf 2 M) (hl : l ∈ L) : ⁅x, l⁆ ∈ Uq M T L := by
  rw [← hVU]
  exact Subgroup.commutator_mem_commutator hx hl

omit hVU in
theorem commutator_Uq_pCore : ⁅Uq M T L, pCoreOf 2 M⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Uq_le_centralizer_pCore h

theorem commutator_pCore_le_Dq : ⁅pCoreOf 2 M, pCoreOf 2 M⁆ ≤ Dq M L := by
  refine le_inf (commutator_le_of_le le_rfl le_rfl) ?_
  have h1 : ⁅⁅pCoreOf 2 M, L⁆, pCoreOf 2 M⁆ = ⊥ := by
    rw [show ⁅pCoreOf 2 M, L⁆ = Vq M L from rfl, hVU]
    exact commutator_Uq_pCore h
  have h2 : ⁅⁅L, pCoreOf 2 M⁆, pCoreOf 2 M⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L]
    exact h1
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3

omit hVU in
theorem mem_Dq_of_comm {x : G} (hx : x ∈ pCoreOf 2 M) (hxL : ∀ l ∈ L, ⁅x, l⁆ ∈ Dq M L) :
    x ∈ Dq M L := by
  have hDn : M ≤ Subgroup.normalizer (Dq M L : Set G) := le_normalizer_Dq h.le_normalizer
  let K : Subgroup G :=
    { carrier := {y | y ∈ pCoreOf 2 M ∧ ∀ l ∈ L, ⁅y, l⁆ ∈ Dq M L}
      one_mem' := ⟨one_mem _, fun l _ => by simp [one_mem]⟩
      mul_mem' := by
        rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨mul_mem hy hz, fun l hl => ?_⟩
        have e : ⁅y * z, l⁆ = y * ⁅z, l⁆ * y⁻¹ * ⁅y, l⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hDn (pCoreOf_le' M hy)) _).1 (hz' l hl))
          (hy' l hl)
      inv_mem' := by
        rintro y ⟨hy, hy'⟩
        refine ⟨inv_mem hy, fun l hl => ?_⟩
        have e : ⁅y⁻¹, l⁆ = y⁻¹ * ⁅y, l⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (hDn (pCoreOf_le' M (inv_mem hy))) _).1
          (inv_mem (hy' l hl))
        simpa using this }
  have hxK : Subgroup.zpowers x ≤ K := (Subgroup.zpowers_le).2 ⟨hx, hxL⟩
  have h2 : ⁅⁅Subgroup.zpowers x, L⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.commutator_le]
    intro y hy l hl
    exact (hxK hy).2 l hl |>.2
  have h1 : ⁅⁅L, Subgroup.zpowers x⁆, L⁆ = ⊥ := by
    rw [Subgroup.commutator_comm L]
    exact h2
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [h.perfect, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  refine ⟨hx, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
  exact (Subgroup.mem_centralizer_iff.1 (h3 hl) x (Subgroup.mem_zpowers x)).symm

end CFSG.Quasithin.MS93.S37
