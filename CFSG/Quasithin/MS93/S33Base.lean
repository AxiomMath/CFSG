module

public import CFSG.Quasithin.MS93.S32Basic

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {V P : Subgroup G}
    (hP : IsPGroup p P) (hVP : V ≤ P) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (hV : V ≠ ⊥) : ⁅V, P⁆ < V := by
  have hle : ⁅V, P⁆ ≤ V := (Subgroup.le_normalizer_iff_commutator_le_left).mp hPN
  refine lt_of_le_of_ne hle fun heq => hV ?_
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries P).mp hnil
  have key : ∀ k, V ≤ P.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hVP
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      calc V = ⁅V, P⁆ := heq.symm
        _ ≤ ⁅P.lowerCentralSeries k, P⁆ := Subgroup.commutator_mono ih le_rfl
  rw [eq_bot_iff, ← hn]
  exact key n

variable [Finite G] {M T L : Subgroup G}

theorem inf_centralizer_Uq (h : PUHyp M T L) :
    T ⊓ Subgroup.centralizer (Uq M T L : Set G) = pCoreOf 2 M := by
  refine le_antisymm ?_ ?_
  · rw [← h.centralizer_Z0q]
    rintro t ⟨htT, htU⟩
    refine ⟨htT, ?_⟩
    have hle : Z0q M T ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [h.Z0q_eq_sup]
      refine sup_le (fun a ha => ?_) (fun u hu => ?_)
      · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
        rw [Set.mem_singleton_iff.mp hx]
        exact Subgroup.mem_centralizer_iff.mp
          ((PU.omegaOneCenterOf_le_centerOf T ha).2) t htT
      · refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
        rw [Set.mem_singleton_iff.mp hx]
        exact (Subgroup.mem_centralizer_iff.mp htU u hu).symm
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hle hz) t rfl).symm
  · exact le_inf h.pCore_le (h.pCoreOf_le_centralizer_Z0q.trans
      (Subgroup.centralizer_le (Uq_le_Z0q h.L_le)))

theorem commutator_Z0q_eq (h : PUHyp M T L) {Y : Subgroup G} (hY : Y ≤ T) :
    ⁅Z0q M T, Y⁆ = ⁅Uq M T L, Y⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono (Uq_le_Z0q h.L_le) le_rfl)
  rw [Subgroup.commutator_le]
  intro z hz y hy
  have hcomm := isMulCommutative_subgroup_iff.mp h.isElemAbelian_Z0q.1
  have hUY : ⁅Uq M T L, Y⁆ ≤ Uq M T L :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp
      ((hY.trans h.le).trans (le_normalizer_Uq h.le_normalizer))
  have hUZ : ⁅Uq M T L, Y⁆ ≤ Z0q M T := hUY.trans (Uq_le_Z0q h.L_le)
  let S : Subgroup G :=
    { carrier := {x | x ∈ Z0q M T ∧ ⁅x, y⁆ ∈ ⁅Uq M T L, Y⁆}
      mul_mem' := by
        rintro x₁ x₂ ⟨hx₁, hc₁⟩ ⟨hx₂, hc₂⟩
        refine ⟨mul_mem hx₁ hx₂, ?_⟩
        have e : ⁅x₁ * x₂, y⁆ = (x₁ * ⁅x₂, y⁆ * x₁⁻¹) * ⁅x₁, y⁆ := by
          simp only [commutatorElement_def]
          group
        have e' : x₁ * ⁅x₂, y⁆ * x₁⁻¹ = ⁅x₂, y⁆ := by
          rw [hcomm _ hx₁ _ (hUZ hc₂), mul_inv_cancel_right]
        rw [e, e']
        exact mul_mem hc₂ hc₁
      one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
      inv_mem' := by
        rintro x ⟨hx, hc⟩
        refine ⟨inv_mem hx, ?_⟩
        have e : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * x := by
          simp only [commutatorElement_def]
          group
        have e' : x⁻¹ * ⁅x, y⁆⁻¹ * x = ⁅x, y⁆⁻¹ := by
          rw [hcomm _ (inv_mem hx) _ (inv_mem (hUZ hc)), mul_assoc, inv_mul_cancel, mul_one]
        rw [e, e']
        exact inv_mem hc }
  have hle : Z0q M T ≤ S := by
    rw [h.Z0q_eq_sup]
    refine sup_le (fun a ha => ⟨omegaOneCenterOf_le_Z0q M T h.le ha, ?_⟩)
      (fun u hu => ⟨Uq_le_Z0q h.L_le hu, Subgroup.commutator_mem_commutator hu hy⟩)
    have hc := Subgroup.mem_centralizer_iff.mp
      ((PU.omegaOneCenterOf_le_centerOf T ha).2) y (hY hy)
    rw [commutatorElement_def, ← hc, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  exact (hle hz).2

theorem commutator_Uq_lt (h : PUHyp M T L) {K : Subgroup G} (hK : K ≤ T) :
    ⁅Uq M T L, K⁆ < Uq M T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine lt_of_le_of_lt (Subgroup.commutator_mono le_rfl hK) ?_
  exact commutator_lt_of_isPGroup h.isPGroup ((h.Uq_le_Xq.trans (Xq_le_pCoreOf M)).trans h.pCore_le)
    (h.le.trans (le_normalizer_Uq h.le_normalizer)) h.Uq_ne_bot

end CFSG.Quasithin.MS93.S33
