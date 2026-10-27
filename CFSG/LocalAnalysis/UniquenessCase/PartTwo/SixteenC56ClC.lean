module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G} {g : G}

theorem c33_h3 (hS : C33Setting M V) (g : G) : H3Cond 2 M V g := by
  intro A hA _ hmax
  obtain ⟨x, rfl⟩ := hA
  have hi : E3.mQuot (conjSubgroup V x) M < 2 := (max_lt_iff.1 hmax).1
  have hmQ : E3.mQuot (conjSubgroup V x) (conjSubgroup V x ⊓ M) =
      E3.mQuot (conjSubgroup V x) M := by
    unfold E3.mQuot
    rw [Subgroup.inf_relIndex_left]
  have hmem : (conjSubgroup V x ⊓ M) ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V x) M) M :=
    ⟨inf_le_right, x, inf_le_left, hmQ⟩
  have hle := hS.gamma_le _ (by omega) _ hmem
  refine Subgroup.commutator_le.2 fun a ha v hv => ?_
  have h1 : v * a = a * v :=
    Subgroup.mem_centralizer_iff.1 (hle ha) v (Subgroup.mem_inf.1 hv).1
  rw [commutatorElement_eq_one_iff_mul_comm.2 h1.symm]
  exact Subgroup.one_mem _

theorem c33_hyp612 (hgeo : GeoDichotomy) (hS : C33Setting M V) (hh : C33Hyp M V g)
    (hr : (2 : ℕ∞) < rStarMV M V) : Hyp612 2 M V g := by
  have hV := hS.elemAbelian
  have hP := c33_prim hgeo hS hh
  have hcore := c33_core hgeo hS hh
  have hP' := c33_prim hgeo (hS.conj g) hcore.swap_hyp
  have hBV : BOf M V g ≤ conjSubgroup V g := inf_le_left
  have hmB : E3.mQuot (conjSubgroup V g) M = 2 := by
    have h := c33_mQuot_eq_two hS hh
    have e : E3.mQuot (conjSubgroup V g) (BOf M V g) = E3.mQuot (conjSubgroup V g) M := by
      unfold E3.mQuot BOf
      rw [Subgroup.inf_relIndex_left]
    rw [← e]
    exact h
  have hcent' : conjSubgroup V g ⊓ Subgroup.centralizer ((UOf M V g : Subgroup G) : Set G) ≤ V := by
    have h := hP'.centralizer_le
    rwa [BOf_swap, conjSubgroup_conjSubgroup_inv] at h
  exact
    { elemAbelian := hV
      normalizer_eq := hS.normalizer_eq
      lt_rStar := hr
      inCalO := ⟨⟨hP.not_conjV_le_M, hP.mQuot_U, fun h => absurd rfl h⟩,
        ⟨hP.not_V_le_conjM, hmB.le, fun h => absurd rfl h⟩⟩
      centralizer_le := hP.centralizer_le
      mem_of_commutator_mem := by
        intro b hb hbV v hv hc
        refine hP.mem_of_commutator_mem b hb (fun hbC => hbV (hcent' (Subgroup.mem_inf.2
          ⟨(Subgroup.mem_inf.1 hb).1, ?_⟩))) v hv hc
        exact Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.1 hx).1) hbC
      centralizer_le' := hcent'
      mem_of_commutator_mem' := by
        intro a ha haV w hw hc
        have haC : a ∉ Subgroup.centralizer (conjSubgroup V g : Set G) := fun hac =>
          haV (hP.centralizer_le (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha).1,
            Subgroup.centralizer_le (fun x hx => hBV hx) hac⟩))
        have h := hP'.mem_of_commutator_mem a (by rwa [BOf_swap]) haC w hw
          (by rwa [conjSubgroup_conjSubgroup_inv, inf_comm])
        rwa [conjSubgroup_conjSubgroup_inv] at h
      h3 := c33_h3 hS g
      not_inCalO1 := fun h => by
        have h1 := h.2.2.1
        rw [hmB] at h1
        omega }

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
