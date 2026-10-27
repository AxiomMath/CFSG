module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative
public import CFSG.Monster.B.GSide.NativeCompletion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.GSide

theorem native_coset_graph_diameter_three_rank_five :
    cgraph.Connected ∧
    (∀ v w : CVert, cgraph.dist v w ≤ 3) ∧ (∀ v : CVert, ∃ u, cgraph.dist v u = 3) ∧
    Nat.card CVert = 13571955000 ∧
    (∀ v : CVert,
      (∀ w : CVert, w = v ∨ w ∈ cgraph.neighborSet v ∨ w ∈ sphereThree v ∨ w ∈ sphereFour v ∨
        w ∈ sphereDistThree v) ∧
      (cgraph.neighborSet v).ncard = 3968055 ∧ (sphereThree v).ncard = 2370830336 ∧
      (sphereFour v).ncard = 11174042880 ∧ (sphereDistThree v).ncard = 23113728 ∧
      (∀ w ∈ cgraph.neighborSet v, vStabOrbit v w = cgraph.neighborSet v) ∧
      (∀ w ∈ sphereThree v, vStabOrbit v w = sphereThree v) ∧
      (∀ w ∈ sphereFour v, vStabOrbit v w = sphereFour v) ∧
      (∀ w ∈ sphereDistThree v, vStabOrbit v w = sphereDistThree v)) ∧
    ∀ v u : CVert, cgraph.dist v u = 3 →
      (cgraph.neighborSet u ∩ sphereFour v).ncard = 3898440 ∧
      (cgraph.neighborSet u ∩ sphereDistThree v).ncard = 69615 :=
  ⟨cgraph_connected, diameter_three_rank_five_of_ambient ambientRootOrbitsHyp⟩

theorem natCard_Shat_eq_mul :
    Nat.card Shat = Nat.card CVert * Nat.card (vStab cv0) := by
  let _ := cvLeftAction
  have hstab : MulAction.stabilizer Shat cv0 = vStab cv0 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_vStab]
    show cvMul cv0 g⁻¹ = cv0 ↔ cvMul cv0 g = cv0
    constructor
    · intro h
      have h' : cvMul (cvMul cv0 g⁻¹) g = cvMul cv0 g := congrArg (fun x => cvMul x g) h
      rwa [← cvMul_mul, inv_mul_cancel, cvMul_one, eq_comm] at h'
    · intro h
      have h' : cvMul (cvMul cv0 g) g⁻¹ = cvMul cv0 g⁻¹ := congrArg (fun x => cvMul x g⁻¹) h
      rwa [← cvMul_mul, mul_inv_cancel, cvMul_one, eq_comm] at h'
  have horb : MulAction.orbit Shat cv0 = Set.univ := by
    refine Set.eq_univ_of_forall fun w => ?_
    obtain ⟨s, hs⟩ := cvMul_transitive cv0 w
    refine ⟨s⁻¹, ?_⟩
    show cvMul cv0 s⁻¹⁻¹ = w
    rw [inv_inv, hs]
  have hfin : Finite CVert := short_F4_involution_coset_graph_data.1
  have hidx := MulAction.index_stabilizer Shat cv0
  rw [hstab, horb, Set.ncard_univ] at hidx
  rw [← (vStab cv0).card_mul_index, hidx, mul_comm]

theorem native_global_label_bijection_and_full_vertex_centralizer :
    Function.Injective clabel ∧
    Set.range clabel = {x : Dfull | ∃ s : Shat, x = (s : Dfull)⁻¹ * Sp8.cQ * s} ∧
    (∀ (v : CVert) (s : Shat), clabel (cvMul v s) = (s : Dfull)⁻¹ * clabel v * s) ∧
    (∀ (v : CVert) (s : Shat), (s : Dfull) * clabel v = clabel v * s ↔ cvMul v s = v) ∧
    Nat.card Shat = 4154781481226426191177580544000000 := by
  refine ⟨(global_label_of_ambient ambientRootOrbitsHyp).1,
    (global_label_of_ambient ambientRootOrbitsHyp).2.1,
    (global_label_of_ambient ambientRootOrbitsHyp).2.2.1,
    (global_label_of_ambient ambientRootOrbitsHyp).2.2.2, ?_⟩
  rw [natCard_Shat_eq_mul, native_coset_graph_diameter_three_rank_five.2.2.2.1,
    natCard_vStab_eq]

theorem native_cgraph_triangulable :
    CFSG.Monster.B.Recog.Triangulable cgraph :=
  cgraph_triangulable_of_ambient ambientRootOrbitsHyp

theorem native_universal_completion
    {Y : Type*} [Group Y] (φv : vStab cv0 →* Y) (φe : cvSetStab {cv0, cw0} →* Y)
    (φt : ∀ j, cvSetStab {cv0, cw0, cu j} →* Y)
    (hve : ∀ a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0}), φv ⟨a, ha⟩ = φe ⟨a, hb⟩)
    (hvt : ∀ j a (ha : a ∈ vStab cv0) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φv ⟨a, ha⟩ = φt j ⟨a, hb⟩)
    (het : ∀ j a (ha : a ∈ cvSetStab {cv0, cw0}) (hb : a ∈ cvSetStab {cv0, cw0, cu j}),
      φe ⟨a, ha⟩ = φt j ⟨a, hb⟩) :
    ∃! Φ : Shat →* Y, (∀ a : vStab cv0, Φ a = φv a) ∧ (∀ a : cvSetStab {cv0, cw0}, Φ a = φe a) ∧
      ∀ j (a : cvSetStab {cv0, cw0, cu j}), Φ a = φt j a :=
  native_universal_completion_of_ambient_cu ambientRootOrbitsHyp φv φe φt hve hvt het

end CFSG.Monster.B.TwoA.Amalgam
