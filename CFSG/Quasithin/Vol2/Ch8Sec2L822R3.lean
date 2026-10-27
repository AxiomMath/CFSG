module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1
public import CFSG.Sporadic.Recognition.M22MultiplierCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2411Cover
public import CFSG.Sporadic.SuzOddCore.Outer

public section

namespace CFSG.Quasithin.H13

theorem schurM22_holds :
    SchurM22 := by
  intro X _ _ hX N _ hNZ ⟨e⟩
  have hs : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
  have hnc : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hperf := CFSG.QuasithinUnique.Lin2.isPerfect_carrier_m22
    rw [Group.isPerfect_def] at hperf
    have hbot : commutator (CFSG.Blueprint.NativeSporadic.Carrier .M22) = ⊥ := by
      rw [eq_bot_iff, commutator_def]
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_def, hc a b]
      group
    have hnt : Nontrivial (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.1
    obtain ⟨x, hx⟩ := exists_ne (1 : CFSG.Blueprint.NativeSporadic.Carrier .M22)
    have hxt : x ∈ commutator (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
      rw [hperf]; exact Subgroup.mem_top x
    rw [hbot, Subgroup.mem_bot] at hxt
    exact hx hxt
  have hcen := CFSG.Sporadic.SuzOddCore.center_eq_bot_of_simple hnc
  have hZN : Subgroup.center X ≤ N := by
    intro z hz
    have hmem : e (QuotientGroup.mk z) ∈
        Subgroup.center (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        Subgroup.mem_center_iff.mp hz x]
    rw [hcen, Subgroup.mem_bot] at hmem
    have h1 : (QuotientGroup.mk z : X ⧸ N) = 1 := e.injective (hmem.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff z).mp h1
  have hEq : N = Subgroup.center X := le_antisymm hNZ hZN
  have e' : X ⧸ Subgroup.center X ≃* CFSG.Blueprint.NativeSporadic.M22 :=
    (QuotientGroup.quotientMulEquivOfEq hEq.symm).trans e
  obtain ⟨-, hd⟩ :=
    CFSG.Sporadic.Recognition.M22Multiplier.center_cyclic_dvd_twelve_of_certificate hX.1 e'
  rw [hEq]
  exact hd

theorem res822ThreeCover_holds
    (h3228 : Stmt3_2_2_eight) (h711n : Stmt7_1_1_normal) (hthree : Input822ThreeInL) :
    Res822ThreeCover :=
  res822ThreeCover_of h3228 h711n hthree schurM22_holds

end CFSG.Quasithin.H13
