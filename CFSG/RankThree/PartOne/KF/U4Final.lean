module

public import CFSG.RankThree.PartOne.KF.U4Main
public import CFSG.RankThree.PartOne.S12.InputsKF2

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.PartOne.Sec12Three CFSG.RankThree.PartOne.KFU.U4Ctx
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory

@[expose] def PSUFourEvenCenterTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (f : ℕ), 2 ≤ f → CFSG.IsQuasisimple X →
    StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 4 2 f → Subgroup.center X = ⊥

theorem kf126U4_of_inputs (hZ : PSUFourEvenCenterTrivial) : KF126U4 := by
  intro G _ _ p A c L E f h hF hf hpq hmodel hE4
  have h3 := h.three_lt
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf1 : f = 1 := by omega
    subst hf1
    have h3' : p ∣ 3 := by simpa using hpq
    have := Nat.le_of_dvd (by norm_num) h3'
    omega
  have hqs : CFSG.IsQuasisimple L :=
    hF.two.elim (fun hG => hG.quasisimple) (fun hS => hS.quasisimple)
  have hZL : Subgroup.center L = ⊥ := hZ L f hf2 hqs hmodel
  have hG : Sec12TwoGeneric p c L E := by
    rcases hF.two with hG | hS
    · exact hG
    · exfalso
      have h5 := hS.center_card
      rw [hZL] at h5
      simp at h5
  have hcomm : ∀ l ∈ L, c * l = l * c := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp
      ((mem_thetaComponentsAt_iff.mp h.L_mem.2).1 hl)).symm
  have hcL : c ∉ L := by
    intro hcL
    have hc1 : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcomm g g.2).symm
    rw [hZL, Subgroup.mem_bot] at hc1
    exact h.c_ne_one (congrArg Subtype.val hc1)
  have R : Restr c L E (E ⊓ L) := ⟨rfl, hG.E_eq, hcomm⟩
  have hcp : c ^ p = 1 := by
    have := h.A_elem
    exact elemPow_eq_one_of_isElementaryAbelian c h.c_mem
  have hco : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hFcard : Nat.card (E ⊓ L : Subgroup G) = p ^ 3 := by
    have h1 := R.card_E hp hco hcL
    rw [hE4] at h1
    have h2 : p ^ 3 * p = p ^ 4 := by ring
    exact mul_right_cancel₀ hp.ne_zero (h1.symm.trans h2.symm)
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmodel
  have hU : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hFexp : ∀ x ∈ (E ⊓ L).subgroupOf L, x ^ p = 1 := by
    intro x hx
    have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp hx).1
    apply Subtype.ext
    have := h.E_elem
    simpa using elemPow_eq_one_of_isElementaryAbelian (x : G) hxE
  have hFcomm : ∀ x ∈ (E ⊓ L).subgroupOf L, ∀ y ∈ (E ⊓ L).subgroupOf L, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val (h.E_elem.is_comm.comm ⟨(x : G), (Subgroup.mem_inf.mp hx).1⟩
      ⟨(y : G), (Subgroup.mem_inf.mp hy).1⟩)
  have hFcard' : Nat.card ((E ⊓ L).subgroupOf L) = p ^ 3 := by
    rw [← hFcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  obtain ⟨ψ, hψ⟩ := exists_diag_iso (K := K) (by omega) hK hp hpq hZL e _ hFexp hFcomm hFcard'
  let C : U4Ctx p A c L E f K :=
    ⟨h, hE4, R, hcL, hU, hf2, hpq, ψ, fun g => by
      have h1 := hψ g
      rw [Subgroup.mem_subgroupOf] at h1
      rw [← h1]
      exact ⟨fun hx => Subgroup.mem_inf.mpr ⟨hx, (ψ g).2⟩, fun hx => (Subgroup.mem_inf.mp hx).1⟩⟩
  refine ⟨fun t ht htL => ?_, fun s hs hsL t ht htL hne => ?_⟩
  · obtain ⟨R', hR'⟩ := C.exists_refl ht htL
    subst hR'
    exact C.refl_conclusions R'
  · obtain ⟨Rs, hRs⟩ := C.exists_refl hs hsL
    obtain ⟨Rt, hRt⟩ := C.exists_refl ht htL
    subst hRs
    subst hRt
    exact C.pair_conclusions Rs Rt hne

end CFSG.RankThree.PartOne
