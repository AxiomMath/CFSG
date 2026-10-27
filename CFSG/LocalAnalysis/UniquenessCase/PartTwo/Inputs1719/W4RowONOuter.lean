module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONGraphLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONSevenFixGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier CFSG.Sporadic.ONOddCore
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

private theorem on_inv_of_graph_congr
    {α : MulAut Pv} (Θ : Pv ≃* Pv)
    (hz : MulAut.congr Θ α zP = zP) {A : GL (Fin 3) PSL3Four.F4}
    (hc : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((MulAut.congr Θ α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = (LinearFlag.conjAut 3 PSL3Four.F4 A *
          LinearFlag.dualAut 3 PSL3Four.F4) (lToS a))
    (hA2 : (LinearFlag.conjAut 3 PSL3Four.F4 A *
      LinearFlag.dualAut 3 PSL3Four.F4) ^ 2 = 1) :
    ∃ z : Pv, IsHeisCenter7 z ∧ α z = z⁻¹ := by
  obtain ⟨m, hm_inv, hm_comm, hm7⟩ := on_outer_exists_inv_of_graph hz hc hA2
  have hm_heis : IsHeisCenter7 m := by
    refine on_isHeisCenter7_of_comm_involution ?_ ?_ ?_ ?_ hm_comm.symm
    · rw [← hm7, pow_orderOf_eq_one]
    · intro h
      rw [h, orderOf_one] at hm7
      omega
    · apply Subtype.ext
      exact onz_sq
    · intro h
      exact onz_ne_one (congrArg Subtype.val h)
  refine ⟨Θ.symm m, ?_, ?_⟩
  · exact IsHeisCenter7.map hm_heis Θ.symm.toMonoidHom Θ.symm.injective
  have h1 : Θ (α (Θ.symm m)) = m⁻¹ := by
    have := hm_inv
    rwa [MulAut.congr_apply] at this
  calc α (Θ.symm m) = Θ.symm (Θ (α (Θ.symm m))) := by simp
    _ = Θ.symm (m⁻¹) := by rw [h1]
    _ = (Θ.symm m)⁻¹ := map_inv _ _

private theorem on_inv_of_field_congr
    {α : MulAut Pv} (Θ : Pv ≃* Pv) {s : Pv} (hΘs : Θ s = zP)
    (hα2 : α * α = 1) (hα1 : α ≠ 1) (hs2 : orderOf s = 2)
    (hz : MulAut.congr Θ α zP = zP) {A : GL (Fin 3) PSL3Four.F4}
    (hc : ∀ a a' : onL, (a' : Equiv.Perm (Fin N)) =
      ((MulAut.congr Θ α ⟨a, onM_le (onL_le_M a.2)⟩ : Pv) : Equiv.Perm (Fin N)) →
        lToS a' = (LinearFlag.conjAut 3 PSL3Four.F4 A *
          LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob) (lToS a))
    (hA2 : (LinearFlag.conjAut 3 PSL3Four.F4 A *
      LinearFlag.fieldAut 3 PSL3Four.F4 PSL3Four.frob) ^ 2 = 1) :
    ∃ z : Pv, IsHeisCenter7 z ∧ α z = z⁻¹ := by
  obtain ⟨-, w, -, -, hw, hw7⟩ := exists_fixed_three_seven_of_field A hA2
  obtain ⟨x, hx, hxr⟩ := on_outer_exists_fixed_of_quotient (t := s) Θ hΘs hz hc hw
    (by norm_num) (by norm_num) hw7
  obtain ⟨hαx, hxc⟩ := Subgroup.mem_inf.1 hx
  have hx7 : x ^ 7 = 1 := by rw [← hxr, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxr
    omega
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs2
    omega
  exact on_exists_inv_of_fix_seven hα2 hα1 hx7 hx1
    (mul_self_eq_one_of_orderOf_eq_two hs2) hs1
    (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm hαx

theorem on_exists_inv_of_outer
    {α : MulAut Pv}
    (hout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range) (hα2 : α * α = 1) :
    ∃ z : Pv, IsHeisCenter7 z ∧ α z = z⁻¹ := by
  have hα1 : α ≠ 1 := by
    rintro rfl
    exact hout ⟨1, map_one _⟩
  have htwo : 2 ∣ Nat.card Pv := by
    rw [card_Pv]
    norm_num
  have hinv : Function.Involutive α := fun x => by
    rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
  obtain ⟨s, hs2, hαs⟩ :=
    CFSG.ComponentClassification.InvolutionFixedPoints.exists_fixed_involution htwo α hinv
  obtain ⟨g, hg, hga⟩ := cti_on_all_involutions_conjugate (s : Equiv.Perm (Fin N)) s.2
    (by rw [Subgroup.orderOf_coe, hs2])
  let gP : Pv := ⟨g, hg⟩
  let Θ : Pv ≃* Pv := MulAut.conj gP⁻¹
  have hΘs : Θ s = zP := by
    apply Subtype.ext
    change g⁻¹ * ((s : Pv) : Equiv.Perm (Fin N)) * g⁻¹⁻¹ = onz
    rw [hga]
    group
  let γ : MulAut Pv := MulAut.congr Θ α
  have hz : γ zP = zP := by
    change MulAut.congr Θ α zP = zP
    rw [← hΘs]
    change Θ (α (Θ.symm (Θ s))) = Θ s
    rw [MulEquiv.symm_apply_apply, hαs]
  have hαord : orderOf α = 2 := by
    refine orderOf_eq_prime ?_ hα1
    rwa [sq]
  have hγord : orderOf γ = 2 := by
    change orderOf (MulAut.congr Θ α) = 2
    rwa [MulEquiv.orderOf_eq]
  have hγγ : γ * γ = 1 := mul_self_eq_one_of_orderOf_eq_two hγord
  change α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner Pv at hout
  have hγout : γ ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
    intro hb
    exact hout ((congr_mem_inner_iff Θ α).1 hb)
  obtain ⟨-, hLm, -, A, hc | hc⟩ :=
    ctuc_on_outer_local_quotient_is_graph_or_field.2.2 γ hγout hz
  · exact on_inv_of_graph_congr Θ hz hc
      (by rw [sq]; exact induced_sq hγγ hLm hc)
  · exact on_inv_of_field_congr Θ hΘs hα2 hα1 hs2 hz hc
      (by rw [sq]; exact induced_sq hγγ hLm hc)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
