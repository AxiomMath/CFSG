module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONSevenFix
public import CFSG.Sporadic.ONOddCore.Involutions
import CFSG.Sporadic.ONOddCore.CertifiedSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 CFSG.ONSchreier

private theorem center_Pv_eq_bot :
    Subgroup.center Pv = ⊥ := by
  have hs : IsSimpleGroup Pv :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.ONOddCore.fam_on_certified_simplicity.2
      onEquivPv.symm
  have hnab : CFSG.RankThree.Native.onSevenA * CFSG.RankThree.Native.onSevenB ≠
      CFSG.RankThree.Native.onSevenB * CFSG.RankThree.Native.onSevenA := by
    intro h
    exact CFSG.RankThree.Native.onSeven_commutator_ne_one
      (commutatorElement_eq_one_iff_mul_comm.2 h)
  exact CFSG.Sporadic.Schreier.center_eq_bot_of_simple hs hnab

private theorem exists_involution_centralizing_on7W_zero :
    ∃ u : Pv, u * u = 1 ∧ u ≠ 1 ∧ u * on7W 0 = on7W 0 * u := by
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({on7W 0} : Set Pv)) 2
    (by rw [card_centralizer_on7W]; norm_num)
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hu2 : u * u = 1 := by
    have h := pow_orderOf_eq_one u
    rw [hu] at h
    simpa [sq] using h
  refine ⟨u, ?_, ?_, Subgroup.mem_centralizer_singleton_iff.1 u.2⟩
  · simpa using congrArg (fun x : ↥(Subgroup.centralizer ({on7W 0} : Set Pv)) => (x : Pv)) hu2
  · intro h
    exact hu1 (Subtype.ext h)

private theorem exists_inv_of_central_involution
    {u : Pv} (hu2 : u * u = 1) (hu1 : u ≠ 1) (hucomm : u * on7W 0 = on7W 0 * u) :
    ∃ z : Pv, IsHeisCenter7 z ∧ u * z * u⁻¹ = z⁻¹ := by
  have hα2 : MulAut.conj u * MulAut.conj u = 1 := by
    have h := map_mul (MulAut.conj : Pv →* MulAut Pv) u u
    rw [hu2, map_one] at h
    exact h.symm
  have hαx : MulAut.conj u (on7W 0) = on7W 0 := by
    rw [MulAut.conj_apply, hucomm]
    group
  have hα1 : MulAut.conj u ≠ 1 := by
    intro h
    have hmem : u ∈ Subgroup.center Pv := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hx : MulAut.conj u x = x := by rw [h, MulAut.one_apply]
      rw [MulAut.conj_apply] at hx
      calc x * u = (u * x * u⁻¹) * u := by rw [hx]
        _ = u * x := by group
    rw [center_Pv_eq_bot, Subgroup.mem_bot] at hmem
    exact hu1 hmem
  obtain ⟨z, hz, hαz⟩ := on_exists_inv_of_fix_on7W_zero hα2 hα1 hαx
  exact ⟨z, hz, by rwa [MulAut.conj_apply] at hαz⟩

theorem on_exists_inv_of_inner
    {t : Pv} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    ∃ z : Pv, IsHeisCenter7 z ∧ t * z * t⁻¹ = z⁻¹ := by
  obtain ⟨u, hu2, hu1, hucomm⟩ := exists_involution_centralizing_on7W_zero
  obtain ⟨z, hz, huz⟩ := exists_inv_of_central_involution hu2 hu1 hucomm
  have htord : orderOf t = 2 := orderOf_eq_prime (by simpa [sq] using ht2) ht1
  have htord' : orderOf (t : Equiv.Perm (Fin N)) = 2 := by
    rw [Subgroup.orderOf_coe, htord]
  have huordP : orderOf u = 2 := orderOf_eq_prime (by simpa [sq] using hu2) hu1
  have huord : orderOf (u : Equiv.Perm (Fin N)) = 2 := by
    rw [Subgroup.orderOf_coe, huordP]
  obtain ⟨gt, hgtP, hgt⟩ :=
    CFSG.Sporadic.ONOddCore.cti_on_all_involutions_conjugate (t : Equiv.Perm (Fin N)) t.2 htord'
  obtain ⟨gu, hguP, hgu⟩ :=
    CFSG.Sporadic.ONOddCore.cti_on_all_involutions_conjugate
      (u : Equiv.Perm (Fin N)) u.2 huord
  let k : Pv := ⟨gt * gu⁻¹, mul_mem hgtP (inv_mem hguP)⟩
  have hku : t = k * u * k⁻¹ := by
    apply Subtype.ext
    have hgu' : onz = gu⁻¹ * (u : Equiv.Perm (Fin N)) * gu := by
      rw [hgu]
      group
    calc (t : Equiv.Perm (Fin N)) = gt * onz * gt⁻¹ := hgt
      _ = gt * (gu⁻¹ * (u : Equiv.Perm (Fin N)) * gu) * gt⁻¹ := by rw [hgu']
      _ = (gt * gu⁻¹) * (u : Equiv.Perm (Fin N)) * (gt * gu⁻¹)⁻¹ := by group
      _ = ((k : Pv) : Equiv.Perm (Fin N)) * (u : Equiv.Perm (Fin N)) *
          ((k : Pv) : Equiv.Perm (Fin N))⁻¹ := rfl
      _ = ((k * u * k⁻¹ : Pv) : Equiv.Perm (Fin N)) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  refine ⟨k * z * k⁻¹, hz.conj k, ?_⟩
  calc t * (k * z * k⁻¹) * t⁻¹
      = (k * u * k⁻¹) * (k * z * k⁻¹) * (k * u * k⁻¹)⁻¹ := by rw [hku]
    _ = k * (u * z * u⁻¹) * k⁻¹ := by group
    _ = k * z⁻¹ * k⁻¹ := by rw [huz]
    _ = (k * z * k⁻¹)⁻¹ := by group

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
