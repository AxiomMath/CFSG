
module

public import CFSG.Quasithin.Background.A3Structure36BSetupBase
public import CFSG.Quasithin.Background.A1aFitting

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

variable {X : Type} [Group X]

theorem map_pCore_le (K : Subgroup X) [K.Normal] (p : ℕ) :
    (CFSG.pCore p ↥K).map K.subtype ≤ CFSG.pCore p X :=
  le_sSup ⟨inferInstance, (CFSG.pCore_isPGroup (p := p) (G := ↥K)).map K.subtype⟩

theorem isNilpotent_kernel (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    Group.IsNilpotent ↥K := by
  have hfin : Finite X := h.finite
  have hKn : K.Normal := hK.data.normal
  have hsolvO : Group.IsSolvable ↥(CFSG.solvableRadical X) := A3.solvableRadical_isSolvable
  have hsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK.data.le_radical)
      (Subgroup.inclusion_injective _)
  refine (isNilpotent_of_pResidual_le_centralizer (K := ↥K) ?_).2.2
  intro p hp _
  have hfp : Fact p.Prime := ⟨hp⟩
  have hNn : (Subgroup.centralizer (CFSG.Open.pCore p ↥K : Set ↥K)).Normal := by
    exact A1a.normal_centralizer_of_normal _
  apply pResidual_le (N := Subgroup.centralizer (CFSG.Open.pCore p ↥K : Set ↥K))
  intro y
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  refine ⟨a, ?_⟩
  have hdvd : p ^ a ∣ orderOf y := ⟨m, hord⟩
  have hym : orderOf (y ^ p ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hord]
    exact Nat.mul_div_cancel_left m (pow_pos hp.pos a)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : u ∈ CFSG.pCore p ↥K := by
    exact hu
  have huR : (u : X) ∈ CFSG.pCore p X := map_pCore_le K p ⟨u, hu', rfl⟩
  by_cases hπ : IsPi X p
  · obtain ⟨D, hDK⟩ := hK.prime p hp hπ
    set z : ↥K := y ^ p ^ a with hz
    have hzK : (z : X) ∈ D.K := hDK ▸ z.2
    have hcop : (orderOf (MulAut.conjNormal (z : X) : MulAut ↥(CFSG.pCore p X))).Coprime p := by
      have h1 : orderOf (MulAut.conjNormal (z : X) : MulAut ↥(CFSG.pCore p X)) ∣ m := by
        have := orderOf_map_dvd (MulAut.conjNormal : X →* MulAut ↥(CFSG.pCore p X)) (z : X)
        rw [Subgroup.orderOf_coe, hym] at this
        exact this
      exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    have h1 := D.faithful _ hcop ((D.mem_K (z : X)).1 hzK)
    have h2 := congrArg (fun φ : MulAut ↥(CFSG.pCore p X) => ((φ ⟨(u : X), huR⟩ : _) : X)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    apply Subtype.ext
    change (u : X) * (z : X) = (z : X) * (u : X)
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  · have hπ' : CFSG.pCore p X ≤ Subgroup.center X := not_not.1 hπ
    have hc := Subgroup.mem_center_iff.1 (hπ' huR) ((y ^ p ^ a : ↥K) : X)
    apply Subtype.ext
    exact hc.symm

theorem kernel_eq_fitting (h : A36BHyp X) {K : Subgroup X} (hK : KernelSetup X K) :
    K = CFSG.fittingSubgroup X := by
  have hfin : Finite X := h.finite
  have hnil := isNilpotent_kernel h hK
  apply le_antisymm
  · exact le_sSup ⟨hK.data.normal, hnil⟩
  · exact le_kernel_of_odd hK.data fitting_le_radical (odd_card_fitting h)

end CFSG.Quasithin.A36B
