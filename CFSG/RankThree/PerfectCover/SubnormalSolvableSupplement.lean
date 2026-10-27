module

public import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PerfectCover

open Subgroup

universe u

theorem perfectResidual_eq_of_normal_of_sup_solvable {H : Type*} [Group H] [Finite H]
    {P N : Subgroup H} (hP : Group.IsPerfect P) (hPn : P.Normal) (hN : N.Normal)
    (hNsol : Group.IsSolvable N) (hPN : P ⊔ N = ⊤) : perfectResidual H = P := by
  apply le_antisymm
  · have hsurj : Function.Surjective ((QuotientGroup.mk' P).comp N.subtype) := by
      intro y
      obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective P y
      have hh : h ∈ N ⊔ P := by
        rw [sup_comm, hPN]
        exact mem_top h
      obtain ⟨n, hn, q, hq, rfl⟩ := mem_sup_of_normal_left.mp hh
      refine ⟨⟨n, hn⟩, ?_⟩
      simp only [MonoidHom.coe_comp, Function.comp_apply, coe_subtype, QuotientGroup.mk'_apply,
        QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff q).mpr hq, mul_one]
    have hsol : Group.IsSolvable (H ⧸ P) := Group.isSolvable_of_surjective hsurj
    exact ((perfect_residual_characterization (G := H)).2.2.2.2.1 P).mp hsol
  · exact (perfect_residual_transport (MonoidHom.id H)).2.2 P hP

theorem perfect_subnormal_solvable_supplement_residual_aux (n : ℕ) :
    ∀ (H : Type u) [Group H] [Finite H], Nat.card H = n → ∀ {P N : Subgroup H},
      Group.IsPerfect P → P.IsSubnormal → N.Normal → Group.IsSolvable N → P ⊔ N = ⊤ →
        P.Normal ∧ perfectResidual H = P := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ hcard P N hP hPsn hN hNsol hPN
  suffices hPn : P.Normal from
    ⟨hPn, perfectResidual_eq_of_normal_of_sup_solvable hP hPn hN hNsol hPN⟩
  rcases hPsn.lt_normal with hPtop | ⟨M, hMn, hPM, hMlt⟩
  · rw [hPtop]
    exact normal_top
  have hMcard : Nat.card M < n := by
    rw [← hcard, ← Subgroup.card_top (G := H)]
    exact Subgroup.card_lt_of_lt hMlt
  have hPM' : Group.IsPerfect (P.subgroupOf M) := by
    have : Group.IsPerfect P := hP
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hPM).symm.toMonoidHom)
      (subgroupOfEquivOfLe hPM).symm.surjective
  have hNM : Group.IsSolvable (N.subgroupOf M) := by
    let f : N.subgroupOf M →* N :=
      MonoidHom.codRestrict (M.subtype.comp (N.subgroupOf M).subtype) N fun x => x.2
    have hf : Function.Injective f := by
      intro x y hxy
      have h : ((x : M) : H) = ((y : M) : H) := congrArg (fun z : N => (z : H)) hxy
      exact Subtype.ext (Subtype.ext h)
    exact Group.isSolvable_of_isSolvable_injective hf
  have hsup : P.subgroupOf M ⊔ N.subgroupOf M = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨m, hm⟩ -
    have hmem : m ∈ N ⊔ P := by
      rw [sup_comm, hPN]
      exact mem_top m
    obtain ⟨y, hy, q, hq, rfl⟩ := mem_sup_of_normal_left.mp hmem
    have hyM : y ∈ M := by
      have := M.mul_mem hm (M.inv_mem (hPM hq))
      rwa [mul_inv_cancel_right] at this
    have hprod : (⟨y * q, hm⟩ : M) = ⟨y, hyM⟩ * ⟨q, hPM hq⟩ := rfl
    rw [hprod, sup_comm]
    exact mul_mem_sup (show (⟨y, hyM⟩ : M) ∈ N.subgroupOf M from hy)
      (show (⟨q, hPM hq⟩ : M) ∈ P.subgroupOf M from hq)
  obtain ⟨-, hres⟩ := ih _ hMcard M rfl hPM' hPsn.subgroupOf
    (N := N.subgroupOf M) inferInstance hNM hsup
  have hPeq : P = (perfectResidual M).map M.subtype := by
    rw [hres, subgroupOf_map_subtype, inf_eq_left.mpr hPM]
  rw [hPeq]
  exact ConjAct.normal_of_characteristic_of_normal

theorem perfect_subnormal_solvable_supplement_residual {H : Type u} [Group H] [Finite H]
    {P N : Subgroup H} (hP : Group.IsPerfect P) (hPsn : P.IsSubnormal) (hN : N.Normal)
    (hNsol : Group.IsSolvable N) (hPN : P ⊔ N = ⊤) :
    P.Normal ∧ perfectResidual H = P :=
  perfect_subnormal_solvable_supplement_residual_aux _ H rfl hP hPsn hN hNsol hPN

end CFSG.RankThree.PerfectCover
