module

public import CFSG.Timmesfeld.Bridge.Asc72Triangle

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

variable {G : Type*} [Group G] {D : Set G}

theorem compStab_eq_of_reach (hS : Setup G D) {x y : G} (hxy : Reach D x y) :
    compStab hS.normal x = compStab hS.normal y := by
  ext g
  rw [mem_compStab_iff, mem_compStab_iff]
  have hc := reach_conj hS.normal g hxy
  constructor
  · intro h
    exact reach_trans (reach_symm hxy) (reach_trans h hc)
  · intro h
    exact reach_trans hxy (reach_trans h (reach_symm hc))

theorem exists_thirdKind [Finite G] (hS : Setup G D) (hdisc : Disconnected D)
    (hnorm : ∀ K : Subgroup G, K.Normal → K = ⊥ ∨ commutator G ≤ K)
    {u v : G} (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (hc : Commute u v) (hnot : u * v ∉ D) :
    ∃ w ∈ D, ¬ Reach D u w ∧ IsTriangle D u w v ∧ IsThirdKind u w v := by
  by_contra hcon
  push Not at hcon
  have hN := hS.normal
  have hD := hS.oddT
  have hvu : Reach D u v := reach_of_commute hu hv hc
  have hker : u * v ∈ ker hN := by
    rw [mem_ker_iff]
    intro x hx
    by_cases hux : Reach D u x
    · rw [← mem_compStab_iff hN, ← compStab_eq_of_reach hS hux]
      exact (compStab hN u).mul_mem (mem_compStab_self hN u) (mem_compStab_of_reach hS hvu)
    ·
      have hxu : ¬ Commute u x := fun h => hux (reach_of_commute hu hx h)
      have hxv : ¬ Commute v x := fun h =>
        hux (reach_trans hvu (reach_of_commute hv hx h))
      have htri : IsTriangle D u x v := ⟨hu, hv, hx, huv, hc, hxu, hxv⟩
      have h4 : orderOf (u * v * x) = 4 := by
        rcases htri.orderOf_cases hD hN with ⟨hodd, -⟩ | h4 | h3
        · exact absurd (htri.mul_mem_of_odd hD hN hodd) hnot
        · exact h4
        · exact absurd h3 (hcon x hx hux htri)
      have hx2 := hD.mul_self_eq_one hx
      have huv2 : u * v * (u * v) = 1 := htri.uv_mul_self hD
      have huvi : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huv2
      have hcomm : Commute x (u * v * x * (u * v)⁻¹) := by
        rw [huvi, commute_iff_mul_sq_eq_one hx2]
        ·
          have e : x * (u * v * x * (u * v)) = (x * (u * v)) ^ 2 := by rw [pow_two]; group
          have hconj : orderOf (x * (u * v)) = 4 := by
            have hsc : SemiconjBy x (u * v * x) (x * (u * v)) := by
              unfold SemiconjBy; group
            rw [← hsc.orderOf_eq, h4]
          rw [e, ← pow_mul, show 2 * 2 = 4 by norm_num, ← hconj, pow_orderOf_eq_one]
        · calc u * v * x * (u * v) * (u * v * x * (u * v))
              = u * v * x * (u * v * (u * v)) * x * (u * v) := by group
            _ = 1 := by rw [huv2, mul_one, mul_assoc (u * v) x x, hx2, mul_one, huv2]
      exact reach_of_commute hx (hN _ _ hx) hcomm
  have hker1 : ker hN ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hker
    exact huv (hD.eq_of_mul_eq_one hu hker)
  have hGker : commutator G ≤ ker hN := (hnorm _ (ker_normal hN)).resolve_left hker1
  have hidx : (ker hN).index ≤ 2 :=
    (Subgroup.index_antitone hGker).trans hS.index_commutator_le_two
  obtain ⟨w, hw, huw⟩ := exists_not_reach hdisc (x := u)
  have hu_not : u ∉ ker hN := by
    intro h
    rw [mem_ker_iff] at h
    have := h w hw
    exact huw (reach_symm (reach_of_mem_compStab_of_odd hN hD.isInvolutionSet hD.oddAcross hw hu
      this))
  have hlt : ker hN < compStab hN u := lt_of_le_of_ne
    (fun g hg => (mem_ker_iff hN).mp hg u hu)
    (fun h => hu_not (h ▸ mem_compStab_self hN u))
  have htop : compStab hN u = ⊤ := by
    have h1 := Subgroup.index_strictAnti hlt
    have hpos : (compStab hN u).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Subgroup.index_eq_one.mp (by omega)
  exact huw (reach_of_mem_compStab_of_odd hN hD.isInvolutionSet hD.oddAcross hu hw
    (htop ▸ Subgroup.mem_top w))

end CFSG.Timmesfeld.Bridge.Asc72
