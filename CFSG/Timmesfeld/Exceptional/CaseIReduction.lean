module

public import CFSG.Timmesfeld.Exceptional.CaseILocal
public import CFSG.Timmesfeld.Exceptional.Polar
public import CFSG.Timmesfeld.Exceptional.Residual

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def LeviOrderThree (D : Set G) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, ¬ Commute x y → Odd (orderOf (x * y)) → ∀ b ∈ D, Commute b x →
    Commute b y → orderOf (x * y) = 3

theorem collinear_sq_of_pq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hPQ : ExcPQ D) {x y b f : G} (hx : x ∈ D) (hy : y ∈ D)
    (hb : b ∈ D) (hf : f ∈ D) (hxy : ¬ Commute x y) (hodd : Odd (orderOf (x * y)))
    (hbx : Commute b x) (hby : Commute b y) (hbf : Commute b f) (hbfD : b * f ∈ D)
    (hxf : ¬ Commute x f) :
    (x * f) ^ 2 ∈ D ∧ Commute x ((x * f) ^ 2) ∧ x * (x * f) ^ 2 ∈ D ∧
      Commute b ((x * f) ^ 2) ∧ b * (x * f) ^ 2 ∈ D := by
  have h4 : orderOf (x * f) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hx hf with h | h | ⟨h, -⟩
    · exact absurd h hxf
    · exact h
    · exfalso
      have hfbD : f * b ∈ D := by rw [← hbf.eq]; exact hbfD
      have h1 := eq_of_collinear_of_odd hD hb hbf.symm hfbD hx hbx.symm h
      apply hxf
      rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hf]
  obtain ⟨hzD, hxz, -, -⟩ := sq_mem_of_orderOf_eq_four hD hx hf h4
  have hxzD := mul_sq_mem_of_orderOf_eq_four hclass hD hx hf h4
  refine ⟨hzD, hxz, hxzD, ?_⟩
  have hfQ : f ∈ twoCore b := mem_map_pCore_centralizer hclass hD hb hf hbf.symm
    (Or.inl (by rw [← hbf.eq]; exact hbfD))
  have hzQ : (x * f) ^ 2 ∈ twoCore b := by
    have h1 := conj_mem_twoCore hbx.symm hfQ
    rw [show (x * f) ^ 2 = x * f * x⁻¹ * f by rw [pow_two, hD.inv_eq hx]; group]
    exact (twoCore b).mul_mem h1 hfQ
  have hbz : Commute b ((x * f) ^ 2) := (commute_of_mem_twoCore hzQ).symm
  refine ⟨hbz, ?_⟩
  by_contra hbzD
  refine hPQ b hb _ hzD hbz ?_ hbzD hzQ
  rintro hzb
  exact mul_not_mem_of_levi hD hy hb hxy hodd hbx hby (hzb ▸ hxzD)

theorem p1_of_commLambda (h : Hyp G D) (hsing : ∀ x ∈ D, rootSet D x = {x})
    (hQ : CommLambda D) : ExcP1 D :=
  fun _ hd _ hc hdc hodd _ hy hdy hdyD hyc =>
    orderOf_eq_three_of_special_line h hsing hQ hd hc hdc hodd hy hdy hdyD hyc

end CFSG.Timmesfeld.Moufang
