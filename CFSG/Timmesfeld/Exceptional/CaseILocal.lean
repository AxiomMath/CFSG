module

public import CFSG.Timmesfeld.Bridge.RootSetsFrame

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

theorem mul_not_mem_of_levi (hD : IsRootInvolutionSet D) {d c b : G} (hc : c ∈ D) (hb : b ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hbd : Commute b d)
    (hbc : Commute b c) : d * b ∉ D := by
  intro hdb
  have hodd' : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
  have h1 := eq_of_collinear_of_odd hD hb hbd.symm hdb hc hbc.symm hodd'
  apply hdc
  rw [eq_inv_of_mul_eq_one_left h1]
  exact (Commute.refl d).inv_right

theorem orderOf_mul_eq_four_of_collinear_of_commute (hD : IsRootInvolutionSet D) {d c y b : G}
    (hc : c ∈ D) (hy : y ∈ D) (hb : b ∈ D) (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c)))
    (hdy : Commute d y) (hdyD : d * y ∈ D) (hby : Commute b y) (hbyD : b * y ∈ D)
    (hbc : Commute b c) : orderOf (y * c) = 4 := by
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hy hc with hyc | h4 | ⟨hoddyc, -⟩
  · exfalso
    have hodd' : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
    have h1 := eq_of_collinear_of_odd hD hy hdy hdyD hc hyc.symm hodd'
    apply hdc
    rw [eq_inv_of_mul_eq_one_left h1]
    exact (Commute.refl d).inv_right
  · exact h4
  · exfalso
    have hodd' : Odd (orderOf (c * y)) := by rwa [orderOf_mul_comm_eq]
    have hybD : y * b ∈ D := by rw [← hby.eq]; exact hbyD
    have h1 := eq_of_collinear_of_odd hD hb hby.symm hybD hc hbc.symm hodd'
    apply hdc
    rw [eq_inv_of_mul_eq_one_left h1, hD.inv_eq hy]
    exact hdy

theorem exists_collinear_special_of_commute_special (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d c u : G} (hd : d ∈ D) (hc : c ∈ D) (hu : u ∈ D)
    (hdc : ¬ Commute d c) (hodd : Odd (orderOf (d * c))) (hud : Commute u d)
    (huc : orderOf (c * u) = 4) : ∃ y ∈ D, Commute d y ∧ d * y ∈ D ∧ orderOf (y * c) = 4 := by
  have hcd : ¬ Commute c d := fun h => hdc h.symm
  have hoddc : Odd (orderOf (c * d)) := by rwa [orderOf_mul_comm_eq]
  have h4w : orderOf (d * (c * u) ^ 2) = 4 :=
    Bridge.orderOf_mul_sq_eq_four_of_commute hclass hD hc hd hu hcd hoddc hud huc
  obtain ⟨hwD, hcw, -, -⟩ := sq_mem_of_orderOf_eq_four hD hc hu huc
  have h4y := Bridge.orderOf_mul_sq_eq_four_of_commute hclass hD hd hc hwD hdc hodd hcw.symm h4w
  obtain ⟨hyD, hdy, -, -⟩ := sq_mem_of_orderOf_eq_four hD hd hwD h4w
  refine ⟨_, hyD, hdy, mul_sq_mem_of_orderOf_eq_four hclass hD hd hwD h4w, ?_⟩
  rw [orderOf_mul_comm_eq]
  exact h4y

end CFSG.Timmesfeld.Moufang
