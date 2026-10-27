module

public import CFSG.Timmesfeld.Bridge.CommLambda

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def GammaMixed (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → ∀ b ∈ rootSet D e, ∀ f ∈ D,
    Commute ((d * e) ^ 2) f → Commute d f → orderOf (f * e) = 4 → Commute ((d * b) ^ 2) f

@[expose] def GammaDouble (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → ∀ b ∈ rootSet D e, ∀ f ∈ D,
    Commute ((d * e) ^ 2) f → orderOf (f * d) = 4 → orderOf (f * e) = 4 →
      Commute ((d * b) ^ 2) f

theorem specialClosure_of_residual [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hM : GammaMixed D) (hS : GammaDouble D) :
    SpecialClosure D := by
  intro d hd e he h4 b hb
  have h4b : orderOf (d * b) = 4 :=
    orderOf_mul_eq_four_of_mem_rootSet hD hd he (mem_rootSet_self hd) hb h4
  have hzD : (d * e) ^ 2 ∈ D := hD.sq_mem hd he h4
  refine mem_rootSet_of_forall_commute hclass hzD (hD.sq_mem hd hb.1 h4b) fun f hf hzf => ?_
  obtain ⟨-, hdz, hez, hede⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  have h4' : orderOf (e * d) = 4 := by rwa [orderOf_mul_comm_eq]
  obtain ⟨-, -, -, hded⟩ := sq_mem_of_orderOf_eq_four hD he hd h4'
  rw [← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hd) (hD.mul_self_eq_one he) h4] at hded
  have hdzD : d * (d * e) ^ 2 ∈ D := by
    rw [← hede]
    have := conj_mem_of_isClass hclass e hd
    rwa [hD.inv_eq he] at this
  have hezD : e * (d * e) ^ 2 ∈ D := by
    rw [← hded]
    have := conj_mem_of_isClass hclass d he
    rwa [hD.inv_eq hd] at this
  have hfz : Commute f ((d * e) ^ 2) := hzf.symm
  rcases commute_or_special_of_collinear hD hzD he hez hezD hf hfz with hfe | hfe
  · exact (commute_mul_sq_iff_of_commute_right hclass hD hd he h4 hb hf hfe.symm).1 hzf
  · rcases commute_or_special_of_collinear hD hzD hd hdz hdzD hf hfz with hfd | hfd
    · exact hM d hd e he h4 b hb f hf hzf hfd.symm hfe
    · exact hS d hd e he h4 b hb f hf hzf hfd hfe

end CFSG.Timmesfeld.Bridge
