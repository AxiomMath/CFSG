module

public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.Timmesfeld.Bridge.OddTranspMain

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup

section ZStar

variable {G : Type*} [Group G] {D : Set G}

theorem eq_one_of_odd_orderOf_of_mem {Q : Subgroup G} (hQ : IsPGroup 2 Q) {y : G} (hy : y ∈ Q)
    (hodd : Odd (orderOf y)) : y = 1 := by
  have h := hQ.orderOf_coprime (Nat.coprime_two_left.mpr hodd) ⟨y, hy⟩
  rw [Subgroup.orderOf_mk, Nat.coprime_self, orderOf_eq_one_iff] at h
  exact h

variable (hD : Bridge.Asc72.IsOddTransp D)
  (hsq : ∀ d ∈ D, ∀ e ∈ D, Commute d e → d ≠ e → d * e ∈ D)
  (hopp : ∀ d ∈ D, ∃ b ∈ D, ¬ Commute d b ∧ Odd (orderOf (d * b)))

include hD hopp in
theorem not_mem_pCore_of_opposite {f : G} (hf : f ∈ D) : f ∉ CFSG.pCore 2 G := by
  intro hfQ
  obtain ⟨b, hb, hfb, hodd⟩ := hopp f hf
  have hb2 : b * b = 1 := by rw [← pow_two, ← hD.1 b hb, pow_orderOf_eq_one]
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hmem : (f * b) ^ 2 ∈ CFSG.pCore 2 G := by
    have h1 := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem f hfQ b
    rw [hbi] at h1
    rw [pow_two, show f * b * (f * b) = f * (b * f * b) by group]
    exact mul_mem hfQ h1
  have hcop : (orderOf (f * b)).Coprime 2 := Nat.coprime_two_right.mpr hodd
  have h1 := eq_one_of_odd_orderOf_of_mem CFSG.pCore_isPGroup hmem
    (by rw [hcop.orderOf_pow]; exact hodd)
  have h2 : orderOf (f * b) = 1 := by
    rw [← hcop.orderOf_pow, h1, orderOf_one]
  rw [orderOf_eq_one_iff] at h2
  apply hfb
  rw [eq_inv_of_mul_eq_one_left h2, hbi]

include hD hsq hopp in
theorem eq_of_mul_mem_pCore {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (hde : d * e ∈ CFSG.pCore 2 G) : d = e := by
  have hd2 : d * d = 1 := by rw [← pow_two, ← hD.1 d hd, pow_orderOf_eq_one]
  have he2 : e * e = 1 := by rw [← pow_two, ← hD.1 e he, pow_orderOf_eq_one]
  by_contra hne
  by_cases hc : Commute d e
  · exact not_mem_pCore_of_opposite hD hopp (hsq d hd e he hc hne) hde
  · rcases hD.2 d hd e he with h2 | hodd
    · exact hc ((commute_iff_mul_sq_eq_one hd2 he2).mpr (orderOf_dvd_iff_pow_eq_one.mp h2))
    · have h1 := eq_one_of_odd_orderOf_of_mem CFSG.pCore_isPGroup hde hodd
      apply hne
      rw [eq_inv_of_mul_eq_one_left h1, inv_eq_of_mul_eq_one_right he2]

end ZStar

theorem zStar_eq_center {G : Type*} [Group G] [Finite G] {D : Set G}
    (hD : Bridge.Asc72.IsOddTransp D) (hN : Connectivity.IsNormalSet D)
    (hgen : Subgroup.closure D = ⊤)
    (hsq : ∀ d ∈ D, ∀ e ∈ D, Commute d e → d ≠ e → d * e ∈ D)
    (hopp : ∀ d ∈ D, ∃ b ∈ D, ¬ Commute d b ∧ Odd (orderOf (d * b))) :
    Bridge.zStar G = Subgroup.center G := by
  apply le_antisymm
  · intro x hx
    have hx' : QuotientGroup.mk' (CFSG.pCore 2 G) x ∈ center (G ⧸ CFSG.pCore 2 G) := hx
    have hcomm : ∀ d ∈ D, Commute x d := by
      intro d hd
      have hd2 : d * d = 1 := by rw [← pow_two, ← hD.1 d hd, pow_orderOf_eq_one]
      have hmem : d * (x * d * x⁻¹) ∈ CFSG.pCore 2 G := by
        rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 G)]
        have hc := mem_center_iff.mp hx' (QuotientGroup.mk' (CFSG.pCore 2 G) d)
        simp only [QuotientGroup.mk'_apply] at hc
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← hc,
          QuotientGroup.mk_inv, mul_inv_cancel_right, ← QuotientGroup.mk_mul, hd2,
          QuotientGroup.mk_one]
      have heq := eq_of_mul_mem_pCore hD hsq hopp hd (hN x d hd) hmem
      calc x * d = x * d * x⁻¹ * x := by group
        _ = d * x := by rw [← heq]
    rw [← centralizer_univ, ← coe_top, ← hgen, centralizer_closure]
    exact fun d hd => (hcomm d hd).symm.eq
  · intro x hx
    show QuotientGroup.mk' (CFSG.pCore 2 G) x ∈ center (G ⧸ CFSG.pCore 2 G)
    rw [mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      simp only [QuotientGroup.mk'_apply]
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hx y]

theorem Setup.degenerate {X : Type} [Group X] [Finite X] {t : X} (h : Setup t)
    (hpair : ∃ τ ∈ conjCent t, τ ≠ t)
    (hdeg : ∀ d ∈ cls t, ∀ e ∈ cls t, orderOf (d * e) ≠ 4) :
    (∀ x ∈ normalClosure ({t} : Set X), ∀ y ∈ normalClosure ({t} : Set X),
        x * y = y * x ∧ x * x = 1) ∨
      CFSG.BenderSuzuki.IsBenderGroup
        (↥(normalClosure ({t} : Set X)) ⧸ Subgroup.center ↥(normalClosure ({t} : Set X))) := by
  have hR := h.isRootInvolutionSet_clsIn
  have hdeg' : ∀ d ∈ clsIn t, ∀ e ∈ clsIn t, orderOf (d * e) ≠ 4 := fun d hd e he h4 =>
    hdeg _ hd _ he (by rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]; exact h4)
  have hOT : Bridge.Asc72.IsOddTransp (clsIn t) := by
    refine ⟨hR.1, fun d hd e he => ?_⟩
    rcases hR.orderOf_mul hd he with h2 | h4 | hodd
    · exact Or.inl (by rw [h2])
    · exact absurd h4 (hdeg' d hd e he)
    · exact Or.inr hodd
  have hNs : Connectivity.IsNormalSet (clsIn t) := fun g x hx => conj_mem_clsIn g x hx
  by_cases hdisc : Connectivity.Disconnected (clsIn t)
  · right
    obtain ⟨τ, ⟨hτc, hτ⟩, hτt⟩ := hpair
    have hDD : ∃ u ∈ clsIn t, ∃ v ∈ clsIn t, u ≠ v ∧ Commute u v ∧ u * v ∈ clsIn t := by
      let u : ↥(normalClosure ({t} : Set X)) := ⟨t, cls_subset t (mem_cls_self t)⟩
      let v : ↥(normalClosure ({t} : Set X)) := ⟨τ, cls_subset t hτ⟩
      have huv : u ≠ v := fun e => hτt (congrArg Subtype.val e).symm
      have hc : Commute u v := Subtype.ext hτc.symm
      exact ⟨u, mem_cls_self t, v, hτ, huv, hc, h.mul_mem_clsIn (mem_cls_self t) hτ hc huv⟩
    have hB := Bridge.OddTransp.oddTranspZStar _ (clsIn t) hOT hNs (closure_clsIn t) hDD hdisc
    have hopp : ∀ d ∈ clsIn t, ∃ b ∈ clsIn t, ¬ Commute d b ∧ Odd (orderOf (d * b)) := by
      intro d hd
      obtain ⟨z, hz, hdz⟩ := Connectivity.exists_not_reach hdisc (x := d)
      exact ⟨z, hz, Connectivity.opposite_of_not_reach hR hd hz hdz⟩
    have hZ := zStar_eq_center hOT hNs (closure_clsIn t)
      (fun d hd e he hde hne => h.mul_mem_clsIn hd he hde hne) hopp
    exact Bridge.Asc72.isBenderGroup_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZ.symm) hB
  · left
    apply h.forall_mul_comm_of_commute
    have hcc : ∀ x ∈ clsIn t, ∀ y ∈ clsIn t, ∀ z ∈ clsIn t, Commute x y → Commute x z →
        Commute y z := by
      intro x hx y hy z hz hxy hxz
      obtain ⟨k, hk⟩ := h.exists_orderOf_eq_two_pow_clsIn hx hy hz hxy hxz
      have hdvd : orderOf (y * z) ∣ 2 := by
        rcases hR.orderOf_mul hy hz with h2 | h4 | hodd
        · rw [h2]
        · exact absurd h4 (hdeg' y hy z hz)
        · rw [hk] at hodd ⊢
          have hk0 : k = 0 := by
            by_contra hk0
            exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hk0).mpr even_two)
          rw [hk0, pow_zero]
          exact one_dvd 2
      exact (commute_iff_mul_sq_eq_one (hR.mul_self_eq_one hy) (hR.mul_self_eq_one hz)).mpr
        (orderOf_dvd_iff_pow_eq_one.mp hdvd)
    have hreach : ∀ x ∈ clsIn t, ∀ y, Connectivity.Reach (clsIn t) x y → Commute x y := by
      intro x hx y hxy
      induction hxy with
      | refl => exact Commute.refl x
      | tail _ hbc ih => exact hcc _ hbc.1 x hx _ hbc.2.1 ih.symm hbc.2.2
    intro d hd e he
    have hde : Connectivity.Reach (clsIn t) ⟨d, cls_subset t hd⟩ ⟨e, cls_subset t he⟩ := by
      by_contra hde
      exact hdisc ⟨_, hd, _, he, hde⟩
    exact commute_coe_iff.mpr (hreach _ hd _ hde)

end CFSG.Timmesfeld.CorB
