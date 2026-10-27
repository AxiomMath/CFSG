module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Unpack

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Minuscule
open scoped commutatorElement

@[expose] noncomputable def twE6X
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (c : k) :
    fixedGroup k θ :=
  xPair θ hθ (twE6Lift_isRoot i) (twE6Lift_ne_rho i) c

@[expose] noncomputable def twE6Y
    {k : Type} [Field k] (θ : k →+* k) (j : Fin 12) : fixedGroup k θ :=
  xFixed θ (twE6Long_isRoot j) (twE6Long_rho j) 1 (map_one θ)

private lemma teComm_coe_commutator {G : Type*} [Group G] (H : Subgroup G) (x y : H) :
    ((⁅x, y⁆ : H) : G) = ⁅(x : G), (y : G)⁆ := by
  change (H.subtype (⁅x, y⁆) : G) = ⁅(x : G), (y : G)⁆
  rw [map_commutatorElement H.subtype]
  simp only [Subgroup.subtype_apply]

private lemma teComm_conj_eq_of_commute {G : Type*} [Group G] {a b : G} (h : Commute a b) :
    a * b * a⁻¹ = b := by
  rw [h.eq, mul_assoc, mul_inv_cancel, mul_one]

private lemma teComm_commutator_mul_mul {G : Type*} [Group G] {x y z w U V : G}
    (hxz : ⁅x, z⁆ = 1) (hyw : ⁅y, w⁆ = 1)
    (hyz : ⁅y, z⁆ = U) (hxw : ⁅x, w⁆ = V)
    (hxU : Commute x U) (hzV : Commute z V) :
    ⁅x * y, z * w⁆ = U * V := by
  simp only [commutatorElement_mul_right_eq_mul_conj, commutatorElement_mul_left_eq_conj_mul]
  rw [hxz, hyw, hyz, hxw]
  simp only [mul_one, one_mul]
  rw [teComm_conj_eq_of_commute hxU]
  rw [show x * x⁻¹ * V = V by group]
  rw [show U * z * V * z⁻¹ = U * (z * V) * z⁻¹ by group]
  rw [hzV.eq]
  group

private lemma twistSign_cast_eq_one {k : Type} [Ring k] [CharP k 2]
    (γ : Fin (Tag.rank .E6) → ℤ) : ((twistSign γ : ℤ) : k) = 1 := by
  rcases twistSign_eq_one_or γ with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
    exact CharTwo.neg_eq 1

private lemma rho_pairRoot_eq (i : Fin 8) :
    rho (twE6PairRoot i) = rho (twE6Lift i) + twE6Lift i.rev := by
  revert i
  decide +kernel

private lemma lift_add_rev_not_isRoot (i : Fin 8) :
    ¬ IsRoot .E6 (twE6Lift i + twE6Lift i.rev) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

private lemma lift_add_rev_ne_zero (i : Fin 8) : twE6Lift i + twE6Lift i.rev ≠ 0 := by
  revert i
  decide +kernel

private lemma rho_lift_add_rho_rev_not_isRoot (i : Fin 8) :
    ¬ IsRoot .E6 (rho (twE6Lift i) + rho (twE6Lift i.rev)) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

private lemma rho_lift_add_rho_rev_ne_zero (i : Fin 8) :
    rho (twE6Lift i) + rho (twE6Lift i.rev) ≠ 0 := by
  revert i
  decide +kernel

private lemma lift_add_rho_pairRoot_not_isRoot (i : Fin 8) :
    ¬ IsRoot .E6 (twE6Lift i + rho (twE6PairRoot i)) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

private lemma lift_add_rho_pairRoot_ne_zero (i : Fin 8) :
    twE6Lift i + rho (twE6PairRoot i) ≠ 0 := by
  revert i
  decide +kernel

private lemma rev_add_pairRoot_not_isRoot (i : Fin 8) :
    ¬ IsRoot .E6 (twE6Lift i.rev + twE6PairRoot i) := by
  rw [← mem_rootFinset]
  revert i
  decide +kernel

private lemma rev_add_pairRoot_ne_zero (i : Fin 8) : twE6Lift i.rev + twE6PairRoot i ≠ 0 := by
  revert i
  decide +kernel

private lemma twE6_xm_comm_pair_core
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (i : Fin 8) (t s : k) :
    ⁅(e6Data_valid.xm k (twE6Lift i) t *
        e6Data_valid.xm k (rho (twE6Lift i)) (θ t)),
      (e6Data_valid.xm k (twE6Lift i.rev) s *
        e6Data_valid.xm k (rho (twE6Lift i.rev)) (θ s))⁆ =
    e6Data_valid.xm k (twE6PairRoot i) (t * θ s) *
      e6Data_valid.xm k (rho (twE6PairRoot i)) (θ (t * θ s)) := by
  have ha : IsRoot .E6 (twE6Lift i) := twE6Lift_isRoot i
  have hb : IsRoot .E6 (twE6Lift i.rev) := twE6Lift_isRoot i.rev
  have hA : IsRoot .E6 (twE6PairRoot i) := twE6PairRoot_isRoot i
  have hAne : rho (twE6PairRoot i) ≠ twE6PairRoot i := twE6PairRoot_ne_rho i
  have hcs : ((e6Data_valid.commSign k (rho (twE6Lift i)) (twE6Lift i.rev) : ℤ) : k) = 1 := by
    rcases e6Data_valid.commSign_eq_one_or k (rho (twE6Lift i)) (twE6Lift i.rev) with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num; exact CharTwo.neg_eq 1
  have hcs2 : ((e6Data_valid.commSign k (twE6Lift i) (rho (twE6Lift i.rev)) : ℤ) : k) = 1 := by
    rcases e6Data_valid.commSign_eq_one_or k (twE6Lift i) (rho (twE6Lift i.rev)) with h | h
    · rw [h]; norm_num
    · rw [h]; norm_num; exact CharTwo.neg_eq 1
  have hrhoA : rho (twE6PairRoot i) = rho (twE6Lift i) + twE6Lift i.rev := rho_pairRoot_eq i
  have hr3 : IsRoot .E6 (rho (twE6Lift i) + twE6Lift i.rev) := by
    rw [← hrhoA]; exact isRoot_rho hA
  have hne3 : rho (twE6Lift i) + twE6Lift i.rev ≠ 0 := by
    rw [← hrhoA]; exact (isRoot_rho hA).ne_zero
  have hxz : ⁅e6Data_valid.xm k (twE6Lift i) t,
      e6Data_valid.xm k (twE6Lift i.rev) s⁆ = 1 :=
    (commute_xm ha hb (lift_add_rev_ne_zero i) (lift_add_rev_not_isRoot i) t s).commutator_eq
  have hyw : ⁅e6Data_valid.xm k (rho (twE6Lift i)) (θ t),
      e6Data_valid.xm k (rho (twE6Lift i.rev)) (θ s)⁆ = 1 :=
    (commute_xm (isRoot_rho ha) (isRoot_rho hb)
      (rho_lift_add_rho_rev_ne_zero i) (rho_lift_add_rho_rev_not_isRoot i)
      (θ t) (θ s)).commutator_eq
  have hyz : ⁅e6Data_valid.xm k (rho (twE6Lift i)) (θ t),
      e6Data_valid.xm k (twE6Lift i.rev) s⁆ =
      e6Data_valid.xm k (rho (twE6PairRoot i)) (θ t * s) := by
    rw [e6Data_valid.commutator_xm_commSign k (isRoot_rho ha) hb hne3 hr3 (θ t) s]
    rw [hcs, one_mul, hrhoA]
  have hxw : ⁅e6Data_valid.xm k (twE6Lift i) t,
      e6Data_valid.xm k (rho (twE6Lift i.rev)) (θ s)⁆ =
      e6Data_valid.xm k (twE6PairRoot i) (t * θ s) := by
    rw [e6Data_valid.commutator_xm_commSign k ha (isRoot_rho hb) hA.ne_zero hA t (θ s)]
    rw [hcs2, one_mul]
    rfl
  have hxU : Commute (e6Data_valid.xm k (twE6Lift i) t)
      (e6Data_valid.xm k (rho (twE6PairRoot i)) (θ t * s)) :=
    commute_xm ha (isRoot_rho hA) (lift_add_rho_pairRoot_ne_zero i)
      (lift_add_rho_pairRoot_not_isRoot i) t (θ t * s)
  have hzV : Commute (e6Data_valid.xm k (twE6Lift i.rev) s)
      (e6Data_valid.xm k (twE6PairRoot i) (t * θ s)) :=
    commute_xm hb hA (rev_add_pairRoot_ne_zero i) (rev_add_pairRoot_not_isRoot i) s (t * θ s)
  rw [teComm_commutator_mul_mul hxz hyw hyz hxw hxU hzV]
  have hW : θ (t * θ s) = θ t * s := by rw [map_mul, hθ]
  rw [hW]
  exact (commute_xm_rho hA hAne (t * θ s) (θ t * s)).eq.symm

theorem twE6_comm_pair
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (i : Fin 8) (t s : k) :
    ⁅twE6X θ hθ i t, twE6X θ hθ i.rev s⁆ =
      xPair θ hθ (twE6PairRoot_isRoot i) (twE6PairRoot_ne_rho i) (t * θ s) := by
  apply Subtype.ext
  rw [teComm_coe_commutator]
  simp only [twE6X, xPair_val, Subgroup.coe_mul, twistSign_cast_eq_one, one_mul]
  exact twE6_xm_comm_pair_core θ hθ i t s

private lemma twE6_memE6_shift_eq (j : Fin 12) (i : Fin 8) :
    memE6 (twE6Lift i + twE6Long j) = (twE6Shift j i).isSome := by
  revert i j
  decide +kernel

private lemma not_isRoot_of_memE6_false
    {v : Fin (Tag.rank .E6) → ℤ} (h : memE6 v = false) : ¬ IsRoot .E6 v := by
  intro hr
  rw [memE6] at h
  rw [(StringData.memDec_iff (Tag.rootCertificate_check .E6)
    (Tag.stringData_check .E6)).2 hr] at h
  exact Bool.false_ne_true h.symm

private lemma rho_lift_add_long (j : Fin 12) (i : Fin 8) :
    rho (twE6Lift i + twE6Long j) = rho (twE6Lift i) + twE6Long j := by
  revert i j
  decide +kernel

private lemma lift_add_long_ne_zero (j : Fin 12) (i : Fin 8) :
    twE6Lift i + twE6Long j ≠ 0 := by
  revert i j
  decide +kernel

private lemma rho_lift_add_long_ne_zero (j : Fin 12) (i : Fin 8) :
    rho (twE6Lift i) + twE6Long j ≠ 0 := by
  revert i j
  decide +kernel

private lemma twE6_xm_shift_none_core
    {k : Type} [Field k] (θ : k →+* k) (j : Fin 12) (i : Fin 8)
    (hj : twE6Shift j i = none) (c : k) :
    ⁅e6Data_valid.xm k (twE6Long j) 1,
      (e6Data_valid.xm k (twE6Lift i) c *
        e6Data_valid.xm k (rho (twE6Lift i)) (θ c))⁆ = 1 := by
  have hmem : memE6 (twE6Lift i + twE6Long j) = false := by
    rw [twE6_memE6_shift_eq, hj]
    rfl
  have hnr : ¬ IsRoot .E6 (twE6Lift i + twE6Long j) := not_isRoot_of_memE6_false hmem
  have hne : twE6Lift i + twE6Long j ≠ 0 := lift_add_long_ne_zero j i
  have hnr' : ¬ IsRoot .E6 (twE6Long j + twE6Lift i) := by rw [add_comm]; exact hnr
  have hne' : twE6Long j + twE6Lift i ≠ 0 := by rw [add_comm]; exact hne
  have hrho_ad : rho (twE6Lift i + twE6Long j) = rho (twE6Lift i) + twE6Long j :=
    rho_lift_add_long j i
  have hnr_rad : ¬ IsRoot .E6 (rho (twE6Lift i) + twE6Long j) := by
    rw [← hrho_ad]
    exact fun hr => hnr (by have h2 := isRoot_rho hr; rwa [rho_rho] at h2)
  have hne_rad : rho (twE6Lift i) + twE6Long j ≠ 0 := rho_lift_add_long_ne_zero j i
  have hnr_rad' : ¬ IsRoot .E6 (twE6Long j + rho (twE6Lift i)) := by
    rw [add_comm]; exact hnr_rad
  have hne_rad' : twE6Long j + rho (twE6Lift i) ≠ 0 := by rw [add_comm]; exact hne_rad
  have h1 : ⁅e6Data_valid.xm k (twE6Long j) 1, e6Data_valid.xm k (twE6Lift i) c⁆ = 1 :=
    (commute_xm (twE6Long_isRoot j) (twE6Lift_isRoot i) hne' hnr' 1 c).commutator_eq
  have h2 : ⁅e6Data_valid.xm k (twE6Long j) 1,
      e6Data_valid.xm k (rho (twE6Lift i)) (θ c)⁆ = 1 :=
    (commute_xm (twE6Long_isRoot j) (isRoot_rho (twE6Lift_isRoot i)) hne_rad' hnr_rad'
      1 (θ c)).commutator_eq
  rw [commutatorElement_mul_right_eq_mul_conj, h1, h2]
  simp

theorem twE6_comm_shift_none
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : Fin 12) (i : Fin 8)
    (hj : twE6Shift j i = none) (c : k) :
    ⁅twE6Y θ j, twE6X θ hθ i c⁆ = 1 := by
  apply Subtype.ext
  rw [teComm_coe_commutator]
  simp only [twE6Y, twE6X, xFixed_val, xPair_val, Subgroup.coe_mul, twistSign_cast_eq_one, one_mul]
  exact twE6_xm_shift_none_core θ j i hj c

private lemma teComm_conj_eq_commutator_mul {G : Type*} [Group G] (a b : G) :
    a * b * a⁻¹ = ⁅a, b⁆ * b := by
  rw [commutatorElement_def]
  group

private lemma commutator_mul_right_correction {G : Type*} [Group G] {z x y A C B : G}
    (hzx : ⁅z, x⁆ = A) (hzy : ⁅z, y⁆ = C) (hxC : ⁅x, C⁆ = B) (hBC : Commute B C) :
    ⁅z, x * y⁆ = A * C * B := by
  rw [commutatorElement_mul_right_eq_mul_conj, hzx, hzy]
  rw [show A * x * C * x⁻¹ = A * (x * C * x⁻¹) by group,
    teComm_conj_eq_commutator_mul x C, hxC]
  rw [hBC.eq]
  group

private lemma commSign_cast_eq_one {k : Type} [Field k] [CharP k 2]
    (α β : Fin (Tag.rank .E6) → ℤ) :
    ((e6Data_valid.commSign k α β : ℤ) : k) = 1 := by
  rcases e6Data_valid.commSign_eq_one_or k α β with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num
    exact CharTwo.neg_eq 1

private lemma proj_A'_last (j : Fin 12) (i : Fin 8) :
    (proj (twE6Lift i + rho (twE6Lift i) + twE6Long j)) twE6Last = 2 := by
  revert i j
  decide +kernel

private lemma A'_add_rho_add_long_not_isRoot (j : Fin 12)
    (i : Fin 8) :
    ¬ IsRoot .E6 (twE6Lift i + rho (twE6Lift i) + twE6Long j +
      (rho (twE6Lift i) + twE6Long j)) := by
  rw [← mem_rootFinset]
  revert i j
  decide +kernel

private lemma A'_add_rho_add_long_ne_zero (j : Fin 12) (i : Fin 8) :
    twE6Lift i + rho (twE6Lift i) + twE6Long j + (rho (twE6Lift i) + twE6Long j) ≠ 0 := by
  revert i j
  decide +kernel

theorem twE6_comm_shift_some
    {k : Type} [Field k] [CharP k 2] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (j : Fin 12)
    (i i' : Fin 8) (hj : twE6Shift j i = some i') (c : k) :
    ∃ z ∈ twE6Cen θ, ⁅twE6Y θ j, twE6X θ hθ i c⁆ = twE6X θ hθ i' c * z := by
  have hcheck := twE6DataCheck_eq
  simp only [twE6DataCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
    true_implies, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_true] at hcheck
  have hE := hcheck.1.1.2 j i
  have hA'data : memE6 (twE6Lift i + rho (twE6Lift i) + twE6Long j) = true ∧
      rho (twE6Lift i + rho (twE6Lift i) + twE6Long j) =
        twE6Lift i + rho (twE6Lift i) + twE6Long j :=
    hE.2.resolve_left (by simp [hj])
  have hA' : IsRoot .E6 (twE6Lift i + rho (twE6Lift i) + twE6Long j) :=
    (StringData.memDec_iff (Tag.rootCertificate_check .E6)
      (Tag.stringData_check .E6)).1 hA'data.1
  have hfix : rho (twE6Lift i + rho (twE6Lift i) + twE6Long j) =
      twE6Lift i + rho (twE6Lift i) + twE6Long j := hA'data.2
  have hc : θ (c * θ c) = c * θ c := by rw [map_mul, hθ, mul_comm]
  have hEq : twE6Lift i + twE6Long j = twE6Lift i' := by
    have hfind : decide (twE6Lift i + twE6Long j = twE6Lift i') = true := by
      unfold twE6Shift at hj
      exact List.find?_some (p := fun i' => decide (twE6Lift i + twE6Long j = twE6Lift i'))
        (a := i') (l := List.finRange 8) hj
    exact of_decide_eq_true hfind
  have hroot_ad : IsRoot .E6 (twE6Lift i + twE6Long j) := hEq.symm ▸ twE6Lift_isRoot i'
  have hrho_ad : rho (twE6Lift i + twE6Long j) = rho (twE6Lift i) + twE6Long j :=
    rho_lift_add_long j i
  have hroot_rad : IsRoot .E6 (rho (twE6Lift i) + twE6Long j) := by
    rw [← hrho_ad]; exact isRoot_rho hroot_ad
  have hr_corr : IsRoot .E6 (twE6Lift i + (rho (twE6Lift i) + twE6Long j)) := by
    rw [← add_assoc]; exact hA'
  refine ⟨xFixed θ hA' hfix (c * θ c) hc, ?_, ?_⟩
  · rw [twE6Cen, ggSub]
    refine Subgroup.mem_iSup_of_mem (proj (twE6Lift i + rho (twE6Lift i) + twE6Long j)) ?_
    refine Subgroup.mem_iSup_of_mem ?_ (xFixed_mem θ hA' hfix (c * θ c) hc)
    exact ⟨by rw [twistedDatum_roots]; exact isRoot_proj hA',
      by rw [proj_A'_last j i]⟩
  · apply Subtype.ext
    rw [teComm_coe_commutator]
    simp only [twE6Y, twE6X, xFixed_val, xPair_val, Subgroup.coe_mul,
      twistSign_cast_eq_one, one_mul]
    have hZ0x : ⁅e6Data_valid.xm k (twE6Long j) 1, e6Data_valid.xm k (twE6Lift i) c⁆ =
        e6Data_valid.xm k (twE6Lift i') c := by
      rw [e6Data_valid.commutator_xm_commSign k (twE6Long_isRoot j) (twE6Lift_isRoot i)
        (by rw [add_comm]; exact hroot_ad.ne_zero) (by rw [add_comm]; exact hroot_ad) 1 c]
      simp only [commSign_cast_eq_one, one_mul]
      rw [add_comm, hEq]
    have hZ0y : ⁅e6Data_valid.xm k (twE6Long j) 1,
        e6Data_valid.xm k (rho (twE6Lift i)) (θ c)⁆ =
        e6Data_valid.xm k (rho (twE6Lift i) + twE6Long j) (θ c) := by
      rw [e6Data_valid.commutator_xm_commSign k (twE6Long_isRoot j)
        (isRoot_rho (twE6Lift_isRoot i))
        (by rw [add_comm]; exact hroot_rad.ne_zero) (by rw [add_comm]; exact hroot_rad) 1 (θ c)]
      simp only [commSign_cast_eq_one, one_mul]
      rw [add_comm]
    have hxC : ⁅e6Data_valid.xm k (twE6Lift i) c,
        e6Data_valid.xm k (rho (twE6Lift i) + twE6Long j) (θ c)⁆ =
        e6Data_valid.xm k (twE6Lift i + rho (twE6Lift i) + twE6Long j) (c * θ c) := by
      rw [e6Data_valid.commutator_xm_commSign k (twE6Lift_isRoot i) hroot_rad hr_corr.ne_zero
        hr_corr c (θ c)]
      simp only [commSign_cast_eq_one, one_mul]
      rw [← add_assoc]
    have hBC : Commute
        (e6Data_valid.xm k (twE6Lift i + rho (twE6Lift i) + twE6Long j) (c * θ c))
        (e6Data_valid.xm k (rho (twE6Lift i) + twE6Long j) (θ c)) :=
      commute_xm hA' hroot_rad (A'_add_rho_add_long_ne_zero j i)
        (A'_add_rho_add_long_not_isRoot j i) (c * θ c) (θ c)
    rw [commutator_mul_right_correction hZ0x hZ0y hxC hBC]
    rw [← hEq, hrho_ad]

end CFSG.StandardType.LieKnownR2.Short
