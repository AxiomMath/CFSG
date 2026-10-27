module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF.D8Module
public import CFSG.RankThree.PartOne.KF.SymTorus

public section

namespace CFSG.RankThree.PartOne.KFU

variable {p : ℕ} {K : Type} [Field K]

abbrev W10 : Type := Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)

@[expose] def invAut : MulAut (torusVec p 4 K) := MulEquiv.inv _

theorem invAut_apply (d : torusVec p 4 K) : (invAut : MulAut (torusVec p 4 K)) d = d⁻¹ := rfl

theorem invAut_mul_self : (invAut : MulAut (torusVec p 4 K)) * invAut = 1 := by
  ext d
  simp [invAut_apply]

@[expose] def invHom : Multiplicative (ZMod 2) →* MulAut (torusVec p 4 K) where
  toFun e := if e = 1 then 1 else invAut
  map_one' := by simp
  map_mul' a b := by
    have hc : ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 := by decide
    have h11 : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide
    have h1n : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
    rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl
    · simp
    · simp [h1n]
    · simp [h1n]
    · simp [h11, h1n, invAut_mul_self]

theorem invHom_apply_one : (invHom (p := p) (K := K)) 1 = 1 := map_one _

theorem invHom_apply_ofAdd :
    (invHom (p := p) (K := K)) (Multiplicative.ofAdd 1) = invAut := by
  have h1n : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide
  simp [invHom, h1n]

theorem commute_invAut (φ : MulAut (torusVec p 4 K)) : Commute φ (invAut) := by
  refine MulEquiv.ext fun d => ?_
  simp [invAut_apply]

theorem commute_invHom (e : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 4)) :
    Commute (invHom (p := p) (K := K) e) (symAut p K σ) := by
  by_cases h : e = 1
  · subst h
    simp [invHom_apply_one]
  · have hc : e = Multiplicative.ofAdd 1 := by
      revert e; decide
    subst hc
    rw [invHom_apply_ofAdd]
    exact (commute_invAut _).symm

@[expose] def act10 : W10 →* MulAut (torusVec p 4 K) :=
  MonoidHom.noncommCoprod invHom (symAut p K) commute_invHom

theorem act10_apply (e : Multiplicative (ZMod 2)) (σ : Equiv.Perm (Fin 4)) :
    (act10 (p := p) (K := K)) (e, σ) = invHom e * symAut p K σ := by
  simp [act10, MonoidHom.noncommCoprod_apply]

theorem act10_one (σ : Equiv.Perm (Fin 4)) (d : torusVec p 4 K) :
    (act10 (p := p) (K := K)) (1, σ) d = symAct p K σ d := by
  rw [act10_apply, invHom_apply_one, one_mul]
  rfl

theorem act10_inv (σ : Equiv.Perm (Fin 4)) (d : torusVec p 4 K) :
    (act10 (p := p) (K := K)) (Multiplicative.ofAdd 1, σ) d = (symAct p K σ d)⁻¹ := by
  rw [act10_apply, invHom_apply_ofAdd]
  rfl

theorem cases_zmod_two (e : Multiplicative (ZMod 2)) : e = 1 ∨ e = Multiplicative.ofAdd 1 := by
  revert e
  decide

theorem ofAdd_one_mul_self : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
  decide

theorem act10_injective (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Function.Injective (act10 (p := p) (K := K)) := by
  obtain ⟨ζ, hζ'⟩ := hζ
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    have := hζ'.dvd_of_pow_eq_one 2 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h] at hζ'
    have := hζ'.eq_orderOf
    rw [orderOf_one] at this
    exact hp.ne_one this
  rw [injective_iff_map_eq_one]
  rintro ⟨e, σ⟩ h
  rcases cases_zmod_two e with rfl | rfl
  · have h1 : symAut p K σ = 1 := by
      have := h
      rw [act10_apply, invHom_apply_one, one_mul] at this
      exact this
    have := symAut_injective (n := 4) (K := K) hp hp2 ⟨ζ, hζ'⟩ (h1.trans (map_one _).symm)
    rw [this]
    rfl
  · exfalso
    have hall : ∀ d : torusVec p 4 K, (symAct p K σ d)⁻¹ = d := fun d => by
      have := congrArg (fun m : MulAut (torusVec p 4 K) => m d) h
      simpa [act10_inv] using this
    set u : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζ'.pow_eq_one⟩ with hu
    have key : ∀ j : Fin 4, (hj : (0 : Fin 4) ≠ j) → σ.symm 0 = j := by
      intro j hj
      have h1 := congrArg (fun d : torusVec p 4 K => (d : Fin 4 → Kˣ) 0) (hall (torusEltV p hj u))
      simp only [coe_torusEltV, Subgroup.coe_inv, Pi.inv_apply] at h1
      rw [torusElt_apply_left hj] at h1
      have h2 : ((symAct p K σ (torusEltV p hj u) : torusVec p 4 K) : Fin 4 → Kˣ) 0 =
          (torusElt 0 j ζ) (σ.symm 0) := rfl
      by_contra hne
      have hne0 : σ.symm 0 ≠ j := hne
      by_cases h0 : σ.symm 0 = 0
      · rw [h2, h0, torusElt_apply_left hj] at h1
        have h1' : ζ⁻¹ = ζ := h1
        have : ζ * ζ = 1 := by
          calc ζ * ζ = ζ⁻¹ * ζ := by rw [h1']
            _ = 1 := inv_mul_cancel ζ
        exact hζ2 (by rw [sq]; exact this)
      · rw [h2, torusElt_apply_other h0 hne0] at h1
        simp at h1
        exact hζ1 h1.symm
    have h1 := key 1 (by decide)
    have h2 := key 2 (by decide)
    rw [h1] at h2
    exact absurd h2 (by decide)

@[expose] def dt1 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def dt2 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

@[expose] def dt3 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

theorem dt1_zero : dt1 0 = 1 := by decide

theorem dt2_zero : dt2 0 = 2 := by decide

theorem dt3_zero : dt3 0 = 3 := by decide

@[expose] def IsDt (σ : Equiv.Perm (Fin 4)) : Prop := σ = dt1 ∨ σ = dt2 ∨ σ = dt3

theorem isDt_involution {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) : σ * σ = 1 := by
  rcases h with rfl | rfl | rfl <;> decide

theorem isDt_ne_one {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) : σ ≠ 1 := by
  rcases h with rfl | rfl | rfl <;> decide

@[expose] def thetaElt (σ : Equiv.Perm (Fin 4)) (u : Kˣ) : Fin 4 → Kˣ :=
  fun i => if i = 0 ∨ i = σ 0 then u else u⁻¹

theorem thetaElt_mem {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) {u : Kˣ} (hu : u ^ p = 1) :
    thetaElt σ u ∈ torusVec p 4 K := by
  refine ⟨fun i => ?_, ?_⟩
  · unfold thetaElt
    split_ifs
    · exact hu
    · rw [inv_pow, hu, inv_one]
  · rcases h with rfl | rfl | rfl
    · simp [Fin.prod_univ_four, thetaElt, dt1_zero]
    · simp [Fin.prod_univ_four, thetaElt, dt2_zero]
    · simp [Fin.prod_univ_four, thetaElt, dt3_zero]

theorem isDt_symm {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) (i : Fin 4) : σ.symm i = σ i := by
  rcases h with rfl | rfl | rfl <;> revert i <;> decide

theorem dt1_vals : dt1 0 = 1 ∧ dt1 1 = 0 ∧ dt1 2 = 3 ∧ dt1 3 = 2 := by decide

theorem dt2_vals : dt2 0 = 2 ∧ dt2 1 = 3 ∧ dt2 2 = 0 ∧ dt2 3 = 1 := by decide

theorem dt3_vals : dt3 0 = 3 ∧ dt3 1 = 2 ∧ dt3 2 = 1 ∧ dt3 3 = 0 := by decide

theorem symAct_mul_self_eq {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) (d : torusVec p 4 K) :
    (symAct p K σ d : Fin 4 → Kˣ) * (d : Fin 4 → Kˣ) =
      thetaElt σ ((d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) (σ 0)) := by
  have hprod : (d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) 1 * (d : Fin 4 → Kˣ) 2 *
      (d : Fin 4 → Kˣ) 3 = 1 := by
    have := d.2.2
    simpa [Fin.prod_univ_four] using this
  funext i
  rw [Pi.mul_apply, coe_symAct, isDt_symm h]
  rcases h with rfl | rfl | rfl
  · obtain ⟨h0, h1, h2, h3⟩ := dt1_vals
    fin_cases i
    · simp [thetaElt, h0, mul_comm]
    · simp [thetaElt, h0, h1]
    · simp [thetaElt, h0, h2]
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← hprod]
      ac_rfl
    · simp [thetaElt, h0, h3]
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← hprod]
      ac_rfl
  · obtain ⟨h0, h1, h2, h3⟩ := dt2_vals
    fin_cases i
    · simp [thetaElt, h0, mul_comm]
    · simp [thetaElt, h0, h1]
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← hprod]
      simp only [mul_comm, mul_left_comm, mul_assoc]; rw [mul_left_comm]
    · simp [thetaElt, h0, h2]
    · simp [thetaElt, h0, h3]
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← hprod]
      ac_rfl
  · obtain ⟨h0, h1, h2, h3⟩ := dt3_vals
    fin_cases i
    · simp [thetaElt, h0, mul_comm]
    · simp [thetaElt, h0, h1]
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← hprod]
      simp only [mul_comm, mul_left_comm, mul_assoc]; rw [mul_left_comm]
    · simp [thetaElt, h0, h2]
      rw [← mul_inv_rev, eq_inv_iff_mul_eq_one, ← hprod]
      ac_rfl
    · simp [thetaElt, h0, h3]

@[expose] def thetaV (p : ℕ) (K : Type) [Field K] {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) :
    rootsOfUnity p K →* torusVec p 4 K where
  toFun u := ⟨thetaElt σ (u : Kˣ), thetaElt_mem h ((mem_rootsOfUnity p _).mp u.2)⟩
  map_one' := by
    apply Subtype.ext
    funext i
    simp [thetaElt]
  map_mul' u v := by
    apply Subtype.ext
    funext i
    simp only [thetaElt, Subgroup.coe_mul, Pi.mul_apply, Subgroup.coe_mul]
    split_ifs <;> simp [mul_comm]

theorem coe_thetaV {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) (u : rootsOfUnity p K) :
    ((thetaV p K h u : torusVec p 4 K) : Fin 4 → Kˣ) = thetaElt σ (u : Kˣ) := rfl

theorem thetaV_injective {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) :
    Function.Injective (thetaV p K h) := by
  intro u v huv
  have := congrFun (congrArg Subtype.val huv) 0
  simp only [coe_thetaV, thetaElt, true_or, ite_true] at this
  exact Subtype.ext this

theorem symAct_thetaV {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) (u : rootsOfUnity p K) :
    symAct p K σ (thetaV p K h u) = thetaV p K h u := by
  apply Subtype.ext
  funext i
  rw [coe_symAct, coe_thetaV, isDt_symm h]
  show thetaElt σ (u : Kˣ) (σ i) = thetaElt σ (u : Kˣ) i
  have hcond : ∀ i, (σ i = 0 ∨ σ i = σ 0) ↔ (i = 0 ∨ i = σ 0) := by
    rcases h with rfl | rfl | rfl <;> decide
  simp only [thetaElt, hcond i]

theorem movedV_inv_dt (hp : p.Prime) (hp2 : p ≠ 2) {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) :
    movedV (act10 (p := p) (K := K) (Multiplicative.ofAdd 1, σ)) = (thetaV p K h).range := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨d, rfl⟩
    show act10 (Multiplicative.ofAdd 1, σ) d * d⁻¹ ∈ (thetaV p K h).range
    have hu0 : ((d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) (σ 0)) ^ p = 1 := by
      rw [mul_pow, d.2.1 0, d.2.1 (σ 0), one_mul]
    have hsq : symAct p K σ d * d = thetaV p K h
        ⟨(d : Fin 4 → Kˣ) 0 * (d : Fin 4 → Kˣ) (σ 0), (mem_rootsOfUnity p _).mpr hu0⟩ :=
      Subtype.ext (symAct_mul_self_eq h d)
    rw [act10_inv, ← mul_inv_rev, mul_comm d, hsq, ← map_inv]
    exact ⟨_, rfl⟩
  · rintro _ ⟨u, rfl⟩
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have hu : u ^ p = 1 := Subtype.ext ((mem_rootsOfUnity p _).mp u.2)
    set y : torusVec p 4 K := thetaV p K h (u⁻¹ ^ (k + 1)) with hy
    apply Subgroup.subset_closure
    refine ⟨y, ?_⟩
    show act10 (Multiplicative.ofAdd 1, σ) y * y⁻¹ = thetaV p K h u
    have hyfix : symAct p K σ y = y := symAct_thetaV h _
    have hyy : y * y = thetaV p K h u⁻¹ := by
      rw [hy, ← map_mul, ← pow_add, show k + 1 + (k + 1) = p + 1 by omega, pow_succ, inv_pow, hu,
        inv_one, one_mul]
    rw [act10_inv, hyfix, ← mul_inv_rev, hyy, ← map_inv, inv_inv]

theorem card_movedV_inv_dt [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) :
    Nat.card (movedV (act10 (p := p) (K := K) (Multiplicative.ofAdd 1, σ))) = p := by
  obtain ⟨ζ, hζ⟩ := hζ
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [movedV_inv_dt hp hp2 h,
    Nat.card_congr (MonoidHom.ofInjective (thetaV_injective h)).toEquiv.symm]
  exact IsPrimitiveRoot.card_rootsOfUnity (IsPrimitiveRoot.coe_units_iff.mpr hζ)

theorem orderOf_act10_inv_dt (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) :
    orderOf (act10 (p := p) (K := K) (Multiplicative.ofAdd 1, σ)) = 2 := by
  rw [orderOf_injective _ (act10_injective hp hp2 hζ) _]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, Prod.mk_mul_mk, isDt_involution h, ofAdd_one_mul_self]
    rfl
  · intro h1
    have := congrArg Prod.snd h1
    exact isDt_ne_one h this

theorem orderOf_act10_one_swap (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    {a b : Fin 4} (hab : a ≠ b) :
    orderOf (act10 (p := p) (K := K) (1, Equiv.swap a b)) = 2 := by
  rw [orderOf_injective _ (act10_injective hp hp2 hζ) _]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two, Prod.mk_mul_mk, Equiv.swap_mul_self]
    rfl
  · intro h1
    have := congrArg (fun w : W10 => w.2 a) h1
    simp [Equiv.swap_apply_left] at this
    exact hab this.symm

theorem movedV_one_swap {a b : Fin 4} :
    movedV (act10 (p := p) (K := K) (1, Equiv.swap a b)) = movedSub p K (Equiv.swap a b) := by
  unfold movedV movedSub
  have : (fun d : torusVec p 4 K => act10 (p := p) (K := K) (1, Equiv.swap a b) d * d⁻¹) =
      fun d => symAct p K (Equiv.swap a b) d * d⁻¹ := funext fun d => by rw [act10_one]
  rw [this]

end CFSG.RankThree.PartOne.KFU
