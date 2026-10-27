module

public import CFSG.Quasithin.Background.B3One

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

@[expose] def sgn2 (a : ZMod 2) : ℤˣ := if a = 0 then 1 else -1

theorem sgn2_add (a b : ZMod 2) : sgn2 (a + b) = sgn2 a * sgn2 b := by revert a b; decide

theorem sgn2_eq_one {a : ZMod 2} : sgn2 a = 1 ↔ a = 0 := by revert a; decide

theorem sgn2_zero : sgn2 0 = 1 := by decide

@[expose] def dotU (u v : U n) : ZMod 2 := ∑ i, u.val i * v.val i

theorem dotU_mul_right (u v w : U n) : dotU u (v * w) = dotU u v + dotU u w := by
  simp only [dotU, U.val_mul, mul_add, Finset.sum_add_distrib]

theorem dotU_mul_left (u v w : U n) : dotU (u * v) w = dotU u w + dotU v w := by
  simp only [dotU, U.val_mul, add_mul, Finset.sum_add_distrib]

theorem dotU_one_right (u : U n) : dotU u 1 = 0 := by simp [dotU]

theorem dotU_one_left (u : U n) : dotU 1 u = 0 := by simp [dotU]

theorem dotU_perm (σ : Gp n) (u v : U n) : dotU (permAct n σ u) (permAct n σ v) = dotU u v := by
  simp only [dotU, permAct_val]
  exact Equiv.sum_comp σ.symm (fun i => u.val i * v.val i)

theorem dotU_eVec_right (u : U n) : dotU u (eVec n) = ∑ i, u.val i := by simp [dotU, eVec]

theorem dotU_eVec_left (u : U n) : dotU (eVec n) u = ∑ i, u.val i := by simp [dotU, eVec]

theorem mem_U0_iff_sum (u : U n) : u ∈ U0 n ↔ ∑ i, u.val i = 0 := by
  show wt n u = 1 ↔ _
  have h2 : wt n u = Multiplicative.ofAdd (∑ i, u.val i) := rfl
  rw [h2]
  exact ofAdd_eq_one

theorem dotU_pair (u : U n) {i j : Fin n} (hij : i ≠ j) :
    dotU u (pair i j) = u.val i + u.val j := by
  unfold dotU pair
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : Finset.univ.filter (fun x : Fin n => x = i ∨ x = j) = {i, j} := by
    ext x
    simp
  rw [this, Finset.sum_pair hij]

@[expose] def dotHom (u : U n) : U n →* ℤˣ where
  toFun v := sgn2 (dotU u v)
  map_one' := by rw [dotU_one_right, sgn2_zero]
  map_mul' v w := by rw [dotU_mul_right, sgn2_add]

@[expose] noncomputable def theta1 (n : ℕ) (u : ↥(Mod.W n Mod.ut0)) : Mod.V n Mod.ut0 →* ℤˣ :=
  QuotientGroup.lift ((Mod.N n Mod.ut0).subgroupOf (Mod.W n Mod.ut0))
    ((dotHom (u : U n)).comp (Mod.W n Mod.ut0).subtype) (by
      intro z hz
      have hz' : (z : U n) ∈ Esub n := hz
      have hu : ∑ i, (u : U n).val i = 0 := (mem_U0_iff_sum _).1 u.2
      rcases (mem_Esub_iff _).1 hz' with h | h
      · simp [h]
      · simp [MonoidHom.mem_ker, dotHom, h, dotU_eVec_right, hu, sgn2_zero])

theorem theta1_mk (u w : ↥(Mod.W n Mod.ut0)) :
    theta1 n u (QuotientGroup.mk w) = sgn2 (dotU (u : U n) (w : U n)) := rfl

theorem theta1_mul (u u' : ↥(Mod.W n Mod.ut0)) : theta1 n (u * u') = theta1 n u * theta1 n u' := by
  refine MonoidHom.ext fun w => ?_
  induction w using QuotientGroup.induction_on with
  | H w =>
    rw [MonoidHom.mul_apply, theta1_mk, theta1_mk, theta1_mk]
    show sgn2 (dotU ((u : U n) * (u' : U n)) (w : U n)) = _
    rw [dotU_mul_left, sgn2_add]

theorem theta1_one : theta1 n 1 = 1 := by
  refine MonoidHom.ext fun w => ?_
  induction w using QuotientGroup.induction_on with
  | H w =>
    rw [theta1_mk]
    show sgn2 (dotU (1 : U n) (w : U n)) = _
    rw [dotU_one_left, sgn2_zero]
    rfl

@[expose] noncomputable def Theta (n : ℕ) : Mod.V n Mod.ut0 →* (Mod.V n Mod.ut0 →* ℤˣ) :=
  QuotientGroup.lift ((Mod.N n Mod.ut0).subgroupOf (Mod.W n Mod.ut0))
    ({ toFun := fun u => theta1 n u, map_one' := theta1_one, map_mul' := theta1_mul } :
      ↥(Mod.W n Mod.ut0) →* (Mod.V n Mod.ut0 →* ℤˣ)) (by
      intro z hz
      have hz' : (z : U n) ∈ Esub n := hz
      rw [MonoidHom.mem_ker]
      refine MonoidHom.ext fun w => ?_
      induction w using QuotientGroup.induction_on with
      | H w =>
        have hw : ∑ i, (w : U n).val i = 0 := (mem_U0_iff_sum _).1 w.2
        show theta1 n z (QuotientGroup.mk w) = 1
        rcases (mem_Esub_iff _).1 hz' with h | h
        · rw [theta1_mk, h, dotU_one_left, sgn2_zero]
        · rw [theta1_mk, h, dotU_eVec_left, hw, sgn2_zero])

theorem Theta_mk (u w : ↥(Mod.W n Mod.ut0)) :
    Theta n (QuotientGroup.mk u) (QuotientGroup.mk w) = sgn2 (dotU (u : U n) (w : U n)) := rfl

theorem Theta_act (g : Gp n) (u w : Mod.V n Mod.ut0) :
    Theta n (Mod.act n Mod.ut0 g u) (Mod.act n Mod.ut0 g w) = Theta n u w := by
  induction u using QuotientGroup.induction_on with
  | H u =>
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [act_mk, act_mk, Theta_mk, Theta_mk]
      show sgn2 (dotU (permAct n g (u : U n)) (permAct n g (w : U n))) = _
      rw [dotU_perm]

theorem Theta_injective (hn : 1 ≤ n) : Function.Injective (Theta n) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  induction u using QuotientGroup.induction_on with
  | H u =>
    have hall : ∀ w : ↥(Mod.W n Mod.ut0), dotU (u : U n) (w : U n) = 0 := by
      intro w
      have := DFunLike.congr_fun hu (QuotientGroup.mk w)
      rw [MonoidHom.one_apply] at this
      have h2 : sgn2 (dotU (u : U n) (w : U n)) = 1 := this
      exact sgn2_eq_one.1 h2
    have hconst : ∀ i j : Fin n, (u : U n).val i = (u : U n).val j := by
      intro i j
      by_cases hij : i = j
      · rw [hij]
      · have h1 := hall ⟨pair i j, pair_mem_U0 hij⟩
        have h2 : dotU (u : U n) (pair i j) = (u : U n).val i + (u : U n).val j := dotU_pair _ hij
        have h3 : (u : U n).val i + (u : U n).val j = 0 := by rw [← h2]; exact h1
        exact (CharTwo.add_eq_zero.1 h3)
    let i₀ : Fin n := ⟨0, hn⟩
    have hc : (u : U n).val i₀ = 0 ∨ (u : U n).val i₀ = 1 := by
      generalize (u : U n).val i₀ = c
      revert c
      decide
    show (QuotientGroup.mk u : Mod.V n Mod.ut0) = 1
    rw [QuotientGroup.eq_one_iff]
    rcases hc with hc | hc
    · have : (u : U n) = 1 := by
        ext i
        rw [hconst i i₀, hc]
        rfl
      show (u : U n) ∈ Esub n
      rw [this]
      exact Subgroup.one_mem _
    · have : (u : U n) = eVec n := by
        ext i
        rw [hconst i i₀, hc]
        rfl
      show (u : U n) ∈ Esub n
      rw [this]
      exact Subgroup.mem_zpowers _

theorem card_dual (hn : 5 ≤ n) :
    Nat.card (Mod.V n Mod.ut0 →* ℤˣ) = Nat.card (Mod.V n Mod.ut0) := by
  have : HasEnoughRootsOfUnity ℤ 2 :=
    { prim := ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
      cyc := rootsOfUnity.isCyclic ℤ 2 }
  have hnt : Nontrivial (Mod.V n Mod.ut0) := (B3_1_1 hn).1
  have hexp : Monoid.exponent (Mod.V n Mod.ut0) = 2 := by
    have hdvd : Monoid.exponent (Mod.V n Mod.ut0) ∣ 2 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (V_sq' Mod.ut0)
    have hne : Monoid.exponent (Mod.V n Mod.ut0) ≠ 1 := fun h => by
      obtain ⟨a, b, hab⟩ := exists_pair_ne (Mod.V n Mod.ut0)
      apply hab
      have h1 := Monoid.pow_exponent_eq_one a
      have h2 := Monoid.pow_exponent_eq_one b
      rw [h, pow_one] at h1 h2
      rw [h1, h2]
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have : HasEnoughRootsOfUnity ℤ (Monoid.exponent (Mod.V n Mod.ut0)) := by
    rw [hexp]
    infer_instance
  exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℤ

theorem Theta_bijective (hn : 5 ≤ n) : Function.Bijective (Theta n) :=
  (Theta_injective (by omega)).bijective_of_nat_card_le (by rw [card_dual hn])

theorem exists_unique_theta (hn : 5 ≤ n) (f : Mod.V n Mod.ut0 →* ℤˣ) :
    ∃! u : Mod.V n Mod.ut0, Theta n u = f := by
  obtain ⟨u, hu⟩ := (Theta_bijective hn).2 f
  exact ⟨u, hu, fun v hv => (Theta_bijective hn).1 (hv.trans hu.symm)⟩

end CFSG.Quasithin.B3
