module

public import CFSG.Monster.B.TwoA.Census.CosetSquares

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.VisQuot
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice CFSG.Monster.Spin
  CFSG.Monster.Griess CFSG.Monster.B.Rep4371

@[expose] def thetaVis (p : Pvis) : Gvis := ⟨thetaEquiv p, thetaEquiv_mem_Gvis p⟩

@[expose, reducible] def rhoGvis (r : Q) : Gvis := thetaVis (rhoPair r)

theorem thetaVis_mul (p q : Pvis) : thetaVis (p * q) = thetaVis q * thetaVis p :=
  Subtype.ext (thetaEquiv_mul p q)

theorem thetaVis_mul_negPair (p : Pvis) : thetaVis (p * negPair) = thetaVis p :=
  Subtype.ext (thetaEquiv_mul_negPair p)

theorem coe_rhoGvis (r : Q) : (rhoGvis r : SpaceB ≃ₗ[ℚ] SpaceB) = rhoEquiv r := rfl

theorem rhoGvis_mul (r r' : Q) : rhoGvis (r * r') = rhoGvis r' * rhoGvis r :=
  Subtype.ext (rhoEquiv_mul r r')

theorem rhoGvis_one : rhoGvis 1 = 1 :=
  Subtype.ext ((congrArg thetaEquiv (map_one rhoPair)).trans thetaEquiv_one)

theorem rhoGvis_inv (r : Q) : rhoGvis r⁻¹ = (rhoGvis r)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← rhoGvis_mul, mul_inv_cancel, rhoGvis_one])

theorem rhoGvis_injective : Function.Injective rhoGvis := fun _ _ h =>
  rhoEquiv_injective (congrArg Subtype.val h)

theorem rhoGvis_mem (r : Q) : rhoGvis r ∈ rhoQ.subgroupOf Gvis :=
  Subgroup.mem_subgroupOf.2 (rhoEquiv_mem_rhoQ r)

theorem mem_rhoQ_subgroupOf_iff (u : Gvis) : u ∈ rhoQ.subgroupOf Gvis ↔ ∃ r : Q, u = rhoGvis r := by
  rw [Subgroup.mem_subgroupOf, mem_rhoQ]
  exact ⟨fun ⟨r, hr⟩ => ⟨r, Subtype.ext hr.symm⟩, fun ⟨r, hr⟩ => ⟨r, by rw [hr]; rfl⟩⟩

theorem rhoPair_mul_comm (p : Pvis) (r : Q) : rhoPair r * p = p * rhoPair (conjQ p r) := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show (r : GL SpinIdx ℚ) * p.1.1 = p.1.1 * (p.1.1⁻¹ * r * p.1.1)
    group
  · show (1 : latticeO) * p.1.2 = p.1.2 * 1
    rw [one_mul, mul_one]

theorem cosetRep_mul_rhoGvis
    (i : ℕ) (r : Q) :
    cosetRep i * rhoGvis r = thetaVis (rhoPair r * cosetPair i) := by
  rw [thetaVis_mul]
  rfl

theorem rhoPair_mul_sq (p : Pvis) (r : Q) :
    (rhoPair r * p) * (rhoPair r * p) = rhoPair r * (p * p) * rhoPair (conjQ p r) := by
  calc (rhoPair r * p) * (rhoPair r * p) = rhoPair r * p * (p * rhoPair (conjQ p r)) := by
        rw [rhoPair_mul_comm p r]
    _ = rhoPair r * (p * p) * rhoPair (conjQ p r) := by simp only [mul_assoc]

theorem rhoPair_mul_mul (r w a : Q) : rhoPair r * rhoPair w * rhoPair a = rhoPair (r * w * a) :=
  ((map_mul rhoPair (r * w) a).trans (congrArg (· * rhoPair a) (map_mul rhoPair r w))).symm

theorem thetaVis_sq_of_eq (p : Pvis) (r w : Q) (hp : p * p = rhoPair w) :
    thetaVis (rhoPair r * p) * thetaVis (rhoPair r * p) = rhoGvis (r * w * conjQ p r) :=
  (thetaVis_mul _ _).symm.trans (congrArg thetaVis ((rhoPair_mul_sq p r).trans
    ((congrArg (fun x => rhoPair r * x * rhoPair (conjQ p r)) hp).trans
      (rhoPair_mul_mul r w (conjQ p r)))))

theorem thetaVis_sq_of_eq_negPair (p : Pvis) (r w : Q) (hp : p * p = rhoPair w * negPair) :
    thetaVis (rhoPair r * p) * thetaVis (rhoPair r * p) = rhoGvis (r * w * conjQ p r) := by
  have hc := Subgroup.mem_center_iff.1 negPair_mem_center (rhoPair (conjQ p r))
  have e : rhoPair r * (rhoPair w * negPair) * rhoPair (conjQ p r) =
      rhoPair r * rhoPair w * rhoPair (conjQ p r) * negPair := by
    calc rhoPair r * (rhoPair w * negPair) * rhoPair (conjQ p r) =
        rhoPair r * (rhoPair w * (negPair * rhoPair (conjQ p r))) := by simp only [mul_assoc]
      _ = rhoPair r * (rhoPair w * (rhoPair (conjQ p r) * negPair)) :=
        congrArg (fun x => rhoPair r * (rhoPair w * x)) hc.symm
      _ = rhoPair r * rhoPair w * rhoPair (conjQ p r) * negPair := by simp only [mul_assoc]
  calc thetaVis (rhoPair r * p) * thetaVis (rhoPair r * p) =
      thetaVis (rhoPair r * (p * p) * rhoPair (conjQ p r)) :=
        (thetaVis_mul _ _).symm.trans (congrArg thetaVis (rhoPair_mul_sq p r))
    _ = thetaVis (rhoPair (r * w * conjQ p r) * negPair) :=
        congrArg thetaVis ((congrArg (fun x => rhoPair r * x * rhoPair (conjQ p r)) hp).trans
          (e.trans (congrArg (· * negPair) (rhoPair_mul_mul r w (conjQ p r)))))
    _ = rhoGvis (r * w * conjQ p r) := thetaVis_mul_negPair _

@[expose] def cosetW (i : ℕ) : Q := if i = 6 then zQ else pauliQ (sqPauli i)

theorem mul_rho_sq
    {i : ℕ} (hi : i = 1 ∨ i = 2 ∨ i = 6) (r : Q) :
    (cosetRep i * rhoGvis r) * (cosetRep i * rhoGvis r) =
      rhoGvis (r * cosetW i * conjQ (cosetPair i) r) := by
  rw [cosetRep_mul_rhoGvis]
  rcases hi with rfl | rfl | rfl
  · exact thetaVis_sq_of_eq _ r _ (cosetPair_sq_of_ne_six (Or.inl rfl))
  · exact thetaVis_sq_of_eq _ r _ (cosetPair_sq_of_ne_six (Or.inr rfl))
  · exact thetaVis_sq_of_eq_negPair _ r _ cosetPair_six_sq

theorem conj_thetaVis (p : Pvis) (u q : Q) :
    rhoGvis (conjQ p u) * thetaVis (rhoPair q * p) * (rhoGvis (conjQ p u))⁻¹ =
      thetaVis (rhoPair ((conjQ p u)⁻¹ * q * u) * p) := by
  have e : rhoPair (conjQ p u)⁻¹ * (rhoPair q * p * rhoPair (conjQ p u)) =
      rhoPair ((conjQ p u)⁻¹ * q * u) * p := by
    calc rhoPair (conjQ p u)⁻¹ * (rhoPair q * p * rhoPair (conjQ p u)) =
        rhoPair (conjQ p u)⁻¹ * rhoPair q * (p * rhoPair (conjQ p u)) := by
          simp only [mul_assoc]
      _ = rhoPair (conjQ p u)⁻¹ * rhoPair q * (rhoPair u * p) :=
        congrArg (rhoPair (conjQ p u)⁻¹ * rhoPair q * ·) (rhoPair_mul_comm p u).symm
      _ = rhoPair (conjQ p u)⁻¹ * rhoPair q * rhoPair u * p := by simp only [mul_assoc]
      _ = rhoPair ((conjQ p u)⁻¹ * q * u) * p :=
        congrArg (· * p) (rhoPair_mul_mul (conjQ p u)⁻¹ q u)
  calc rhoGvis (conjQ p u) * thetaVis (rhoPair q * p) * (rhoGvis (conjQ p u))⁻¹ =
      rhoGvis (conjQ p u) * thetaVis (rhoPair q * p) * rhoGvis (conjQ p u)⁻¹ :=
        congrArg (rhoGvis (conjQ p u) * thetaVis (rhoPair q * p) * ·)
          (rhoGvis_inv (conjQ p u)).symm
    _ = thetaVis (rhoPair (conjQ p u)⁻¹ * (rhoPair q * p * rhoPair (conjQ p u))) :=
        ((thetaVis_mul _ _).trans (congrArg (· * _) (thetaVis_mul _ _))).symm
    _ = thetaVis (rhoPair ((conjQ p u)⁻¹ * q * u) * p) := congrArg thetaVis e

theorem conj_mul_rho
    (i : ℕ) (u q : Q) :
    rhoGvis (conjQ (cosetPair i) u) * (cosetRep i * rhoGvis q) *
        (rhoGvis (conjQ (cosetPair i) u))⁻¹ =
      cosetRep i * rhoGvis ((conjQ (cosetPair i) u)⁻¹ * q * u) := by
  rw [cosetRep_mul_rhoGvis, cosetRep_mul_rhoGvis]
  exact conj_thetaVis (cosetPair i) u q

@[expose] def gQ (k : ℕ) : Q := pauliQ (genPauli k)

theorem pairN_zero_right (a : ℕ) : Model.pairN a 0 = false := by
  rw [Model.pairN, Nat.and_zero]
  rfl

theorem pairN_zero_left (d : ℕ) : Model.pairN 0 d = false := by
  rw [Model.pairN, Nat.zero_and]
  rfl

theorem pauliQ_false_zero : pauliQ (false, 0, 0) = 1 := pauliQ_sqPauli_one

theorem pauliQ_z : pauliQ (true, 0, 0) = zQ := by
  rw [pauliQ, toSC]
  simp only [pauli_s, pauli_a, pauli_d, boolZ_true, toC_zero, toD_zero]
  rfl

theorem pauliQ_T_xor (a b : ℕ) :
    pauliQ (false, a ^^^ b, 0) = pauliQ (false, a, 0) * pauliQ (false, b, 0) := by
  rw [← pauliQ_mul]
  congr 1
  simp only [Model.Pauli.mul, pauli_s, pauli_a, pauli_d, pairN_zero_right, Nat.xor_zero,
    Bool.xor_false]

theorem pauliQ_D_xor (d e : ℕ) :
    pauliQ (false, 0, d ^^^ e) = pauliQ (false, 0, d) * pauliQ (false, 0, e) := by
  rw [← pauliQ_mul]
  congr 1
  simp only [Model.Pauli.mul, pauli_s, pauli_a, pauli_d, pairN_zero_left, Nat.xor_zero,
    Bool.xor_false]

theorem mod_two_pow_succ_xor (A m : ℕ) :
    A % 2 ^ (m + 1) = A % 2 ^ m ^^^ (if A.testBit m then 2 ^ m else 0) := by
  refine Nat.eq_of_testBit_eq fun j => ?_
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_mod_two_pow]
  rcases lt_trichotomy j m with h | rfl | h
  · have h1 : j < m + 1 := by omega
    split_ifs <;> simp [h, h1, Nat.ne_of_gt h]
  · split_ifs with hA <;> simp [hA]
  · have h1 : ¬ j < m + 1 := by omega
    have h2 : ¬ j < m := by omega
    split_ifs <;> simp [h1, h2, Nat.ne_of_lt h]

theorem pauliQ_mod_a (s : Bool) (a d : ℕ) : pauliQ (s, a % 2 ^ 12, d) = pauliQ (s, a, d) := by
  rw [pauliQ, pauliQ]
  congr 1
  refine SpinCoord.ext rfl ?_ rfl
  exact toC_ext fun j => by rw [Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]

theorem pauliQ_mod_d (s : Bool) (a d : ℕ) : pauliQ (s, a, d % 2 ^ 12) = pauliQ (s, a, d) := by
  rw [pauliQ, pauliQ]
  congr 1
  refine SpinCoord.ext rfl rfl ?_
  exact toD_ext fun j => by rw [Nat.testBit_mod_two_pow, decide_eq_true j.2, Bool.true_and]

theorem pauliQ_split (s : Bool) (A D : ℕ) :
    pauliQ (s, A, D) = pauliQ (s, 0, 0) * pauliQ (false, A, 0) * pauliQ (false, 0, D) := by
  rw [← pauliQ_mul, ← pauliQ_mul]
  congr 1
  simp only [Model.Pauli.mul, pauli_s, pauli_a, pauli_d, pairN_zero_right, Nat.xor_zero,
    Nat.zero_xor, Bool.xor_false]

theorem gQ_lt {k : ℕ} (hk : k < 12) : gQ k = pauliQ (false, 2 ^ k, 0) := by
  rw [gQ, genPauli, ite_eq_left hk]

theorem gQ_add (m : ℕ) : gQ (m + 12) = pauliQ (false, 0, 2 ^ m) := by
  rw [gQ, genPauli, ite_eq_right (by omega), Nat.add_sub_cancel]

theorem gQ_comm : gQ 12 * gQ 0 = pauliQ (true, 0, 0) * (gQ 0 * gQ 12) := by
  rw [gQ, gQ, ← pauliQ_mul, ← pauliQ_mul, ← pauliQ_mul]
  congr 1

theorem pauliQ_T_bit (A m : ℕ) : pauliQ (false, A % 2 ^ (m + 1), 0) =
    pauliQ (false, A % 2 ^ m, 0) * pauliQ (false, if A.testBit m then 2 ^ m else 0, 0) := by
  rw [mod_two_pow_succ_xor, pauliQ_T_xor]

theorem pauliQ_D_bit (D m : ℕ) : pauliQ (false, 0, D % 2 ^ (m + 1)) =
    pauliQ (false, 0, D % 2 ^ m) * pauliQ (false, 0, if D.testBit m then 2 ^ m else 0) := by
  rw [mod_two_pow_succ_xor, pauliQ_D_xor]

theorem pauliQ_T_mem (S : Subgroup Q) (hS : ∀ k < 12, gQ k ∈ S) :
    ∀ m ≤ 12, ∀ A : ℕ, pauliQ (false, A % 2 ^ m, 0) ∈ S
  | 0, _, A => by
    rw [pow_zero, Nat.mod_one, pauliQ_false_zero]
    exact S.one_mem
  | m + 1, hm, A => by
    rw [pauliQ_T_bit]
    refine S.mul_mem (pauliQ_T_mem S hS m (by omega) A) ?_
    by_cases hb : A.testBit m = true
    · rw [ite_eq_left hb, ← gQ_lt (by omega)]
      exact hS m (by omega)
    · rw [ite_eq_right hb, pauliQ_false_zero]
      exact S.one_mem

theorem pauliQ_D_mem (S : Subgroup Q) (hS : ∀ k < 12, gQ (k + 12) ∈ S) :
    ∀ m ≤ 12, ∀ D : ℕ, pauliQ (false, 0, D % 2 ^ m) ∈ S
  | 0, _, D => by
    rw [pow_zero, Nat.mod_one, pauliQ_false_zero]
    exact S.one_mem
  | m + 1, hm, D => by
    rw [pauliQ_D_bit]
    refine S.mul_mem (pauliQ_D_mem S hS m (by omega) D) ?_
    by_cases hb : D.testBit m = true
    · rw [ite_eq_left hb, ← gQ_add]
      exact hS m (by omega)
    · rw [ite_eq_right hb, pauliQ_false_zero]
      exact S.one_mem

theorem pauliQ_z_mem (S : Subgroup Q) (h0 : gQ 0 ∈ S) (h12 : gQ 12 ∈ S) :
    pauliQ (true, 0, 0) ∈ S := by
  have e : pauliQ (true, 0, 0) = gQ 12 * gQ 0 * (gQ 0 * gQ 12)⁻¹ := by
    rw [gQ_comm, mul_inv_cancel_right]
  rw [e]
  exact S.mul_mem (S.mul_mem h12 h0) (S.inv_mem (S.mul_mem h0 h12))

theorem pauliQ_mem_of_gQ (S : Subgroup Q) (hS : ∀ k < 24, gQ k ∈ S) (s : Bool) (A D : ℕ) :
    pauliQ (s, A, D) ∈ S := by
  rw [pauliQ_split, ← pauliQ_mod_a false A 0, ← pauliQ_mod_d false 0 D]
  refine S.mul_mem (S.mul_mem ?_ (pauliQ_T_mem S (fun k hk => hS k (by omega)) 12 le_rfl A))
    (pauliQ_D_mem S (fun k hk => hS (k + 12) (by omega)) 12 le_rfl D)
  cases s
  · rw [pauliQ_false_zero]
    exact S.one_mem
  · exact pauliQ_z_mem S (hS 0 (by norm_num)) (hS 12 (by norm_num))

theorem closure_gQ : Subgroup.closure (gQ '' {k | k < 24}) = ⊤ := by
  rw [eq_top_iff]
  intro r _
  obtain ⟨s, -, A, -, D, -, rfl⟩ := exists_qP r
  rw [qP]
  exact pauliQ_mem_of_gQ (Subgroup.closure (gQ '' {k | k < 24}))
    (fun k hk => Subgroup.subset_closure ⟨k, hk, rfl⟩) (s % 2 == 1) A D

theorem mem_closure_conj (p : Pvis) (y : Q) :
    conjQ p y ∈ Subgroup.closure ((fun k => conjQ p (gQ k)) '' {k | k < 24}) := by
  have hy : y ∈ Subgroup.closure (gQ '' {k | k < 24}) := by
    rw [closure_gQ]
    exact Subgroup.mem_top y
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, rfl⟩ := hy
    exact Subgroup.subset_closure ⟨k, hk, rfl⟩
  | one =>
    rw [show conjQ p 1 = 1 from map_one (conjQ p)]
    exact Subgroup.one_mem _
  | mul a b _ _ ha hb =>
    rw [show conjQ p (a * b) = conjQ p a * conjQ p b from map_mul (conjQ p) a b]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show conjQ p a⁻¹ = (conjQ p a)⁻¹ from map_inv (conjQ p) a]
    exact Subgroup.inv_mem _ ha

theorem closure_conj_gQ (p : Pvis) :
    Subgroup.closure ((fun k => conjQ p (gQ k)) '' {k | k < 24}) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx := mem_closure_conj p ((conjQ p).symm x)
  rwa [MulEquiv.apply_symm_apply] at hx

theorem closure_rho_conj (p : Pvis) :
    Subgroup.closure ((fun k => rhoGvis (conjQ p (gQ k))) '' {k | k < 24}) =
      rhoQ.subgroupOf Gvis := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact rhoGvis_mem _
  · set K := Subgroup.closure ((fun k => rhoGvis (conjQ p (gQ k))) '' {k | k < 24})
    let K' : Subgroup Q :=
      { carrier := {x | rhoGvis x ∈ K}
        mul_mem' := fun {a b} ha hb => by
          show rhoGvis (a * b) ∈ K
          rw [rhoGvis_mul]
          exact K.mul_mem hb ha
        one_mem' := by
          show rhoGvis 1 ∈ K
          rw [rhoGvis_one]
          exact K.one_mem
        inv_mem' := fun {a} ha => by
          show rhoGvis a⁻¹ ∈ K
          rw [rhoGvis_inv]
          exact K.inv_mem ha }
    have hK' : K' = ⊤ := by
      rw [eq_top_iff, ← closure_conj_gQ p, Subgroup.closure_le]
      rintro _ ⟨k, hk, rfl⟩
      exact Subgroup.subset_closure ⟨k, hk, rfl⟩
    intro f hf
    obtain ⟨x, rfl⟩ := (mem_rhoQ_subgroupOf_iff f).1 hf
    have hx : x ∈ K' := hK' ▸ Subgroup.mem_top x
    exact hx

@[expose] def qmatClass (f : Gvis) : Set Gvis := {g | ∃ u ∈ rhoQ.subgroupOf Gvis, g = u⁻¹ * f * u}

theorem mem_qmatClass_self (f : Gvis) : f ∈ qmatClass f :=
  ⟨1, Subgroup.one_mem _, by rw [inv_one, one_mul, mul_one]⟩

theorem qmatClass_eq_of_mem {f g : Gvis} (h : g ∈ qmatClass f) : qmatClass g = qmatClass f := by
  obtain ⟨u, hu, rfl⟩ := h
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨u * v, Subgroup.mul_mem _ hu hv, by group⟩
  · rintro ⟨v, hv, rfl⟩
    refine ⟨u⁻¹ * v, Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv, ?_⟩
    group

theorem orbit_closure_conjAct (p : Pvis) (f : Gvis) :
    MulAction.orbit (Subgroup.closure
      ((fun k => ConjAct.toConjAct (rhoGvis (conjQ p (gQ k)))) '' {k | k < 24})) f =
      qmatClass f := by
  have hcl : Subgroup.closure
      ((fun k => ConjAct.toConjAct (rhoGvis (conjQ p (gQ k)))) '' {k | k < 24}) =
      (rhoQ.subgroupOf Gvis).map (ConjAct.toConjAct : Gvis ≃* ConjAct Gvis).toMonoidHom := by
    rw [← closure_rho_conj p, MonoidHom.map_closure, Set.image_image]
    rfl
  rw [hcl]
  ext g
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨c, u, hu, rfl⟩, rfl⟩
    refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    rw [Subgroup.smul_def, ConjAct.smul_def, inv_inv]
    rfl
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨ConjAct.toConjAct u⁻¹, u⁻¹, Subgroup.inv_mem _ hu, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, ConjAct.smul_def]
    show u⁻¹ * f * u⁻¹⁻¹ = u⁻¹ * f * u
    rw [inv_inv]

theorem qmatClass_subset
    (i : ℕ) {f : Gvis} (hf : f ∈ cosetR i) :
    ∀ g ∈ qmatClass f, g ∈ cosetR i ∧ (g * g = 1 ↔ f * f = 1) := by
  rintro _ ⟨u, hu, rfl⟩
  have hpu : piVis u = 1 := by
    rw [← MonoidHom.mem_ker, ker_piVis]
    exact hu
  refine ⟨?_, ?_⟩
  · rw [mem_cosetR_iff] at hf ⊢
    rw [map_mul, map_mul, map_inv, hpu, inv_one, one_mul, mul_one, hf]
  · have e : u⁻¹ * f * u * (u⁻¹ * f * u) = u⁻¹ * (f * f) * u⁻¹⁻¹ := by group
    rw [e]
    exact conj_eq_one_iff

end CFSG.Monster.B.TwoA.Census
