module

public import CFSG.Quasithin.Vol2.Ch12Sec6Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 Equiv

namespace S126E

@[expose] def tf (u v : Fin 4) (i : Fin 8) : Fin 8 :=
  if i.val < 4 then ⟨(i.val ^^^ u.val) % 8, Nat.mod_lt _ (by norm_num)⟩
  else ⟨(i.val ^^^ v.val) % 8, Nat.mod_lt _ (by norm_num)⟩

theorem tf_tf : ∀ u v : Fin 4, ∀ i : Fin 8, tf u v (tf u v i) = i := by
  decide +kernel

@[expose] def xr (u u' : Fin 4) : Fin 4 := ⟨(u.val ^^^ u'.val) % 4, Nat.mod_lt _ (by norm_num)⟩

theorem tf_comp : ∀ u v u' v' : Fin 4, ∀ i : Fin 8,
    tf u v (tf u' v' i) = tf (xr u u') (xr v v') i := by
  decide +kernel

theorem xr_self : ∀ u : Fin 4, xr u u = 0 := by
  decide

theorem eq_of_xr_eq_zero : ∀ u u' : Fin 4, xr u u' = 0 → u = u' := by
  decide

theorem tf_zero : ∀ i : Fin 8, tf 0 0 i = i := by
  decide

@[expose] def tau (u v : Fin 4) : Perm (Fin 8) := Function.Involutive.toPerm (tf u v) (tf_tf u v)

theorem tau_apply (u v : Fin 4) (i : Fin 8) : tau u v i = tf u v i := rfl

theorem tau_mul (u v u' v' : Fin 4) : tau u v * tau u' v' = tau (xr u u') (xr v v') :=
  Equiv.ext fun i => tf_comp u v u' v' i

theorem tau_zero : tau 0 0 = 1 :=
  Equiv.ext fun i => tf_zero i

theorem tau_inv (u v : Fin 4) : (tau u v)⁻¹ = tau u v := by
  rw [inv_eq_iff_mul_eq_one, tau_mul, xr_self, xr_self, tau_zero]

theorem tau_inv_apply (u v : Fin 4) (i : Fin 8) : (tau u v)⁻¹ i = tf u v i := by
  rw [tau_inv, tau_apply]

theorem tf_inj : ∀ u v u' v' : Fin 4, tf u v 0 = tf u' v' 0 → tf u v 4 = tf u' v' 4 →
    u = u' ∧ v = v' := by
  decide

theorem tau_inj {u v u' v' : Fin 4} (h : tau u v = tau u' v') : u = u' ∧ v = v' :=
  tf_inj u v u' v' (congrArg (fun σ : Perm (Fin 8) => σ 0) h)
    (congrArg (fun σ : Perm (Fin 8) => σ 4) h)

theorem tau_eq_one_iff {u v : Fin 4} : tau u v = 1 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    rw [← tau_zero] at h
    exact tau_inj h
  · rintro ⟨rfl, rfl⟩
    exact tau_zero

@[expose] def E16 : Subgroup (Perm (Fin 8)) where
  carrier := {σ | ∃ u v : Fin 4, σ = tau u v}
  one_mem' := ⟨0, 0, tau_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨u, v, rfl⟩ ⟨u', v', rfl⟩
    exact ⟨xr u u', xr v v', tau_mul u v u' v'⟩
  inv_mem' := by
    rintro _ ⟨u, v, rfl⟩
    exact ⟨u, v, tau_inv u v⟩

theorem tau_mem (u v : Fin 4) : tau u v ∈ E16 := ⟨u, v, rfl⟩

theorem card_E16_le : Nat.card E16 ≤ 16 := by
  have hs : Function.Surjective
      fun p : Fin 4 × Fin 4 => (⟨tau p.1 p.2, tau_mem p.1 p.2⟩ : E16) := by
    rintro ⟨σ, u, v, rfl⟩
    exact ⟨(u, v), rfl⟩
  have h := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_prod, Nat.card_fin] at h
  omega

@[expose] def c1 : Perm (Fin 8) := swap 0 1 * swap 1 2

@[expose] def c2 : Perm (Fin 8) := swap 4 5 * swap 5 6

theorem c1_mem : c1 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, c1, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  rfl

theorem c2_mem : c2 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup, c2, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
    Equiv.Perm.sign_swap (by decide)]
  rfl

theorem c1_pow_three : c1 ^ 3 = 1 := by
  decide

theorem c2_pow_three : c2 ^ 3 = 1 := by
  decide

theorem c1_block : ∀ i : Fin 8, (i.val < 4 ↔ (c1 i).val < 4) := by
  decide

theorem c2_block : ∀ i : Fin 8, (i.val < 4 ↔ (c2 i).val < 4) := by
  decide

@[expose] def rho1 (a c : Fin 8) : Perm (Fin 8) := c1 * swap (partner a) c * swap a (partner a)

@[expose] def rho2 (e g : Fin 8) : Perm (Fin 8) := c2 * swap (partner e) g * swap e (partner e)

theorem partner_zero : partner 0 = 1 := rfl

theorem partner_four : partner 4 = 5 := rfl

theorem comm_c1 (σ : Perm (Fin 8)) (hσ : ∀ i, σ (partner i) = partner (σ i)) :
    c1 * σ * c1⁻¹ * σ⁻¹ = rho1 (σ 0) (σ 2) := by
  have h1 : σ 1 = partner (σ 0) := by rw [← hσ 0, partner_zero]
  have e : c1 * σ * c1⁻¹ * σ⁻¹ = c1 * (σ * swap 1 2 * σ⁻¹) * (σ * swap 0 1 * σ⁻¹) := by
    rw [c1, mul_inv_rev, swap_inv, swap_inv]
    group
  rw [e, ← swap_apply_apply, ← swap_apply_apply, h1, rho1]

theorem comm_c2 (σ : Perm (Fin 8)) (hσ : ∀ i, σ (partner i) = partner (σ i)) :
    c2 * σ * c2⁻¹ * σ⁻¹ = rho2 (σ 4) (σ 6) := by
  have h1 : σ 5 = partner (σ 4) := by rw [← hσ 4, partner_four]
  have e : c2 * σ * c2⁻¹ * σ⁻¹ = c2 * (σ * swap 5 6 * σ⁻¹) * (σ * swap 4 5 * σ⁻¹) := by
    rw [c2, mul_inv_rev, swap_inv, swap_inv]
    group
  rw [e, ← swap_apply_apply, ← swap_apply_apply, h1, rho2]

theorem rho1_chk : ∀ a c : Fin 8, (∀ i, rho1 a c (partner i) = partner (rho1 a c i)) →
    ((∀ i : Fin 8, i.val < 4 → (rho1 a c i).val < 4) ∨
      (∀ i : Fin 8, i.val < 4 → 4 ≤ (rho1 a c i).val)) →
    ∃ u : Fin 4, a = tf u 0 0 ∧ c = tf u 0 2 := by
  decide +kernel

theorem rho2_chk : ∀ e g : Fin 8, (∀ i, rho2 e g (partner i) = partner (rho2 e g i)) →
    ((∀ i : Fin 8, i.val < 4 → (rho2 e g i).val < 4) ∨
      (∀ i : Fin 8, i.val < 4 → 4 ≤ (rho2 e g i).val)) →
    ∃ v : Fin 4, e = tf 0 v 4 ∧ g = tf 0 v 6 := by
  decide +kernel

theorem tf_vals : ∀ u v : Fin 4, tf u 0 0 = tf u v 0 ∧ tf u 0 2 = tf u v 2 ∧
    tf 0 v 4 = tf u v 4 ∧ tf 0 v 6 = tf u v 6 := by
  decide

theorem tf_partner : ∀ u v : Fin 4, ∀ i : Fin 8, tf u v (partner i) = partner (tf u v i) := by
  decide +kernel

theorem eq_tau_of_vals {σ : Perm (Fin 8)} (hσ : ∀ i, σ (partner i) = partner (σ i)) {u v : Fin 4}
    (h0 : σ 0 = tf u v 0) (h2 : σ 2 = tf u v 2) (h4 : σ 4 = tf u v 4) (h6 : σ 6 = tf u v 6) :
    σ = tau u v := by
  have hp : ∀ j, σ j = tf u v j → σ (partner j) = tf u v (partner j) := fun j hj => by
    rw [hσ j, hj, tf_partner]
  refine Equiv.ext fun i => ?_
  rw [tau_apply]
  fin_cases i
  · exact h0
  · exact hp 0 h0
  · exact h2
  · exact hp 2 h2
  · exact h4
  · exact hp 4 h4
  · exact h6
  · exact hp 6 h6

theorem eq_tau_of_comm {σ : Perm (Fin 8)} (hσ : PresPart σ) (h1 : PresPart (c1 * σ * c1⁻¹ * σ⁻¹))
    (h2 : PresPart (c2 * σ * c2⁻¹ * σ⁻¹)) : σ ∈ E16 := by
  rw [comm_c1 σ hσ.1] at h1
  rw [comm_c2 σ hσ.1] at h2
  obtain ⟨u, hu0, hu2⟩ := rho1_chk _ _ h1.1 h1.2
  obtain ⟨v, hv4, hv6⟩ := rho2_chk _ _ h2.1 h2.2
  obtain ⟨e0, e2, e4, e6⟩ := tf_vals u v
  exact ⟨u, v, eq_tau_of_vals hσ.1 (hu0.trans e0) (hu2.trans e2) (hv4.trans e4) (hv6.trans e6)⟩

end S126E

end CFSG.Quasithin.H13
