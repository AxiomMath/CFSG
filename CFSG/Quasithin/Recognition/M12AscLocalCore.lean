module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Group
public import CFSG.Quasithin.Recognition.M12AscHPres

public section

namespace CFSG.Quasithin

variable {H : Type*} [Group H]

structure Q32Data (z : H) (Q : Subgroup H) : Prop where
  card_eq : Nat.card Q = 32
  z_mem : z ∈ Q
  z_ne_one : z ≠ 1
  z_sq : z * z = 1
  z_central : ∀ h : H, h * z = z * h
  center_le : ∀ q ∈ Q, (∀ y ∈ Q, q * y = y * q) → q = 1 ∨ q = z
  sq_mem : ∀ q ∈ Q, q * q = 1 ∨ q * q = z
  comm_mem : ∀ q ∈ Q, ∀ y ∈ Q, q * y * q⁻¹ * y⁻¹ = 1 ∨ q * y * q⁻¹ * y⁻¹ = z

section Anti

variable {z g g' h h' : H}

theorem anti_symm' (hz2 : z * z = 1) (h1 : g * h = z * (h * g)) : h * g = z * (g * h) := by
  rw [h1, ← mul_assoc, hz2, one_mul]

theorem mul_comm_of_anti_anti (hz : ∀ t : H, t * z = z * t) (hz2 : z * z = 1)
    (h1 : g * h = z * (h * g)) (h2 : g' * h = z * (h * g')) : g * g' * h = h * (g * g') := by
  calc g * g' * h = g * (g' * h) := by group
    _ = g * (z * (h * g')) := by rw [h2]
    _ = (g * z) * (h * g') := by group
    _ = (z * g) * (h * g') := by rw [hz g]
    _ = z * ((g * h) * g') := by group
    _ = z * ((z * (h * g)) * g') := by rw [h1]
    _ = (z * z) * (h * (g * g')) := by group
    _ = h * (g * g') := by rw [hz2, one_mul]

theorem anti_mul_of_anti_comm (h1 : g * h = z * (h * g)) (h2 : g' * h = h * g') :
    g * g' * h = z * (h * (g * g')) := by
  calc g * g' * h = g * (g' * h) := by group
    _ = g * (h * g') := by rw [h2]
    _ = (g * h) * g' := by group
    _ = (z * (h * g)) * g' := by rw [h1]
    _ = z * (h * (g * g')) := by group

theorem anti_mul_of_comm_anti (hz : ∀ t : H, t * z = z * t)
    (h1 : g * h = h * g) (h2 : g' * h = z * (h * g')) : g * g' * h = z * (h * (g * g')) := by
  calc g * g' * h = g * (g' * h) := by group
    _ = g * (z * (h * g')) := by rw [h2]
    _ = (g * z) * (h * g') := by group
    _ = (z * g) * (h * g') := by rw [hz g]
    _ = z * ((g * h) * g') := by group
    _ = z * ((h * g) * g') := by rw [h1]
    _ = z * (h * (g * g')) := by group

theorem mul_comm_of_anti_anti_right (hz : ∀ t : H, t * z = z * t) (hz2 : z * z = 1)
    (h1 : g * h = z * (h * g)) (h2 : g * h' = z * (h' * g)) : g * (h * h') = (h * h') * g := by
  calc g * (h * h') = (g * h) * h' := by group
    _ = (z * (h * g)) * h' := by rw [h1]
    _ = z * (h * (g * h')) := by group
    _ = z * (h * (z * (h' * g))) := by rw [h2]
    _ = z * ((h * z) * (h' * g)) := by group
    _ = z * ((z * h) * (h' * g)) := by rw [hz h]
    _ = (z * z) * (h * h' * g) := by group
    _ = (h * h') * g := by rw [hz2, one_mul]

end Anti

namespace Q32Data

variable {z : H} {Q : Subgroup H}

theorem comm_cases (hQ : Q32Data z Q) {q y : H} (hq : q ∈ Q) (hy : y ∈ Q) :
    q * y = y * q ∨ q * y = z * (y * q) := by
  rcases hQ.comm_mem q hq y hy with h | h
  · left
    calc q * y = (q * y * q⁻¹ * y⁻¹) * (y * q) := by group
      _ = y * q := by rw [h, one_mul]
  · right
    calc q * y = (q * y * q⁻¹ * y⁻¹) * (y * q) := by group
      _ = z * (y * q) := by rw [h]

theorem inv_eq_mul_z (hQ : Q32Data z Q) {q : H} (hq : q * q = z) : q⁻¹ = q * z := by
  apply inv_eq_of_mul_eq_one_right
  rw [← mul_assoc, hq, hQ.z_sq]

theorem eq_mul_z_of_eq_z_mul (hQ : Q32Data z Q) {w y : H} (h : w = z * y) : y = w * z := by
  rw [h, mul_assoc, hQ.z_central y, ← mul_assoc, hQ.z_sq, one_mul]

end Q32Data

structure Act3 (σ : H ≃* H) (z : H) (Q : Subgroup H) : Prop where
  σ3 : ∀ q, σ (σ (σ q)) = q
  σz : σ z = z
  σQ : ∀ q ∈ Q, σ q ∈ Q
  fix : ∀ q ∈ Q, σ q = q → q = 1 ∨ q = z

namespace Act3

variable {σ : H ≃* H} {z : H} {Q : Subgroup H}

theorem fixed_coset (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {q : H} (hq : q ∈ Q)
    (h : σ q = q ∨ σ q = q * z) : q = 1 ∨ q = z := by
  rcases h with h | h
  · exact hσ.fix q hq h
  · exfalso
    have h2 : σ (σ q) = q := by
      rw [h, map_mul, hσ.σz, h, mul_assoc, hQ.z_sq, mul_one]
    have h3 : q = q * z := by
      calc q = σ (σ (σ q)) := (hσ.σ3 q).symm
        _ = σ q := by rw [h2]
        _ = q * z := h
    exact hQ.z_ne_one (by simpa using h3.symm)

theorem trip (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {q : H} (hq : q ∈ Q) :
    q * σ q * σ (σ q) = 1 ∨ q * σ q * σ (σ q) = z := by
  have hq1 : σ q ∈ Q := hσ.σQ q hq
  have hq2 : σ (σ q) ∈ Q := hσ.σQ _ hq1
  have hwQ : q * σ q * σ (σ q) ∈ Q := Q.mul_mem (Q.mul_mem hq hq1) hq2
  have hσw : σ (q * σ q * σ (σ q)) = σ q * σ (σ q) * q := by
    rw [map_mul, map_mul, hσ.σ3 q]
  refine hσ.fixed_coset hQ hwQ ?_
  rcases hQ.comm_cases hq (Q.mul_mem hq1 hq2) with h | h
  · left
    rw [hσw, ← h, ← mul_assoc]
  · right
    have hw' : q * σ q * σ (σ q) = z * (σ q * σ (σ q) * q) := by rw [mul_assoc]; exact h
    rw [hσw]
    exact hQ.eq_mul_z_of_eq_z_mul hw'

theorem noncomm (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {q : H} (hq : q ∈ Q) (hq2 : q * q = z) :
    q * σ q ≠ σ q * q := by
  intro hc
  have hs2 : σ (σ q) * σ (σ q) = z := by
    rw [← map_mul, ← map_mul, hq2, hσ.σz, hσ.σz]
  have hc1 : σ q * σ (σ q) = σ (σ q) * σ q := by
    have := congrArg σ hc
    simpa only [map_mul] using this
  have hc2 : σ (σ q) * q = q * σ (σ q) := by
    have := congrArg σ hc1
    simpa only [map_mul, hσ.σ3] using this
  have hsp : σ (σ q) * (q * σ q) = (q * σ q) * σ (σ q) := by
    calc σ (σ q) * (q * σ q) = (σ (σ q) * q) * σ q := by group
      _ = (q * σ (σ q)) * σ q := by rw [hc2]
      _ = q * (σ (σ q) * σ q) := by group
      _ = q * (σ q * σ (σ q)) := by rw [← hc1]
      _ = (q * σ q) * σ (σ q) := by group
  have hpp : (q * σ q) * (q * σ q) = 1 := by
    calc (q * σ q) * (q * σ q) = q * (σ q * q) * σ q := by group
      _ = q * (q * σ q) * σ q := by rw [← hc]
      _ = (q * q) * (σ q * σ q) := by group
      _ = z * z := by rw [hq2, ← map_mul, hq2, hσ.σz]
      _ = 1 := hQ.z_sq
  have hps : (q * σ q * σ (σ q)) * (q * σ q * σ (σ q)) = 1 := by
    rcases hσ.trip hQ hq with h | h
    · rw [h, mul_one]
    · rw [h, hQ.z_sq]
  have hps2 : (q * σ q * σ (σ q)) * (q * σ q * σ (σ q)) = z := by
    calc (q * σ q * σ (σ q)) * (q * σ q * σ (σ q))
        = (q * σ q) * (σ (σ q) * (q * σ q)) * σ (σ q) := by group
      _ = (q * σ q) * ((q * σ q) * σ (σ q)) * σ (σ q) := by rw [hsp]
      _ = ((q * σ q) * (q * σ q)) * (σ (σ q) * σ (σ q)) := by group
      _ = 1 * z := by rw [hpp, hs2]
      _ = z := one_mul z
  exact hQ.z_ne_one (hps2.symm.trans hps)

theorem exists_norm (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {e : H} (he : e ∈ Q) (he2 : e * e = z) :
    ∃ e' : H, (e' = e ∨ e' = e * z) ∧ e' * e' = z ∧ e' * σ e' = σ (σ e') := by
  have hs2 : σ (σ e) * σ (σ e) = z := by
    rw [← map_mul, ← map_mul, he2, hσ.σz, hσ.σz]
  have hinv : (σ (σ e))⁻¹ = σ (σ e) * z := hQ.inv_eq_mul_z hs2
  rcases hσ.trip hQ he with hw | hw
  · refine ⟨e * z, Or.inr rfl, ?_, ?_⟩
    · calc e * z * (e * z) = e * e * (z * z) := by
            rw [mul_assoc, ← mul_assoc z e z, ← hQ.z_central e, mul_assoc e z z, ← mul_assoc,
              ← mul_assoc, mul_assoc (e * e)]
        _ = z := by rw [he2, hQ.z_sq, mul_one]
    · have h1 : e * σ e = σ (σ e) * z := by
        rw [← hinv]
        exact eq_inv_of_mul_eq_one_left hw
      rw [map_mul, map_mul, hσ.σz, hσ.σz]
      calc e * z * (σ e * z) = e * σ e * (z * z) := by
            rw [mul_assoc, ← mul_assoc z (σ e) z, ← hQ.z_central (σ e), mul_assoc (σ e) z z,
              ← mul_assoc, ← mul_assoc, mul_assoc (e * σ e)]
        _ = σ (σ e) * z := by rw [hQ.z_sq, mul_one, h1]
  · refine ⟨e, Or.inl rfl, he2, ?_⟩
    have h1 : e * σ e = z * (σ (σ e))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact hw
    calc e * σ e = z * (σ (σ e))⁻¹ := h1
      _ = z * (σ (σ e) * z) := by rw [hinv]
      _ = z * (z * σ (σ e)) := by rw [hQ.z_central (σ (σ e))]
      _ = σ (σ e) := by rw [← mul_assoc, hQ.z_sq, one_mul]

end Act3

section Order8

variable {z : H}

theorem orderOf_eq_four (hz1 : z ≠ 1) (hz2 : z * z = 1) {e : H} (he : e * e = z) :
    orderOf e = 4 := by
  have hnot : ¬ e ^ 2 ^ 1 = 1 := by
    intro h
    apply hz1
    rw [← he]
    simpa [pow_two] using h
  have hfin : e ^ 2 ^ (1 + 1) = 1 := by
    show e ^ 4 = 1
    calc e ^ 4 = (e * e) * (e * e) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = z * z := by rw [he]
      _ = 1 := hz2
  have := orderOf_eq_prime_pow (p := 2) (n := 1) hnot hfin
  simpa using this

theorem cent_eq [Finite H] (hz1 : z ≠ 1) (hz2 : z * z = 1) {E : Subgroup H}
    (hE : Nat.card E ≤ 8) {e f c : H} (he : e ∈ E) (hf : f ∈ E) (hc : c ∈ E) (he2 : e * e = z)
    (hef : e * f ≠ f * e) (hce : c * e = e * c) : c = 1 ∨ c = e ∨ c = z ∨ c = e * z := by
  have hord : orderOf e = 4 := orderOf_eq_four hz1 hz2 he2
  set C : Subgroup H := E ⊓ Subgroup.centralizer {e} with hC
  have heC : e ∈ C := ⟨he, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hzp : Subgroup.zpowers e ≤ C := (Subgroup.zpowers_le).2 heC
  have hcard4 : Nat.card (Subgroup.zpowers e) = 4 := by rw [Nat.card_zpowers, hord]
  have hfC : f ∉ C := fun h => hef (Subgroup.mem_centralizer_singleton_iff.1 h.2).symm
  have hCE : C < E := lt_of_le_of_ne inf_le_left (fun h => hfC (h ▸ hf))
  have h1 : 4 ∣ Nat.card C := hcard4 ▸ Subgroup.card_dvd_of_le hzp
  have h3 : Nat.card C < Nat.card E := Subgroup.card_lt_of_lt hCE
  have hpos : 0 < Nat.card C := Nat.card_pos
  have h4 : Nat.card C = 4 := by
    obtain ⟨m, hm⟩ := h1
    omega
  have hCzp : Subgroup.zpowers e = C :=
    Subgroup.eq_of_le_of_card_ge hzp (by rw [hcard4, h4])
  have hcC : c ∈ Subgroup.zpowers e := by
    rw [hCzp]
    exact ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 hce⟩
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hcC)
  have hmod : e ^ (n % 4) = c := by
    have := pow_mod_orderOf e n
    rw [hord] at this
    rw [this, hn]
  have hn4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hn4 with h | h | h | h
  · left
    rw [h, pow_zero] at hmod
    exact hmod.symm
  · right; left
    rw [h, pow_one] at hmod
    exact hmod.symm
  · right; right; left
    rw [h, pow_two, he2] at hmod
    exact hmod.symm
  · right; right; right
    rw [h, pow_three, he2] at hmod
    exact hmod.symm

theorem closure_eq_of_card_le [Finite H] (hz1 : z ≠ 1) (hz2 : z * z = 1) {E : Subgroup H}
    (hE : Nat.card E ≤ 8) {e f : H} (he : e ∈ E) (hf : f ∈ E) (he2 : e * e = z)
    (hef : e * f ≠ f * e) : Subgroup.closure ({e, f} : Set H) = E := by
  have hord : orderOf e = 4 := orderOf_eq_four hz1 hz2 he2
  set S : Subgroup H := Subgroup.closure ({e, f} : Set H) with hS
  have hSE : S ≤ E := by
    rw [hS, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact he
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hf
  have heS : e ∈ S := Subgroup.subset_closure (by simp)
  have hfS : f ∈ S := Subgroup.subset_closure (by simp)
  have hzpS : Subgroup.zpowers e ≤ S := (Subgroup.zpowers_le).2 heS
  have hcard4 : Nat.card (Subgroup.zpowers e) = 4 := by rw [Nat.card_zpowers, hord]
  have hlt : Subgroup.zpowers e < S := by
    refine lt_of_le_of_ne hzpS (fun h => hef ?_)
    have hfz : f ∈ Subgroup.zpowers e := h ▸ hfS
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hfz
    rw [← hk]
    exact (Commute.self_zpow e k).eq
  have h1 : 4 ∣ Nat.card S := hcard4 ▸ Subgroup.card_dvd_of_le hzpS
  have h2 : 4 < Nat.card S := hcard4 ▸ Subgroup.card_lt_of_lt hlt
  have h3 : Nat.card S ≤ Nat.card E := Subgroup.card_le_of_le hSE
  have h4 : Nat.card S = 8 := by
    obtain ⟨m, hm⟩ := h1
    omega
  exact Subgroup.eq_of_le_of_card_ge hSE (by omega)

theorem eq_or_eq_mul_z_of_sq (hz1 : z ≠ 1) (hz2 : z * z = 1) {e k : H} (hk2 : k * k = z)
    (h : k = 1 ∨ k = e ∨ k = z ∨ k = e * z) : k = e ∨ k = e * z := by
  rcases h with h | h | h | h
  · exfalso
    rw [h, mul_one] at hk2
    exact hz1 hk2.symm
  · exact Or.inl h
  · exfalso
    rw [h, hz2] at hk2
    exact hz1 hk2.symm
  · exact Or.inr h

end Order8

namespace Act3

variable {σ : H ≃* H} {z : H} {Q : Subgroup H}

theorem sq_σ (hσ : Act3 σ z Q) {e : H} (he2 : e * e = z) : σ e * σ e = z := by
  rw [← map_mul, he2, hσ.σz]

theorem sq_σσ (hσ : Act3 σ z Q) {e : H} (he2 : e * e = z) : σ (σ e) * σ (σ e) = z :=
  hσ.sq_σ (hσ.sq_σ he2)

theorem norm_σ {e : H} (hn : e * σ e = σ (σ e)) :
    σ e * σ (σ e) = σ (σ (σ e)) := by
  have := congrArg σ hn
  simpa only [map_mul] using this

theorem cls [Finite H] (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {E : Subgroup H}
    (hE : Nat.card E ≤ 8) (hEQ : E ≤ Q) (hEσ : ∀ q ∈ E, σ q ∈ E) {e k : H} (he : e ∈ E)
    (he2 : e * e = z) (hn : e * σ e = σ (σ e)) (hk : k ∈ E) (hk2 : k * k = z) :
    k = e ∨ k = e * z ∨ k = σ e ∨ k = σ e * z ∨ k = σ (σ e) ∨ k = σ (σ e) * z := by
  have he1 : σ e ∈ E := hEσ e he
  have hee2 : σ (σ e) ∈ E := hEσ _ he1
  have hnc : e * σ e ≠ σ e * e := hσ.noncomm hQ (hEQ he) he2
  have hnc2 : σ e * e ≠ e * σ e := fun h => hnc h.symm
  have hk1 : k ∈ Q := hEQ hk
  have heQ : e ∈ Q := hEQ he
  have he1Q : σ e ∈ Q := hEQ he1
  rcases hQ.comm_cases hk1 heQ with hke | hke
  · have := cent_eq hQ.z_ne_one hQ.z_sq hE he he1 hk he2 hnc hke
    rcases eq_or_eq_mul_z_of_sq hQ.z_ne_one hQ.z_sq hk2 this with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hQ.comm_cases hk1 he1Q with hk1' | hk1'
    · have := cent_eq hQ.z_ne_one hQ.z_sq hE he1 he hk (hσ.sq_σ he2) hnc2 hk1'
      rcases eq_or_eq_mul_z_of_sq hQ.z_ne_one hQ.z_sq hk2 this with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · have hkc : k * σ (σ e) = σ (σ e) * k := by
        rw [← hn]
        exact mul_comm_of_anti_anti_right hQ.z_central hQ.z_sq hke hk1'
      have hnc3 : σ (σ e) * e ≠ e * σ (σ e) := by
        intro h
        apply hnc
        rw [← hn] at h
        have h' : e * (σ e * e) = e * (e * σ e) := by
          calc e * (σ e * e) = (e * σ e) * e := by group
            _ = e * (e * σ e) := h
        exact (mul_left_cancel h').symm
      have := cent_eq hQ.z_ne_one hQ.z_sq hE hee2 he hk (hσ.sq_σσ he2) hnc3 hkc
      rcases eq_or_eq_mul_z_of_sq hQ.z_ne_one hQ.z_sq hk2 this with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem refl_ne (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {τ : H ≃* H}
    (hτσ : ∀ q, τ (σ q) = σ (σ (τ q))) {e : H} (he : e ∈ Q) (he2 : e * e = z)
    (hn : e * σ e = σ (σ e)) : τ e ≠ e := by
  intro hτ
  have h1 : τ (σ e) = σ (σ e) := by rw [hτσ, hτ]
  have h2 : τ (σ (σ e)) = σ e := by rw [hτσ, h1, hσ.σ3]
  have h3 : e * σ (σ e) = σ e := by
    have := congrArg τ hn
    rw [map_mul, hτ, h1, h2] at this
    exact this
  have h4 : σ (σ e) * e = σ e := by
    have := congrArg σ (congrArg σ hn)
    simpa only [map_mul, hσ.σ3] using this
  have hee : σ (σ e) ∈ Q := hσ.σQ _ (hσ.σQ _ he)
  have := hσ.noncomm hQ hee (hσ.sq_σσ he2)
  rw [hσ.σ3] at this
  exact this (h4.trans h3.symm)

theorem refl_cls [Finite H] (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {τ : H ≃* H}
    (hτσ : ∀ q, τ (σ q) = σ (σ (τ q))) (hτz : τ z = z) {E : Subgroup H}
    (hE : Nat.card E ≤ 8) (hEQ : E ≤ Q) (hEσ : ∀ q ∈ E, σ q ∈ E) (hEτ : ∀ q ∈ E, τ q ∈ E)
    {e : H} (he : e ∈ E) (he2 : e * e = z) (hn : e * σ e = σ (σ e)) :
    τ e = e * z ∨ τ e = σ e * z ∨ τ e = σ (σ e) * z := by
  have hk2 : τ e * τ e = z := by rw [← map_mul, he2, hτz]
  have hcls := hσ.cls hQ hE hEQ hEσ he he2 hn (hEτ e he) hk2
  have hn1 : σ e * σ (σ e) = σ (σ (σ e)) := norm_σ hn
  have hn2 : σ (σ e) * σ (σ (σ e)) = σ (σ (σ (σ e))) := norm_σ hn1
  rcases hcls with h | h | h | h | h | h
  · exact absurd h (hσ.refl_ne hQ hτσ (hEQ he) he2 hn)
  · exact Or.inl h
  · exfalso
    have hfix : τ (σ (σ e)) = σ (σ e) := by rw [hτσ, hτσ, h, hσ.σ3]
    exact hσ.refl_ne hQ hτσ (hσ.σQ _ (hσ.σQ _ (hEQ he))) (hσ.sq_σσ he2) hn2 hfix
  · exact Or.inr (Or.inl h)
  · exfalso
    have hfix : τ (σ e) = σ e := by rw [hτσ, h, hσ.σ3]
    exact hσ.refl_ne hQ hτσ (hσ.σQ _ (hEQ he)) (hσ.sq_σ he2) hn1 hfix
  · exact Or.inr (Or.inr h)

end Act3

section Q2

variable {z : H} {Q K : Subgroup H} {σ : H ≃* H}

theorem two_mul_le_of_lt_of_dvd {a b : ℕ} (hb : 0 < b) (hab : a < b) (hdvd : a ∣ b) :
    2 * a ≤ b := by
  obtain ⟨m, rfl⟩ := hdvd
  rcases m with _ | _ | m
  · simp at hb
  · simp at hab
  · calc 2 * a = a * 2 := mul_comm _ _
      _ ≤ a * (m + 1 + 1) := Nat.mul_le_mul_left a (by omega)

theorem mem_centralizer_of_comm {a c : H} (hK : Subgroup.closure ({a, σ a} : Set H) = K)
    (h1 : c * a = a * c) (h2 : c * σ a = σ a * c) :
    c ∈ Subgroup.centralizer (K : Set H) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [← hK] at hy
  have hsub : ({a, σ a} : Set H) ⊆ (Subgroup.centralizer {c} : Subgroup H) := by
    intro t ht
    rcases ht with rfl | ht
    · exact Subgroup.mem_centralizer_singleton_iff.2 h1.symm
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact Subgroup.mem_centralizer_singleton_iff.2 h2.symm
  exact Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.closure_le _).2 hsub hy)

theorem Act3.exists_adjust (hQ : Q32Data z Q) (hσ : Act3 σ z Q) {a q : H} (haQ : a ∈ Q)
    (ha2 : a * a = z) (hq : q ∈ Q) :
    ∃ k : H, (k = 1 ∨ k = σ a ∨ k = a ∨ k = a * σ a) ∧
      (k * q) * a = a * (k * q) ∧ (k * q) * σ a = σ a * (k * q) := by
  have ha1Q : σ a ∈ Q := hσ.σQ a haQ
  have hnc : a * σ a ≠ σ a * a := hσ.noncomm hQ haQ ha2
  have hA : a * σ a = z * (σ a * a) := by
    rcases hQ.comm_cases haQ ha1Q with h | h
    · exact absurd h hnc
    · exact h
  have hA' : σ a * a = z * (a * σ a) := anti_symm' hQ.z_sq hA
  have hz := hQ.z_central
  have hz2 := hQ.z_sq
  have hCa : Commute a a := Commute.refl a
  have hCa1 : Commute (σ a) (σ a) := Commute.refl _
  rcases hQ.comm_cases hq haQ with hqa | hqa <;> rcases hQ.comm_cases hq ha1Q with hqb | hqb
  · refine ⟨1, Or.inl rfl, ?_, ?_⟩
    · rw [one_mul]; exact hqa
    · rw [one_mul]; exact hqb
  · refine ⟨a, Or.inr (Or.inr (Or.inl rfl)), ?_, ?_⟩
    · exact (Commute.mul_left hCa hqa).eq
    · exact mul_comm_of_anti_anti hz hz2 hA hqb
  · refine ⟨σ a, Or.inr (Or.inl rfl), ?_, ?_⟩
    · exact mul_comm_of_anti_anti hz hz2 hA' hqa
    · exact (Commute.mul_left hCa1 hqb).eq
  · have h1 : a * σ a * a = z * (a * (a * σ a)) := anti_mul_of_comm_anti hz rfl hA'
    have h1' : a * σ a * σ a = z * (σ a * (a * σ a)) := anti_mul_of_anti_comm hA rfl
    refine ⟨a * σ a, Or.inr (Or.inr (Or.inr rfl)), ?_, ?_⟩
    · exact mul_comm_of_anti_anti hz hz2 h1 hqa
    · exact mul_comm_of_anti_anti hz hz2 h1' hqb

theorem Act3.exists_mul_mem_Q2 [Finite H] (hQ : Q32Data z Q) (hσ : Act3 σ z Q) (hKQ : K ≤ Q)
    (hK8 : Nat.card K ≤ 8) {a : H} (haK : a ∈ K) (hσaK : σ a ∈ K) (ha2 : a * a = z) {q : H}
    (hq : q ∈ Q) : ∃ k ∈ K, k * q ∈ Q ⊓ Subgroup.centralizer (K : Set H) := by
  have hKcl : Subgroup.closure ({a, σ a} : Set H) = K :=
    closure_eq_of_card_le hQ.z_ne_one hQ.z_sq hK8 haK hσaK ha2 (hσ.noncomm hQ (hKQ haK) ha2)
  obtain ⟨k, hk, h1, h2⟩ := hσ.exists_adjust hQ (hKQ haK) ha2 hq
  have hkK : k ∈ K := by
    rcases hk with rfl | rfl | rfl | rfl
    · exact K.one_mem
    · exact hσaK
    · exact haK
    · exact K.mul_mem haK hσaK
  exact ⟨k, hkK, Q.mul_mem (hKQ hkK) hq, mem_centralizer_of_comm hKcl h1 h2⟩

theorem Act3.card_Q2_le [Finite H] (hQ : Q32Data z Q) (hσ : Act3 σ z Q) (hKQ : K ≤ Q)
    {a : H} (haK : a ∈ K) (hσaK : σ a ∈ K) (ha2 : a * a = z) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer (K : Set H)) ≤ 8 := by
  have hnc : a * σ a ≠ σ a * a := hσ.noncomm hQ (hKQ haK) ha2
  set A : Subgroup H := Q ⊓ Subgroup.centralizer {a} with hA
  set Q2 : Subgroup H := Q ⊓ Subgroup.centralizer (K : Set H) with hQ2
  have hAQ : A < Q := by
    refine lt_of_le_of_ne inf_le_left (fun h => hnc ?_)
    have : σ a ∈ A := h ▸ (hKQ hσaK)
    exact (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm
  have hQ2A : Q2 < A := by
    have hle : Q2 ≤ A := by
      intro c hc
      refine ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 hc.2 a haK).symm
    refine lt_of_le_of_ne hle (fun h => hnc ?_)
    have haA : a ∈ A := ⟨hKQ haK, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    have haQ2 : a ∈ Q2 := h ▸ haA
    exact (Subgroup.mem_centralizer_iff.1 haQ2.2 (σ a) hσaK).symm
  have h1 : Nat.card A < Nat.card Q := Subgroup.card_lt_of_lt hAQ
  have h2 : Nat.card Q2 < Nat.card A := Subgroup.card_lt_of_lt hQ2A
  have h3 : Nat.card A ∣ Nat.card Q := Subgroup.card_dvd_of_le hAQ.le
  have h4 : Nat.card Q2 ∣ Nat.card A := Subgroup.card_dvd_of_le hQ2A.le
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hQc := hQ.card_eq
  have h5 := two_mul_le_of_lt_of_dvd (by omega) h1 h3
  have h6 := two_mul_le_of_lt_of_dvd hpos h2 h4
  omega

theorem Q2_stable {φ : H ≃* H} (ψ : H → H) (hψφ : ∀ y, φ (ψ y) = y)
    (hψK : ∀ y ∈ K, ψ y ∈ K) (hφQ : ∀ c ∈ Q, φ c ∈ Q) {c : H}
    (hc : c ∈ Q ⊓ Subgroup.centralizer (K : Set H)) :
    φ c ∈ Q ⊓ Subgroup.centralizer (K : Set H) := by
  rw [Subgroup.mem_inf] at hc ⊢
  refine ⟨hφQ c hc.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := Subgroup.mem_centralizer_iff.1 hc.2 (ψ y) (hψK y hy)
  calc y * φ c = φ (ψ y) * φ c := by rw [hψφ]
    _ = φ (ψ y * c) := (map_mul φ _ _).symm
    _ = φ (c * ψ y) := by rw [h1]
    _ = φ c * φ (ψ y) := map_mul φ _ _
    _ = φ c * y := by rw [hψφ]

theorem Act3.exists_sq_mem_Q2 [Finite H] (hQ : Q32Data z Q) (hσ : Act3 σ z Q) (hKQ : K ≤ Q)
    (hK8 : Nat.card K = 8) {a : H} (haK : a ∈ K) (hσaK : σ a ∈ K) (ha2 : a * a = z) :
    ∃ b ∈ Q ⊓ Subgroup.centralizer (K : Set H), b * b = z := by
  by_contra hno
  push Not at hno
  have hzK : z ∈ K := ha2 ▸ K.mul_mem haK haK
  have hsq : ∀ c ∈ Q ⊓ Subgroup.centralizer (K : Set H), c * c = 1 := fun c hc =>
    (hQ.sq_mem c hc.1).resolve_right (hno c hc)
  have hab : ∀ c ∈ Q ⊓ Subgroup.centralizer (K : Set H),
      ∀ d ∈ Q ⊓ Subgroup.centralizer (K : Set H), c * d = d * c := by
    intro c hc d hd
    have hcd : c * d ∈ Q ⊓ Subgroup.centralizer (K : Set H) := Subgroup.mul_mem _ hc hd
    have h1 := hsq _ hcd
    have hc' : c⁻¹ = c := inv_eq_of_mul_eq_one_right (hsq c hc)
    have hd' : d⁻¹ = d := inv_eq_of_mul_eq_one_right (hsq d hd)
    calc c * d = (c * d)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = d * c := by rw [mul_inv_rev, hc', hd']
  have hQK : ∀ q ∈ Q, q ∈ K := by
    intro q hq
    obtain ⟨k, hk, hkq⟩ := hσ.exists_mul_mem_Q2 hQ hKQ hK8.le haK hσaK ha2 hq
    have hcen : ∀ y ∈ Q, (k * q) * y = y * (k * q) := by
      intro y hy
      obtain ⟨k', hk', hk'y⟩ := hσ.exists_mul_mem_Q2 hQ hKQ hK8.le haK hσaK ha2 hy
      have h1 : (k * q) * k'⁻¹ = k'⁻¹ * (k * q) :=
        (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hkq).2 k'⁻¹ (K.inv_mem hk')).symm
      have h2 : (k * q) * (k' * y) = (k' * y) * (k * q) := hab _ hkq _ hk'y
      calc (k * q) * y = (k * q) * (k'⁻¹ * (k' * y)) := by group
        _ = ((k * q) * k'⁻¹) * (k' * y) := by group
        _ = (k'⁻¹ * (k * q)) * (k' * y) := by rw [h1]
        _ = k'⁻¹ * ((k * q) * (k' * y)) := by group
        _ = k'⁻¹ * ((k' * y) * (k * q)) := by rw [h2]
        _ = y * (k * q) := by group
    rcases hQ.center_le (k * q) (Subgroup.mem_inf.1 hkq).1 hcen with h | h
    · have : q = k⁻¹ := by
        calc q = k⁻¹ * (k * q) := by group
          _ = k⁻¹ := by rw [h, mul_one]
      rw [this]
      exact K.inv_mem hk
    · have : q = k⁻¹ * z := by
        calc q = k⁻¹ * (k * q) := by group
          _ = k⁻¹ * z := by rw [h]
      rw [this]
      exact K.mul_mem (K.inv_mem hk) hzK
  have h1 := Subgroup.card_le_of_le (show Q ≤ K from fun q hq => hQK q hq)
  have h32 := hQ.card_eq
  omega

end Q2

section Rot

variable {z : H} {Q : Subgroup H} {σ τ : H ≃* H}

theorem Act3.exists_rot [Finite H] (hQ : Q32Data z Q) (hσ : Act3 σ z Q)
    (hτσ : ∀ q, τ (σ q) = σ (σ (τ q))) (hτz : τ z = z) {E : Subgroup H} (hE : Nat.card E ≤ 8)
    (hEQ : E ≤ Q) (hEσ : ∀ q ∈ E, σ q ∈ E) (hEτ : ∀ q ∈ E, τ q ∈ E) {e : H} (he : e ∈ E)
    (he2 : e * e = z) (hn : e * σ e = σ (σ e)) :
    ∃ e' ∈ E, e' * e' = z ∧ e' * σ e' = σ (σ e') ∧ τ e' = σ e' * z := by
  have hn1 : σ e * σ (σ e) = σ (σ (σ e)) := Act3.norm_σ hn
  have hn2 : σ (σ e) * σ (σ (σ e)) = σ (σ (σ (σ e))) := Act3.norm_σ hn1
  rcases hσ.refl_cls hQ hτσ hτz hE hEQ hEσ hEτ he he2 hn with h | h | h
  · refine ⟨σ e, hEσ e he, hσ.sq_σ he2, hn1, ?_⟩
    rw [hτσ, h]
    simp only [map_mul, hσ.σz]
  · exact ⟨e, he, he2, hn, h⟩
  · refine ⟨σ (σ e), hEσ _ (hEσ e he), hσ.sq_σσ he2, hn2, ?_⟩
    rw [hτσ, hτσ, h]
    simp only [map_mul, hσ.σz, hσ.σ3]

end Rot

section Conj

variable {z : H} {Q : Subgroup H}

theorem inv_conj_eq {x : H} (hx3 : x * x * x = 1) (w : H) :
    x⁻¹ * w * x = x * (x * w * x⁻¹) * x⁻¹ := by
  have hxi : x⁻¹ = x * x := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hx3)
  have hxx : x⁻¹ * x⁻¹ = x := by rw [← mul_inv_rev, ← hxi, inv_inv]
  calc x⁻¹ * w * x = (x * x) * w * (x⁻¹ * x⁻¹) := by rw [← hxi, hxx]
    _ = x * (x * w * x⁻¹) * x⁻¹ := by group

theorem act3_of_conj {σ : H ≃* H} {x : H} (hσ : ∀ q, σ q = x * q * x⁻¹) (hx3 : x * x * x = 1)
    (hzc : ∀ h : H, h * z = z * h) (hQn : ∀ g : H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hfix : ∀ q ∈ Q, q * x = x * q → q = 1 ∨ q = z) : Act3 σ z Q where
  σ3 q := by
    simp only [hσ]
    calc x * (x * (x * q * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * q * (x * x * x)⁻¹ := by group
      _ = q := by rw [hx3]; group
  σz := by
    rw [hσ, hzc x]
    group
  σQ q hq := by
    rw [hσ]
    exact hQn x q hq
  fix q hq h := by
    apply hfix q hq
    rw [hσ] at h
    calc q * x = (x * q * x⁻¹) * x := by rw [h]
      _ = x * q := by group

theorem conj_τσ {σ τ : H ≃* H} {x u : H} (hσ : ∀ q, σ q = x * q * x⁻¹)
    (hτ : ∀ q, τ q = u * q * u⁻¹) (hx3 : x * x * x = 1) (hu2 : u * u = 1)
    (hux : u * x * u = x⁻¹) (q : H) : τ (σ q) = σ (σ (τ q)) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have h1 : u * x * u⁻¹ = x⁻¹ := by rw [hui]; exact hux
  have h2 : u * x⁻¹ * u⁻¹ = x := by
    calc u * x⁻¹ * u⁻¹ = (u * x * u⁻¹)⁻¹ := by group
      _ = x := by rw [h1, inv_inv]
  simp only [hσ, hτ]
  calc u * (x * q * x⁻¹) * u⁻¹ = (u * x * u⁻¹) * (u * q * u⁻¹) * (u * x⁻¹ * u⁻¹) := by group
    _ = x⁻¹ * (u * q * u⁻¹) * x := by rw [h1, h2]
    _ = x * (x * (u * q * u⁻¹) * x⁻¹) * x⁻¹ := inv_conj_eq hx3 _

theorem conj_τ2 {τ : H ≃* H} {u : H} (hτ : ∀ q, τ q = u * q * u⁻¹) (hu2 : u * u = 1) (q : H) :
    τ (τ q) = q := by
  simp only [hτ]
  calc u * (u * q * u⁻¹) * u⁻¹ = (u * u) * q * (u * u)⁻¹ := by group
    _ = q := by rw [hu2]; group

theorem conj_τz {τ : H ≃* H} {u : H} (hτ : ∀ q, τ q = u * q * u⁻¹)
    (hzc : ∀ h : H, h * z = z * h) : τ z = z := by
  rw [hτ, hzc u]
  group

end Conj

section Rels

variable {z : H}

theorem conj_sq {x e : H} (hz : ∀ h : H, h * z = z * h) (he2 : e * e = z) :
    (x * e * x⁻¹) * (x * e * x⁻¹) = z := by
  calc (x * e * x⁻¹) * (x * e * x⁻¹) = x * (e * e) * x⁻¹ := by group
    _ = x * z * x⁻¹ := by rw [he2]
    _ = z := by rw [hz x]; group

theorem sq_rel {e c : H} (he : e * e = z) (hc : c * c = z) : e * e * c⁻¹ * c⁻¹ = 1 := by
  calc e * e * c⁻¹ * c⁻¹ = (e * e) * (c * c)⁻¹ := by group
    _ = 1 := by rw [he, hc]; exact mul_inv_cancel z

theorem pow4_eq_one (hz2 : z * z = 1) {e : H} (he : e * e = z) : e ^ 4 = 1 := by
  calc e ^ 4 = (e * e) * (e * e) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [he, hz2]

theorem rel3 (hz2 : z * z = 1) {x e : H} (he2 : e * e = z)
    (hanti : (x * e * x⁻¹) * e = z * (e * (x * e * x⁻¹))) :
    (x * e * x⁻¹) * e * (x * e⁻¹ * x⁻¹) * e = 1 := by
  calc (x * e * x⁻¹) * e * (x * e⁻¹ * x⁻¹) * e
      = ((x * e * x⁻¹) * e * (x * e * x⁻¹)⁻¹) * e := by group
    _ = (z * (e * (x * e * x⁻¹)) * (x * e * x⁻¹)⁻¹) * e := by rw [hanti]
    _ = z * (e * e) := by group
    _ = 1 := by rw [he2, hz2]

theorem rel4 {x e : H} (hn : e * (x * e * x⁻¹) = x * (x * e * x⁻¹) * x⁻¹) :
    e * (x * e * x⁻¹) * (x * x * e⁻¹ * x⁻¹ * x⁻¹) = 1 := by
  rw [hn]
  group

theorem comm_rel {g h : H} (hgh : g * h = h * g) : g * h * g⁻¹ * h⁻¹ = 1 := by
  calc g * h * g⁻¹ * h⁻¹ = (g * h) * (h * g)⁻¹ := by group
    _ = 1 := by rw [hgh]; exact mul_inv_cancel _

theorem rel_u {x u e : H} (hz : ∀ h : H, h * z = z * h) (hz2 : z * z = 1) (he2 : e * e = z)
    (hue : u * e * u = (x * e * x⁻¹) * z) : u * e * u * (x * e * x⁻¹) = 1 := by
  rw [hue]
  have h1 := conj_sq (x := x) hz he2
  calc (x * e * x⁻¹) * z * (x * e * x⁻¹) = (x * e * x⁻¹) * (z * (x * e * x⁻¹)) := mul_assoc _ _ _
    _ = (x * e * x⁻¹) * ((x * e * x⁻¹) * z) := by rw [hz (x * e * x⁻¹)]
    _ = ((x * e * x⁻¹) * (x * e * x⁻¹)) * z := (mul_assoc _ _ _).symm
    _ = z * z := by rw [h1]
    _ = 1 := hz2

end Rels

section Finish

variable {z : H} {Q : Subgroup H}

theorem exists_hPres_of_data [Finite H] (hQ : Q32Data z Q)
    (hQn : ∀ g : H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    {K : Subgroup H} (hKQ : K ≤ Q) (hKn : ∀ g : H, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hK8 : Nat.card K = 8) {x u a : H} (hx3 : x * x * x = 1)
    (hfix : ∀ q ∈ Q, q * x = x * q → q = 1 ∨ q = z) (hu2 : u * u = 1) (hux : u * x * u = x⁻¹)
    (haK : a ∈ K) (ha2 : a * a = z) (han : a * (x * a * x⁻¹) = x * (x * a * x⁻¹) * x⁻¹)
    (hua : u * a * u = (x * a * x⁻¹) * z)
    (hgen : ∀ P : Subgroup H, Q ≤ P → x ∈ P → u ∈ P → P = ⊤) :
    ∃ b : H, HPres a b x u ∧ Subgroup.closure ({a, b, x, u} : Set H) = ⊤ := by
  obtain ⟨σ, hσe⟩ : ∃ σ : H ≃* H, ∀ q, σ q = x * q * x⁻¹ :=
    ⟨MulAut.conj x, fun q => by simp [MulAut.conj_apply]⟩
  obtain ⟨τ, hτe⟩ : ∃ τ : H ≃* H, ∀ q, τ q = u * q * u⁻¹ :=
    ⟨MulAut.conj u, fun q => by simp [MulAut.conj_apply]⟩
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hz := hQ.z_central
  have hz2 := hQ.z_sq
  have hσ : Act3 σ z Q := act3_of_conj hσe hx3 hz hQn hfix
  have hτσ : ∀ q, τ (σ q) = σ (σ (τ q)) := conj_τσ hσe hτe hx3 hu2 hux
  have hτ2 : ∀ q, τ (τ q) = q := conj_τ2 hτe hu2
  have hτz : τ z = z := conj_τz hτe hz
  have hn : a * σ a = σ (σ a) := by simp only [hσe]; exact han
  have hKσ : ∀ q ∈ K, σ q ∈ K := fun q hq => by rw [hσe]; exact hKn x q hq
  have hσaK : σ a ∈ K := hKσ a haK
  have haQ : a ∈ Q := hKQ haK
  set Q2 : Subgroup H := Q ⊓ Subgroup.centralizer (K : Set H) with hQ2
  have hQ2σ : ∀ c ∈ Q2, σ c ∈ Q2 := fun c hc =>
    Q2_stable (fun y => σ (σ y)) (fun y => hσ.σ3 y) (fun y hy => hKσ _ (hKσ y hy)) hσ.σQ hc
  have hQ2τ : ∀ c ∈ Q2, τ c ∈ Q2 := fun c hc =>
    Q2_stable τ hτ2 (fun y hy => by rw [hτe]; exact hKn u y hy)
      (fun q hq => by rw [hτe]; exact hQn u q hq) hc
  have hE8 : Nat.card Q2 ≤ 8 := hσ.card_Q2_le hQ hKQ haK hσaK ha2
  have hzQ2 : z ∈ Q2 := Subgroup.mem_inf.2 ⟨hQ.z_mem, Subgroup.mem_centralizer_iff.2 (fun y _ => hz y)⟩
  obtain ⟨b₀, hb₀Q2, hb₀2⟩ := hσ.exists_sq_mem_Q2 hQ hKQ hK8 haK hσaK ha2
  obtain ⟨b₁, hb₁, hb₁2, hb₁n⟩ := hσ.exists_norm hQ (Subgroup.mem_inf.1 hb₀Q2).1 hb₀2
  have hb₁Q2 : b₁ ∈ Q2 := by
    rcases hb₁ with h | h
    · rw [h]; exact hb₀Q2
    · rw [h]; exact Q2.mul_mem hb₀Q2 hzQ2
  obtain ⟨b, hbQ2, hb2, hbn, hτb⟩ :=
    hσ.exists_rot hQ hτσ hτz hE8 inf_le_left hQ2σ hQ2τ hb₁Q2 hb₁2 hb₁n
  have hbσQ2 : σ b ∈ Q2 := hQ2σ b hbQ2
  have hbσσQ2 : σ (σ b) ∈ Q2 := hQ2σ _ hbσQ2
  have hbQ : b ∈ Q := (Subgroup.mem_inf.1 hbQ2).1
  have hab : a * b = b * a := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hbQ2).2 a haK
  have hab1 : a * σ b = σ b * a :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hbσQ2).2 a haK
  have hab2 : a * σ (σ b) = σ (σ b) * a :=
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hbσσQ2).2 a haK
  have hAa : (x * a * x⁻¹) * a = z * (a * (x * a * x⁻¹)) := by
    have hnc := hσ.noncomm hQ haQ ha2
    rcases hQ.comm_cases (hσ.σQ a haQ) haQ with h | h
    · exact absurd h.symm hnc
    · simpa only [hσe] using h
  have hAb : (x * b * x⁻¹) * b = z * (b * (x * b * x⁻¹)) := by
    have hnc := hσ.noncomm hQ hbQ hb2
    rcases hQ.comm_cases (hσ.σQ b hbQ) hbQ with h | h
    · exact absurd h.symm hnc
    · simpa only [hσe] using h
  have hbn' : b * (x * b * x⁻¹) = x * (x * b * x⁻¹) * x⁻¹ := by simp only [hσe] at hbn; exact hbn
  have hub : u * b * u = (x * b * x⁻¹) * z := by
    have := hτb
    rw [hτe, hσe, hui] at this
    exact this
  have hP : HPres a b x u := by
    refine ⟨pow4_eq_one hz2 ha2, sq_rel (conj_sq hz ha2) ha2, rel3 hz2 ha2 hAa, rel4 han, hx3,
      pow4_eq_one hz2 hb2, sq_rel hb2 ha2, sq_rel (conj_sq hz hb2) ha2, rel3 hz2 hb2 hAb,
      rel4 hbn', comm_rel hab, ?_, ?_, hu2, ?_, rel_u hz hz2 ha2 hua, rel_u hz hz2 hb2 hub⟩
    · have h1 : a * (x * b * x⁻¹) = (x * b * x⁻¹) * a := by simpa only [hσe] using hab1
      calc a * (x * b * x⁻¹) * a⁻¹ * (x * b⁻¹ * x⁻¹)
          = a * (x * b * x⁻¹) * a⁻¹ * (x * b * x⁻¹)⁻¹ := by group
        _ = 1 := comm_rel h1
    · have e2 : x * x * b * x⁻¹ * x⁻¹ = σ (σ b) := by simp only [hσe]; group
      have e2' : x * x * b⁻¹ * x⁻¹ * x⁻¹ = (σ (σ b))⁻¹ := by
        rw [← e2]
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [e2, e2']
      exact comm_rel hab2
    · calc u * x * u * x = x⁻¹ * x := by rw [hux]
        _ = 1 := inv_mul_cancel x
  refine ⟨b, hP, ?_⟩
  have hKcl : Subgroup.closure ({a, σ a} : Set H) = K :=
    closure_eq_of_card_le hQ.z_ne_one hz2 hK8.le haK hσaK ha2 (hσ.noncomm hQ haQ ha2)
  have hQ2cl : Subgroup.closure ({b, σ b} : Set H) = Q2 :=
    closure_eq_of_card_le hQ.z_ne_one hz2 hE8 hbQ2 hbσQ2 hb2 (hσ.noncomm hQ hbQ hb2)
  set P : Subgroup H := Subgroup.closure ({a, b, x, u} : Set H) with hPdef
  have haP : a ∈ P := Subgroup.subset_closure (by simp)
  have hbP : b ∈ P := Subgroup.subset_closure (by simp)
  have hxP : x ∈ P := Subgroup.subset_closure (by simp)
  have huP : u ∈ P := Subgroup.subset_closure (by simp)
  have hσP : ∀ q ∈ P, σ q ∈ P := fun q hq => by
    rw [hσe]
    exact P.mul_mem (P.mul_mem hxP hq) (P.inv_mem hxP)
  have hKP : K ≤ P := by
    rw [← hKcl, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact haP
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hσP a haP
  have hQ2P : Q2 ≤ P := by
    rw [← hQ2cl, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | ht
    · exact hbP
    · rw [Set.mem_singleton_iff] at ht
      rw [ht]
      exact hσP b hbP
  have hQP : Q ≤ P := by
    intro q hq
    obtain ⟨k, hk, hkq⟩ := hσ.exists_mul_mem_Q2 hQ hKQ hK8.le haK hσaK ha2 hq
    have : q = k⁻¹ * (k * q) := by group
    rw [this]
    exact P.mul_mem (P.inv_mem (hKP hk)) (hQ2P hkq)
  exact hgen P hQP hxP huP

end Finish

section Perm3

theorem perm3_cycle_conj_cube :
    ∀ r s : Equiv.Perm (Fin 3), r * r * r = 1 → r ≠ 1 → s * s = 1 → s ≠ 1 →
      (r⁻¹ * s * r * s) * (r⁻¹ * s * r * s) * (r⁻¹ * s * r * s) = 1 := by
  decide +kernel

theorem perm3_cycle_conj_ne :
    ∀ r s : Equiv.Perm (Fin 3), r * r * r = 1 → r ≠ 1 → s * s = 1 → s ≠ 1 →
      r⁻¹ * s * r * s ≠ 1 := by
  decide +kernel

theorem perm3_gen :
    ∀ r s y : Equiv.Perm (Fin 3), r ≠ 1 → r * r * r = 1 → s ≠ 1 → s * s = 1 →
      (y = 1 ∨ y = r ∨ y = r * r ∨ y = s ∨ y = s * r ∨ y = s * r * r) := by decide

theorem perm3_inv_ne :
    ∀ r s : Equiv.Perm (Fin 3), r ≠ 1 → r * r * r = 1 → s = 1 → s * r * s = r⁻¹ → False := by
  decide

theorem perm3_exists_cycle : ∃ r : Equiv.Perm (Fin 3), r * r * r = 1 ∧ r ≠ 1 := by decide

theorem pow32_ne_one {G : Type*} [Group G] {r : G} (h3 : r * r * r = 1) (h1 : r ≠ 1) :
    r ^ 32 ≠ 1 := by
  have h32 : r ^ 32 = r * r := by
    calc r ^ 32 = (r * r * r) ^ 10 * (r * r) := by
          rw [← pow_three', ← pow_mul, ← pow_two, ← pow_add]
      _ = r * r := by rw [h3, one_pow, one_mul]
  rw [h32]
  intro h2
  apply h1
  calc r = r * (r * r) := by rw [h2, mul_one]
    _ = r * r * r := (mul_assoc _ _ _).symm
    _ = 1 := h3

end Perm3

section Main

variable {z : H} {Q : Subgroup H}

theorem top_of_perm {ρ : H →* Equiv.Perm (Fin 3)} (hρk : ∀ h : H, ρ h = 1 ↔ h ∈ Q) {x u : H}
    (hx : ρ x ≠ 1) (hx3 : x * x * x = 1) (hu2 : u * u = 1) (hux : u * x * u = x⁻¹)
    {P : Subgroup H} (hQP : Q ≤ P) (hxP : x ∈ P) (huP : u ∈ P) : P = ⊤ := by
  have hx3' : ρ x * ρ x * ρ x = 1 := by rw [← map_mul, ← map_mul, hx3, map_one]
  have hu2' : ρ u * ρ u = 1 := by rw [← map_mul, hu2, map_one]
  have hu1 : ρ u ≠ 1 := by
    intro h
    refine perm3_inv_ne (ρ x) (ρ u) hx hx3' h ?_
    rw [← map_mul, ← map_mul, hux, map_inv]
  rw [eq_top_iff]
  intro h _
  have hy := perm3_gen (ρ x) (ρ u) (ρ h) hx hx3' hu1 hu2'
  have hex : ∃ p ∈ P, ρ p = ρ h := by
    rcases hy with hy | hy | hy | hy | hy | hy
    · exact ⟨1, P.one_mem, by rw [map_one, hy]⟩
    · exact ⟨x, hxP, hy.symm⟩
    · exact ⟨x * x, P.mul_mem hxP hxP, by rw [map_mul, hy]⟩
    · exact ⟨u, huP, hy.symm⟩
    · exact ⟨u * x, P.mul_mem huP hxP, by rw [map_mul, hy]⟩
    · exact ⟨u * x * x, P.mul_mem (P.mul_mem huP hxP) hxP, by rw [map_mul, map_mul, hy]⟩
  obtain ⟨p, hpP, hp⟩ := hex
  have hq : p⁻¹ * h ∈ Q := (hρk _).1 (by rw [map_mul, map_inv, hp, inv_mul_cancel])
  have h' : p * (p⁻¹ * h) ∈ P := P.mul_mem hpP (hQP hq)
  rwa [mul_inv_cancel_left] at h'

theorem exists_hPres_of_core [Finite H] {K : Subgroup H} {ρ : H →* Equiv.Perm (Fin 3)}
    (hQ : Q32Data z Q) (hρs : Function.Surjective ρ) (hρk : ∀ h : H, ρ h = 1 ↔ h ∈ Q)
    (hsyl : ∀ x : H, x ≠ 1 → x * x * x = 1 → ∀ q ∈ Q, q * x = x * q → q = 1 ∨ q = z)
    (hKQ : K ≤ Q) (hKn : K.Normal) (hK8 : Nat.card K = 8) (hKa : ∃ a ∈ K, a * a = z)
    {v : H} (hv2 : v * v = 1) (hvQ : v ∉ Q) :
    ∃ a b x u : H, HPres a b x u ∧ a * a = z ∧ Subgroup.closure ({a, b, x, u} : Set H) = ⊤ := by
  have hz := hQ.z_central
  have hz2 := hQ.z_sq
  have hQn : ∀ g : H, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
    intro g q hq
    rw [← hρk] at hq ⊢
    rw [map_mul, map_mul, hq, mul_one, map_inv, mul_inv_cancel]
  have hKn' : ∀ g : H, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g k hk => hKn.conj_mem k hk g
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hsv : ρ v ≠ 1 := fun h => hvQ ((hρk v).1 h)
  have hsv2 : ρ v * ρ v = 1 := by rw [← map_mul, hv2, map_one]
  obtain ⟨r₀, hr₀3, hr₀1⟩ := perm3_exists_cycle
  obtain ⟨x₀, hx₀⟩ := hρs r₀
  obtain ⟨c, hc⟩ : ∃ c : H, c = x₀⁻¹ * v * x₀ * v := ⟨_, rfl⟩
  have hρc : ρ c = r₀⁻¹ * ρ v * r₀ * ρ v := by
    rw [hc]
    simp only [map_mul, map_inv, hx₀]
  have hc3' : ρ c * ρ c * ρ c = 1 := by
    rw [hρc]
    exact perm3_cycle_conj_cube r₀ (ρ v) hr₀3 hr₀1 hsv2 hsv
  have hc1' : ρ c ≠ 1 := by
    rw [hρc]
    exact perm3_cycle_conj_ne r₀ (ρ v) hr₀3 hr₀1 hsv2 hsv
  have hc3Q : c * c * c ∈ Q := (hρk _).1 (by rw [map_mul, map_mul]; exact hc3')
  have hc96 : (c * c * c) ^ 32 = 1 := by
    have := pow_card_eq_one' (G := ↥Q) (x := (⟨c * c * c, hc3Q⟩ : ↥Q))
    rw [hQ.card_eq] at this
    simpa using congrArg Subtype.val this
  have hvc : v * c * v = c⁻¹ := by
    have h1 : v * c * v⁻¹ = v * x₀⁻¹ * v * x₀ := by
      rw [hc]
      group
    have h2 : c⁻¹ = v * x₀⁻¹ * v * x₀ := by
      rw [hc]
      calc (x₀⁻¹ * v * x₀ * v)⁻¹ = v⁻¹ * x₀⁻¹ * v⁻¹ * x₀ := by group
        _ = v * x₀⁻¹ * v * x₀ := by rw [hvi]
    calc v * c * v = v * c * v⁻¹ := by rw [hvi]
      _ = v * x₀⁻¹ * v * x₀ := h1
      _ = c⁻¹ := h2.symm
  obtain ⟨x, hxdef⟩ : ∃ x : H, x = c ^ 32 := ⟨_, rfl⟩
  have hx3 : x * x * x = 1 := by
    calc x * x * x = (c * c * c) ^ 32 := by
          rw [hxdef, ← pow_add, ← pow_add, ← pow_three', ← pow_mul]
      _ = 1 := hc96
  have hρx : ρ x ≠ 1 := by
    rw [hxdef, map_pow]
    exact pow32_ne_one hc3' hc1'
  have hx1 : x ≠ 1 := fun h => hρx (by rw [h, map_one])
  have hvx : v * x * v = x⁻¹ := by
    have h1 : (v * c * v⁻¹) ^ 32 = v * c ^ 32 * v⁻¹ := conj_pow
    rw [hvi, hvc, inv_pow] at h1
    rw [hxdef]
    exact h1.symm
  have hfix : ∀ q ∈ Q, q * x = x * q → q = 1 ∨ q = z := hsyl x hx1 hx3
  obtain ⟨σ, hσe⟩ : ∃ σ : H ≃* H, ∀ q, σ q = x * q * x⁻¹ :=
    ⟨MulAut.conj x, fun q => by simp [MulAut.conj_apply]⟩
  obtain ⟨τ, hτe⟩ : ∃ τ : H ≃* H, ∀ q, τ q = v * q * v⁻¹ :=
    ⟨MulAut.conj v, fun q => by simp [MulAut.conj_apply]⟩
  have hσ : Act3 σ z Q := act3_of_conj hσe hx3 hz hQn hfix
  have hτσ : ∀ q, τ (σ q) = σ (σ (τ q)) := conj_τσ hσe hτe hx3 hv2 hvx
  have hτz : τ z = z := conj_τz hτe hz
  obtain ⟨e, he, he2⟩ := hKa
  have hzK : z ∈ K := he2 ▸ K.mul_mem he he
  obtain ⟨e₁, he₁, he₁2, he₁n⟩ := hσ.exists_norm hQ (hKQ he) he2
  have he₁K : e₁ ∈ K := by
    rcases he₁ with h | h
    · rw [h]; exact he
    · rw [h]; exact K.mul_mem he hzK
  have hKσ : ∀ q ∈ K, σ q ∈ K := fun q hq => by rw [hσe]; exact hKn' x q hq
  have hKτ : ∀ q ∈ K, τ q ∈ K := fun q hq => by rw [hτe]; exact hKn' v q hq
  obtain ⟨a, haK, ha2, han, hτa⟩ :=
    hσ.exists_rot hQ hτσ hτz hK8.le hKQ hKσ hKτ he₁K he₁2 he₁n
  have han' : a * (x * a * x⁻¹) = x * (x * a * x⁻¹) * x⁻¹ := by
    simp only [hσe] at han
    exact han
  have hua : v * a * v = (x * a * x⁻¹) * z := by
    have := hτa
    rw [hτe, hσe, hvi] at this
    exact this
  obtain ⟨b, hP, hcl⟩ := exists_hPres_of_data hQ hQn hKQ hKn' hK8 hx3 hfix hv2 hvx haK ha2 han' hua
    (fun P hQP hxP huP => top_of_perm hρk hρx hx3 hv2 hvx hQP hxP huP)
  exact ⟨a, b, x, v, hP, ha2, hcl⟩

end Main

end CFSG.Quasithin
