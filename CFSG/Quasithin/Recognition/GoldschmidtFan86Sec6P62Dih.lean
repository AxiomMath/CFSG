module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Swap

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P62

theorem inv_of_conj {Q : Type*} [Group Q] {σ τ : Q} (h5 : orderOf σ = 5) (h2 : τ * τ = 1)
    {i : ℕ} (hi : τ * σ * τ⁻¹ = σ ^ i) (hne : τ * σ * τ⁻¹ ≠ σ) : τ * σ * τ⁻¹ = σ⁻¹ := by
  have hτ : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right h2
  have h1 : σ ^ (i * i) = σ ^ 1 := by
    rw [pow_one, pow_mul, ← hi, conj_pow, ← hi, hτ]
    calc τ * (τ * σ * τ) * τ = (τ * τ) * σ * (τ * τ) := by group
      _ = σ := by rw [h2]; group
  have h3 : i * i ≡ 1 [MOD 5] := by
    have := (pow_eq_pow_iff_modEq).1 h1
    rwa [h5] at this
  have h4 : i % 5 = 1 ∨ i % 5 = 4 := by
    have h := h3
    unfold Nat.ModEq at h
    rw [Nat.mul_mod] at h
    have hlt : i % 5 < 5 := Nat.mod_lt _ (by norm_num)
    generalize i % 5 = m at h hlt ⊢
    interval_cases m <;> simp_all
  have hpow : σ ^ i = σ ^ (i % 5) := by rw [← h5, pow_mod_orderOf]
  have hσ5 : σ ^ 5 = 1 := by rw [← h5]; exact pow_orderOf_eq_one σ
  rcases h4 with h | h
  · exact absurd (by rw [hi, hpow, h, pow_one]) hne
  · rw [hi, hpow, h]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hσ5)

theorem exists_swap (F : FanTree Γ G) {v : V} (hv : valence Γ v = 5) {a b : V} (ha : Γ.Adj v a)
    (hb : Γ.Adj v b) :
    ∃ s ∈ MulAction.stabilizer G v, s • a = b ∧ s • b = a ∧ s * s ∈ nbrStab Γ G v ∧
      ∃ c, Γ.Adj v c ∧ s • c = c := by
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence v
  obtain ⟨t, ⟨htv, hta⟩, htn, ht2⟩ := exists_reflection F ha
  have hfin : Finite (Γ.neighborSet v) := F.finite_neighborSet v
  let _ : Fintype (Γ.neighborSet v) := Fintype.ofFinite _
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ := F.localHom v ⟨x, hx⟩ with hσ
  set τ := F.localHom v ⟨t, htv⟩ with hτ
  have hσo : orderOf σ = 5 := by rw [hσ, F.orderOf_localHom hx hxo, hv]
  have htt : τ * τ = 1 := by
    rw [hτ, ← map_mul]
    exact MonoidHom.mem_ker.1 ((F.mem_ker_localHom v (⟨t, htv⟩ * ⟨t, htv⟩)).2 ht2)
  have hτ1 : τ ≠ 1 := fun h => htn ((F.mem_ker_localHom v ⟨t, htv⟩).1 (MonoidHom.mem_ker.2 h))
  have hτa : τ ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext (MulAction.mem_stabilizer_iff.1 hta)
  have hpow : ∀ (j : ℕ) (p : Γ.neighborSet v), ((σ ^ j) p : V) = x ^ j • (p : V) :=
    fun j p => F.localHom_pow_apply_coe v ⟨x, hx⟩ j p
  obtain ⟨i, k, hk, hconj⟩ := F.conj_mem_pow_mul_nbrStab hx hxo htv
  have hK : F.localHom v ⟨k, F.nbrStab_le_stabilizer v hk⟩ = 1 :=
    MonoidHom.mem_ker.1 ((F.mem_ker_localHom v _).2 hk)
  have e : (⟨t, htv⟩ : MulAction.stabilizer G v) * ⟨x, hx⟩ * ⟨t, htv⟩⁻¹ =
      ⟨x, hx⟩ ^ i * ⟨k, F.nbrStab_le_stabilizer v hk⟩ := Subtype.ext (by simpa using hconj)
  have hconj' : τ * σ * τ⁻¹ = σ ^ i := by
    have := congrArg (F.localHom v) e
    simp only [map_mul, map_pow, map_inv, hK, mul_one] at this
    exact this
  have hne' : τ * σ * τ⁻¹ ≠ σ := by
    intro h
    apply hτ1
    have hc : τ * σ = σ * τ := mul_inv_eq_iff_eq_mul.1 h
    ext p
    obtain ⟨j, hj⟩ := F.exists_pow_smul_eq hx hxo ha p.2
    have hp : (σ ^ j) ⟨a, ha⟩ = p := Subtype.ext (by rw [hpow, hj])
    rw [← hp]
    have := congrArg (fun q : Equiv.Perm (Γ.neighborSet v) => q ⟨a, ha⟩)
      ((Commute.pow_right (show Commute τ σ from hc) j).eq)
    simp only [Equiv.Perm.mul_apply, hτa] at this
    rw [this]
    rfl
  have hinv := inv_of_conj hσo htt hconj' hne'
  obtain ⟨j, hj⟩ := F.exists_pow_smul_eq hx hxo ha hb
  have hρa : (σ ^ j) ⟨a, ha⟩ = ⟨b, hb⟩ := Subtype.ext (by rw [hpow, hj])
  have hτρ : τ * σ ^ j = (σ ^ j)⁻¹ * τ := by
    have : τ * σ ^ j * τ⁻¹ = (σ ^ j)⁻¹ := by rw [← conj_pow, hinv, inv_pow]
    exact mul_inv_eq_iff_eq_mul.1 this
  have hss : σ ^ j * τ * (σ ^ j * τ) = 1 := by
    calc σ ^ j * τ * (σ ^ j * τ) = σ ^ j * (τ * σ ^ j) * τ := by group
      _ = σ ^ j * ((σ ^ j)⁻¹ * τ) * τ := by rw [hτρ]
      _ = τ * τ := by group
      _ = 1 := htt
  obtain ⟨c, hc⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (σ := σ ^ j * τ) (by rw [Fintype.card_eq_nat_card]; rcases F.valence v with h | h <;> omega)
    (by rw [pow_one, sq, hss])
  have hs : x ^ j * t ∈ MulAction.stabilizer G v :=
    (MulAction.stabilizer G v).mul_mem ((MulAction.stabilizer G v).pow_mem hx j) htv
  have hlift : F.localHom v ⟨x ^ j * t, hs⟩ = σ ^ j * τ := by
    have : (⟨x ^ j * t, hs⟩ : MulAction.stabilizer G v) = ⟨x, hx⟩ ^ j * ⟨t, htv⟩ := Subtype.ext rfl
    rw [this, map_mul, map_pow]
  have happ : ∀ p : Γ.neighborSet v, ((σ ^ j * τ) p : V) = (x ^ j * t) • (p : V) := by
    intro p
    rw [← hlift]
    rfl
  refine ⟨x ^ j * t, hs, ?_, ?_, ?_, c.1, c.2, ?_⟩
  · rw [← happ ⟨a, ha⟩, Equiv.Perm.mul_apply, hτa, hρa]
  · have h1 : τ ⟨b, hb⟩ = (σ ^ j)⁻¹ ⟨a, ha⟩ := by
      rw [← hρa]
      have := congrArg (fun q : Equiv.Perm (Γ.neighborSet v) => q ⟨a, ha⟩) hτρ
      simp only [Equiv.Perm.mul_apply, hτa] at this
      exact this
    rw [← happ ⟨b, hb⟩, Equiv.Perm.mul_apply, h1]
    simp
  · have : F.localHom v (⟨x ^ j * t, hs⟩ * ⟨x ^ j * t, hs⟩) = 1 := by rw [map_mul, hlift, hss]
    exact (F.mem_ker_localHom v _).1 (MonoidHom.mem_ker.2 this)
  · rw [← happ c, hc]

end P62

end CFSG.Quasithin.Fan86
