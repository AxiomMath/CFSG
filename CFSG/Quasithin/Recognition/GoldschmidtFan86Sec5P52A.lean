module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv

theorem units_eq_neg_one {p : ℕ} (hp : p = 3 ∨ p = 5) (u : (ZMod p)ˣ) (h2 : u ^ 2 = 1)
    (h1 : u ≠ 1) : u = -1 := by
  rcases hp with rfl | rfl <;> revert u <;> decide

theorem val_neg_one_units {p : ℕ} (hp : p = 3 ∨ p = 5) :
    (((-1 : (ZMod p)ˣ) : (ZMod p)) : ZMod p).val = p - 1 := by
  rcases hp with rfl | rfl <;> decide


variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_conjChar_exp {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hxo : orderOf x = Fan86.valence Γ v) :
    ∃ ψ : MulAction.stabilizer G v →* (ZMod (Fan86.valence Γ v))ˣ,
      (∀ g : MulAction.stabilizer G v, (g : G) ∈ nbrStab Γ G v ↔
        ψ g = 1 ∧ ∃ a, Γ.Adj v a ∧ (g : G) • a = a) ∧
      ∀ g : MulAction.stabilizer G v, ∃ k ∈ nbrStab Γ G v,
        (g : G) * x * (g : G)⁻¹ = x ^ ((ψ g : ZMod (Fan86.valence Γ v)).val) * k := by
  have hp := F.valence_isPrime v
  have : Fact (Fan86.valence Γ v).Prime := ⟨hp⟩
  have := F.finite_neighborSet v
  let D : FrobPrime.Data (Γ.neighborSet v) (Fan86.valence Γ v) :=
    { Q := (F.localHom v).range
      σ := F.localHom v ⟨x, hx⟩
      σ_mem := MonoidHom.mem_range.2 ⟨_, rfl⟩
      card_eq := rfl
      orderOf_σ := F.orderOf_localHom hx hxo
      conj := FrobPrime.conj_pow_of_frobenius hp rfl (F.localHom v).range
        (F.localHom_frobenius v) (MonoidHom.mem_range.2 ⟨_, rfl⟩) (F.orderOf_localHom hx hxo) }
  refine ⟨D.conjChar.comp (F.localHom v).rangeRestrict, fun g => ⟨fun hK => ?_, ?_⟩, fun g => ?_⟩
  · have hker : F.localHom v g = 1 := MonoidHom.mem_ker.1 ((F.mem_ker_localHom v g).2 hK)
    have h1 : (F.localHom v).rangeRestrict g = 1 := Subtype.ext hker
    obtain ⟨a, ha⟩ := F.exists_adj v
    exact ⟨by rw [MonoidHom.comp_apply, h1, map_one], a, ha, hK a ha⟩
  · rintro ⟨h1, a, ha, h2⟩
    have h3 := D.eq_one_of_conjChar_eq_one (q := (F.localHom v).rangeRestrict g) h1
      (a := ⟨a, ha⟩) (Subtype.ext h2)
    exact (F.mem_ker_localHom v g).1 (MonoidHom.mem_ker.2 h3)
  · let X : MulAction.stabilizer G v := ⟨x, hx⟩
    set n : ℕ := (((D.conjChar.comp (F.localHom v).rangeRestrict) g : (ZMod (Fan86.valence Γ v))ˣ) :
      ZMod (Fan86.valence Γ v)).val with hn
    have hspec := D.conjChar_spec ((F.localHom v).rangeRestrict g)
    have hk : (X ^ n)⁻¹ * (g * X * g⁻¹) ∈ (F.localHom v).ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv, map_pow]
      have h1 : F.localHom v g * F.localHom v X * (F.localHom v g)⁻¹ = (F.localHom v X) ^ n :=
        hspec
      rw [h1]
      simp
    refine ⟨((X ^ n)⁻¹ * (g * X * g⁻¹) : MulAction.stabilizer G v), (F.mem_ker_localHom v _).1 hk,
      ?_⟩
    show (g : G) * x * (g : G)⁻¹ = x ^ n * ((x ^ n)⁻¹ * ((g : G) * x * (g : G)⁻¹))
    rw [mul_inv_cancel_left]

theorem exists_inverted {v : V} {z x : G} (hz : z ∈ MulAction.stabilizer G v)
    (hzz : z * z = 1) (hza : ∃ a, Γ.Adj v a ∧ z • a = a) (hzK : z ∉ nbrStab Γ G v)
    (hx : x ∈ MulAction.stabilizer G v) (hxo : orderOf x = Fan86.valence Γ v) :
    ∃ x₀ ∈ MulAction.stabilizer G v, orderOf x₀ = Fan86.valence Γ v ∧ z * x₀ * z⁻¹ = x₀⁻¹ := by
  have hp := F.valence_isPrime v
  have hp35 : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  obtain ⟨ψ, hψK, hψe⟩ := F.exists_conjChar_exp hx hxo
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hψz : ψ ⟨z, hz⟩ = -1 := by
    refine units_eq_neg_one hp35 _ ?_ ?_
    · rw [← map_pow]
      have : (⟨z, hz⟩ : MulAction.stabilizer G v) ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hzz
      rw [this, map_one]
    · intro h1
      exact hzK ((hψK ⟨z, hz⟩).2 ⟨h1, hza⟩)
  obtain ⟨k, hkK, hzx⟩ := hψe ⟨z, hz⟩
  rw [hψz, val_neg_one_units hp35] at hzx
  have hxp : x ^ Fan86.valence Γ v = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hxK : x ∉ nbrStab Γ G v := F.not_mem_nbrStab_of_orderOf hx hxo
  have hzx' : z * x * z = x ^ (Fan86.valence Γ v - 1) * k := by
    simpa [hz1] using hzx
  have hp3 : 3 ≤ Fan86.valence Γ v := by omega
  have : Fact (Fan86.valence Γ v).Prime := ⟨hp⟩
  set p := Fan86.valence Γ v with hpdef
  have hfin : Finite (MulAction.stabilizer G v) := F.loc_finite v
  set w : G := z * x * z * x⁻¹ with hw
  have hwG : w ∈ MulAction.stabilizer G v :=
    (MulAction.stabilizer G v).mul_mem
      ((MulAction.stabilizer G v).mul_mem ((MulAction.stabilizer G v).mul_mem hz hx) hz)
      ((MulAction.stabilizer G v).inv_mem hx)
  have hwinv : z * w * z⁻¹ = w⁻¹ := by
    have e1 : z * w * z⁻¹ = (z * z) * x * z * x⁻¹ * z⁻¹ := by rw [hw]; group
    have e2 : w⁻¹ = x * z⁻¹ * x⁻¹ * z⁻¹ := by rw [hw]; group
    rw [e1, e2, hzz, one_mul, hz1]
  have hwk : w = x ^ (p - 1) * k * x⁻¹ := by rw [hw, hzx']
  have hpo : p ∣ orderOf w := by
    set φ := F.localHom v with hφ
    let X : MulAction.stabilizer G v := ⟨x, hx⟩
    have hσ : orderOf (φ X) = p := F.orderOf_localHom hx hxo
    have hkK' : (⟨k, F.nbrStab_le_stabilizer v hkK⟩ : MulAction.stabilizer G v) ∈ φ.ker :=
      (F.mem_ker_localHom v _).2 hkK
    have hφw : φ ⟨w, hwG⟩ = φ X ^ (p - 2) := by
      have : (⟨w, hwG⟩ : MulAction.stabilizer G v) = X ^ (p - 1) *
          ⟨k, F.nbrStab_le_stabilizer v hkK⟩ * X⁻¹ := by
        apply Subtype.ext
        simpa using hwk
      rw [this, map_mul, map_mul, map_pow, map_inv, MonoidHom.mem_ker.1 hkK', mul_one,
        show p - 1 = (p - 2) + 1 by omega, pow_succ, mul_inv_cancel_right]
    have hne1 : φ X ^ (p - 2) ≠ 1 := by
      intro h1
      have := orderOf_dvd_of_pow_eq_one h1
      rw [hσ] at this
      have := Nat.le_of_dvd (by omega) this
      omega
    have hp1 : (φ X ^ (p - 2)) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hσ, pow_orderOf_eq_one, one_pow]
    have hord : orderOf (φ X ^ (p - 2)) = p := orderOf_eq_prime hp1 hne1
    have h2 : orderOf (φ ⟨w, hwG⟩) ∣ orderOf (⟨w, hwG⟩ : MulAction.stabilizer G v) :=
      orderOf_map_dvd φ _
    rw [hφw, hord, Subgroup.orderOf_mk] at h2
    exact h2
  have hopos : 0 < orderOf w := by
    have := orderOf_pos (⟨w, hwG⟩ : MulAction.stabilizer G v)
    rwa [Subgroup.orderOf_mk] at this
  have hdvd : orderOf w / p ∣ orderOf w := Nat.div_dvd_of_dvd hpo
  have hu : orderOf (w ^ (orderOf w / p)) = p := by
    have hn0 : orderOf w / p ≠ 0 := by
      intro h0
      have := Nat.div_eq_zero_iff.1 h0
      rcases this with h | h
      · omega
      · have := Nat.le_of_dvd hopos hpo
        omega
    rw [orderOf_pow_of_dvd hn0 hdvd, Nat.div_div_self hpo hopos.ne']
  refine ⟨w ^ (orderOf w / p), (MulAction.stabilizer G v).pow_mem hwG _, hu, ?_⟩
  have h1 := congrArg (· ^ (orderOf w / p)) hwinv
  simpa only [conj_pow, inv_pow] using h1

end FanTree

end CFSG.Quasithin.Fan86
