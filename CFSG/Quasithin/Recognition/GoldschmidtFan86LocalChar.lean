module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86LocalFrob

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph Equiv

theorem units_pow_four {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) (u : (ZMod p)ˣ) :
    u ^ 4 = 1 := by
  have h1 : u ^ (p - 1) = 1 := by
    have := pow_card_eq_one (x := u)
    rwa [ZMod.card_units] at this
  rcases hp with rfl | rfl
  · calc u ^ 4 = (u ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by
        have h2 : u ^ 2 = 1 := by simpa using h1
        rw [h2, one_pow]
  · simpa using h1

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem exists_conjChar {v : V} {x : G} (hx : x ∈ MulAction.stabilizer G v)
    (hxo : orderOf x = Fan86.valence Γ v) :
    ∃ ψ : MulAction.stabilizer G v →* (ZMod (Fan86.valence Γ v))ˣ,
      ∀ g : MulAction.stabilizer G v, (g : G) ∈ nbrStab Γ G v ↔
        ψ g = 1 ∧ ∃ a, Γ.Adj v a ∧ (g : G) • a = a := by
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
  refine ⟨D.conjChar.comp (F.localHom v).rangeRestrict, fun g => ⟨fun hK => ?_, ?_⟩⟩
  · have hker : F.localHom v g = 1 := MonoidHom.mem_ker.1 ((F.mem_ker_localHom v g).2 hK)
    have h1 : (F.localHom v).rangeRestrict g = 1 := Subtype.ext hker
    obtain ⟨a, ha⟩ := F.exists_adj v
    exact ⟨by rw [MonoidHom.comp_apply, h1, map_one], a, ha, hK a ha⟩
  · rintro ⟨h1, a, ha, h2⟩
    have h3 := D.eq_one_of_conjChar_eq_one (q := (F.localHom v).rangeRestrict g) h1
      (a := ⟨a, ha⟩) (Subtype.ext h2)
    exact (F.mem_ker_localHom v g).1 (MonoidHom.mem_ker.2 h3)

theorem exists_cyclic_gen {v a : V} (hva : Γ.Adj v a) (S : Subgroup G)
    (hS : S ≤ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) :
    ∃ g ∈ S, g ^ 4 ∈ nbrStab Γ G v ∧ ∀ s ∈ S, ∃ n : ℤ, g ^ n * s⁻¹ ∈ nbrStab Γ G v := by
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence v
  obtain ⟨ψ, hψ⟩ := F.exists_conjChar hx hxo
  have : Fact (Fan86.valence Γ v).Prime := ⟨F.valence_isPrime v⟩
  have hp35 : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  let φ : S →* (ZMod (Fan86.valence Γ v))ˣ := ψ.comp (Subgroup.inclusion (hS.trans inf_le_left))
  have key : ∀ s : S, (s : G) ∈ nbrStab Γ G v ↔ φ s = 1 := fun s =>
    (hψ (Subgroup.inclusion (hS.trans inf_le_left) s)).trans
      ⟨fun h => h.1, fun h => ⟨h, a, hva, MulAction.mem_stabilizer_iff.1 (hS s.2).2⟩⟩
  obtain ⟨⟨c, hc⟩, hgen⟩ := IsCyclic.exists_generator (α := φ.range)
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 hc
  refine ⟨g, g.2, ?_, fun s hs => ?_⟩
  · have : ((g ^ 4 : S) : G) ∈ nbrStab Γ G v := (key _).2 (by
      rw [map_pow, hg]
      exact units_pow_four hp35 c)
    simpa using this
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (hgen ⟨φ ⟨s, hs⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩)
    have hn' : c ^ n = φ ⟨s, hs⟩ := congrArg Subtype.val hn
    refine ⟨n, ?_⟩
    have : ((g ^ n * ⟨s, hs⟩⁻¹ : S) : G) ∈ nbrStab Γ G v := (key _).2 (by
      rw [map_mul, map_zpow, map_inv, hg, hn', mul_inv_cancel])
    simpa using this

theorem exists_edge_char {v a : V} (hva : Γ.Adj v a) :
    ∃ φ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) →*
        (ZMod (Fan86.valence Γ v))ˣ,
      (∀ e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a),
        (e : G) ∈ nbrStab Γ G v ↔ φ e = 1) ∧
      (nbrStab Γ G v).relIndex (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) =
        Nat.card φ.range ∧
      Nat.card φ.range ∣ Fan86.valence Γ v - 1 ∧ Nat.card φ.range ≠ 1 := by
  obtain ⟨x, hx, hxo⟩ := F.exists_orderOf_eq_valence v
  obtain ⟨ψ, hψ⟩ := F.exists_conjChar hx hxo
  have : Fact (Fan86.valence Γ v).Prime := ⟨F.valence_isPrime v⟩
  let φ : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) →*
      (ZMod (Fan86.valence Γ v))ˣ := ψ.comp (Subgroup.inclusion inf_le_left)
  have key : ∀ e : ↥(MulAction.stabilizer G v ⊓ MulAction.stabilizer G a),
      (e : G) ∈ nbrStab Γ G v ↔ φ e = 1 := fun e =>
    (hψ (Subgroup.inclusion inf_le_left e)).trans
      ⟨fun h => h.1, fun h => ⟨h, a, hva, MulAction.mem_stabilizer_iff.1 e.2.2⟩⟩
  refine ⟨φ, key, ?_, ?_, ?_⟩
  · have hker : (nbrStab Γ G v).subgroupOf
        (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) = φ.ker := by
      ext e
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, key]
    rw [Subgroup.relIndex, hker, Subgroup.index_ker]
  · have h1 := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_eq_fintype_card (α := (ZMod (Fan86.valence Γ v))ˣ), ZMod.card_units] at h1
  · intro h1
    obtain ⟨g, hg, hga, c, hc, hgc⟩ := F.frobenius_nonreg v a hva
    have hmem : g ∈ MulAction.stabilizer G v ⊓ MulAction.stabilizer G a :=
      ⟨hg, MulAction.mem_stabilizer_iff.2 hga⟩
    have hφ1 : φ ⟨g, hmem⟩ = 1 := by
      have h2 : φ ⟨g, hmem⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [Subgroup.card_eq_one.1 h1] at h2
      exact Subgroup.mem_bot.1 h2
    exact hgc (mem_nbrStab.1 ((key ⟨g, hmem⟩).2 hφ1) c hc)

theorem relIndex_nbrStab_mem_two_four {v a : V} (hva : Γ.Adj v a) :
    (nbrStab Γ G v).relIndex (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) ∈
      ({2, 4} : Set ℕ) := by
  obtain ⟨φ, -, hidx, hdvd, hne⟩ := F.exists_edge_char hva
  rw [hidx]
  have hp35 : Fan86.valence Γ v = 3 ∨ Fan86.valence Γ v = 5 := F.valence v
  generalize Nat.card φ.range = m at hdvd hne ⊢
  rcases hp35 with h3 | h5
  · have h2 : Fan86.valence Γ v - 1 = 2 := by omega
    rw [h2] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> simp_all
  · have h4 : Fan86.valence Γ v - 1 = 4 := by omega
    rw [h4] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> simp_all

theorem relIndex_nbrStab_eq_two {v a : V} (hva : Γ.Adj v a) (h3 : Fan86.valence Γ v = 3) :
    (nbrStab Γ G v).relIndex (MulAction.stabilizer G v ⊓ MulAction.stabilizer G a) = 2 := by
  obtain ⟨φ, -, hidx, hdvd, hne⟩ := F.exists_edge_char hva
  rw [hidx]
  generalize Nat.card φ.range = m at hdvd hne ⊢
  have h2 : Fan86.valence Γ v - 1 = 2 := by omega
  rw [h2] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases m <;> simp_all

end FanTree

end CFSG.Quasithin.Fan86
