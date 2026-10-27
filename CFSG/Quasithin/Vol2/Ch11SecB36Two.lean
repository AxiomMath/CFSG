module

public import CFSG.Quasithin.Background.E3Prop
public import CFSG.Quasithin.Vol2.Ch11SecANat2
public import CFSG.Quasithin.Vol2.Ch11StatementsE
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

section General

variable {G : Type} [Group G] [Finite G]

theorem exists_two_or_odd_pow {W : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (W : Set G)) (hxC : x ∉ Subgroup.centralizer (W : Set G)) :
    (∃ k : ℕ, (∃ e : ℕ, (x ^ k) ^ 2 ^ e = 1) ∧ x ^ k ∉ Subgroup.centralizer (W : Set G)) ∨
      ∃ k p : ℕ, p.Prime ∧ p ≠ 2 ∧ (x ^ k) ^ p ∈ Subgroup.centralizer (W : Set G) ∧
        x ^ k ∉ Subgroup.centralizer (W : Set G) := by
  set φ := conjHomL W (Subgroup.normalizer (W : Set G)) le_rfl with hφdef
  have hker : ∀ z (hz : z ∈ Subgroup.normalizer (W : Set G)),
      φ ⟨z, hz⟩ = 1 ↔ z ∈ Subgroup.centralizer (W : Set G) := by
    intro z hz
    rw [← MonoidHom.mem_ker, ker_conjHomL, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  have hpow : ∀ j : ℕ, φ ⟨x ^ j, Subgroup.pow_mem _ hxN j⟩ = φ ⟨x, hxN⟩ ^ j := by
    intro j
    rw [← map_pow]
    rfl
  set d := orderOf (φ ⟨x, hxN⟩) with hddef
  have hd1 : d ≠ 1 := fun h => hxC ((hker x hxN).mp (orderOf_eq_one_iff.mp h))
  have hdpos : 0 < d := orderOf_pos _
  by_cases hodd : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ d
  · obtain ⟨p, hp, hp2, hpd⟩ := hodd
    right
    refine ⟨d / p, p, hp, hp2, ?_, ?_⟩
    · have e : (x ^ (d / p)) ^ p = x ^ d := by rw [← pow_mul, Nat.div_mul_cancel hpd]
      rw [e]
      refine (hker _ (Subgroup.pow_mem _ hxN d)).mp ?_
      rw [hpow, hddef, pow_orderOf_eq_one]
    · intro hC
      have h1 := (hker _ (Subgroup.pow_mem _ hxN (d / p))).mpr hC
      rw [hpow] at h1
      have h2 : d ∣ d / p := orderOf_dvd_of_pow_eq_one h1
      have h3 : 0 < d / p := Nat.div_pos (Nat.le_of_dvd hdpos hpd) hp.pos
      have h4 : d / p < d := Nat.div_lt_self hdpos hp.one_lt
      exact absurd (Nat.le_of_dvd h3 h2) (by omega)
  · left
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨b, ⟨a, ?_⟩, ?_⟩
    · rw [← pow_mul, mul_comm, ← hab, pow_orderOf_eq_one]
    · intro hC
      have h1 := (hker _ (Subgroup.pow_mem _ hxN b)).mpr hC
      rw [hpow] at h1
      have hdb : d ∣ b := orderOf_dvd_of_pow_eq_one h1
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
      have hp2 : p = 2 := by
        by_contra h
        exact hodd ⟨p, hp, h, hpd⟩
      subst hp2
      exact (Nat.not_even_iff_odd.mpr hb) (even_iff_two_dvd.mpr (hpd.trans hdb))

end General

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem sParam_le_nParam_gen (hyp : Hyp11 G T L I n) {V₁ H W : Subgroup G}
    (h31 : Hyp11_3_1 T L I n V₁ H) (hW : IsElemAbelian 2 W)
    (hWc : ¬ E3.wClos W 0 T ≤ pCoreOf 2 H) : (E3.sParam hW : ℕ∞) ≤ E1.nParam H := by
  obtain ⟨S, hS⟩ : ∃ S : Sylow 2 G, (S : Subgroup G) = T :=
    ⟨hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2, rfl⟩
  subst hS
  exact E3.e3_20 hW h31.hstar h31.moves hWc

end CFSG.Quasithin.Vol2.Ch11.SecB
