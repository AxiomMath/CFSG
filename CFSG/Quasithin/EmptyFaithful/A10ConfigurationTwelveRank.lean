module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveCent

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.CT
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

theorem perm6_pow9 : ∀ σ : Equiv.Perm (Fin 6), σ ^ 9 = 1 → σ ^ 3 = 1 := by decide +kernel

theorem exists_elemAbelian_nine {X : Type*} [Group X] (e : X ≃* alternatingGroup (Fin 6)) :
    ∃ P : Subgroup X, Nat.card P = 9 ∧ (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ 3 = 1 := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_alternating_six
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 3 (n := 2)
    (by rw [hX]; norm_num)
  refine ⟨P, by rw [hP]; norm_num, ?_, ?_⟩
  · have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hP
    exact fun a b => this.is_comm.comm a b
  · intro a
    have h9 : a ^ 9 = 1 := by
      have := pow_card_eq_one' (G := P) (x := a)
      rwa [hP] at this
    have h9' : (e (a : X)) ^ 9 = 1 := by
      rw [← map_pow]
      have : (a : X) ^ 9 = 1 := by
        have := congrArg Subtype.val h9
        simpa using this
      rw [this, map_one]
    have h3' : (e (a : X)) ^ 3 = 1 := by
      apply Subtype.ext
      have := perm6_pow9 (e (a : X) : Equiv.Perm (Fin 6)) (by
        have := congrArg Subtype.val h9'
        simpa using this)
      simpa using this
    have h3 : (a : X) ^ 3 = 1 := by
      apply e.injective
      rw [map_pow, h3', map_one]
    exact Subtype.ext (by simpa using h3)

variable {G : Type} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

theorem CE_le_normalizer : E.CE ≤ Subgroup.normalizer (E.E₀ : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem zpow_x₃_mem_HH {n : ℤ} (h : E.x₃ ^ n ∈ E.HH) : E.x₃ ^ n = 1 := by
  have hr : E.x₃ ^ n = E.x₃ ^ (n % 3) := by
    have := zpow_mod_orderOf E.x₃ n
    rw [E.orderOf_x₃] at this
    simpa using this.symm
  rw [hr] at h ⊢
  have hc : E.x₃ * E.x₃ * E.x₃ = 1 := by rw [← pow_three']; exact E.x₃_cube
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, zpow_zero]
  · rw [h1, zpow_one] at h
    exact absurd h E.x₃_not_mem_HH
  · rw [h2, zpow_two] at h
    have e1 : E.x₃ = (E.x₃ * E.x₃) * (E.x₃ * E.x₃) := by
      calc E.x₃ = E.x₃ * (E.x₃ * E.x₃ * E.x₃) := by rw [hc, mul_one]
        _ = _ := by group
    exact absurd (e1 ▸ E.HH.mul_mem h h) E.x₃_not_mem_HH

theorem false_of_alternating_six [Finite G] (hQ : quasithinIsQTKECat G)
    (hcent : ∀ y ∈ E.HH, E.x₃ * y = y * E.x₃) (e : ↥E.HH ≃* alternatingGroup (Fin 6)) : False := by
  classical
  obtain ⟨P, hP9, hPc, hP3⟩ := exists_elemAbelian_nine e
  let C : Subgroup G := Subgroup.zpowers E.x₃
  have hCcard : Nat.card C = 3 := by rw [Nat.card_zpowers, E.orderOf_x₃]
  let ι₁ : ↥P →* G := E.HH.subtype.comp P.subtype
  have hcomm : ∀ (p : ↥P) (q : ↥C), Commute (ι₁ p) (C.subtype q) := by
    intro p q
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 q.2
    show ((p : ↥E.HH) : G) * (q : G) = (q : G) * ((p : ↥E.HH) : G)
    rw [← hn]
    have hpc : Commute E.x₃ ((p : ↥E.HH) : G) := hcent _ (p : ↥E.HH).2
    exact ((hpc.zpow_left n).eq).symm
  let φ : ↥P × ↥C →* G := MonoidHom.noncommCoprod ι₁ C.subtype hcomm
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨p, q⟩ hpq
    have h1 : ((p : ↥E.HH) : G) * (q : G) = 1 := by
      simpa [φ, ι₁, MonoidHom.noncommCoprod_apply] using hpq
    have hq : (q : G) = ((p : ↥E.HH) : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hqHH : (q : G) ∈ E.HH := by
      rw [hq]
      exact E.HH.inv_mem (p : ↥E.HH).2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 q.2
    have hq1 : (q : G) = 1 := by
      rw [← hn] at hqHH ⊢
      exact E.zpow_x₃_mem_HH hqHH
    have hp1 : ((p : ↥E.HH) : G) = 1 := by
      rw [hq1, mul_one] at h1
      exact h1
    have hp : p = 1 := Subtype.ext (Subtype.ext hp1)
    have hq' : q = 1 := Subtype.ext hq1
    rw [hp, hq']
    exact Subgroup.one_mem _
  have hrange : φ.range ≤ Subgroup.normalizer (E.E₀ : Set G) := by
    rintro _ ⟨⟨p, q⟩, rfl⟩
    simp only [φ, MonoidHom.noncommCoprod_apply]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact E.CE_le_normalizer (E.HH_le_CE (p : ↥E.HH).2)
    · exact (Subgroup.zpowers_le.2 E.x₃_mem_normalizer) q.2
  have hAcomm : ∀ a b : ↥P × ↥C, a * b = b * a := by
    intro a b
    refine Prod.ext (hPc _ _) ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2.2
    apply Subtype.ext
    show (a.2 : G) * (b.2 : G) = (b.2 : G) * (a.2 : G)
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  have hApow : ∀ a : ↥P × ↥C, a ^ 3 = 1 := by
    intro a
    refine Prod.ext (hP3 a.1) ?_
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2.2
    apply Subtype.ext
    show (a.2 : G) ^ 3 = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : E.x₃ ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact E.x₃_cube
    rw [this, one_zpow]
  have hAcard : Nat.card (↥P × ↥C) = 3 ^ 3 := by
    rw [Nat.card_prod, hP9, hCcard]
    norm_num
  have hloc : CFSG.Open.IsTwoLocal (Subgroup.normalizer (E.E₀ : Set G)) := by
    refine ⟨E.E₀, ?_, ?_, rfl⟩
    · intro h
      have := E.card_E₀
      rw [h] at this
      simp at this
    · exact IsPGroup.of_card (n := 2) (by rw [E.card_E₀]; norm_num)
  have h3 : 3 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (E.E₀ : Set G)) :=
    CFSG.SectionRank.le_pRank_of_injective (by norm_num) hAcomm hApow hAcard φ hφinj hrange
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  have h4 : CFSG.Open.evenRank G ≤ 2 := hQ.2.2
  omega

end Emb

end CFSG.Quasithin.A10
