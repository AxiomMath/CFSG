module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart
public import CFSG.Quasithin.Background.Ordering

public section

namespace CFSG.Quasithin.H13.A5.SpBorel

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem exists_mulEquiv_sylow {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}
    [Fact p.Prime] (e : X ≃* Y) (P : Sylow p X) (U : Sylow p Y) :
    ∃ φ : X ≃* Y, ∀ x, x ∈ (P : Subgroup X) ↔ φ x ∈ (U : Subgroup Y) := by
  have hsurj : Function.Surjective e.toMonoidHom := e.surjective
  let P' : Sylow p Y := Sylow.mapSurjective hsurj P
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P' U
  refine ⟨e.trans (MulAut.conj y), fun x => ?_⟩
  have h1 : ((y • P' : Sylow p Y) : Subgroup Y) = U := by rw [hy]
  rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv, Sylow.coe_mapSurjective]
  simp only [MulEquiv.trans_apply, MulAut.conj_apply]
  rw [show y⁻¹ * (y * e x * y⁻¹) * y = e x by group]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x', hx', hxx⟩
    rw [← e.injective hxx]
    exact hx'

theorem mem_normalizer_iff_of_mulEquiv {X Y : Type} [Group X] [Group Y] (φ : X ≃* Y)
    {P : Subgroup X} {U : Subgroup Y} (hφ : ∀ x, x ∈ P ↔ φ x ∈ U) (x : X) :
    x ∈ Subgroup.normalizer (P : Set X) ↔ φ x ∈ Subgroup.normalizer (U : Set Y) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h u
    obtain ⟨g, rfl⟩ := φ.surjective u
    rw [← map_inv, ← map_mul, ← map_mul, ← hφ, ← hφ]
    exact h g
  · intro h g
    rw [hφ, hφ, map_mul, map_mul, map_inv]
    exact h (φ g)

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)

theorem proj_injective {K : Type} [Field K] [Finite K] {f r : ℕ} (hf : 1 ≤ f) (hr : 1 ≤ r)
    (hK : Nat.card K = 2 ^ f) : Function.Injective (proj r K) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj]
  apply Subgroup.eq_bot_of_card_eq
  rw [card_spScalars_eq_gcd K hr, hK]
  have hodd : Odd (2 ^ f - 1) := by
    have : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    have h2 : Even (2 ^ f) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  exact Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hodd)

theorem clause4 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f)
    (hX : StatedClassicalModel X .PSp 2 2 f) (P : Sylow 2 X)
    (h3 : 3 ∣ Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X))) :
    ∃ E : Subgroup X, E ≤ Subgroup.normalizer ((P : Subgroup X) : Set X) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : CharP K 2 := charP_two_of_card hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU⟩ := exists_sylow_projUnipotent (r := 2) (K := K) 2 (by norm_num)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_sylow e P U
  have hN : ∀ x, x ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) ↔
      φ x ∈ projBorel 2 K := by
    intro x
    rw [mem_normalizer_iff_of_mulEquiv φ hφ x, hU, normalizer_projUnipotent 2 (by norm_num)]
  have hcard : Nat.card (Subgroup.normalizer ((P : Subgroup X) : Set X)) =
      Nat.card (borelSubgroup 2 K) := by
    rw [Nat.card_congr (φ.toEquiv.subtypeEquiv hN), projBorel,
      ← Nat.card_congr ((borelSubgroup 2 K).equivMapOfInjective _
        (proj_injective (f := f) (by omega) (by norm_num) hK)).toEquiv]
  rw [hcard, card_borelSubgroup, hK] at h3
  have h3q : 3 ∣ 2 ^ f - 1 := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exfalso
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow (Nat.prime_three.dvd_of_dvd_pow h))
      omega
    · exact Nat.prime_three.dvd_of_dvd_pow h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3
    (by rw [Nat.card_units, hK]; exact h3q)
  set Z := Subgroup.zpowers ω with hZ
  let ψ : (Fin 2 → ↥Z) →* X := φ.symm.toMonoidHom.comp ((proj 2 K).comp
    ((SymplecticTorusWeyl.torusHom (r := 2) (k := K)).comp (Z.subtype.compLeft (Fin 2))))
  have hψinj : Function.Injective ψ := by
    refine φ.symm.injective.comp ((proj_injective (f := f) (by omega) (by norm_num) hK).comp
      (SymplecticTorusWeyl.torusHom_injective.comp fun a b h => funext fun i => ?_))
    exact Subtype.ext (congrFun h i)
  refine ⟨ψ.range, ?_, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨t, rfl⟩
    rw [hN]
    refine ⟨SymplecticTorusWeyl.torusHom (Z.subtype.compLeft (Fin 2) t),
      torus_le_borelSubgroup ⟨_, rfl⟩, ?_⟩
    simp [ψ]
  · obtain ⟨s, hs⟩ := x.2
    obtain ⟨t, ht⟩ := y.2
    apply Subtype.ext
    show (x : X) * y = y * x
    rw [← hs, ← ht, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨t, rfl⟩
    rw [← map_pow]
    have : t ^ 3 = 1 := by
      funext i
      have h1 : (t i) ^ Nat.card ↥Z = 1 := pow_card_eq_one'
      rw [Nat.card_zpowers, hω] at h1
      simpa using h1
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv, Nat.card_fun, Nat.card_zpowers, hω,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num

end CFSG.Quasithin.H13.A5.SpBorel
