module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Lang

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem exists_conj_eq_twInndiagFieldAut {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp2 : p ≠ 2) (δ : K ≃+* K)
    (hδ : orderOf δ = p) (x : twInndiagGroup K σ)
    (hx : (MulAut.conj x * twInndiagFieldAut K σ δ) ^ p = 1) :
    ∃ g : twInndiagGroup K σ, MulAut.conj g * (MulAut.conj x * twInndiagFieldAut K σ δ) *
      (MulAut.conj g)⁻¹ = twInndiagFieldAut K σ δ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨φ, hφ, hφord, hφtop, hcardAut, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega) hK2
  have hcyc : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨φ, hφtop⟩
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hp2n : p ∣ 2 * n := by
    rw [← hδ, ← hcardAut]
    exact orderOf_dvd_natCard δ
  have hpn : p ∣ n := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).dvd_of_dvd_mul_left hp2n
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set e := n / p with he
  have hep : e * p = n := Nat.div_mul_cancel hpn
  have he1 : 1 ≤ e := Nat.div_pos (Nat.le_of_dvd (by omega) hpn) hp.pos
  have hen : e < n := Nat.div_lt_self (by omega) hp.one_lt
  have hn3 : 3 ≤ n := le_trans (by have := hp.two_le; omega) (Nat.le_of_dvd (by omega) hpn)
  have hq3 : 3 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)
  set τ₀ := σ * φ ^ e with hτ₀
  have hσφ : σ = φ ^ n := RingEquiv.ext fun c => by rw [hσ, ringEquiv_pow_sq_apply hφ]
  have hφ2n : φ ^ (2 * n) = 1 := by rw [← hφord]; exact pow_orderOf_eq_one φ
  have hτφ : τ₀ = φ ^ (n + e) := by rw [hτ₀, hσφ, ← pow_add]
  have hτp : τ₀ ^ p = 1 := by
    obtain ⟨k, hk⟩ := hpodd
    have hm : (n + e) * p = 2 * n * (k + 1) := by
      calc (n + e) * p = n * (p + 1) := by rw [← hep]; ring
        _ = 2 * n * (k + 1) := by rw [hk]; ring
    rw [hτφ, ← pow_mul, hm, pow_mul, hφ2n, one_pow]
  have hτ1 : τ₀ ≠ 1 := by
    intro h1
    rw [hτφ] at h1
    have hdvd := orderOf_dvd_of_pow_eq_one h1
    rw [hφord] at hdvd
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
  have hτord : orderOf τ₀ = p := orderOf_eq_prime hτp hτ1
  have hzz : Subgroup.zpowers τ₀ = Subgroup.zpowers δ :=
    (IsCyclic.subgroup_eq_iff_card_eq).2 (by rw [Nat.card_zpowers, Nat.card_zpowers, hτord, hδ])
  obtain ⟨r, hr⟩ : ∃ r : ℕ, δ ^ r = τ₀ := by
    have h : τ₀ ∈ Subgroup.zpowers δ := hzz ▸ Subgroup.mem_zpowers τ₀
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, τ₀ ^ r' = δ := by
    have h : δ ∈ Subgroup.zpowers τ₀ := hzz ▸ Subgroup.mem_zpowers δ
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  set x' := ((List.range r).map fun i => (twInndiagFieldAut K σ δ ^ i) x).prod with hx'
  have hβr : (MulAut.conj x * twInndiagFieldAut K σ δ) ^ r =
      MulAut.conj x' * twInndiagFieldAut K σ τ₀ := by
    rw [CFSG.RankThree.PartOne.KE.conj_mul_pow_aut, ← map_pow, hr]
  have hβrp : (MulAut.conj x' * twInndiagFieldAut K σ τ₀) ^ p = 1 := by
    rw [← hβr, ← pow_mul, mul_comm, pow_mul, hx, one_pow]
  obtain ⟨g, hg⟩ := exists_conj_eq_twInndiagFieldAut_frob hn hK σ hσ φ hφ hp.one_lt.le hpodd he1
    hep hq3 x' hβrp
  rw [← hτ₀] at hg
  have hrr : (MulAut.conj x * twInndiagFieldAut K σ δ) ^ (r * r') =
      MulAut.conj x * twInndiagFieldAut K σ δ := by
    have hσrr : δ ^ (r * r') = δ ^ 1 := by rw [pow_mul, hr, hr', pow_one]
    rw [pow_eq_pow_iff_modEq, hδ] at hσrr
    have hdvd : orderOf (MulAut.conj x * twInndiagFieldAut K σ δ) ∣ p :=
      orderOf_dvd_of_pow_eq_one hx
    have h2 := Nat.ModEq.of_dvd hdvd hσrr
    rw [← pow_eq_pow_iff_modEq, pow_one] at h2
    exact h2
  refine ⟨g, ?_⟩
  rw [← hrr, pow_mul, hβr, ← conj_pow, hg, ← map_pow, hr']

theorem twInndiag_le_normalizer (σ : K ≃+* K) :
    twInndiagGroup K σ ≤
      Subgroup.normalizer (graphFixedRootGroup TwistTag.E6 K σ.toRingHom :
        Set (ModGL TwistTag.E6.tag K)) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (hc | ⟨b, hb, rfl⟩)
  · exact Subgroup.le_normalizer hc
  · exact rootDiagUnit_mem_normalizer_graphFixedRootGroup hb

variable (K) in
@[expose] noncomputable def twConj (σ : K ≃+* K) :
    twInndiagGroup K σ →* MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) where
  toFun w := mulAutRestrict _ (MulAut.conj (w : ModGL TwistTag.E6.tag K))
    (map_conj_eq_of_mem_normalizer (twInndiag_le_normalizer σ w.2))
  map_one' := MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_mulAutRestrict, MulAut.one_apply]
    simp)
  map_mul' v w := MulEquiv.ext fun h => Subtype.ext (by
    rw [MulAut.mul_apply, coe_mulAutRestrict, coe_mulAutRestrict, coe_mulAutRestrict]
    simp [MulAut.conj_apply, mul_assoc])

theorem coe_twConj (σ : K ≃+* K) (w : twInndiagGroup K σ)
    (h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
    ((twConj K σ w h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
      ModGL TwistTag.E6.tag K) =
        (w : ModGL TwistTag.E6.tag K) * h * (w : ModGL TwistTag.E6.tag K)⁻¹ :=
  rfl

end RecipeExcLang

end CFSG.StandardType
