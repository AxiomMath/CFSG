module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesFix
public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial

namespace ExcFramesHalf

open ExcFrames

section Field

variable {K L : Type} [Field K] [Field L]

theorem exists_ext_ringAut (ι : K →+* L) {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hL : Nat.card L = 2 ^ (2 * f)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : σ ^ p = 1) : ∃ σ' : L ≃+* L, σ' ^ p = 1 ∧ ∀ c, σ' (ι c) = ι (σ c) := by
  obtain ⟨φ, hφ, hord, htop, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  obtain ⟨ψ, hψ, hordψ, -, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * f) hL
  have hfin : IsOfFinOrder φ := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [htop]; exact Subgroup.mem_top σ))
  have hfj : f ∣ j * p := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one (by rw [pow_mul, hj, hσ])
  have h2 : 2 ∣ p + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact even_iff_two_dvd.mp h.add_one
  refine ⟨ψ ^ (j * (p + 1)), ?_, fun c => ?_⟩
  · rw [← pow_mul]
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hordψ]
    calc 2 * f ∣ (p + 1) * (j * p) := mul_dvd_mul h2 hfj
      _ = j * (p + 1) * p := by ring
  · rw [ringAut_pow_apply_of_frobenius hψ, ← map_pow, ← ringAut_pow_apply_of_frobenius hφ,
      pow_mul, hj, pow_succ, hσ, one_mul]


theorem baseChangeGL_comm {τ : Tag} (ι : K →+* L) {σ : K ≃+* K} {σ' : L ≃+* L}
    (h : ∀ c, σ' (ι c) = ι (σ c)) (x : ModGL τ K) :
    baseChangeGL σ'.toRingHom (baseChangeGL ι x) =
      baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) x) := by
  have e : Units.map (entrywiseHom σ.toRingHom) x = baseChangeGL σ.toRingHom x := Units.ext rfl
  have hcomp : σ'.toRingHom.comp ι = ι.comp σ.toRingHom :=
    RingHom.ext fun c => show σ' (ι c) = ι (σ c) from h c
  rw [e, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]

end Field

section NormalForm


theorem exists_normalForm {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    [CharP K 2] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup τ K)) (hα : α ^ p = 1) :
    ∃ (a : adjointGroup τ K) (σ : K ≃+* K), σ ^ p = 1 ∧ ∀ h : adjointGroup τ K,
      (α h : ModGL τ K) =
        (a : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
          (a : ModGL τ K)⁻¹ := by
  rcases hτ with rfl | hτ
  · have : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
    obtain ⟨-, hnf, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    set Θ' : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * f)) := Θ with hΘ'
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf α
    dsimp only at hgk
    have hθ : Θ' α = Multiplicative.ofAdd (((k : ℕ) : ZMod (2 * f))) := hΘ α g k hgk
    have h0 : (((p * (k : ℕ) : ℕ)) : ZMod (2 * f)) = 0 := by
      have h1 : Θ' (α ^ p) = 1 := by rw [hα]; exact map_one Θ'
      rw [map_pow, hθ, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h1
      exact_mod_cast h1
    have hdvd : 2 * f ∣ p * k := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    obtain ⟨j, hj⟩ : 2 ∣ (k : ℕ) := h2p.dvd_of_dvd_mul_left ((dvd_mul_right 2 f).trans hdvd)
    have hfj : f ∣ p * j := by
      refine Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) ?_
      rw [show 2 * (p * j) = p * (k : ℕ) by rw [hj]; ring]
      exact hdvd
    obtain ⟨t, ht⟩ := hfj
    have hσjp : (frobAut K ^ j) ^ p = 1 := by
      rw [← pow_mul, mul_comm, ht, pow_mul, frobAut_pow_card hK, one_pow]
    refine ⟨g, frobAut K ^ j, hσjp, fun h => ?_⟩
    have e : α h = g * (ReeTag.F4.finiteExceptionalAut K ^ (k : ℕ)) h * g⁻¹ := by
      rw [hgk]
      rfl
    rw [e, hj, finiteExceptionalAut_pow_two_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, ReeTag.coe_finiteFrobeniusAut_pow (σ := frobAut K) frobAut_apply j h]
    rfl
  · obtain ⟨hnf, Θ, hΘ, -, -, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf α
    dsimp only at hgσ
    have hσ : Θ α = σ := hΘ α g σ hgσ
    exact ⟨g, σ, by rw [← hσ, ← map_pow, hα, map_one], hgσ⟩

end NormalForm

section Conj


theorem exists_conj_of_normalForm {τ : Tag} {K L : Type} [Field K] [Field L] {p : ℕ}
    [Fact p.Prime] (ι : K →+* L) {σ : K ≃+* K} {σ' : L ≃+* L} (hσ' : σ' ^ p = 1)
    (hext : ∀ c, σ' (ι c) = ι (σ c)) (α : MulAut (adjointGroup τ K)) (a : adjointGroup τ K)
    (hα : ∀ h : adjointGroup τ K, (α h : ModGL τ K) =
      (a : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) *
        (a : ModGL τ K)⁻¹)
    (c : adjointGroup τ L) : ∃ y : adjointGroup τ L, ∀ x : adjointGroup τ K,
      c * adjBaseChange ι x * c⁻¹ ∈ TableBExc.torusPow τ L p →
        adjBaseChange ι (α x) = y * adjBaseChange ι x * y⁻¹ := by
  set c' : adjointGroup τ L := ⟨baseChangeGL σ'.toRingHom (c : ModGL τ L),
    baseChangeGL_mem_adjointGroup σ'.toRingHom c.2⟩ with hc'
  refine ⟨adjBaseChange ι a * c'⁻¹ * c, fun x hx => Subtype.ext ?_⟩
  have hv := mem_torusPow_iff_coe.mp hx
  set v : ModGL τ L := ((c * adjBaseChange ι x * c⁻¹ : adjointGroup τ L) : ModGL τ L) with hvdef
  have hvfix : baseChangeGL σ'.toRingHom v = v := by
    have e : baseChangeGL σ'.toRingHom v = Units.map (entrywiseHom σ'.toRingHom) v :=
      Units.ext rfl
    rw [e]
    exact units_map_entrywise_eq_self hσ' hv
  have hx' : baseChangeGL ι (x : ModGL τ K) = (c : ModGL τ L)⁻¹ * v * c := by
    rw [hvdef, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_adjBaseChange]
    group
  have hσx : baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K)) =
      (c' : ModGL τ L)⁻¹ * v * c' := by
    rw [← baseChangeGL_comm ι hext, hx', map_mul, map_mul, map_inv, hvfix]
  rw [coe_adjBaseChange, hα x, map_mul, map_mul, map_inv, hσx]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_adjBaseChange]
  rw [hx']
  group

end Conj

end ExcFramesHalf

end CFSG.StandardType
