module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesWeyl
public import CFSG.LieType.Chevalley.EvenE7E8AutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace ExcFrames

section Field

variable {L : Type} [Field L] {p : ℕ} [Fact p.Prime]

theorem pow_prime_mod (m : ℕ) : m ^ p % p = m % p := by
  have h := ZMod.pow_card (m : ZMod p)
  rw [← Nat.cast_pow] at h
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h

theorem ringAut_apply_eq_self {σ : L ≃+* L} (hσ : σ ^ p = 1) {c : L} (hc : c ^ p = 1) :
    σ c = c := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases h1 : c = 1
  · rw [h1, map_one]
  have hco : orderOf c = p := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hc) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have hprim : IsPrimitiveRoot c p := hco ▸ IsPrimitiveRoot.orderOf c
  obtain ⟨m, -, hm⟩ := hprim.eq_pow_of_pow_eq_one (ξ := σ c) (by rw [← map_pow, hc, map_one])
  have hj : ∀ j : ℕ, (σ ^ j) c = c ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, RingAut.mul_apply, ← hm, map_pow, ih, ← pow_mul, ← pow_succ]
  have hcp : c ^ (m ^ p) = c := by
    have h := hj p
    rw [hσ] at h
    exact h.symm
  rw [← hm]
  calc c ^ m = c ^ (m % p) := pow_eq_pow_mod m hc
    _ = c ^ (m ^ p % p) := by rw [pow_prime_mod]
    _ = c ^ (m ^ p) := (pow_eq_pow_mod _ hc).symm
    _ = c := hcp

end Field

section Entrywise

variable {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem units_map_entrywise_eq_self {σ : K ≃+* K} (hσ : σ ^ p = 1) {v : ModGL τ K}
    (hv : v ∈ splitPow τ K p) : Units.map (entrywiseHom σ.toRingHom) v = v := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hv.1
  have hbp : b ^ p = 1 :=
    rootDiagUnit_injective (by rw [← rootDiagUnit_pow, hv.2, rootDiagUnit_one])
  refine Units.ext ?_
  change entrywise σ.toRingHom (rootDiag b) = rootDiag b
  rw [entrywise_rootDiag]
  congr 1
  funext i
  refine Units.ext ?_
  rw [Units.coe_map]
  have hbi : (b i : K) ^ p = 1 := by
    have h := congrFun hbp i
    rw [Pi.pow_apply, Pi.one_apply] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  exact ringAut_apply_eq_self hσ hbi

end Entrywise

section Frob

@[expose] noncomputable def frobAut (K : Type) [Field K] [Finite K] [CharP K 2] : K ≃+* K :=
  RingEquiv.ofBijective (frobenius K 2) (Finite.injective_iff_bijective.mp (frobenius_inj K 2))

theorem frobAut_apply {K : Type} [Field K] [Finite K] [CharP K 2] (c : K) :
    frobAut K c = c ^ 2 :=
  rfl

theorem frobAut_pow_apply {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (c : K) :
    (frobAut K ^ n) c = c ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, RingAut.mul_apply, frobAut_apply, map_pow, ih, ← pow_mul, ← pow_succ]

theorem frobAut_pow_card {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : frobAut K ^ f = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine RingEquiv.ext fun c => ?_
  rw [frobAut_pow_apply, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rfl

end Frob

section Inner


theorem exists_inner_on_torusPow_E7E8 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ f) {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime]
    (α : MulAut (adjointGroup τ K)) (hα : α ^ p = 1) :
    ∃ a : adjointGroup τ K, ∀ v ∈ TableBExc.torusPow τ K p, α v = a * v * a⁻¹ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  obtain ⟨hnf, Θ, hΘ, -, -, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf α
  dsimp only at hgσ
  have hσ : Θ α = σ := hΘ α g σ hgσ
  have hσp : σ ^ p = 1 := by rw [← hσ, ← map_pow, hα, map_one]
  refine ⟨g, fun v hv => Subtype.ext ?_⟩
  rw [hgσ v, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    units_map_entrywise_eq_self hσp (mem_torusPow_iff_coe.mp hv)]

theorem exists_inner_on_torusPow_F4 {f : ℕ} (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (α : MulAut (adjointGroup .F4 K)) (hα : α ^ p = 1) :
    ∃ a : adjointGroup .F4 K, ∀ v ∈ TableBExc.torusPow .F4 K p, α v = a * v * a⁻¹ := by
  have hp : p.Prime := Fact.out
  have : CharP K ReeTag.F4.prime := inferInstanceAs (CharP K 2)
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
  refine ⟨g, fun v hv => ?_⟩
  have hFv : (ReeTag.F4.finiteFrobeniusAut K ^ j) v = v := by
    refine Subtype.ext ?_
    rw [ReeTag.coe_finiteFrobeniusAut_pow (σ := frobAut K) frobAut_apply j v]
    exact units_map_entrywise_eq_self hσjp (mem_torusPow_iff_coe.mp hv)
  have e : α v = g * (ReeTag.F4.finiteExceptionalAut K ^ (k : ℕ)) v * g⁻¹ := by
    rw [hgk]
    rfl
  rw [e, hj, finiteExceptionalAut_pow_two_mul, hFv]
  rfl

end Inner

end ExcFrames

end CFSG.StandardType
