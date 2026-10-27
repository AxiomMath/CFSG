module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4Cart
public import CFSG.LocalAnalysis.UniquenessCase.Lie.ConclAt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.Open
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom torus coe_torusHom statedSp_ext
  mem_statedSp_iff torusHom_injective)
open Subgroup Matrix
open scoped Pointwise

variable {K : Type} [Field K]

theorem uc22pwI2_exists_equiv_sylow {X G : Type} [Group X] [Group G] [Finite G] (e : X ≃* G)
    (U : Sylow 2 X) (R : Sylow 2 G) :
    ∃ e' : X ≃* G, (U : Subgroup X).map e'.toMonoidHom = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (uc22pwI2SylowMap e U) R
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hR' : (R : Subgroup G) = MulAut.conj g • (U : Subgroup X).map e.toMonoidHom :=
    (congrArg (fun S : Sylow 2 G => (S : Subgroup G)) hg).symm
  rw [hR']
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨e q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩

theorem uc22pwI2_sp4R [Finite K] [CharP K 2] {n e m' : ℕ} (hm' : Odd m') (hn : Nat.card K = 2 ^ n)
    (hn2 : 2 ≤ n) (hnem : n = 2 ^ e * m') {P : Type} [Group P] (hP : IsPGroup 2 P)
    (ψ : P →* MulAut (StatedSp 2 K))
    (hψ : ∀ (g : P) (x : StatedSp 2 K), x ∈ unipotent 2 K ↔ ψ g x ∈ unipotent 2 K) :
    ∃ E : Subgroup (StatedSp 2 K), uc22pwlie_ConclAt uc22pwI2Ep (StatedSp 2 K) (unipotent 2 K) P ψ n m' E ∧
      uc22pwlie_RShape (unipotent 2 K) E ψ := by
  have hmem : ∀ g, ψ g ∈ uc22pwI2Stab K := fun g => mem_uc22pwI2Stab.2 (hψ g)
  let a : P → Monoid.End (Fin 2 → Kˣ) := fun g => uc22pwI2ActHom K ⟨ψ g, hmem g⟩
  have ha : ∀ g, ∃ m : ℕ, m' ∣ m ∧ ∀ t, a g t = ((uc22pwI2RhoE K) ^ m) t := by
    intro g
    obtain ⟨m, hm⟩ := uc22pwI2_act_eq_rho_pow (n := n) (by omega) hn (hmem g)
    refine ⟨m, ?_, hm⟩
    obtain ⟨k, hk⟩ := hP g
    have h1 : (a g) ^ 2 ^ k = 1 := by
      have h2 : (⟨ψ g, hmem g⟩ : uc22pwI2Stab K) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        change (ψ g) ^ 2 ^ k = 1
        rw [← map_pow, hk, map_one]
      change (uc22pwI2ActHom K ⟨ψ g, hmem g⟩) ^ 2 ^ k = 1
      rw [← map_pow, h2, map_one]
    have hag : a g = (uc22pwI2RhoE K) ^ m := MonoidHom.ext hm
    refine uc22pwI2_dvd_of_rho_pow hm' hn hn2 hnem (k := k) (fun t => ?_)
    rw [← hag, h1]
    rfl
  obtain ⟨ET, hEp, hpi, he1, he2⟩ := uc22pwI2_exists_torus_subgroup hm' hn hnem a ha
  have hspec : ∀ g t, ψ g (torusHom t) * (torusHom (a g t))⁻¹ ∈ unipotent 2 K :=
    fun g t => uc22pwI2Act_spec (hmem g) t
  have hEpE := hEp.map torusHom torusHom_injective
  have hodd : Odd (Nat.card (Fin 2 → Kˣ)) := by
    rw [Nat.card_fun, Nat.card_units, hn, Nat.card_eq_fintype_card, Fintype.card_fin]
    have he2 : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, by omega⟩
    exact (Nat.Even.sub_odd Nat.one_le_two_pow he2 odd_one).pow
  have hsqinj : ∀ x y : Fin 2 → Kˣ, x ^ 2 = y ^ 2 → x = y := by
    intro x y h
    have h1 : (x * y⁻¹) ^ 2 = 1 := by rw [mul_pow, h, inv_pow, mul_inv_cancel]
    have h2 : (x * y⁻¹) ^ Nat.card (Fin 2 → Kˣ) = 1 := pow_card_eq_one'
    have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [(Nat.coprime_two_left.2 hodd).gcd_eq_one] at h3
    exact mul_inv_eq_one.1 (orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3))
  have hρinj : Function.Injective (uc22pwI2RhoE K) := fun x y hxy =>
    hsqinj x y (by rw [← uc22pwI2Rho_sq, ← uc22pwI2Rho_sq, hxy])
  let ρ : MulAut (Fin 2 → Kˣ) :=
    MulEquiv.ofBijective (uc22pwI2RhoE K) ⟨hρinj, Finite.injective_iff_surjective.1 hρinj⟩
  have hρpow : ∀ (m : ℕ) (t : Fin 2 → Kˣ), (ρ ^ m) t = ((uc22pwI2RhoE K) ^ m) t := by
    intro m
    induction m with
    | zero => intro t; rfl
    | succ m ih =>
      intro t
      rw [pow_succ', pow_succ', MulAut.mul_apply, ih]
      rfl
  have hEN : ET.map torusHom ≤ normalizer ((unipotent 2 K : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) := by
    rw [normalizer_unipotent]
    rintro _ ⟨t, -, rfl⟩
    exact torus_le_borelSubgroup ⟨t, rfl⟩
  refine ⟨ET.map torusHom, ⟨hEN, hEpE, ?_, ?_, ?_, ?_⟩, Fin 2 → Kˣ, inferInstance, inferInstance, torusHom, ρ,
    torusHom_injective, hodd, ?_, ?_, uc22pwI2Rho_sq, fun g => ?_⟩
  · show {p | p.Prime ∧ p ∣ Nat.card ↥(ET.map torusHom)} = {p | p.Prime ∧ p ∣ 2 ^ n - 1}
    rw [Subgroup.card_map_of_injective torusHom_injective]
    exact hpi
  · intro g x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have h1 : ψ g (torusHom t) =
        (ψ g (torusHom t) * (torusHom (a g t))⁻¹) * torusHom (a g t) := by group
    rw [h1, sup_comm]
    exact Subgroup.mul_mem_sup (hspec g t) ⟨a g t, he1 g t ht, rfl⟩
  · intro g x hx
    obtain ⟨hxE, hxα⟩ := uc22pwlie_mem_of_mem_oPi hEpE.1 hx
    obtain ⟨t, ht, rfl⟩ := hxE
    have hord : orderOf (torusHom t : StatedSp 2 K) = orderOf t :=
      orderOf_injective (torusHom : (Fin 2 → Kˣ) →* StatedSp 2 K) torusHom_injective t
    have hat : a g t = t := he2 g t ht fun p hp hpd => (hxα p hp (hord ▸ hpd)).2
    have h2 := hspec g t
    rwa [hat] at h2
  · obtain ⟨w, hw2, hwinv, hwgen⟩ := uc22pwI2_sp4_weyl (K := K)
    refine ⟨w, hw2, ?_, ?_⟩
    · rintro _ ⟨t, -, rfl⟩
      exact hwinv t
    · rw [normalizer_unipotent]
      exact hwgen
  · rw [normalizer_unipotent]
    rintro _ ⟨t, rfl⟩
    exact torus_le_borelSubgroup ⟨t, rfl⟩
  · rintro _ ⟨t, -, rfl⟩
    exact ⟨t, rfl⟩
  · obtain ⟨m, -, hm⟩ := ha g
    refine ⟨m, fun t => ?_⟩
    rw [hρpow, ← hm]
    exact hspec g t

theorem uc22pwlie_sp4_of_isSp4R {X : Type} [Group X] [Finite X] {n : ℕ} (hn2 : 2 < n) (hX : IsSp4 X n)
    (U : Sylow 2 X) {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    ∃ E : Subgroup X, uc22pwlie_ConclAt uc22pwI2Ep X (U : Subgroup X) P ψ n m' E ∧
      uc22pwlie_RShape (U : Subgroup X) E ψ := by
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  let e₁ : X ≃* StatedSp 2 K := e₀.trans (CFSG.QuasithinUnique.Lin2.Five.projEquiv K).symm
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unipotent (K := K) 2 2
  obtain ⟨e', he'⟩ := uc22pwI2_exists_equiv_sylow e₁ U U₀
  rw [hU₀] at he'
  have hψ' : ∀ (g : P) (y : StatedSp 2 K), y ∈ unipotent 2 K ↔
      ((MulAut.congr e').toMonoidHom.comp ψ) g y ∈ unipotent 2 K := by
    intro g y
    have h1 : ((MulAut.congr e').toMonoidHom.comp ψ) g y = e' (ψ g (e'.symm y)) := by
      simp [MulAut.congr_apply]
    rw [h1, ← he', uc22pwlie_mem_map_iff, uc22pwlie_mem_map_iff, MulEquiv.symm_apply_apply]
    exact hψ g (e'.symm y)
  obtain ⟨E', hE', hR⟩ := uc22pwI2_sp4R hm' hK (by omega) hnem hP ((MulAut.congr e').toMonoidHom.comp ψ) hψ'
  rw [← he'] at hE' hR
  exact ⟨_, uc22pwlie_ConclAt.of_mulEquiv
    (fun {Y Z} _ _ e E h => by simpa using uc22pwI2Ep.map e.toMonoidHom e.injective h) e' ψ hE',
    uc22pwlie_RShape.of_mulEquiv e' ψ hR⟩

theorem uc22pwlie_sp4_of_isSp4 {X : Type} [Group X] [Finite X] {n : ℕ} (hn2 : 2 < n) (hX : IsSp4 X n)
    (U : Sylow 2 X) {P : Type} [Group P] (hP : IsPGroup 2 P) (ψ : P →* MulAut X)
    (hψ : ∀ (g : P) (x : X), x ∈ (U : Subgroup X) ↔ ψ g x ∈ (U : Subgroup X))
    {e m' : ℕ} (hm' : Odd m') (hnem : n = 2 ^ e * m') :
    uc22pwlie_Concl uc22pwI2Ep X (U : Subgroup X) P ψ n m' := by
  obtain ⟨E, hE, -⟩ := uc22pwlie_sp4_of_isSp4R hn2 hX U hP ψ hψ hm' hnem
  exact ⟨E, hE⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
