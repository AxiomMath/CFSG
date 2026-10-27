module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.Walter.Suzuki

open scoped MatrixGroups
open CFSG.GorensteinWalter

theorem four_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 4 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  exact ⟨k * (k + 1), by
    have : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
    omega⟩

theorem eight_dvd_sq_sub_one {q : ℕ} (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  have := sq_mod_eight_of_odd hq
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq.pos
  omega

theorem factorization_two_twelve : (12 : ℕ).factorization 2 = 2 := by
  rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem subsingleton_sylow_two_of_card_twelve {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 12)
    (hC : ∀ u : X, orderOf u = 2 → Nat.card (Subgroup.centralizer ({u} : Set X)) = 4) :
    Subsingleton (Sylow 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ∀ T : Sylow 2 X, Nat.card (T : Subgroup X) = 4 := by
    intro T
    rw [T.card_eq_multiplicity, hX, factorization_two_twelve]
    norm_num
  refine ⟨fun T₁ T₂ => ?_⟩
  have hne : (T₁ : Subgroup X) ⊓ T₂ ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective
        (fun x : ↥(T₁ : Subgroup X) × ↥(T₂ : Subgroup X) => (x.1 : X) * x.2) := by
      rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      simp only at hab
      have h1 : (a' : X)⁻¹ * a = b' * (b : X)⁻¹ := by
        calc (a' : X)⁻¹ * a = (a' : X)⁻¹ * (a * b) * (b : X)⁻¹ := by group
          _ = (a' : X)⁻¹ * (a' * b') * (b : X)⁻¹ := by rw [hab]
          _ = b' * (b : X)⁻¹ := by group
      have hmem : (a' : X)⁻¹ * a ∈ (T₁ : Subgroup X) ⊓ T₂ :=
        ⟨T₁.mul_mem (T₁.inv_mem a'.2) a.2, h1 ▸ T₂.mul_mem b'.2 (T₂.inv_mem b.2)⟩
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hb : (b : X) = b' := by
        rw [hmem] at hab
        exact mul_left_cancel hab
      exact Prod.ext (Subtype.ext hmem.symm) (Subtype.ext hb)
    have := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, h4, h4, hX] at this
    norm_num at this
  have h2dvd : 2 ∣ Nat.card ((T₁ : Subgroup X) ⊓ T₂ : Subgroup X) := by
    have hp : IsPGroup 2 ((T₁ : Subgroup X) ⊓ T₂ : Subgroup X) :=
      T₁.isPGroup'.to_le inf_le_left
    rcases hp.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact h2
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hu' : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have hle : ∀ T : Sylow 2 X, (u : X) ∈ T →
      (T : Subgroup X) = Subgroup.centralizer ({(u : X)} : Set X) := by
    intro T huT
    have hab := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := T)
      (by rw [h4]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hC u hu', h4])
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨u, huT⟩)
  exact Sylow.ext ((hle T₁ u.2.1).trans (hle T₂ u.2.2).symm)

variable (K : Type) [Field K] [Finite K]

theorem two_dvd_card_psl2 (hK : IsOddPrimePower (Nat.card K)) : 2 ∣ Nat.card PSL(2, K) := by
  rw [psl2_card_formula K hK]
  have hodd : Odd (Nat.card K) := by
    obtain ⟨p, n, -, hp, -, h⟩ := hK
    rw [h]
    exact hp.pow
  obtain ⟨m, hm⟩ := four_dvd_sq_sub_one hodd
  rw [hm, show Nat.card K * (4 * m) = 2 * (2 * (Nat.card K * m)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]
  exact dvd_mul_right 2 _

theorem eq_three_or_five_of_isMulCommutative {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hp : Odd p) (hf : 0 < f) {t : PSL(2, K)} (ht : orderOf t = 2)
    (hab : IsMulCommutative (Subgroup.centralizer ({t} : Set PSL(2, K)))) :
    p ^ f = 3 ∨ p ^ f = 5 := by
  obtain ⟨h1, h3⟩ := psl2_centralizer_involution K hK hp hf ht
  have key : ∀ n : ℕ,
      Nonempty (Subgroup.centralizer ({t} : Set PSL(2, K)) ≃* DihedralGroup n) → n = 1 ∨ n = 2 := by
    rintro n ⟨e⟩
    by_contra hn
    simp only [not_or] at hn
    apply DihedralGroup.not_commutative hn.1 hn.2
    exact ⟨⟨fun a b => e.symm.injective (by rw [map_mul, map_mul]; exact hab.is_comm.comm _ _)⟩⟩
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    rcases hp with ⟨k, hk⟩
    omega
  have hq3 : 3 ≤ p ^ f := hp3.trans (Nat.le_self_pow hf.ne' p)
  have hq : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hp.pow (n := f))
    omega
  rcases hq with hq | hq
  · obtain ⟨-, he⟩ := h1 hq
    have := key _ he
    omega
  · obtain ⟨-, he⟩ := h3 hq
    have := key _ he
    omega

theorem card_centralizer_of_card_three {p f : ℕ} [Fact p.Prime] (hK : Nat.card K = p ^ f)
    (hp : Odd p) (hf : 0 < f) (h3 : p ^ f = 3) {t : PSL(2, K)} (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set PSL(2, K))) = 4 := by
  obtain ⟨-, h⟩ := psl2_centralizer_involution K hK hp hf ht
  rw [(h (by rw [h3])).1, h3]

theorem card_psl2_of_card {q : ℕ} (hK : IsOddPrimePower (Nat.card K)) (hq : Nat.card K = q) :
    Nat.card PSL(2, K) = q * (q ^ 2 - 1) / 2 := by
  rw [psl2_card_formula K hK, hq]

theorem subsingleton_ringEquiv_of_card_prime {p : ℕ} [Fact p.Prime] (hK : Nat.card K = p) :
    Subsingleton (K ≃+* K) := by
  have := Fintype.ofFinite K
  have hKF : Fintype.card K = p := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K p := charP_of_card_eq_prime hKF
  let e : ZMod p ≃+* K := ZMod.ringEquiv K hKF
  refine ⟨fun σ τ => RingEquiv.ext fun x => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective x
  have h1 : (σ : K →+* K).comp (e : ZMod p →+* K) = (τ : K →+* K).comp e :=
    RingHom.ext_zmod _ _
  exact DFunLike.congr_fun h1 a

theorem card_mulAut_psl2_le_of_card_five (hK : Nat.card K = 5) :
    Nat.card (MulAut PSL(2, K)) ≤ 120 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpp : IsOddPrimePower (Nat.card K) :=
    ⟨5, 1, Nat.prime_five, by decide, le_rfl, by rw [hK]; norm_num⟩
  have h3 : 3 < Nat.card K := by rw [hK]; norm_num
  have hsub := subsingleton_ringEquiv_of_card_prime K hK
  have hR : Nat.card (K ≃+* K) = 1 := by
    have : Unique (K ≃+* K) :=
      { default := RingEquiv.refl K, uniq := fun _ => Subsingleton.elim _ _ }
    exact Nat.card_unique
  have hP : Nat.card (PGammaL2 K) = 120 := by
    rw [SemidirectProduct.card, pgl2_card_formula, hR, hK]
    norm_num
  have : Finite (PGammaL2 K) := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  have := Nat.card_le_card_of_surjective _
    (pGammaL2ToMulAutPSL2_surjective K (p := 5) (f := 1) (by rw [hK]; norm_num) hpp h3)
  rwa [hP] at this

end CFSG.Walter.Suzuki
