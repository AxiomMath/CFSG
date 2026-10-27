module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.H13.U43

variable {G : Type} [Group G] [Finite G]

theorem exists_central_involution_of_ne_bot {A : Subgroup G} (hA : IsPGroup 2 A) (h1 : A ≠ ⊥) :
    ∃ c ∈ A, orderOf c = 2 ∧ ∀ s ∈ A, s * c = c * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 h1
  have hcnt : Nontrivial (Subgroup.center A) := hA.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center A) := hA.to_subgroup _
  have hdvd : 2 ∣ Nat.card (Subgroup.center A) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hZ
    have hk0 : k ≠ 0 := by
      rintro rfl
      have h1 : Nat.card (Subgroup.center A) = 1 := by simpa using hk
      have := Finite.one_lt_card_iff_nontrivial.mpr hcnt
      omega
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center A) 2 hdvd
  refine ⟨((y : A) : G), (y : A).2, ?_, fun s hs => ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hy
  · have := Subgroup.mem_center_iff.mp y.2 ⟨s, hs⟩
    exact congrArg Subtype.val this

omit [Finite G] in
theorem commute_pow_conj_of_normalizes {A : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (A : Set G)) (hcA : c ∈ A) (hc : ∀ s ∈ A, s * c = c * s)
    (i : ℕ) : c * (y ^ i * c * (y ^ i)⁻¹) = (y ^ i * c * (y ^ i)⁻¹) * c := by
  have hyi : y ^ i ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hy i
  have hmem : y ^ i * c * (y ^ i)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hyi c).mp hcA
  exact (hc _ hmem).symm

theorem exists_conj_pow {p : ℕ} [Fact p.Prime] {x₀ x : G} (hx₀ : orderOf x₀ = p)
    (hx : orderOf x = p) (hsyl : (Nat.card G).factorization p = 1) :
    ∃ (g : G) (k : ℕ), g⁻¹ * x * g = x₀ ^ k := by
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow p G, (P₀ : Subgroup G) = Subgroup.zpowers x₀ :=
    ⟨Sylow.ofCard (Subgroup.zpowers x₀) (by rw [Nat.card_zpowers, hx₀, hsyl, pow_one]), rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Sylow p G, (P : Subgroup G) = Subgroup.zpowers x :=
    ⟨Sylow.ofCard (Subgroup.zpowers x) (by rw [Nat.card_zpowers, hx, hsyl, pow_one]), rfl⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
  have hxP : x ∈ (P : Subgroup G) := by
    rw [hP]
    exact Subgroup.mem_zpowers x
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxP
  obtain ⟨s, hs, hsx⟩ := hxP
  rw [hP₀] at hs
  have hsx' : g * s * g⁻¹ = x := by simpa using hsx
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s x₀).1 (mem_powers_iff_mem_zpowers.2 hs)
  refine ⟨g, n, ?_⟩
  rw [hn, ← hsx']
  group

theorem exists_noncommute_pow {x₀ x f : G} (hx₀ : orderOf x₀ = 7)
    (hsyl : (Nat.card G).factorization 7 = 1) (hx : orderOf x = 7) (hf : orderOf f = 2)
    (h₀ : ∀ f : G, orderOf f = 2 →
      ¬ (f * (x₀ * f * x₀⁻¹) = (x₀ * f * x₀⁻¹) * f ∧
        f * (x₀ ^ 2 * f * (x₀ ^ 2)⁻¹) = (x₀ ^ 2 * f * (x₀ ^ 2)⁻¹) * f)) :
    ∃ i : ℕ, ¬ (f * (x ^ i * f * (x ^ i)⁻¹) = (x ^ i * f * (x ^ i)⁻¹) * f) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, k, hk⟩ := exists_conj_pow hx₀ hx hsyl
  by_contra hcon
  push Not at hcon
  set φ := MulAut.conj g⁻¹ with hφ
  have hφx : φ x = x₀ ^ k := by
    rw [hφ, MulAut.conj_apply, inv_inv]
    exact hk
  have hforder : orderOf (φ f) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact hf
  have hcomm : ∀ i : ℕ, φ f * ((x₀ ^ k) ^ i * φ f * ((x₀ ^ k) ^ i)⁻¹) =
      ((x₀ ^ k) ^ i * φ f * ((x₀ ^ k) ^ i)⁻¹) * φ f := by
    intro i
    have h' := congrArg φ (hcon i)
    simpa only [map_mul, map_inv, map_pow, hφx] using h'
  have hk7 : ¬ 7 ∣ k := by
    intro hd
    have h1 : x₀ ^ k = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hx₀]; exact hd)
    have h2 : orderOf (φ x) = 7 := by rw [MulEquiv.orderOf_eq]; exact hx
    rw [hφx, h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hcop : Nat.Coprime k 7 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk7)
  obtain ⟨i₁, -, hi₁⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop (by norm_num : (7 : ℕ) ≠ 0)
  obtain ⟨i₂, -, hi₂⟩ := Nat.exists_mul_mod_eq_of_coprime 2 hcop (by norm_num : (7 : ℕ) ≠ 0)
  have hp1 : x₀ ^ (k * i₁) = x₀ := by
    have h := pow_mod_orderOf x₀ (k * i₁)
    rw [hx₀, hi₁] at h
    simpa using h.symm
  have hp2 : x₀ ^ (k * i₂) = x₀ ^ 2 := by
    have h := pow_mod_orderOf x₀ (k * i₂)
    rw [hx₀, hi₂] at h
    simpa using h.symm
  apply h₀ (φ f) hforder
  refine ⟨?_, ?_⟩
  · have := hcomm i₁
    rwa [← pow_mul, hp1] at this
  · have := hcomm i₂
    rwa [← pow_mul, hp2] at this

theorem no_seven_normalizes_two_group
    (hQ : ∀ x f : G, orderOf x = 7 → orderOf f = 2 →
      ∃ i : ℕ, ¬ (f * (x ^ i * f * (x ^ i)⁻¹) = (x ^ i * f * (x ^ i)⁻¹) * f))
    {y : G} (hy : orderOf y = 7) {A : Subgroup G} (hA : IsPGroup 2 A) (h1 : A ≠ ⊥)
    (hn : y ∈ Subgroup.normalizer (A : Set G)) : False := by
  obtain ⟨c, hcA, hco, hc⟩ := exists_central_involution_of_ne_bot hA h1
  obtain ⟨i, hi⟩ := hQ y c hy hco
  exact hi (commute_pow_conj_of_normalizes hn hcA hc i)

end CFSG.Quasithin.H13.U43
