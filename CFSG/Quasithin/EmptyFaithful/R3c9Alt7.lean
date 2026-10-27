module

public import CFSG.Quasithin.EmptyFaithful.R3c9Four

public section

namespace CFSG.Quasithin.R3c9

open Equiv

@[expose] def r3c9Rho : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5

@[expose] def r3c9Sigma : Perm (Fin 7) := swap 1 3 * swap 4 5

theorem r3c9Rho_mem : r3c9Rho ∈ alternatingGroup (Fin 7) := by
  change Perm.sign r3c9Rho = 1
  rw [r3c9Rho, Perm.sign_mul, Perm.sign_mul, Perm.sign_mul,
    Perm.sign_swap (by decide : (0 : Fin 7) ≠ 1), Perm.sign_swap (by decide : (1 : Fin 7) ≠ 2),
    Perm.sign_swap (by decide : (2 : Fin 7) ≠ 3), Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5)]
  norm_num

theorem r3c9Sigma_mem : r3c9Sigma ∈ alternatingGroup (Fin 7) := by
  change Perm.sign r3c9Sigma = 1
  rw [r3c9Sigma, Perm.sign_mul, Perm.sign_swap (by decide : (1 : Fin 7) ≠ 3),
    Perm.sign_swap (by decide : (4 : Fin 7) ≠ 5)]
  norm_num

theorem exists_noncomm_two_subgroup_alt7 :
    ∃ H : Subgroup (alternatingGroup (Fin 7)), IsPGroup 2 H ∧
      ∃ x ∈ H, ∃ y ∈ H, x * y ≠ y * x := by
  set ρ : alternatingGroup (Fin 7) := ⟨r3c9Rho, r3c9Rho_mem⟩
  set σ : alternatingGroup (Fin 7) := ⟨r3c9Sigma, r3c9Sigma_mem⟩
  have hσ2 : σ * σ = 1 := Subtype.ext (by decide)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by decide)
  have hne : ρ * σ ≠ σ * ρ := fun h => by
    have := congrArg Subtype.val h
    revert this
    decide
  have hρ4 : orderOf ρ = 4 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf r3c9Rho = 4
    apply (orderOf_eq_iff (by norm_num)).mpr
    constructor
    · decide
    · intro m hm0 hm4
      interval_cases m <;> decide
  have hσU : σ ∉ Subgroup.zpowers ρ := by
    rintro ⟨k, hk⟩
    apply hne
    rw [← hk]
    exact ((Commute.refl ρ).zpow_left k).eq.symm
  have hinv : ∀ x ∈ Subgroup.zpowers ρ, σ * x * σ⁻¹ = x⁻¹ := by
    rintro _ ⟨k, rfl⟩
    have := map_zpow (MulAut.conj σ) ρ k
    simp only [MulAut.conj_apply] at this
    rw [this, hrel, inv_zpow]
  obtain ⟨d⟩ := CFSG.Walter.nonempty_sup_zpowers_mulEquiv_dihedralGroup (Subgroup.zpowers ρ) σ hσU hσ2
    hinv
  refine ⟨Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ, IsPGroup.of_card (n := 3) ?_, ρ,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ), σ, Subgroup.mem_sup_right (Subgroup.mem_zpowers σ), hne⟩
  rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card, Nat.card_zpowers, hρ4]
  norm_num

theorem mem_smul_sylow_iff_conj {H : Type*} [Group H] {p : ℕ} (P : Sylow p H) (g d : H) :
    d ∈ ((g • P : Sylow p H) : Subgroup H) ↔ g⁻¹ * d * g ∈ (P : Subgroup H) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.smul_def, MulAut.conj_apply, show g⁻¹ * (g * y * g⁻¹) * g = y by group]
    exact hy
  · intro h
    exact ⟨_, h, by rw [MulAut.smul_def, MulAut.conj_apply]; group⟩

theorem a7_sylow_two_not_comm (P : Sylow 2 (alternatingGroup (Fin 7))) :
    ∃ x ∈ (P : Subgroup (alternatingGroup (Fin 7))), ∃ y ∈ (P : Subgroup (alternatingGroup (Fin 7))),
      x * y ≠ y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ := exists_noncomm_two_subgroup_alt7
  obtain ⟨Q, hQ⟩ := hH2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) Q P
  have hmem : ∀ z ∈ H, g * z * g⁻¹ ∈ (P : Subgroup (alternatingGroup (Fin 7))) := by
    intro z hz
    rw [← hg, mem_smul_sylow_iff_conj, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact hQ hz
  refine ⟨_, hmem x hx, _, hmem y hy, fun h => hxy ?_⟩
  calc x * y = g⁻¹ * (g * x * g⁻¹ * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * y * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
    _ = y * x := by group

theorem card_a7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem fourSelfCentTwo_alt7 : FourSelfCentTwo (alternatingGroup (Fin 7)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro V hV4 hV2 hVc c hc ⟨k, hk⟩
  by_contra hcV
  have hcomm : ∀ (v : ↥V) (x : ↥(Subgroup.zpowers c)),
      Commute (V.subtype v) ((Subgroup.zpowers c).subtype x) := by
    intro v x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    have h1 : Commute (v : alternatingGroup (Fin 7)) c := (hc v v.2).symm
    show Commute (v : alternatingGroup (Fin 7)) (x : alternatingGroup (Fin 7))
    rw [← hn]
    exact h1.zpow_right n
  let φ : ↥V × ↥(Subgroup.zpowers c) →* alternatingGroup (Fin 7) :=
    V.subtype.noncommCoprod (Subgroup.zpowers c).subtype hcomm
  have hφ : ∀ a : ↥V × ↥(Subgroup.zpowers c),
      φ a = (a.1 : alternatingGroup (Fin 7)) * (a.2 : alternatingGroup (Fin 7)) := fun a => rfl
  let W : Subgroup (alternatingGroup (Fin 7)) := φ.range
  have hVW : V ≤ W := fun v hv => ⟨(⟨v, hv⟩, 1), by simp [hφ]⟩
  have hcW : c ∈ W := ⟨(1, ⟨c, Subgroup.mem_zpowers c⟩), by simp [hφ]⟩
  have hWcard : Nat.card W ∣ 2 ^ (k + 2) := by
    have h1 : Nat.card W ∣ Nat.card (↥V × ↥(Subgroup.zpowers c)) := Subgroup.card_range_dvd φ
    have h2 : Nat.card (↥V × ↥(Subgroup.zpowers c)) = 2 ^ (k + 2) := by
      rw [Nat.card_prod, hV4, Nat.card_zpowers, hk]
      ring
    rw [← h2]
    exact h1
  obtain ⟨j, hj, hjW⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hWcard
  have hgt : 4 < Nat.card W := by
    by_contra hle
    push Not at hle
    have := Subgroup.eq_of_le_of_card_ge hVW (by rw [hV4]; exact hle)
    exact hcV (this ▸ hcW)
  have hdvd : Nat.card W ∣ 2520 := by
    rw [← card_a7]
    exact Subgroup.card_subgroup_dvd_card W
  have hj3 : j = 3 := by
    rw [hjW] at hgt hdvd
    have h1 : 3 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j <;> omega
    have h2 : j ≤ 3 := by
      by_contra h
      push Not at h
      have h3 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have h4 := h3.trans hdvd
      omega
    omega
  have hW8 : Nat.card W = 8 := by rw [hjW, hj3]; norm_num
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    refine Prod.ext (Subtype.ext (hVc _ a.1.2 _ b.1.2)) (Subtype.ext ?_)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2.2
    show (a.2 : alternatingGroup (Fin 7)) * (b.2 : alternatingGroup (Fin 7)) =
      (b.2 : alternatingGroup (Fin 7)) * (a.2 : alternatingGroup (Fin 7))
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self c m n).eq
  let P : Sylow 2 (alternatingGroup (Fin 7)) := Sylow.ofCard W (by
    rw [hW8, card_a7, show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num)
  obtain ⟨x, hx, y, hy, hxy⟩ := a7_sylow_two_not_comm P
  exact hxy (hWab x hx y hy)

end CFSG.Quasithin.R3c9
