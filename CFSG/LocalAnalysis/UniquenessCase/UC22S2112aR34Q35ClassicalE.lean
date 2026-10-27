module

public import CFSG.GroupTheory.SylowPQMaximal.Defs
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalImprimSp
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalImprimSU
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalWeights
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalNormal
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalGL42
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35NaturalSpEnd
import CFSG.LieType.Classical.SteinbergBLSymplectic
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural

open CFSG.Open CFSG.GroupTheory
open Matrix

private theorem finite_of_card_eq_three_or_five {K : Type}
    (hK : Nat.card K = 3 ∨ Nat.card K = 5) : Finite K := by
  rcases hK with h | h
  · exact Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  · exact Nat.finite_of_card_ne_zero (by rw [h]; norm_num)

private theorem finite_of_card_eq_nine {K : Type} (hK : Nat.card K = 9) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)

variable {K : Type} [Field K]

private theorem charP_of_card_eq_prime {q : ℕ} (hq : q.Prime) (hK : Nat.card K = q) : CharP K q := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq.ne_zero)
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hcard : Fintype.card K = q := by rw [← Nat.card_eq_fintype_card, hK]
  have hdvd : ringChar K ∣ q := by
    rw [← hcard, hn]
    exact dvd_pow_self _ n.ne_zero
  exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hdvd)

private theorem ringChar_ne_two_of_card_eq_three_or_five (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    ringChar K ≠ 2 := by
  rcases hK with h | h
  · have h3 : CharP K 3 := charP_of_card_eq_prime (by norm_num) h
    have : ringChar K = 3 := ringChar.eq_iff.mpr h3
    omega
  · have h5 : CharP K 5 := charP_of_card_eq_prime (by norm_num) h
    have : ringChar K = 5 := ringChar.eq_iff.mpr h5
    omega

private theorem ringChar_ne_two_of_card_eq_nine (hK : Nat.card K = 9) : ringChar K ≠ 2 := by
  have hfin : Finite K := finite_of_card_eq_nine hK
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have h9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]
  have hpow : ringChar K ^ (n : ℕ) = 3 ^ 2 := by rw [← hn, h9]; norm_num
  have hdvd : ringChar K ∣ 3 ^ 2 := by
    rw [← hpow]
    exact dvd_pow_self _ n.pos.ne'
  have hdvd3 : ringChar K ∣ 3 := hp.dvd_of_dvd_pow hdvd
  have hp3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd3
  omega

private theorem not_isSquare_two_of_card_eq_three_or_five (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    ¬ IsSquare (2 : K) := by
  have hKfin : Finite K := finite_of_card_eq_three_or_five hK
  let : Fintype K := Fintype.ofFinite K
  rw [FiniteField.isSquare_two_iff]
  have hcard : Fintype.card K = 3 ∨ Fintype.card K = 5 := by
    rw [← Nat.card_eq_fintype_card]; exact hK
  rcases hcard with h | h <;> simp [h]

private theorem factorization_51840_two : (51840 : ℕ).factorization 2 = 7 := by
  rw [show (51840 : ℕ) = 2 ^ 7 * (3 ^ 4 * 5) by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self]
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (3 ^ 4 * 5 : ℕ))

private theorem factorization_9360000_two : (9360000 : ℕ).factorization 2 = 7 := by
  rw [show (9360000 : ℕ) = 2 ^ 7 * (3 ^ 2 * 5 ^ 4 * 13) by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self]
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (3 ^ 2 * 5 ^ 4 * 13 : ℕ))

private theorem factorization_13063680_two : (13063680 : ℕ).factorization 2 = 9 := by
  rw [show (13063680 : ℕ) = 2 ^ 9 * (3 ^ 6 * 5 * 7) by norm_num]
  rw [Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  simp [Nat.prime_two.factorization_self]
  exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ (3 ^ 6 * 5 * 7 : ℕ))

private theorem card_subgroupOf_statedScalars_eq_card_inf {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι K)) :
    Nat.card ((StatedScalars ι K).subgroupOf H) = Nat.card ↥(H ⊓ StatedScalars ι K) := by
  have h := Subgroup.card_map_of_injective (K := (StatedScalars ι K).subgroupOf H)
    (f := H.subtype) H.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, inf_comm] at h
  exact h.symm

private theorem card_scalars_statedSp_two (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) = 2 := by
  have hKfin : Finite K := finite_of_card_eq_three_or_five hK
  rw [card_subgroupOf_statedScalars_eq_card_inf,
    CFSG.LieType.Classical.card_statedSp_inf_statedScalars (n := 2) (by norm_num),
    CFSG.LieType.Classical.card_sq_eq_one_units]
  rcases hK with h | h <;> rw [h] <;> norm_num

private theorem scalar_injective_fin_four :
    Function.Injective (GeneralLinearGroup.scalar (Fin 4) : Kˣ →* GL (Fin 4) K) := by
  intro a b h
  have h1 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) h
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h1
  exact Units.ext h1

private theorem exists_units_orderOf_eq_four_of_card_eq_nine (hK : Nat.card K = 9) :
    ∃ i : Kˣ, orderOf i = 4 := by
  classical
  have hKfin : Finite K := finite_of_card_eq_nine hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 8 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
  refine ⟨g ^ 2, ?_⟩
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; norm_num), hord]

private theorem card_scalars_statedSU_four_three (hK : Nat.card K = 9) :
    Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 3 K)) = 4 := by
  classical
  have hKfin : Finite K := finite_of_card_eq_nine hK
  let : Fintype K := Fintype.ofFinite K
  rw [card_subgroupOf_statedScalars_eq_card_inf]
  have hmem : ∀ c : Kˣ, GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 3 K ↔ c ^ 4 = 1 := by
    intro c
    have h := CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 3) (f := 1) Nat.prime_three
      (by rw [hK]; norm_num) (n := 4) (by norm_num) (c := c)
    simpa using h
  have hcard : Nat.card ↥(StatedSU 4 3 K ⊓ StatedScalars (Fin 4) K) =
      Nat.card {c : Kˣ // c ^ 4 = 1} := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun c : {c : Kˣ // c ^ 4 = 1} =>
        (⟨GeneralLinearGroup.scalar (Fin 4) (c : Kˣ),
          Subgroup.mem_inf.2 ⟨(hmem (c : Kˣ)).2 c.2, ⟨(c : Kˣ), rfl⟩⟩⟩ :
          ↥(StatedSU 4 3 K ⊓ StatedScalars (Fin 4) K))) ⟨fun c d h => ?_, fun A => ?_⟩)).symm
    · exact Subtype.ext (scalar_injective_fin_four (congrArg Subtype.val h))
    · obtain ⟨hAS, c, hc⟩ := Subgroup.mem_inf.1 A.2
      rw [← hc] at hAS
      exact ⟨⟨c, (hmem c).1 hAS⟩, Subtype.ext hc⟩
  rw [hcard]
  refine le_antisymm ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (n := 4) (by norm_num)
  · obtain ⟨i, hiord⟩ := exists_units_orderOf_eq_four_of_card_eq_nine hK
    rw [Nat.card_eq_fintype_card]
    have hinj : Function.Injective
        (fun z : Subgroup.zpowers i => (⟨z.1, by
          have hz : z.1 ∈ Subgroup.zpowers i := z.2
          have hdvd : orderOf z.1 ∣ orderOf i := orderOf_dvd_of_mem_zpowers hz
          rw [hiord] at hdvd
          exact (orderOf_dvd_iff_pow_eq_one).1 hdvd⟩ : {c : Kˣ // c ^ 4 = 1})) := by
      intro a b h
      exact Subtype.ext (congrArg (fun x : {c : Kˣ // c ^ 4 = 1} => (x : Kˣ)) h)
    calc 4 = Fintype.card (Subgroup.zpowers i) := by rw [Fintype.card_zpowers, hiord]
      _ ≤ Fintype.card {c : Kˣ // c ^ 4 = 1} := Fintype.card_le_of_injective _ hinj

theorem sp4_sylowPQMaximal {K : Type} [Field K] (hK : Nat.card K = 3 ∨ Nat.card K = 5) :
    SylowPQMaximal 2 5 (StatedSp 2 K) := by
  classical
  intro P H hPH hH
  by_contra hnot
  have hKfin : Finite K := finite_of_card_eq_three_or_five hK
  let : Fintype K := Fintype.ofFinite K
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_three_or_five hK
  have hnotsq : ¬ IsSquare (2 : K) := not_isSquare_two_of_card_eq_three_or_five hK
  have hGfin : Finite (StatedSp 2 K) := Subtype.finite
  have hHfin : Finite H := Subtype.finite
  have hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 5 :=
    (isPiSubgroup_pair_iff (p := 2) (q := 5)).1 hH
  have h5 : 5 ∣ Nat.card H := by
    by_contra h5dvd
    apply hnot
    have hpos : Nat.card H ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have huniq : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card H → d = 2 := by
      intro d hd hdv
      rcases hΓ d hd hdv with h | h
      · exact h
      · exact absurd (h ▸ hdv) h5dvd
    have hpow : Nat.card H = 2 ^ (Nat.card H).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hpos huniq
    exact IsPGroup.of_card (p := 2) hpow
  let ρ : H →* GL (Fin 2 ⊕ Fin 2) K := (StatedSp 2 K).subtype.comp H.subtype
  have hρ : Function.Injective ρ := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hO5 : ∀ A : Subgroup H, A.Normal → IsPGroup 5 A → A = ⊥ := by
    intro A hA hA5
    have hAnorm : A.Normal := hA
    rcases hK with h3 | h5
    · exact sp4_three_eq_bot_of_normal_five h3 P H hPH hA5
    · exact sp4_five_eq_bot_of_normal_five h5 P H hPH hA5
  have hab : ∀ A : Subgroup H, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      IsPGroup 2 A → A ≤ (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ := by
    intro A hA hcomm hA2
    by_contra hns
    have hAnorm : A.Normal := hA
    obtain ⟨κ, W, hntriv, hind, htop, hW0, hperm⟩ :=
      exists_blocks_of_not_le_scalars (K := K) (ι := Fin 2 ⊕ Fin 2) hK2 ρ hcomm hA2 hns
    have hκ : Nontrivial κ := hntriv
    apply hnot
    exact sp4_isPGroup_of_blocks hK P H hPH hH (AlgebraicClosure K) W hind htop hW0
      (fun h hh i => by
        obtain ⟨j, hj⟩ := hperm ⟨h, hh⟩ i
        exact ⟨j, by simpa [ρ] using hj⟩)
  obtain ⟨N, hN, hcardN⟩ := exists_isQuatType (ι := Fin 2 ⊕ Fin 2) hK2
    (by norm_num : Fintype.card (Fin 2 ⊕ Fin 2) = 4) ρ hρ hΓ h5 hO5 hab
  let S₀ : Subgroup (StatedSp 2 K) :=
    (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)
  have hS0card : Nat.card S₀ = 2 := by
    simpa [S₀] using card_scalars_statedSp_two (K := K) hK
  have hS0p : IsPGroup 2 S₀ := IsPGroup.of_card (p := 2) (n := 1) (by simpa using hS0card)
  have hS0norm : S₀.Normal :=
    (inferInstance : (StatedScalars (Fin 2 ⊕ Fin 2) K).Normal).subgroupOf (StatedSp 2 K)
  have hS0P : S₀ ≤ (P : Subgroup (StatedSp 2 K)) := IsPGroup.le_sylow_of_normal hS0p P
  have hS0H : S₀ ≤ H := hS0P.trans hPH
  have hZs_card : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ) = 2 := by
    have hZs_eq : (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ = S₀.subgroupOf H := by
      ext g
      simp [S₀, ρ, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [hZs_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0H).toEquiv]
    exact hS0card
  have hNcard : Nat.card N = 32 := by rw [hcardN, hZs_card]
  have hι_card : Fintype.card (Fin 2 ⊕ Fin 2) = 4 := by norm_num
  have hι4 : ((Fintype.card (Fin 2 ⊕ Fin 2) : ℕ) : K) ≠ 0 := by
    rw [hι_card]
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
    have h4 : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [h4]
    exact mul_ne_zero h2 h2
  have hspan : Submodule.span K (Set.range fun x : N =>
      (ρ x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) = ⊤ :=
    span_eq_top_of_isQuatType (ι := Fin 2 ⊕ Fin 2) hK2 hι4 ρ hρ hN
      (by rw [hcardN, hι_card]; norm_num)
  have hker : ∀ g : H, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈
      (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ) → g ∈ N := by
    intro g hg
    have hA : ∀ x ∈ N, ρ g * ρ x * (ρ g)⁻¹ * (ρ x)⁻¹ ∈
        StatedScalars (Fin 2 ⊕ Fin 2) K := by
      intro x hx
      exact hg x hx
    obtain ⟨y, hyN, hyS⟩ := exists_mem_mul_inv_mem_scalars (ι := Fin 2 ⊕ Fin 2) hK2 hι4 ρ hρ
      hN hspan (ρ g) hA
    have hgy : g * y⁻¹ ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ := by
      rw [Subgroup.mem_comap, map_mul, map_inv]
      exact hyS
    have hgyN : g * y⁻¹ ∈ N := hN.scalars_le hgy
    have hyinv : y⁻¹ ∈ N := N.inv_mem hyN
    have hg_eq : g = (g * y⁻¹) * y := by group
    rw [hg_eq]
    exact N.mul_mem hgyN hyN
  have hZc : ∀ z ∈ (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ,
      ∀ g : H, g * z = z * g := by
    intro z hz g
    apply hρ
    rw [map_mul, map_mul]
    have hz'' : ρ z ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := Subgroup.mem_comap.mp hz
    have hz' : ρ z ∈ Subgroup.center (GL (Fin 2 ⊕ Fin 2) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hz''
    exact Subgroup.mem_center_iff.mp hz' (ρ g)
  have hZ2 : IsPGroup 2 ((StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ) :=
    isPGroup_two_scalars (ι := Fin 2 ⊕ Fin 2) ρ hρ hΓ hO5
  have hGfac : (Nat.card (StatedSp 2 K)).factorization 2 = 7 := by
    rcases hK with h3 | h5
    · rw [card_statedSp_two_of_card_eq_three h3]; exact factorization_51840_two
    · have hcard : Nat.card (StatedSp 2 K) = 9360000 := by
        rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two, h5]
        norm_num
      rw [hcard]; exact factorization_9360000_two
  have hPcard : Nat.card (P : Subgroup (StatedSp 2 K)) = 128 := by
    rw [P.card_eq_multiplicity, hGfac]
    norm_num
  have h16 : ¬ 16 * Nat.card N ∣ Nat.card H := by
    rw [hNcard]
    intro hdvd
    have hdvd' : (512 : ℕ) ∣ Nat.card H := by norm_num at hdvd ⊢; exact hdvd
    have hdvdG : (512 : ℕ) ∣ Nat.card (StatedSp 2 K) :=
      hdvd'.trans (Subgroup.card_subgroup_dvd_card H)
    have h9 : 9 ≤ (Nat.card (StatedSp 2 K)).factorization 2 := by
      have h512 : (2 ^ 9 : ℕ) ∣ Nat.card (StatedSp 2 K) := by
        rwa [show (2 ^ 9 : ℕ) = 512 by norm_num]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization
        (n := Nat.card (StatedSp 2 K)) (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)).1 h512
    rw [hGfac] at h9
    omega
  have h4 : 4 * Nat.card N ∣ Nat.card H := by
    rw [hNcard]
    have h128 : 4 * 32 = 128 := by norm_num
    rw [h128, ← hPcard]
    exact Subgroup.card_dvd_of_le hPH
  have hNnorm : N.Normal := hN.normal
  obtain ⟨c, g, hc, hg⟩ := exists_conj_eq_sq
    (Z := (StatedScalars (Fin 2 ⊕ Fin 2) K).comap ρ) (N := N)
    hN.scalars_le hZc hZ2 hcardN hN.sq_mem hker hΓ h5 h16 h4
  exact sp4_false_of_conj_eq_sq hK2 hnotsq ρ hρ (fun g => (g : H).1.2) hN hcardN hc hg

theorem sp4_three_sylowPQMaximal {K : Type} [Field K] (hK : Nat.card K = 3) :
    SylowPQMaximal 2 5 (StatedSp 2 K) :=
  sp4_sylowPQMaximal (Or.inl hK)

theorem sp4_five_sylowPQMaximal {K : Type} [Field K] (hK : Nat.card K = 5) :
    SylowPQMaximal 2 5 (StatedSp 2 K) :=
  sp4_sylowPQMaximal (Or.inr hK)

theorem su4_three_sylowPQMaximal {K : Type} [Field K] (hK : Nat.card K = 9) :
    SylowPQMaximal 2 5 (StatedSU 4 3 K) := by
  classical
  intro P H hPH hH
  by_contra hnot
  have hKfin : Finite K := finite_of_card_eq_nine hK
  let : Fintype K := Fintype.ofFinite K
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_card_eq_nine hK
  have hGfin : Finite (StatedSU 4 3 K) := Subtype.finite
  have hHfin : Finite H := Subtype.finite
  have hΓ : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 5 :=
    (isPiSubgroup_pair_iff (p := 2) (q := 5)).1 hH
  have h5 : 5 ∣ Nat.card H := by
    by_contra h5dvd
    apply hnot
    have hpos : Nat.card H ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have huniq : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card H → d = 2 := by
      intro d hd hdv
      rcases hΓ d hd hdv with h | h
      · exact h
      · exact absurd (h ▸ hdv) h5dvd
    have hpow : Nat.card H = 2 ^ (Nat.card H).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd hpos huniq
    exact IsPGroup.of_card (p := 2) hpow
  let ρ : H →* GL (Fin 4) K := (StatedSU 4 3 K).subtype.comp H.subtype
  have hρ : Function.Injective ρ := by
    intro a b hab
    exact Subtype.ext (Subtype.ext hab)
  have hO5 : ∀ A : Subgroup H, A.Normal → IsPGroup 5 A → A = ⊥ := by
    intro A hA hA5
    have hAnorm : A.Normal := hA
    exact su4_three_eq_bot_of_normal_five hK P H hPH hA5
  have hab : ∀ A : Subgroup H, A.Normal → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      IsPGroup 2 A → A ≤ (StatedScalars (Fin 4) K).comap ρ := by
    intro A hA hcomm hA2
    by_contra hns
    have hAnorm : A.Normal := hA
    obtain ⟨κ, W, hntriv, hind, htop, hW0, hperm⟩ :=
      exists_blocks_of_not_le_scalars (K := K) (ι := Fin 4) hK2 ρ hcomm hA2 hns
    have hκ : Nontrivial κ := hntriv
    apply hnot
    exact su4_three_isPGroup_of_blocks hK P H hPH hH (AlgebraicClosure K) W hind htop hW0
      (fun h hh i => by
        obtain ⟨j, hj⟩ := hperm ⟨h, hh⟩ i
        exact ⟨j, by simpa [ρ] using hj⟩)
  obtain ⟨N, hN, hcardN⟩ := exists_isQuatType (ι := Fin 4) hK2
    (by norm_num : Fintype.card (Fin 4) = 4) ρ hρ hΓ h5 hO5 hab
  let S₀ : Subgroup (StatedSU 4 3 K) :=
    (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 3 K)
  have hS0card : Nat.card S₀ = 4 := by
    simpa [S₀] using card_scalars_statedSU_four_three (K := K) hK
  have hS0p : IsPGroup 2 S₀ := IsPGroup.of_card (p := 2) (n := 2) (by simpa using hS0card)
  have hS0norm : S₀.Normal :=
    (inferInstance : (StatedScalars (Fin 4) K).Normal).subgroupOf (StatedSU 4 3 K)
  have hS0P : S₀ ≤ (P : Subgroup (StatedSU 4 3 K)) := IsPGroup.le_sylow_of_normal hS0p P
  have hS0H : S₀ ≤ H := hS0P.trans hPH
  have hZs_card : Nat.card ((StatedScalars (Fin 4) K).comap ρ) = 4 := by
    have hZs_eq : (StatedScalars (Fin 4) K).comap ρ = S₀.subgroupOf H := by
      ext g
      simp [S₀, ρ, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [hZs_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS0H).toEquiv]
    exact hS0card
  have hNcard : Nat.card N = 64 := by rw [hcardN, hZs_card]
  have hι_card : Fintype.card (Fin 4) = 4 := by norm_num
  have hι4 : ((Fintype.card (Fin 4) : ℕ) : K) ≠ 0 := by
    rw [hι_card]
    have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
    have h4 : ((4 : ℕ) : K) = 2 * 2 := by norm_num
    rw [h4]
    exact mul_ne_zero h2 h2
  have hspan : Submodule.span K (Set.range fun x : N =>
      (ρ x : Matrix (Fin 4) (Fin 4) K)) = ⊤ :=
    span_eq_top_of_isQuatType (ι := Fin 4) hK2 hι4 ρ hρ hN
      (by rw [hcardN, hι_card]; norm_num)
  have hker : ∀ g : H, (∀ x ∈ N, g * x * g⁻¹ * x⁻¹ ∈
      (StatedScalars (Fin 4) K).comap ρ) → g ∈ N := by
    intro g hg
    have hA : ∀ x ∈ N, ρ g * ρ x * (ρ g)⁻¹ * (ρ x)⁻¹ ∈ StatedScalars (Fin 4) K := by
      intro x hx
      exact hg x hx
    obtain ⟨y, hyN, hyS⟩ := exists_mem_mul_inv_mem_scalars (ι := Fin 4) hK2 hι4 ρ hρ
      hN hspan (ρ g) hA
    have hgy : g * y⁻¹ ∈ (StatedScalars (Fin 4) K).comap ρ := by
      rw [Subgroup.mem_comap, map_mul, map_inv]
      exact hyS
    have hgyN : g * y⁻¹ ∈ N := hN.scalars_le hgy
    have hyinv : y⁻¹ ∈ N := N.inv_mem hyN
    have hg_eq : g = (g * y⁻¹) * y := by group
    rw [hg_eq]
    exact N.mul_mem hgyN hyN
  have hZc : ∀ z ∈ (StatedScalars (Fin 4) K).comap ρ, ∀ g : H, g * z = z * g := by
    intro z hz g
    apply hρ
    rw [map_mul, map_mul]
    have hz'' : ρ z ∈ StatedScalars (Fin 4) K := Subgroup.mem_comap.mp hz
    have hz' : ρ z ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hz''
    exact Subgroup.mem_center_iff.mp hz' (ρ g)
  have hZ2 : IsPGroup 2 ((StatedScalars (Fin 4) K).comap ρ) :=
    isPGroup_two_scalars (ι := Fin 4) ρ hρ hΓ hO5
  have hGfac : (Nat.card (StatedSU 4 3 K)).factorization 2 = 9 := by
    rw [card_statedSU_four_three hK]
    exact factorization_13063680_two
  have hPcard : Nat.card (P : Subgroup (StatedSU 4 3 K)) = 512 := by
    rw [P.card_eq_multiplicity, hGfac]
    norm_num
  have h16 : ¬ 16 * Nat.card N ∣ Nat.card H := by
    rw [hNcard]
    intro hdvd
    have hdvd' : (1024 : ℕ) ∣ Nat.card H := by norm_num at hdvd ⊢; exact hdvd
    have hdvdG : (1024 : ℕ) ∣ Nat.card (StatedSU 4 3 K) :=
      hdvd'.trans (Subgroup.card_subgroup_dvd_card H)
    have h10 : 10 ≤ (Nat.card (StatedSU 4 3 K)).factorization 2 := by
      have h1024 : (2 ^ 10 : ℕ) ∣ Nat.card (StatedSU 4 3 K) := by
        rwa [show (2 ^ 10 : ℕ) = 1024 by norm_num]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization
        (n := Nat.card (StatedSU 4 3 K)) (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩)).1 h1024
    rw [hGfac] at h10
    omega
  have h8 : 8 * Nat.card N ∣ Nat.card H := by
    rw [hNcard]
    have h512 : 8 * 64 = 512 := by norm_num
    rw [h512, ← hPcard]
    exact Subgroup.card_dvd_of_le hPH
  have hNnorm : N.Normal := hN.normal
  exact (not_eight_mul_dvd_card (Z := (StatedScalars (Fin 4) K).comap ρ) (N := N)
    hN.scalars_le hZc hZ2 hcardN hN.sq_mem hker hΓ h5 h16) h8

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Natural
