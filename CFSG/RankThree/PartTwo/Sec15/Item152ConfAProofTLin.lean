module

import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG
open Matrix
open scoped commutatorElement

namespace Proof152ConfA

theorem eq_one_of_mulVec_eq_self {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (M : GL (Fin 2) (ZMod p)) (hdet : (M : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1) {k : ℕ}
    (hk : M ^ 2 ^ k = 1) {v : Fin 2 → ZMod p} (hv : v ≠ 0)
    (hMv : (M : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ v = v) : M = 1 := by
  set N : Matrix (Fin 2) (Fin 2) (ZMod p) := (M : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 with hN
  have hNv : N *ᵥ v = 0 := by rw [hN, sub_mulVec, one_mulVec, hMv, sub_self]
  have hdetN : N.det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨v, hv, hNv⟩
  have hN2 : N * N = 0 := by
    rw [Matrix.det_fin_two] at hdet hdetN
    simp only [hN, Matrix.sub_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at hdetN
    ext i j
    fin_cases i <;> fin_cases j
    · simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination ((M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 - 1) * hdet -
        (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 * hdetN
    · simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 * hdet -
        (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 * hdetN
    · simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 * hdet -
        (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 * hdetN
    · simp [hN, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      linear_combination ((M : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 - 1) * hdet -
        (M : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 1 * hdetN
  have hM : (M : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 + N := by rw [hN]; abel
  have hpow : ∀ n : ℕ, (M : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n = 1 + (n : ZMod p) • N := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, hM, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hN2, smul_zero,
        add_zero, Nat.cast_succ, add_smul, one_smul]
      abel
  have h1 := congrArg (fun U : GL (Fin 2) (ZMod p) => (U : Matrix (Fin 2) (Fin 2) (ZMod p))) hk
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h1
  rw [hpow] at h1
  have h2 : ((2 ^ k : ℕ) : ZMod p) • N = 0 := add_eq_left.mp h1
  have h3 : ((2 ^ k : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have hN0 : N = 0 := (smul_eq_zero.mp h2).resolve_left h3
  apply Units.ext
  rw [Units.val_one, hM, hN0, add_zero]

variable {G : Type} [Group G] [Finite G]

theorem eq_commutator_of_isPGroup_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P H₁ H₂ : Subgroup G}
    (hP : IsPGroup p P) (hV : Nat.card (↥P ⧸ frattini ↥P) = p ^ 2)
    (h₁ : H₁ ≤ Subgroup.normalizer (P : Set G)) (h₂ : H₂ ≤ Subgroup.normalizer (P : Set G))
    (hU2 : IsPGroup 2 ↥(⁅H₁, H₂⁆ : Subgroup G))
    (hUC : ¬ ⁅H₁, H₂⁆ ≤ Subgroup.centralizer (P : Set G)) :
    P = ⁅⁅H₁, H₂⁆, P⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hΦc, hcomm, hpow, -, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (W := ↥P ⧸ frattini ↥P) (fun a b => hcomm.is_comm.comm a b) hpow hV
  set Nn := Subgroup.normalizer (P : Set G) with hNn
  set σ : Nn →* MulAut ↥P := P.normalizerMonoidHom with hσ
  set ρ : Nn →* GL (Fin 2) (ZMod p) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp
      ((CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥P)).comp σ)
    with hρ
  have hUN : ⁅H₁, H₂⁆ ≤ Nn :=
    (Subgroup.commutator_mono h₁ h₂).trans (Subgroup.commutator_le_self Nn)
  have hdetU : ⁅H₁, H₂⁆ ≤ ((Matrix.GeneralLinearGroup.det.comp ρ).ker).map Nn.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, h₁ ha⟩ : Nn), ⟨b, h₂ hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  obtain ⟨u, huU, huC⟩ := Set.not_subset.mp hUC
  have huN : u ∈ Nn := hUN huU
  obtain ⟨k, hk⟩ := hU2 ⟨u, huU⟩
  have hk' : u ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set M := ρ ⟨u, huN⟩ with hM
  have hMk : M ^ 2 ^ k = 1 := by
    rw [hM, ← map_pow]
    have : (⟨u, huN⟩ : Nn) ^ 2 ^ k = 1 := Subtype.ext hk'
    rw [this, map_one]
  have hMdet : (M : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    obtain ⟨n, hn, hnu⟩ := hdetU huU
    have hn' : n = ⟨u, huN⟩ := Subtype.ext hnu
    rw [hn'] at hn
    have h1 : Matrix.GeneralLinearGroup.det M = 1 := hn
    have := congrArg Units.val h1
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hM1 : M ≠ 1 := by
    intro hM1
    apply huC
    have hker : σ ⟨u, huN⟩ ∈
        (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥P)).ker := by
      rw [MonoidHom.mem_ker]
      apply (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective
      rw [map_one]
      exact hM1
    obtain ⟨j, hj⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hP).2 ⟨_, hker⟩
    have hj' : (σ ⟨u, huN⟩) ^ p ^ j = 1 := congrArg Subtype.val hj
    have hk'' : (σ ⟨u, huN⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨u, huN⟩ : Nn) ^ 2 ^ k = 1 := Subtype.ext hk'
      rw [this, map_one]
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hj') (orderOf_dvd_of_pow_eq_one hk'')
    rw [(Nat.coprime_pow_primes j k Fact.out Nat.prime_two hp2).gcd_eq_one, Nat.dvd_one,
      orderOf_eq_one_iff] at h1
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg (fun τ : MulAut ↥P => ((τ ⟨x, hx⟩ : ↥P) : G)) h1
    simp only [hσ, MulAut.one_apply] at this
    rw [Sec4.normalizerMonoidHom_apply_coe] at this
    calc x * u = u * x * u⁻¹ * u := by rw [this]
      _ = u * x := by group
  have hCP : P ⊓ Subgroup.centralizer (Subgroup.zpowers u : Set G) ≤
      (frattini ↥P).map P.subtype := by
    intro y hy
    have hyu : u * y * u⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.mp hy.2 u (Subgroup.mem_zpowers u)
      calc u * y * u⁻¹ = y * u * u⁻¹ := by rw [this]
        _ = y := by group
    have hfix : σ ⟨u, huN⟩ ⟨y, hy.1⟩ = ⟨y, hy.1⟩ := by
      apply Subtype.ext
      rw [hσ, Sec4.normalizerMonoidHom_apply_coe]
      exact hyu
    set w : ↥P ⧸ frattini ↥P := ((⟨y, hy.1⟩ : ↥P) : ↥P ⧸ frattini ↥P) with hw
    have hwfix : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥P)
        (σ ⟨u, huN⟩) w = w := by
      rw [hw, (CFSG.GroupTheory.frattini_automorphism_kernel hP).1, hfix]
    by_contra hyΦ
    have hw1 : w ≠ 1 := by
      intro h
      apply hyΦ
      exact ⟨⟨y, hy.1⟩, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
    have hv : Multiplicative.toAdd (e w) ≠ 0 := by
      intro h
      apply hw1
      apply e.injective
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [h]; rfl)
    have hMv := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e
      (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥P)
        (σ ⟨u, huN⟩)) w
    rw [hwfix] at hMv
    exact hM1 (eq_one_of_mulVec_eq_self hp2 M hMdet hMk hv hMv)
  have hZ2 : IsPGroup 2 (Subgroup.zpowers u) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk',
      _root_.one_zpow]
  have hP2 : ¬ 2 ∣ Nat.card P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
    rw [hn]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  have hZN : Subgroup.zpowers u ≤ Subgroup.normalizer (P : Set G) := Subgroup.zpowers_le.mpr huN
  have hfac := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    2 Nat.prime_two (Subgroup.zpowers u) P hZ2 hP2 hZN
  have hcP : ⁅P, Subgroup.zpowers u⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hZN
  have hPle : P ≤ ⁅P, Subgroup.zpowers u⁆ ⊔ (frattini ↥P).map P.subtype :=
    (le_of_eq hfac).trans (sup_le_sup_left hCP _)
  have htop : (⁅P, Subgroup.zpowers u⁆).subgroupOf P ⊔ frattini ↥P = ⊤ := by
    rw [eq_top_iff]
    have h1 : ((⁅P, Subgroup.zpowers u⁆ ⊔ (frattini ↥P).map P.subtype).subgroupOf P) =
        (⁅P, Subgroup.zpowers u⁆).subgroupOf P ⊔ frattini ↥P := by
      rw [Subgroup.subgroupOf_sup hcP (Subgroup.map_subtype_le _), Subgroup.subgroupOf,
        Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    rw [← h1]
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (hPle x.2)
  have hK := frattini_nongenerating htop
  have hPc : P ≤ ⁅P, Subgroup.zpowers u⁆ := by
    intro x hx
    have : (⟨x, hx⟩ : ↥P) ∈ (⁅P, Subgroup.zpowers u⁆).subgroupOf P := hK ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  refine le_antisymm (hPc.trans ?_) ?_
  · rw [Subgroup.commutator_comm (⁅H₁, H₂⁆)]
    exact Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr huU)
  · rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hUN

end Proof152ConfA

end CFSG.RankThree.PartTwo.Sec15
