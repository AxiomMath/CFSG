module

public import CFSG.RankThree.PartOne.U5K.Kf.Diagz

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.KCUnitaryModel

theorem exists_central_involution {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) :
    ∃ q ∈ Q, q ≠ 1 ∧ q * q = 1 ∧ ∀ q' ∈ Q, q * q' = q' * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hne
  have hZ := hQ.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center Q) := hQ.to_subgroup _
  obtain ⟨n, hn, hcard⟩ := hZ2.nontrivial_iff_card.1 hZ
  have hdvd : 2 ∣ Nat.card (Subgroup.center Q) := by
    rw [hcard]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxG : orderOf (((x : Q) : G)) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  refine ⟨((x : Q) : G), (x : Q).2, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hxG
    omega
  · rw [← pow_two]
    have := pow_orderOf_eq_one (((x : Q) : G))
    rwa [hxG] at this
  · intro q' hq'
    have := Subgroup.mem_center_iff.1 x.2 ⟨q', hq'⟩
    exact congrArg Subtype.val this.symm

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem ZetaData.exists_lift_involution (Z : ZetaData h p)
    {q : MulAut (primeFormP h (idGram K 5))}
    (hq : q ∈ (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range) (hq2 : q * q = 1) :
    ∃ y : primeFormUnitary h (idGram K 5), y * y = 1 ∧
      primeFormConjHom h (idGram K 5) y = q := by
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP (h := h) (idGram K 5) q).1 hq
  set y₁ : primeFormUnitary h (idGram K 5) := ⟨s, s.2.1⟩ with hy₁
  have hy₁q : primeFormConjHom h (idGram K 5) y₁ = q := hs.symm
  have h2 : y₁ * y₁ ∈ idScalarKernel h 5 := by
    rw [← Z.conj_eq_one_iff, map_mul, hy₁q]
    exact hq2
  obtain ⟨κ, hκq, hκ⟩ := h2
  have hf1 := h.one_le
  set m : ℕ := 2 ^ (f - 1) + 1 with hm
  have h2m : 2 * m = 2 ^ f + 2 := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp only [hm, Nat.add_sub_cancel, pow_succ]
    ring
  set c : Kˣ := κ⁻¹ ^ m with hc
  have hcq : c ^ (2 ^ f + 1) = 1 := by
    rw [hc, ← pow_mul, mul_comm, pow_mul, inv_pow, hκq, inv_one, one_pow]
  have hc2 : c * c = κ⁻¹ := by
    calc c * c = κ⁻¹ ^ (m + m) := by rw [hc]; exact (pow_add _ _ _).symm
      _ = κ⁻¹ ^ (2 ^ f + 1 + 1) := by congr 1; omega
      _ = κ⁻¹ ^ (2 ^ f + 1) * κ⁻¹ := pow_succ _ _
      _ = κ⁻¹ := by rw [inv_pow, hκq, inv_one, one_mul]
  refine ⟨scalarU (h := h) c hcq * y₁, ?_, ?_⟩
  · apply Subtype.ext
    have hY : (y₁ : GL (Fin 5) K) * (y₁ : GL (Fin 5) K) = GeneralLinearGroup.scalar (Fin 5) κ := by
      simpa using hκ
    rw [Subgroup.coe_mul, Subgroup.coe_mul, scalarU_coe, Subgroup.coe_one]
    calc (GeneralLinearGroup.scalar (Fin 5) c * (y₁ : GL (Fin 5) K)) *
          (GeneralLinearGroup.scalar (Fin 5) c * (y₁ : GL (Fin 5) K))
        = GeneralLinearGroup.scalar (Fin 5) c * ((y₁ : GL (Fin 5) K) *
            GeneralLinearGroup.scalar (Fin 5) c) * (y₁ : GL (Fin 5) K) := by group
      _ = GeneralLinearGroup.scalar (Fin 5) c * (GeneralLinearGroup.scalar (Fin 5) c *
            (y₁ : GL (Fin 5) K)) * (y₁ : GL (Fin 5) K) := by
          rw [(commute_scalar c (y₁ : GL (Fin 5) K)).eq]
      _ = GeneralLinearGroup.scalar (Fin 5) (c * c) * ((y₁ : GL (Fin 5) K) * y₁) := by
          rw [map_mul]
          group
      _ = 1 := by rw [hY, ← map_mul, hc2, inv_mul_cancel, map_one]
  · rw [map_mul, (Z.conj_eq_one_iff _).2 ⟨c, hcq, rfl⟩, one_mul, hy₁q]

end CFSG.RankThree.PartOne.U5K.Kf
