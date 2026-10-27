module

public import CFSG.LieType.Chevalley.RankOneGaussian
public import Mathlib.GroupTheory.Sylow
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof

open CFSG.LieType.Chevalley

variable {K : Type} [Field K]

@[expose] def HSLHom (K : Type) [Field K] : Kˣ →* SL2 K where
  toFun := HSL
  map_one' := by
    apply Subtype.ext
    rw [coe_HSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_HSL, coe_HSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem HSLHom_apply (t : Kˣ) : HSLHom K t = HSL t := rfl

theorem HSLHom_injective : Function.Injective (HSLHom K) := by
  intro a b h
  have h1 := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simp only [HSLHom_apply, coe_HSL] at h1
  exact Units.ext (by simpa using h1)

theorem exists_conj_le_sylow' {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (Q : Sylow p G) (E : Subgroup G) (hE : IsPGroup p E) :
    ∃ y : G, E.map (MulAut.conj y).toMonoidHom ≤ Q := by
  obtain ⟨S, hES⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨g, ?_⟩
  have hgS : (g • S : Sylow p G).toSubgroup = S.toSubgroup.map (MulAut.conj g).toMonoidHom := rfl
  rw [hg] at hgS
  rw [hgS]
  exact Subgroup.map_mono hES

theorem factorization_three_sl2 [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    (Nat.card (SL2 K)).factorization 3 = (Nat.card K - 1).factorization 3 := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  have hsq : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have h0 : Nat.card K ≠ 0 := by omega
  have h1 : Nat.card K - 1 ≠ 0 := by omega
  have h2 : Nat.card K + 1 ≠ 0 := by omega
  rw [hsq, Nat.factorization_mul h0 (mul_ne_zero h1 h2), Nat.factorization_mul h1 h2]
  have hn0 : ¬ 3 ∣ Nat.card K := by omega
  have hn2 : ¬ 3 ∣ Nat.card K + 1 := by omega
  simp only [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hn0,
    Nat.factorization_eq_zero_of_not_dvd hn2, zero_add, add_zero]

theorem exists_conj_HSL_of_three [Finite K] (h3 : 3 ∣ Nat.card K - 1) (A : SL2 K)
    (hA : ∃ k : ℕ, A ^ 3 ^ k = 1) : ∃ (P : SL2 K) (t : Kˣ), P * A * P⁻¹ = HSL t := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D := (HSLHom K).range with hD
  have hDcard : Nat.card D = Nat.card K - 1 := by
    rw [hD, ← Nat.card_congr (MonoidHom.ofInjective (f := HSLHom K) HSLHom_injective).toEquiv,
      Nat.card_units]
  obtain ⟨P₀⟩ : Nonempty (Sylow 3 D) := inferInstance
  let Q : Sylow 3 (SL2 K) := Sylow.ofCard ((P₀ : Subgroup D).map D.subtype) (by
    rw [Subgroup.card_map_of_injective D.subtype_injective, Sylow.card_eq_multiplicity P₀,
      hDcard, factorization_three_sl2 h3])
  have hE : IsPGroup 3 (Subgroup.zpowers A) := by
    obtain ⟨k, hk⟩ := hA
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hk, one_zpow]
  obtain ⟨y, hy⟩ := exists_conj_le_sylow' Q _ hE
  have hmem : y * A * y⁻¹ ∈ D := by
    have h1 : y * A * y⁻¹ ∈ (Subgroup.zpowers A).map (MulAut.conj y).toMonoidHom :=
      ⟨A, Subgroup.mem_zpowers A, rfl⟩
    have h2 := hy h1
    rw [Sylow.coe_ofCard] at h2
    obtain ⟨d, -, hd⟩ := h2
    rw [← hd]
    exact d.2
  obtain ⟨t, ht⟩ := hmem
  exact ⟨y, t, ht.symm⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof
