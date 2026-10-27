module

public import CFSG.RankThree.PartOne.S11c.Sec68
public import CFSG.RankThree.PartOne.K159.CoverPSL
public import CFSG.RankThree.PartOne.K159.CoverPSU

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PartOne
open scoped MatrixGroups

section Classical

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem ker_comp_mk'_eq_center {T : Type} [Group T] (e : K ⧸ Subgroup.center K ≃* T) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).ker = Subgroup.center K := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem exists_elemAbelian_four_psl {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) :
    ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  have : Fact p.Prime := ⟨hp⟩
  let ψ : K ⧸ Subgroup.center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := ker_comp_mk'_eq_center ψ
  have hodd' : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  have hcard : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpk
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hzk : (z : K) ∈ φ.ker := by rw [hker]; exact z.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_psl hp hp2 hζo hζ (by omega : 2 ≤ m) hφs
    hker.le hodd' hzk hz1 hzp
  refine ⟨B, hBp, hBc, le_trans ?_ hBcard⟩
  simp only [hpn, ↓reduceIte]
  exact Nat.pow_le_pow_right hp.pos (by omega)

theorem exists_elemAbelian_four_psu {p ℓ n f : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpZ : p ∣ Nat.card (Subgroup.center K)) (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) :
    ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B := by
  classical
  have hp2 : p ≠ 2 := by omega
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have hp5 := five_le_of_prime' hp hp3
  have hn5 : 5 ≤ n := le_trans hp5 (Nat.le_of_dvd (by omega) hpn)
  have : Fact p.Prime := ⟨hp⟩
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData ℓ f k :=
    ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : K ⧸ Subgroup.center K ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by omega)).symm
  let φ : K →* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU n :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := ker_comp_mk'_eq_center ψ
  have hodd' : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hzk : (z : K) ∈ φ.ker := by rw [hker]; exact z.2
  obtain ⟨B, hBp, hBc, hBcard⟩ := CFSG.RankThree.PartOne.K159.exists_elemAbelian_unitary hU hp hp3
    hpq (by omega : 3 ≤ n) φ hφs hker.le hodd' hzk hz1 hzp
  refine ⟨B, hBp, hBc, le_trans ?_ hBcard⟩
  simp only [hpn, ↓reduceIte]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end Classical

section Table

theorem exists_elemAbelian_four_of_model
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) {t : StatedLieTag} {n ℓ f : ℕ}
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) t n ℓ f) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B := by
  have hdvd := card_center_dvd_of_model hGA hK hmod
  rcases prime_dvd_table hp hp3 (hpZ.trans hdvd) with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
  · exact exists_elemAbelian_four_psl hp hp3 hpZ hodd hmod hpn hpq
  · exact exists_elemAbelian_four_psu hp hp3 hpZ hodd hmod hpn hpq

end Table

@[expose] def CenterRankFour : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.twoLocalOddRank X ≤ 3 → CFSG.IsKGroup X →
    ∀ (O : Subgroup X) [O.Normal], CFSG.IsQuasisimple (X ⧸ O) → ∀ p : ℕ, p.Prime → 3 < p →
      p ∣ Nat.card (Subgroup.center (X ⧸ O)) → Odd (Nat.card (Subgroup.center (X ⧸ O))) →
        ∃ B : Subgroup (X ⧸ O), (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
          p ^ 4 ≤ Nat.card B

end CFSG.RankThree.PartOne.K159
