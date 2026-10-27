module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.gorenstein_5_4_15

namespace CFSG
end CFSG
open CFSG
/-! # Proposition 4.8(a) from BG Section 4 -/

section Main

open scoped FixedPoints

public theorem CFSG.proposition_4_8_a {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime]
    [Fact (IsPGroup p R)] (hrank : groupRank R ≤ 2) (hexp : Monoid.exponent R = p) :
    Nat.card R ≤ p ^ 3 := by
  classical
  obtain ⟨A, hAnorm, hAcomm, hAmax⟩ := exists_maximal_normal_abelian_subgroup_local' (G := R)
  letI : A.Normal := hAnorm
  have hAcent_le : Subgroup.centralizer (A : Set R) ≤ A :=
    maximal_normal_abelian_selfCentralizing_local (G := R) (p := p) A hAnorm hAcomm hAmax
  have hA_le_cent : A ≤ Subgroup.centralizer (A : Set R) :=
    (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm
  have hAself : Subgroup.centralizer (A : Set R) = A := le_antisymm hAcent_le hA_le_cent
  have hAq : IsPGroup p A := (Fact.out : IsPGroup p R).to_subgroup A
  have hArank : generatorRank A ≤ 2 :=
    (generatorRank_le_groupRank_of_isPGroup_abelian_subgroup (R := R) (q := p) hAq hAcomm).trans
      hrank
  have hAexp_dvd : Monoid.exponent A ∣ p := by
    rw [← Subgroup.exponent_toSubmonoid]
    exact (Monoid.exponent_submonoid_dvd A.toSubmonoid).trans (by simp [hexp])
  have hAcard : Nat.card A ≤ p ^ 2 :=
    natCard_abelian_subgroup_le_p_sq_of_rank_le_two_and_exponent_dvd_p
      (R := R) (p := p) hAq hAcomm hArank hAexp_dvd
  have hAelem : IsElementaryAbelian p A := {
    toIsMulCommutative := hAcomm
    exponent_dvd_p := hAexp_dvd
  }
  let φ : R →* MulAut A := MulAut.conjNormal (H := A)
  have hker_eq_cent : φ.ker = Subgroup.centralizer (A : Set R) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
    constructor
    · intro hx a ha
      have hx_apply : (φ x) ⟨a, ha⟩ = ⟨a, ha⟩ := by
        simp [hx]
      have hconj : x * a * x⁻¹ = a := by
        simpa [φ] using congrArg Subtype.val hx_apply
      have := congrArg (fun t : R => t * x) hconj
      simpa [mul_assoc] using this.symm
    · intro hx
      ext a
      have hcomm : (a : R) * x = x * a := hx a a.2
      have hconj : x * (a : R) * x⁻¹ = a := by
        calc
          x * (a : R) * x⁻¹ = ((a : R) * x) * x⁻¹ := by rw [hcomm]
          _ = a := by simp [mul_assoc]
      simpa [φ, MulAut.conjNormal_apply, MulAut.conj_apply] using hconj
  have hker_eq_A : φ.ker = A := by rw [hker_eq_cent, hAself]
  have hφ_range_p : IsPGroup p φ.range := by
    have hRtop : IsPGroup p (⊤ : Subgroup R) := by
      simpa using (Fact.out : IsPGroup p R).to_subgroup (⊤ : Subgroup R)
    rw [MonoidHom.range_eq_map]
    exact IsPGroup.map (p := p) (H := (⊤ : Subgroup R)) hRtop φ
  have hquot_card : Nat.card (R ⧸ A) = Nat.card φ.range := by
    calc
      Nat.card (R ⧸ A) = Nat.card (R ⧸ φ.ker) := by rw [hker_eq_A]
      _ = Nat.card φ.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have hφcard : Nat.card φ.range ≤ p :=
    natCard_pSubgroup_mulAut_le_p_of_elementaryAbelian_card_le_p_sq
      (A := A) (p := p) hφ_range_p hAcard
  calc
    Nat.card R = Nat.card (R ⧸ A) * Nat.card A := by
      simpa [Nat.mul_comm] using (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := A))
    _ = Nat.card φ.range * Nat.card A := by rw [hquot_card]
    _ ≤ p * p ^ 2 := Nat.mul_le_mul hφcard hAcard
    _ = p ^ 3 := by
      simp [pow_succ, Nat.mul_comm]

end Main
