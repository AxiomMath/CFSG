module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieG2
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieRows
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section G2Row


theorem noCfgS429_of_adjointG2 {S : Type} [Group S] [Finite S] {F : Type} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (τ : S ≃* adjointGroup Tag.G2 F) :
    NoCfgS429 S := by
  intro A σ K hc
  haveI := hc.isPerfect
  have hσ3 := cfgS429_pow_three hc
  obtain ⟨E, hEK, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_type429 hc.isType
  have hfix : ∀ k ∈ K, σ k = k := fun k hk => Sec4.mem_autFix.mp (hc.le_autFix hk)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F = 2 := by
    have := Fintype.ofFinite F
    have hp : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by rw [← Nat.card_eq_fintype_card, hF])
    exact ringChar.eq F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3F : ¬ 3 ∣ Nat.card F := by
    rw [hF]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hZ : ∀ s : adjointGroup Tag.G2 F, (∀ t, s * t = t * s) → s = 1 := by
    intro s hs
    have hsZ : s ∈ Subgroup.center (adjointGroup Tag.G2 F) :=
      Subgroup.mem_center_iff.mpr fun t => (hs t).symm
    rw [center_adjointGroup_eq_bot] at hsZ
    exact (Subgroup.mem_bot).mp hsZ
  set α := MulAut.congr τ σ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hσ3, map_one]
  by_cases hin : IsInnerAut α
  ·
    refine false_of_fix_e9_of_mulEquiv τ
      (MulAut.conj : adjointGroup Tag.G2 F →* MulAut _).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
      hσ3 hc.ne_one hEK hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    exact card_le_nine_inn (fun E hE h27 =>
      CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_adjointG2 F h3F ⟨E, hE, h27⟩) hZ hB h3B hcB
  ·
    have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
    obtain ⟨φ, hφ, k, hαk⟩ := g2_order_three_field_descent hchar3 h4 hα3 hin
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
    obtain ⟨m, rfl⟩ := h3n
    have hcard : Nat.card (fixSubfield φ) = 2 ^ m := by
      have h := card_fixSubfield_pow φ
      rw [hφ, hF, show 2 ^ (3 * m) = (2 ^ m) ^ 3 by rw [← pow_mul, mul_comm]] at h
      exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
    have hfixeq : Sec4.autFix (g2FieldHom F φ) = (g2Incl φ).range := by
      ext h
      rw [Sec4.mem_autFix, mem_range_g2Incl_iff hchar φ]
    have eα : Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield φ) := by
      rw [hαk]
      exact ((autFixConjEquiv (MulAut.conj k) (g2FieldHom F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (g2Incl_injective φ)).symm
    exact g2Excl429 (fixSubfield φ) m hcard (by omega) S (Sec4.autFix σ) K
      ⟨(Sec4.autFixCongrEquiv τ σ).symm.trans eα⟩ hc.le_autFix hc.isPerfect hc.isSubnormal
      hc.isType

end G2Row

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
