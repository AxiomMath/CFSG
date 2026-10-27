module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LRowCover
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieD4
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.NoE27Exc

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projSU)

section G2Row


theorem rowU3_G2 {S : Type} [Group S] [Finite S] {f : ℕ}
    (hm : ChevalleyExceptionalModel S .G2 2 f) {σ : MulAut S} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    {Y : Subgroup S} (hYC : Y ≤ Sec4.autFix σ) [Group.IsPerfect Y]
    (hsub : (Y.subgroupOf (Sec4.autFix σ)).IsSubnormal) {m : ℕ} (hmo : Odd m) (hm1 : 1 < m)
    (π : Y →* projSU 3 2 m) (hπ : Function.Surjective π)
    (hker : Nat.Coprime (Nat.card π.ker) 3) : False := by
  obtain ⟨⟨-, -, -, h3f⟩, F, _, _, hF, ⟨eA⟩⟩ := hm
  have hn : 2 ≤ f := by
    by_contra hlt
    have : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have eC : AdjointQuotient .G2 F ≃* adjointGroup .G2 F :=
    (QuotientGroup.quotientMulEquivOfEq (center_adjointGroup_eq_bot (τ := .G2) (K := F))).trans
      QuotientGroup.quotientBot
  set τ : S ≃* adjointGroup .G2 F := eA.trans eC with hτ
  obtain ⟨E, hEY, hEc, hE3, hE9, hEZ⟩ := exists_e9_of_cover hmo hm1 π hπ hker
  have hfix : ∀ k ∈ Y, σ k = k := fun k hk => Sec4.mem_autFix.mp (hYC hk)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar F = 2 := by
    have := Fintype.ofFinite F
    have hp : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [← Nat.card_eq_fintype_card, hF])
    exact ringChar.eq F 2
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn
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
    refine RonanK429Lie.false_of_fix_e9_of_mulEquiv τ
      (MulAut.conj : adjointGroup Tag.G2 F →* MulAut _).range ?_ (fun s => ⟨s, rfl⟩) hZ hin
      hσ3 hσ1 hEY hEc hE3 hE9 hfix hEZ
    intro B hB h3B hcB
    exact RonanK429Lie.card_le_nine_inn (fun E hE h27 =>
      CFSG.HardMathSupport.Dickson.Sec6.I1431.noE27_adjointG2 F h3F ⟨E, hE, h27⟩) hZ hB h3B hcB
  ·
    have hchar3 : ringChar F ≠ 3 := by rw [hchar]; norm_num
    obtain ⟨φ, hφ, k, hαk⟩ := g2_order_three_field_descent hchar3 h4 hα3 hin
    obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
    obtain ⟨n', rfl⟩ := h3n
    have hcard : Nat.card (fixSubfield φ) = 2 ^ n' := by
      have h := card_fixSubfield_pow φ
      rw [hφ, hF, show 2 ^ (3 * n') = (2 ^ n') ^ 3 by rw [← pow_mul, mul_comm]] at h
      exact Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h
    have hfixeq : Sec4.autFix (g2FieldHom F φ) = (g2Incl φ).range := by
      ext h
      rw [Sec4.mem_autFix, mem_range_g2Incl_iff hchar φ]
    have eα : Sec4.autFix α ≃* adjointGroup Tag.G2 (fixSubfield φ) := by
      rw [hαk]
      exact ((RonanK429Lie.autFixConjEquiv (MulAut.conj k) (g2FieldHom F φ)).trans
        (MulEquiv.subgroupCongr hfixeq)).trans
          (MonoidHom.ofInjective (g2Incl_injective φ)).symm
    exact false_of_g2_cover hcard (by omega) ((Sec4.autFixCongrEquiv τ σ).symm.trans eα) hYC
      hsub hmo hm1 π hπ

end G2Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
