module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bGamma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7b
open scoped MatrixGroups

theorem le_finrank_range_sub_one_of_sl2_irreducible {F : Type} [Field F] [Fintype F]
    [CharP F 2] {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) SL(2, F) W) (hirr : ρ.IsIrreducible)
    (hnt : ∃ g, ρ g ≠ 1) {t : SL(2, F)} (ht1 : t ≠ 1) (htt : t * t = 1) :
    n ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  classical
  have : Fact ρ.IsIrreducible := ⟨hirr⟩
  obtain ⟨d, hd, hD, hdesc⟩ := binary_SL2_irreducible_Frobenius_descent hn hF ρ hnt
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, hE, hEfin, hEchar, ιF, ιD, J, hJ, hJn, ⟨Φ⟩, hshift, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) W)
  have hw : Module.finrank (ZMod 2) W = d * 2 ^ J.card := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
    change 2 ^ Module.finrank (ZMod 2) W = 2 ^ (d * 2 ^ J.card)
    have hwcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
    simp only [Nat.card_zmod] at hwcard
    rw [← hwcard, natCard_eq_pow_finrank (ρ := ρ), hdim, hD, ← pow_mul]
  have hc := natCard_fixW_involution ρ (Module.finBasis (EndRing ρ) W)
    ιF ιD J hJ Φ t ht1 htt
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (ρ t - 1)) =
      d * 2 ^ (J.card - 1) := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ))
    change 2 ^ Module.finrank (ZMod 2) (LinearMap.ker (ρ t - 1)) =
      2 ^ (d * 2 ^ (J.card - 1))
    have hkcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.ker (ρ t - 1))
    simp only [Nat.card_zmod] at hkcard
    have heq : ↥(LinearMap.ker (ρ t - 1)) ≃ {w : W // ρ t w = w} :=
      Equiv.subtypeEquivRight fun w => by
        simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [← hkcard, Nat.card_congr heq, hc, hD, ← pow_mul]
  have hJpos : 1 ≤ J.card := Finset.card_pos.mpr hJ
  have hpow : 2 ^ J.card = 2 * 2 ^ (J.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsmall : J.card ≤ 2 ^ (J.card - 1) := by
    have := Nat.lt_two_pow_self (n := J.card - 1)
    omega
  have horb : n ≤ J.card * d := n_le_card_mul (by omega) (by omega) hJn hJ hshift
  have hrank := LinearMap.finrank_range_add_finrank_ker (ρ t - 1)
  rw [hw, hker, hpow] at hrank
  have hbound := Nat.mul_le_mul_right d hsmall
  have heq : d * (2 * 2 ^ (J.card - 1)) =
      d * 2 ^ (J.card - 1) + d * 2 ^ (J.card - 1) := by ring
  rw [heq] at hrank
  rw [mul_comm (2 ^ (J.card - 1)) d] at hbound
  omega

theorem le_finrank_range_sub_one_of_sl2 {F : Type} [Field F] [Fintype F] [CharP F 2]
    {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (hperf : Group.IsPerfect SL(2, F))
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (ρ : Representation (ZMod 2) SL(2, F) W) (hnt : ∃ g, ρ g ≠ 1)
    {t : SL(2, F)} (ht1 : t ≠ 1) (htt : t * t = 1) :
    n ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  have hfix : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
      (σ : Representation (ZMod 2) SL(2, F) V),
      repFixedSpace σ {t} = LinearMap.ker (σ t - 1) := by
    intro V _ _ σ
    ext v
    simp only [mem_repFixedSpace, Set.mem_singleton_iff, forall_eq, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  have key := rep_induction (k := ZMod 2) (G := SL(2, F))
    (fun {V} _ _ _ σ => (∃ g, σ g ≠ 1) →
      n ≤ Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace σ {t}))
    (fun {V} _ _ _ σ hsub hex => by
      obtain ⟨g, hg⟩ := hex
      exact (hg (LinearMap.ext fun v => hsub.elim _ _)).elim)
    (fun {V} _ _ _ σ hirr hex => by
      have : Finite V := Module.finite_of_finite (ZMod 2)
      have h := le_finrank_range_sub_one_of_sl2_irreducible hn hF σ hirr hex ht1 htt
      have hdim := LinearMap.finrank_range_add_finrank_ker (σ t - 1)
      rw [hfix]
      omega)
    (fun {V} _ _ _ σ U hU hQ hex => by
      have hcod := codim_sub_quot σ U {t}
      by_cases hntU : ∃ g, U.toRepresentation g ≠ 1
      · have := hU hntU
        omega
      · by_cases hntQ : ∃ g, U.quotient g ≠ 1
        · have := hQ hntQ
          omega
        · push Not at hntU hntQ
          have htriv := trivial_of_sub_quot hperf (MonoidHom.id SL(2, F)) σ U hntU hntQ
          obtain ⟨g, hg⟩ := hex
          exact (hg (htriv g)).elim)
    (Module.finrank (ZMod 2) W) ρ rfl
  have h := key hnt
  rw [hfix] at h
  have hdim := LinearMap.finrank_range_add_finrank_ker (ρ t - 1)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6B3
