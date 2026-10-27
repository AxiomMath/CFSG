module

public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFourDefs
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFourAux
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.TriD4OuterAux.Two
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartTwo.Sec11

section D4


theorem not_pullDatum_d4_of_threeA (h3A : DFourThreeAKill) {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (hσ3 : σ ^ 3 = 1)
    (hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥)
    (β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hβ : orderOf β = 3) :
    ¬ PullDatum β := by
  intro h
  have hinj := conj_injective_of_center_eq_bot hZ
  by_cases hin : β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
    MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range
  · obtain ⟨x, rfl, hx3, hx1⟩ := exists_conj_of_isInnerAut hinj hβ hin
    have h3 : ¬ 3 ∣ 2 ^ f := fun h3 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    obtain ⟨g, hg⟩ := KS11Lie6Proof.d4ThreeConj_holds K (2 ^ f) σ hK hσ h3 x hx3 hx1
    have hz3 : (g * x * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hz1 : g * x * g⁻¹ ≠ 1 := fun h1 => hx1 (conj_eq_one_iff.mp h1)
    have h' := h.conj_inner g
    rcases hg with hgS | hgC
    · rcases Nat.even_or_odd f with hfe | hfo
      · have hf2 : 2 ≤ f := by
          obtain ⟨k, hk⟩ := hfe
          omega
        exact h3A K f σ hf2 hK hσ _ hgS hz3 hz1 h'
      · exact not_pullDatum_threeA_odd hfo hK hσ3 hgS hz3 hz1 h'
    · exact not_pullDatum_threeB hf hK hσ hσ3 hgC hz3 hz1 h'
  · exact h.false_of_coreFreeAt
      (CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.coreFreeAt_three_D4_outer_two hf hK σ hσ
        β (by rw [← hβ]; exact pow_orderOf_eq_one β) hin)

theorem kChevTwo_trialityD4_of_threeA (h3A : DFourThreeAKill) (n : ℕ) (hn : 1 ≤ n) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      Blueprint.ChevalleyExceptionalModel X .trialityD4 2 n →
        ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ hXq hX β hβ
  obtain ⟨K, _, _, _, σ, hK, hσ, hσ3, -, hsimple, ⟨e⟩⟩ :=
    Res417Seven.exists_graphFixedRootGroup_of_trialityD4 hX
  have : IsSimpleGroup X := e.isSimpleGroup
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨-, hs, -⟩ := hXq
      obtain ⟨a, b, hab⟩ := hs.toNontrivial
      apply hab
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      rw [QuotientGroup.eq, h]
      exact Subgroup.mem_top _
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    have hy' : e.symm y ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff] at hy ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hy (e g)
    rw [hZX, Subgroup.mem_bot] at hy'
    rw [← e.apply_symm_apply y, hy', map_one]
  exact not_innThetaNoncyclic_of_mulEquiv e hZX
    (fun β' hβ' => not_pullDatum_d4_of_threeA h3A hn hK hσ hσ3 hZ β' hβ') β hβ

end D4

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

end
