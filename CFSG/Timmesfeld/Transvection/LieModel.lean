module

public import CFSG.Blueprint.Catalog
public import CFSG.Timmesfeld.Transvection.Statement
import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

private theorem lieModel_statedSp {n f : ℕ} (hn : 2 ≤ n) (hf2 : 2 ≤ f) :
    LieModel (StatedSp n (GaloisField 2 f)) .PSp n 2 f := by
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by omega, hn, fun h => ?_⟩, GaloisField 2 f,
    inferInstance, inferInstance, GaloisField.card 2 f (by omega),
    ⟨((QuotientGroup.quotientMulEquivOfEq
      (Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := n)
        (K := GaloisField 2 f))).trans QuotientGroup.quotientBot).symm⟩⟩
  have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have h2 : 2 ^ f = 2 := congrArg Prod.snd h
  omega

private theorem lieModel_SU_quotient_center {m f : ℕ} (hf : 1 ≤ f) (hm : 4 ≤ m) :
    LieModel (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m ⧸
      Subgroup.center (Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) m))
      .PSU m 2 f :=
  Or.inl ⟨by decide, Unitary.statedClassicalModel_center_quotient
    ⟨Nat.prime_two, hf, by omega, fun h => by have := congrArg Prod.fst h; simp at this; omega⟩
    (card_galoisField_two_mul hf)⟩

theorem lieModel_of_transvectionConclusion {H : Type} [Group H]
    {Δ : Set (Subgroup H)} {f : ℕ} (hf : 1 ≤ f) (hf2 : 2 ≤ f)
    (h : TransvectionConclusion H Δ f hf) :
    (∃ n, 2 ≤ n ∧ LieModel H .PSp n 2 f) ∨ ∃ m, 4 ≤ m ∧ LieModel H .PSU m 2 f := by
  rcases h with ⟨n, hn, Φ, hΦ, -⟩ | ⟨m, hm, Φ, hΦ, hker, -⟩
  · exact Or.inl ⟨n, hn, (lieModel_statedSp hn hf2).of_mulEquiv (MulEquiv.ofBijective Φ hΦ)⟩
  · exact Or.inr ⟨m, hm, (lieModel_SU_quotient_center hf hm).of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ))⟩

end CFSG.Timmesfeld.Transvection
