module

public import CFSG.RankThree.SteinbergR3ESmallReeCosetDescent
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem smallRee_fixed_data_odd
    {a : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ : orderOf σ = p) :
    ∃ b : ℕ, (2 * b + 1) * p = 2 * a + 1 ∧ Nat.card (fixSubfield σ) = 3 ^ (2 * b + 1) ∧
      ((ReeTag.G2.reeGammaFieldAut K a σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
          (ReeTag.G2.reeGamma K a).subtype =
        (ReeTag.G2.reeGamma (fixSubfield σ) b).map (baseChangeGL (fixSubfield σ).subtype) := by
  obtain ⟨hpf, hcard⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_three (by omega) hK σ
  rw [hσ] at hpf hcard
  obtain ⟨d, hd⟩ := hpf
  have hd' : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left _ hp.pos]
  rw [hd'] at hcard
  have hdodd : Odd d := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact (Nat.odd_mul.1 h1).2
  obtain ⟨b, hb⟩ := hdodd
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hab : a = b + d * m := by
    have e1 : p * d = 2 * (d * m) + d := by rw [hm]; ring
    omega
  exact ⟨b, by rw [← hb, mul_comm, ← hd], by rw [hcard, hb],
    CFSG.RankThree.fixed_reeGamma_eq_map σ hcard hab⟩

end CFSG.SignalizerFunctorTheorem.CatalogBridge
