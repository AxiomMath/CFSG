module

public import CFSG.Permutation.FiveTransitive.ElevenGroupSmallThreeAutomorphism

public section

namespace CFSG

namespace FiveTransitive.ElevenNormalizerThreeCentralizer

theorem exists_order_three
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 11 Q) (hcard : Nat.card Q ≤ 121)
    (hN : 9 ∣ Nat.card (Subgroup.normalizer (Q : Set G))) :
    ∃ g : Subgroup.normalizer (Q : Set G), orderOf g = 3 ∧
      ∀ q : Q, g.val * q.val = q.val * g.val := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let f := Q.normalizerMonoidHom
  have hnot : ¬ 9 ∣ Nat.card f.range := by
    intro hd
    exact ElevenGroupSmallThreeAutomorphism.nine_not_dvd_card hQ hcard
      (hd.trans (Subgroup.card_subgroup_dvd_card _))
  have hthree : 3 ∣ Nat.card f.ker := by
    by_contra hn
    have hc : Nat.Coprime 3 (Nat.card f.ker) :=
      (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hn
    have he := f.ker.card_mul_index
    rw [Subgroup.index_ker] at he
    rw [← he] at hN
    exact hnot ((hc.pow_left 2).dvd_of_dvd_mul_left hN)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 3 hthree
  refine ⟨z.val,(Subgroup.orderOf_coe z).trans hz,?_⟩
  intro q
  have hh := congrArg (fun a : MulAut Q => (a q).val) z.property
  change z.val.val * q.val * z.val.val⁻¹ = q.val at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

end FiveTransitive.ElevenNormalizerThreeCentralizer

end CFSG
