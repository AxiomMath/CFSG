module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import CFSG.Permutation.FiveTransitive.ElevenElementaryAutNineFree
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.ElevenCentralizingFive

theorem exists_five
    {G F : Type} [Group G] [Finite G] [Fintype F] [DecidableEq F]
    (Q : Subgroup G) (hcomm : IsMulCommutative Q)
    (hp : ∀ q : Q, q ^ 11 = 1) (hcard : Nat.card Q ≤ 1331)
    (hF : Nat.card F = 6)
    (rho : Subgroup.normalizer (Q : Set G) →* Equiv.Perm F)
    (hrho : rho.range = ⊤) :
    ∃ g : Subgroup.normalizer (Q : Set G), orderOf g = 5 ∧
      ∀ q : Q, g.val * q.val = q.val * g.val := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  let N := Subgroup.normalizer (Q : Set G)
  let sigma := Q.normalizerMonoidHom
  have hA : Nat.card (alternatingGroup F) = 360 := by
    rw [nat_card_alternatingGroup,hF]
    norm_num [Nat.factorial]
  have hsmall : ¬ Nat.card (alternatingGroup F) ∣ Nat.card sigma.range := by
    intro hd
    apply ElevenElementaryAutNineFree.nine_not_dvd_card Q hcomm hp hcard
    exact (show 9 ∣ Nat.card (alternatingGroup F) by rw [hA]; norm_num).trans
      (hd.trans sigma.range.card_subgroup_dvd_card)
  let K := sigma.ker
  let f : K →* Equiv.Perm F := rho.comp K.subtype
  have hAlt : alternatingGroup F ≤ f.range := by
    intro q hq
    obtain ⟨g,hg,hgs⟩ := SimpleGoursat.exists_lift_with_aux_eq_one_of_not_dvd
      N (Equiv.Perm F) (MulAut Q) rho sigma (alternatingGroup F)
      (by rw [hrho]; exact le_top) hsmall q hq
    exact ⟨⟨g,hgs⟩,hg⟩
  have hd : 5 ∣ Nat.card K :=
    (show 5 ∣ Nat.card (alternatingGroup F) by rw [hA]; norm_num).trans
      ((Subgroup.card_dvd_of_le hAlt).trans (Subgroup.card_range_dvd f))
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 hd
  refine ⟨g.val,(Subgroup.orderOf_coe g).trans hg,?_⟩
  have hc : g.val.val ∈ Subgroup.centralizer (Q : Set G) := by
    have hh := g.property
    change g.val ∈ Q.normalizerMonoidHom.ker at hh
    rw [Q.normalizerMonoidHom_ker] at hh
    exact hh
  intro q
  exact (Subgroup.mem_centralizer_iff.mp hc q.val q.property).symm

end FiveTransitive.ElevenCentralizingFive

end CFSG
