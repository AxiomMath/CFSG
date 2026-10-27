module

public import CFSG.Permutation.FiveTransitive.SixFixedFourGlobalExterior
public import CFSG.Permutation.FiveTransitive.SmallThreeNormalizerFiveCentralizes
public import CFSG.Permutation.FiveTransitive.SmallThreeOrbitExponent
public import CFSG.Permutation.FiveTransitive.Degree39CommutingThreeFixed
public import CFSG.Permutation.FiveTransitive.Degree39ThreeOrbitCount
public import CFSG.Permutation.FiveTransitive.Degree39FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree39ThreeSubgroupBound

open MulAction FixedNormalizerAction

theorem card_le_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q) (hQcard : Nat.card Q ≤ 81)
    (hF : Nat.card (Fixed (X := X) Q) = 6) (him : Image (X := X) Q = ⊤)
    (horbit : ∀ x : X, x ∉ fixedPoints Q X → Nat.card (orbit Q x) = 3) :
    Nat.card Q ≤ 3 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let N := Normalizer Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hdiv : 5 ∣ Nat.card rho.range := by
    change 5 ∣ Nat.card (Image (X := X) Q)
    rw [him,Subgroup.card_top,Nat.card_perm,hF]
    norm_num [Nat.factorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hdiv.trans (Subgroup.card_range_dvd rho))
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hgf := Degree39FiveFree.fixed_card_eq_four P hcard h5 hnotAlt g.val
    (by simpa only [Subgroup.orderOf_coe] using hg)
  obtain ⟨x,hx,hgx⟩ := SixFixedFourGlobalExterior.exists_fixed_exterior P Q hF g hg5 hgf
  have hcomm := SmallThreeNormalizerFiveCentralizes.centralizes_of_fixed_three_orbit
    Q hQ hQcard g hg5 x hgx (horbit x hx)
  have hsmall : ∀ y : X, Nat.card (orbit Q y) ≤ 3 := by
    intro y
    by_cases hy : y ∈ fixedPoints Q X
    · have hh := mem_fixedPoints_iff_card_orbit_eq_one.mp hy
      rw [← Nat.card_eq_fintype_card] at hh
      omega
    · rw [horbit y hy]
  have hbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 9 := by
    intro q hqne
    have hq3 : q ^ 3 = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
      intro y
      simpa only [one_smul] using SmallThreeOrbitExponent.cube_smul_eq hQ hsmall q y
    have hcases := Degree39CommutingThreeFixed.fixed_card_six_or_nine
      P hcard h5 hnotAlt g.val q.val (congrArg Subtype.val hg5)
      (congrArg Subtype.val hq3) (fun he => hqne (Subtype.ext he)) hgf (hcomm q).symm
    change Nat.card (Function.fixedPoints q.val.val) ≤ 9
    omega
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← fixed_eq Q]; exact hF
  let s := (fixedPoints Q X).toFinset
  have hs : s.card = 6 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card,hfixed]
  exact Degree39ThreeOrbitCount.card_le_three hcard s hs
    (fun q y hy => (Set.mem_toFinset.mp hy) q) hsmall hbound

end FiveTransitive.Degree39ThreeSubgroupBound

end CFSG
