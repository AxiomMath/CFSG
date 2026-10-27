module

public import CFSG.Permutation.FiveTransitive.Degree54TwoEntrance
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.TwoGroupFiveAutomorphism

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoLowerBound
open MulAction Subgroup FixedNormalizerAction SylowFixedActionCore

private theorem centralizer_five_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 6) :
    ¬ 5 ∣ Nat.card (centralizer (Q : Set P)) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (Q : Set P)) 5 hd
  have hzP : orderOf z.val = 5 := (Subgroup.orderOf_coe z).trans hz
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := fun q =>
    (z.property q.val q.property).symm
  let g : Normalizer Q := ⟨z.val,centralizer_le_normalizer (Q : Set P) z.property⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom (Normalizer Q) F
  have hg : g ^ 5 = 1 := Subtype.ext (hzP ▸ pow_orderOf_eq_one z.val)
  have hglobal := Degree54FiveFree.fixed_card_eq_four P hcard h5 hnotAlt z.val hzP
  let f : Function.fixedPoints (rho g) → Function.fixedPoints z.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hle : Nat.card (Function.fixedPoints (rho g)) ≤ 4 := by
    rw [← hglobal]
    exact Nat.card_le_card_of_injective f (fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun t => t.val) h)))
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change ((rho g) ^ 5) x = x
    rw [← map_pow,hg,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm
  have hlocal : Nat.card (Function.fixedPoints (rho g)) = 1 := by omega
  have he : Function.fixedPoints (rho g) ≃
      {x : fixedPoints Q X // z.val.val x.val = x.val} :=
    { toFun := fun x => ⟨⟨x.val.val,(fixed_eq (X := X) Q) ▸ x.val.property⟩,
        congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val.val,by simpa only [F,fixed_eq (X := X) Q] using x.val.property⟩,
        Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := CentralizingFixedPointCongruence.card_modEq P Q hQ z.val hcomm
  rw [hglobal,← Nat.card_congr he,hlocal] at hc
  norm_num [Nat.ModEq] at hc

private theorem sixteen_le_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 6) (him : Image (X := X) Q = ⊤) :
    16 ≤ Nat.card Q := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  let f := Q.normalizerMonoidHom
  let rho := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hN : 5 ∣ Nat.card (Normalizer Q) := by
    apply dvd_trans (b := Nat.card (Image (X := X) Q))
    · rw [him,Subgroup.card_top,Nat.card_perm,hF]
      norm_num [Nat.factorial]
    · exact Subgroup.card_range_dvd rho
  have hk : ¬ 5 ∣ Nat.card f.ker := by
    have he : Nat.card f.ker = Nat.card (centralizer (Q : Set P)) := by
      rw [Q.normalizerMonoidHom_ker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (centralizer_le_normalizer (Q : Set P))).toEquiv
    rw [he]
    exact centralizer_five_free P hcard h5 hnotAlt Q hQ hF
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  rw [← hm] at hN
  have hd : 5 ∣ Nat.card (MulAut Q) :=
    (((show Nat.Prime 5 by decide).dvd_mul.mp hN).resolve_left hk).trans
      (Subgroup.card_subgroup_dvd_card f.range)
  by_contra hn
  have he := TwoGroupFiveAutomorphism.card_eq_sixteen_of_five_dvd_aut_card Q hQ (by omega) hd
  omega

theorem sylow_sixteen_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    16 ≤ Nat.card S := by
  obtain ⟨hF,him⟩ := Degree54TwoEntrance.fixed_six_and_image P hcard h5 hnotAlt s hs S
  have hb := sixteen_le_card P hcard h5 hnotAlt (sylowImage X P s S)
    (S.isPGroup'.map _) hF him
  rwa [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective] at hb

end FiveTransitive.Degree54TwoLowerBound

end CFSG
