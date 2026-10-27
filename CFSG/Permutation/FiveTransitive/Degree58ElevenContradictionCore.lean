module

public import CFSG.Permutation.FiveTransitive.Degree58LargeSylowData
public import CFSG.Permutation.FiveTransitive.AmbientSylowSmallFixedImage
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence

public section

namespace CFSG

namespace FiveTransitive.Degree58ElevenContradictionCore

open MulAction Subgroup FixedNormalizerAction

private theorem centralizes_eleven
    {G : Type} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : Nat.card Q = 11)
    (g : Normalizer Q) (hg : g ^ 3 = 1) :
    ∀ q : Q, g.val * q.val = q.val * g.val := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : IsCyclic Q := isCyclic_of_prime_card hQ
  have hAut : Nat.card (MulAut Q) = 10 := by
    rw [IsCyclic.card_mulAut Q,hQ,Nat.totient_prime (by decide)]
  let a := Q.normalizerMonoidHom g
  have ha3 : a ^ 3 = 1 := by rw [← map_pow,hg,map_one]
  have ha : a = 1 := by
    by_contra hn
    have ho : orderOf a = 3 := orderOf_eq_prime ha3 hn
    have hd := orderOf_dvd_natCard a
    rw [ho,hAut] at hd
    norm_num at hd
  intro q
  have hh := congrArg (fun b : MulAut Q => (b q).val) ha
  change g.val * q.val * g.val⁻¹ = q.val at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

private theorem false_of_fixed_counts
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hX : Fintype.card X = 58)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q)
    (hF : Nat.card (fixedPoints Q X) = 3)
    (g : Normalizer Q) (hg : orderOf g = 3)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val)
    (hsmall : Nat.card (Function.fixedPoints g.val.val) ≤ 4) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho := toPermHom (Normalizer Q) F
  have hfixeq : (F : Set X) = fixedPoints Q X := fixed_eq Q
  have hFc : Nat.card F = 3 := by rw [hfixeq]; exact hF
  have hm11 := CentralizingFixedPointCongruence.card_modEq P Q hQ g.val hcomm
  rw [← hfixeq] at hm11
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm11
  change Nat.card (Function.fixedPoints g.val.val) % 11 =
    Nat.card (Function.fixedPoints (rho g)) % 11 at hm11
  have hl : Nat.card (Function.fixedPoints (rho g)) ≤ 3 := by
    have hb := Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho g) => x.val) Subtype.val_injective
    exact hb.trans hFc.le
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 3 = 1 := by
    funext x
    change ((rho g) ^ 3) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hmF := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 3) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 3 = Fintype.card (Function.fixedPoints (rho g)) % 3 at hmF
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hFc] at hmF
  let b : Function.End X := g.val.val.toFun
  have hb : b ^ 3 = 1 := by
    funext x
    change ((g ^ 3).val.val) x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hmX := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 3) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card X % 3 = Fintype.card (Function.fixedPoints g.val.val) % 3 at hmX
  rw [hX,← Nat.card_eq_fintype_card] at hmX
  omega

theorem excluded_of_three_eleven_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
    (h5 : IsMultiplyPretransitive P X 5)
    (hthree : ∀ s : Set X, s.ncard = 5 → ¬ 3 ∣ Nat.card (fixingSubgroup P s))
    (heleven : ∀ s : Set X, s.ncard = 5 → ¬ 11 ∣ Nat.card (fixingSubgroup P s)) : False := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let S : Sylow 11 P := Sylow.nonempty.some
  let Q : Subgroup P := S
  have hQcard : Nat.card Q = 11 := Degree58LargeSylowData.sylow_card P hcard h5
    (Or.inr (Or.inr rfl)) heleven S
  have hF : Nat.card (fixedPoints Q X) = 3 := by
    have hh := Degree58LargeSylowData.sylow_fixed_card P hcard h5
      (Or.inr (Or.inr rfl)) heleven S
    exact hh
  have him : Image (X := X) Q = ⊤ := AmbientSylowSmallFixedImage.sylow_fixed_image
    11 3 (by decide) (by decide) P (by omega) h5 S hF
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let rho := toPermHom N F
  have hFc : Nat.card F = 3 := by
    change Nat.card (Fixed (X := X) Q) = 3
    rw [fixed_eq]
    exact hF
  have hd : 3 ∣ Nat.card rho.range := by
    change 3 ∣ Nat.card (Image (X := X) Q)
    rw [him,Subgroup.card_top,Nat.card_perm,hFc]
    norm_num [Nat.factorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 3
    (hd.trans (Subgroup.card_range_dvd rho))
  have hcomm := centralizes_eleven Q hQcard g (hg ▸ pow_orderOf_eq_one g)
  have hsmall : Nat.card (Function.fixedPoints g.val.val) ≤ 4 := by
    by_contra hn
    have hlarge : 5 ≤ (Function.fixedPoints g.val.val).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hlarge
    let u : fixingSubgroup P s := ⟨g.val,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 3 := (Subgroup.orderOf_coe u).symm.trans ((Subgroup.orderOf_coe g).trans hg)
    exact hthree s hs (hu ▸ orderOf_dvd_natCard u)
  exact false_of_fixed_counts P hcard Q S.isPGroup' hF g hg hcomm hsmall

end FiveTransitive.Degree58ElevenContradictionCore

end CFSG
