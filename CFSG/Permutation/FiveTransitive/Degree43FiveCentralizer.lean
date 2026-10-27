module

public import CFSG.Permutation.FiveTransitive.FiveSevenFixedFree
public import CFSG.Permutation.FiveTransitive.NormalizerFixedComplement
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree43FiveCentralizer

open MulAction

theorem card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hfixed : Nat.card (fixedPoints Q X) = 8)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 7)
    (hc : g.val ∈ Subgroup.centralizer (Q : Set P)) : Nat.card Q ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let Y := NormalizerFixedComplement.Domain (X := X) Q
  let _ : Fintype Y := Fintype.ofFinite Y
  have hY : Fintype.card Y = 35 := by
    rw [← Nat.card_eq_fintype_card,NormalizerFixedComplement.card_domain,
      ← Nat.card_coe_set_eq,hfixed,Nat.card_eq_fintype_card,hcard]
  let N := Subgroup.normalizer (Q : Set P)
  let i : Q →* N :=
    { toFun := fun q => ⟨q.val,Q.le_normalizer q.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let rho : N →* Equiv.Perm Y := toPermHom N Y
  let theta : Q →* Equiv.Perm Y := rho.comp i
  have hinj : Function.Injective theta := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ fixedPoints Q X
    · exact (hx a).trans (hx b).symm
    · exact congrArg Subtype.val (DFunLike.congr_fun hab (⟨x,hx⟩ : Y))
  let J := theta.range
  have hJ : IsPGroup 5 J := hQ.of_surjective theta.rangeRestrict theta.rangeRestrict_surjective
  have hno : fixedPoints J Y = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    apply y.property
    intro q
    exact congrArg Subtype.val (hy (⟨theta q,⟨q,rfl⟩⟩ : J))
  have hcomm (q : Q) : rho g * theta q = theta q * rho g := by
    have hh : g * i q = i q * g := by
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp hc) q.val q.property).symm
    change rho g * rho (i q) = rho (i q) * rho g
    simpa only [map_mul] using congrArg rho hh
  have hcent : rho g ∈ Subgroup.centralizer (J : Set (Equiv.Perm Y)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro q ⟨a,rfl⟩
    exact (hcomm a).symm
  have hg7 : (rho g) ^ 7 = 1 := by
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
  have hgne : rho g ≠ 1 := by
    intro he
    have hsub : (fixedPoints Q X)ᶜ ⊆ Function.fixedPoints g.val.val := by
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun he (⟨x,hx⟩ : Y))
    have hle := Set.ncard_le_ncard hsub
    rw [Set.ncard_compl,← Nat.card_coe_set_eq,hfixed,← Nat.card_coe_set_eq,
      Nat.card_eq_fintype_card (α := X),hcard] at hle
    have hne : g.val.val ≠ 1 := by
      intro hh
      have hgone : g = 1 := Subtype.ext (Subtype.ext hh)
      rw [hgone,orderOf_one] at hg
      omega
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
      g.val.property hne
    rw [hcard] at hb
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard] at hle
    omega
  have hC := FiveSevenFixedFree.centralizer_card J hJ hY hno (rho g) hg7 hgne hcent
  let f : Q →* Subgroup.centralizer ({rho g} : Set (Equiv.Perm Y)) :=
    theta.codRestrict _ (fun q => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcomm q).symm)
  have hf : Function.Injective f := by
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  have hd := Subgroup.card_dvd_of_injective f hf
  rw [hC] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hele : e ≤ 1 := by
    by_contra hn
    have h25 : 25 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    have hh := h25.trans hd
    norm_num at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 5) hele).trans (by norm_num)

end FiveTransitive.Degree43FiveCentralizer

end CFSG
