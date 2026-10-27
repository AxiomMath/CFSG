module

public import CFSG.Permutation.FiveTransitive.Degree72FiveSevenExterior
public import CFSG.Permutation.FiveTransitive.Degree72FiveFixedBound

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveSevenProjection
open MulAction FixedNormalizerAction

theorem conjugation_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 7)
    (g : Normalizer Q) (hg : orderOf g = 7) : Q.normalizerMonoidHom g = 1 := by
  classical
  obtain ⟨T,hT,hnot,hgfix⟩ := Degree72FiveSevenExterior.exists_invariant_type P hcard h5 hnotAlt Q hQ hF g hg
  let rho := toPermHom Q T
  have hdis : Disjoint (fixedPoints Q X) (T : Set X) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hnot ⟨x,hy⟩ hx
  have hinj : Function.Injective rho := by
    apply (injective_iff_map_eq_one _).mpr
    intro q hq
    by_contra hn
    have hsub : fixedPoints Q X ∪ (T : Set X) ⊆ fixedBy X q := by
      intro x hx
      rcases hx with hx | hx
      · exact hx q
      · exact congrArg Subtype.val (DFunLike.congr_fun hq (⟨x,hx⟩ : T))
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_union_eq hdis,← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hF] at hh
    change 7 + Nat.card T ≤ Nat.card (fixedBy X q) at hh
    rw [hT] at hh
    have hb := Degree72FiveFixedBound.nonidentity_fixed_le P hcard h5 hnotAlt Q hQ q hn
    omega
  apply DFunLike.ext
  intro q
  apply hinj
  apply Equiv.ext
  intro x
  apply Subtype.ext
  change (Q.normalizerMonoidHom g q).val • x.val = q.val • x.val
  rw [Q.normalizerMonoidHom_apply_apply_coe,mul_smul,mul_smul]
  have hgi : g.val⁻¹ • x.val = x.val := by
    calc
      g.val⁻¹ • x.val = g.val⁻¹ • (g.val • x.val) := congrArg (fun y => g.val⁻¹ • y) (hgfix x).symm
      _ = x.val := inv_smul_smul _ _
  rw [hgi]
  exact hgfix (q • x)

end FiveTransitive.Degree72FiveSevenProjection

end CFSG
