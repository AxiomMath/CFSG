module

public import CFSG.Permutation.FiveTransitive.Degree68FiveExterior
public import CFSG.Permutation.FiveTransitive.Degree68FiveFixedBound
public import CFSG.Permutation.FiveTransitive.Degree68FiveKernelBound

public section

namespace CFSG

namespace FiveTransitive.Degree68FiveProjection
open MulAction FixedNormalizerAction

theorem exists_projection
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q) (hF : Nat.card (fixedPoints Q X) = 8)
    (g : Normalizer Q) (hg : orderOf g = 7) :
    ∃ T : SubMulAction Q X, Nat.card (toPermHom Q T).ker ≤ 5 ∧
      ∀ q : Q, toPermHom Q T (Q.normalizerMonoidHom g q) = toPermHom Q T q := by
  classical
  obtain ⟨T,hT,hnot,hgfix⟩ := Degree68FiveExterior.exists_invariant_type P hcard h5 hnotAlt Q hQ hF g hg
  let rho := toPermHom Q T
  let K := rho.ker
  let s := (fixedPoints Q X ∪ (T : Set X)).toFinset
  have hdis : Disjoint (fixedPoints Q X) (T : Set X) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hnot ⟨x,hy⟩ hx
  have hs : s.card = 33 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq,
      Set.ncard_union_eq hdis,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hF]
    change 8 + Nat.card T = 33
    rw [hT]
  have hfix (k : K) (x : X) (hx : x ∈ s) : k • x = x := by
    rcases Set.mem_toFinset.mp hx with hx | hx
    · exact hx k.val
    · have he : rho k.val = 1 := k.property
      exact congrArg Subtype.val (DFunLike.congr_fun he (⟨x,hx⟩ : T))
  have hbound (k : K) (hk : k ≠ 1) : Nat.card (fixedBy X k) ≤ 33 :=
    Degree68FiveFixedBound.nonidentity_fixed_le P hcard h5 hnotAlt Q hQ k.val
      (fun he => hk (Subtype.ext he))
  have hK : Nat.card K ≤ 5 := Degree68FiveKernelBound.card_le_five
    (hQ.to_subgroup K) hcard s hs hfix hbound
  refine ⟨T,hK,?_⟩
  intro q
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

end FiveTransitive.Degree68FiveProjection

end CFSG
