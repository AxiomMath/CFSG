module

public import CFSG.Permutation.FiveTransitive.Degree48LargeSylowActual

public section

namespace CFSG

namespace FiveTransitive.Degree48ElevenFiveFree
open MulAction Subgroup FixedNormalizerAction

theorem normalizer_not_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ 5 ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow 11 P) : ¬ 5 ∣ Nat.card (Subgroup.normalizer (S : Set P)) := by
  classical
  intro hd
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let N := Normalizer (S : Subgroup P)
  let F := Fixed (X := X) (S : Subgroup P)
  let _ : Fintype F := Fintype.ofFinite _
  have hF : Nat.card F = 4 := by
    change Nat.card (Fixed (X := X) (S : Subgroup P)) = 4
    rw [fixed_eq]
    exact Degree48LargeSylowActual.sylow_eleven_fixed_card P hcard h5 hnotAlt S
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 5 hd
  let f := toPermHom N F z
  have hf5 : f ^ 5 = 1 := by
    change (toPermHom N F z) ^ 5 = 1
    rw [← map_pow,← hz,pow_orderOf_eq_one,map_one]
  have hf : f = 1 := by
    by_contra hn
    have ho : orderOf f = 5 := orderOf_eq_prime hf5 hn
    have hdiv : 5 ∣ (Nat.card F).factorial := by
      rw [← Nat.card_perm]
      exact ho ▸ orderOf_dvd_natCard f
    rw [hF] at hdiv
    norm_num at hdiv
  have hsub : (F : Set X) ⊆ Function.fixedPoints z.val.val := by
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hf (⟨x,hx⟩ : F))
  have hlo : 4 ≤ Nat.card (Function.fixedPoints z.val.val) := by
    rw [← hF,Nat.card_coe_set_eq,Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub
  have hsmall : Nat.card (Function.fixedPoints z.val.val) < 5 := by
    by_contra hn
    have hlarge : 5 ≤ (Function.fixedPoints z.val.val).ncard := by
      rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨s,hs,hs5⟩ := Set.exists_subset_card_eq hlarge
    let u : fixingSubgroup P s := ⟨z.val,(mem_fixingSubgroup_iff P).mpr (fun x hx => hs hx)⟩
    have hu : orderOf u = 5 := by
      exact (Subgroup.orderOf_coe u).symm.trans ((Subgroup.orderOf_coe z).trans hz)
    exact hfree s hs5 (hu ▸ orderOf_dvd_natCard u)
  have hfix : Nat.card (Function.fixedPoints z.val.val) = 4 := by omega
  have hzperm : orderOf z.val.val = 5 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact hz
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := z.val.val) (by rw [hzperm]; norm_num)
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,hcard,hk,
    Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzperm] at hfix
  omega

end FiveTransitive.Degree48ElevenFiveFree

end CFSG
