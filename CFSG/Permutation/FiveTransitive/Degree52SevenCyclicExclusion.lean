module

public import CFSG.Permutation.FiveTransitive.PrimeCyclicFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree52SevenCyclicExclusion

open MulAction PrimeCyclicFixedAction

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (r : P) [Fintype (cyclicFixedPoints X P r)] (hr : orderOf r = 7)
    (hfixed : Nat.card (cyclicFixedPoints X P r) = 10)
    (hAlt : alternatingGroup (cyclicFixedPoints X P r) ≤
      (toPermHom (cyclicNormalizer P r) (cyclicFixedPoints X P r)).range) : False := by
  classical
  let F := cyclicFixedPoints X P r
  have hp : Nat.Prime 7 := by norm_num
  change Nat.card F = 10 at hfixed
  let FC := cyclicComplement X P r
  let _ : Fintype FC := Fintype.ofFinite _
  let c := complementPerm X P r
  have hcorder : orderOf c = 7 := orderOf_complementPerm X P r hp hr
  have hcprime : Nat.Prime (orderOf c) := by rw [hcorder]; exact hp
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order hcprime
  have hcsupport : c.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support,Finset.mem_univ,iff_true]
    exact complementPerm_fixedPointFree X P r x
  have hFCle : Fintype.card FC = 42 := by
    have he : Nat.card FC = Nat.card X - Nat.card F := by
      change Nat.card ((F : Set X)ᶜ : Set X) = _
      rw [Nat.card_coe_set_eq,Set.ncard_compl,← Nat.card_coe_set_eq]
      rfl
    rw [Nat.card_eq_fintype_card (α := X),hcard] at he
    rw [← Nat.card_eq_fintype_card]
    omega
  have hshape : Fintype.card FC = 7 * c.cycleType.card := by
    calc
      _ = c.support.card := by rw [hcsupport,Finset.card_univ]
      _ = c.cycleType.sum := c.sum_cycleType.symm
      _ = _ := by
        rw [hm,hcorder]
        simp only [Multiset.sum_replicate,Multiset.card_replicate,nsmul_eq_mul,Nat.cast_id]
        exact Nat.mul_comm _ _
  have hFge : 5 ≤ Fintype.card F := by rw [← Nat.card_eq_fintype_card,hfixed]; omega
  have hcycles : c.cycleType.card < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card,hfixed]
    omega
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  exact hnotAlt (alternatingGroup_le_of_prime_cyclic_fixed_action_cycle_count
    X P (by omega) hexp r hp hr (show 5 ≤ Fintype.card F by omega) hAlt hcycles)

end FiveTransitive.Degree52SevenCyclicExclusion

end CFSG
