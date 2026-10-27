module

public import CFSG.Quasithin.EmptyFaithful.T1521SL2EOff
public import CFSG.Quasithin.EmptyFaithful.T1521SL2EAct
public import CFSG.Quasithin.EmptyFaithful.T1521SOff

public section

namespace CFSG.Quasithin

open CFSG.PSL2Table CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.L21521E
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem thompsonJ_le_innerPart_l2 {S L : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hL : IsPSL 2 2 n ↥L)
    (hSyl : IsSylowTwoOf (S ⊓ L) L) (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    thompsonJ S ≤ innerPart1521 S L := by
  obtain ⟨K, hKf, hKfin, φ, hK, hφ⟩ := exists_equiv_unipotent (by omega) hL hSyl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hVL : S ⊓ L ≤ L := inf_le_right
  have hVS : S ⊓ L ≤ S := inf_le_left
  have hV : IsElemAbelian 2 (S ⊓ L) := isElemAbelian_of_equiv_unipotent φ hφ hVL
  refine thompsonJ_le_innerPart_of_offender hVS hV (centralizer_le_innerPart hSN φ hφ) ?_
  intro A hA hAS hineq
  refine centralizes_of_offender_twist hn hK
    (fun x : K => ((φ.symm (mk (unip x)) : ↥L) : G)) (coord_injective φ)
    (coord_mem φ hφ) (fun y hy => coord_surj φ hφ hVL hy) hA ?_ hineq
  intro a ha
  have haS : a ∈ S := hAS ha
  exact exists_twist_conj φ hφ (hSN haS) (fun y hy => ⟨S.mul_mem (S.mul_mem haS hy.1)
    (S.inv_mem haS), (Subgroup.mem_normalizer_iff.mp (hSN haS) y).mp hy.2⟩)

end CFSG.Quasithin
