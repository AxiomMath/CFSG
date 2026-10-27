module

public import CFSG.Sporadic.Mathieu.Chain

public section

namespace CFSG.Sporadic.Mathieu

open MulAction CFSG.Sporadic.Th CFSG.Sporadic.Mathieu.Native

variable {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))} {D : Data} {a b : G}

theorem closure_pair_eq_top {M : Type*} [Group M] {K : Subgroup M} {x y : M}
    (hK : K = Subgroup.closure {x, y}) (hx : x ∈ K) (hy : y ∈ K) :
    Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩} : Set K) = ⊤ := by
  subst hK
  refine Eq.trans ?_ (Subgroup.closure_closure_coe_preimage (k := {x, y}))
  congr 1
  ext ⟨g, hg⟩
  simp [Subtype.ext_iff]

theorem card_stabilizer_eq {H X : Type*} [Group H] [MulAction H X] [IsPretransitive H X] (x : X)
    (hX : 0 < Nat.card X) : Nat.card (stabilizer H x) = Nat.card H / Nat.card X := by
  rw [← Subgroup.card_mul_index (stabilizer H x), index_stabilizer_of_transitive,
    Nat.mul_div_cancel _ hX]

theorem isMultiplyPretransitive_two (H : Hyp G D a b) (hk : 2 ≤ D.k) (hn : 2 ≤ n) :
    IsMultiplyPretransitive G (Fin n) 2 := by
  refine is_two_pretransitive_iff.2 fun {u v u' v'} huv huv' => ?_
  obtain ⟨g, g0, g1⟩ := exists_smul_eq_two H hk hn u v huv
  obtain ⟨g', g0', g1'⟩ := exists_smul_eq_two H hk hn u' v' huv'
  refine ⟨g' * g⁻¹, ?_, ?_⟩
  · rw [mul_smul, inv_smul_eq_iff.2 g0.symm, g0']
  · rw [mul_smul, inv_smul_eq_iff.2 g1.symm, g1']

theorem isSimpleGroup_of_check (H : Hyp G D a b) (hk : 2 ≤ D.k) (hn : 2 ≤ n)
    (hpX : D.pX.Prime) (hpY : D.pY.Prime) (hpXY : D.pXY.Prime)
    (hXY : Nat.Coprime (D.pX ^ (D.eX + 1)) (D.pY ^ (D.eY + 1)))
    (hst : Nat.Coprime (D.pXY ^ (D.eXY + 1)) (D.sizes.prod / n)) : IsSimpleGroup G := by
  have h2 := isMultiplyPretransitive_two H hk hn
  have : IsPreprimitive G (Fin n) := isPreprimitive_of_is_two_pretransitive h2
  have : IsPretransitive G (Fin n) := isPretransitive_of_is_two_pretransitive
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Fin n) (by simpa using hn) (gs D a b 0)
    (gs D a b 1) (closure_gs H) ⟨0, by omega⟩ ?_ ?_
  · rw [orderOf_X H hpX, orderOf_Y H hpY]
    exact hXY
  · rw [orderOf_XY H hpXY, card_stabilizer_eq _ (by simp; omega), card_eq H, Nat.card_fin]
    exact hst

theorem isSimpleGroup_of_check_duads (H : Hyp G D a b) (hk : 4 ≤ D.k) (hn : 5 ≤ n)
    (hpX : D.pX.Prime) (hpY : D.pY.Prime) (hpXY : D.pXY.Prime)
    (hXY : Nat.Coprime (D.pX ^ (D.eX + 1)) (D.pY ^ (D.eY + 1)))
    (hst : Nat.Coprime (D.pXY ^ (D.eXY + 1)) (D.sizes.prod / n.choose 2)) : IsSimpleGroup G := by
  have h2 := isMultiplyPretransitive_two H (by omega) (by omega)
  have hpre := Set.powersetCard.isPretransitive_of_isMultiplyPretransitive G h2
  have hprim := isPreprimitive_duads (G := G) ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    ⟨3, by omega⟩ ⟨4, by omega⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (exists_smul_eq_three H (by omega) (by omega))
    (exists_smul_eq_four H hk (by omega))
  have hfaith := Set.powersetCard.faithfulSMul (G := G) (α := Fin n) (n := 2) (by norm_num) (by
      rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      exact_mod_cast (by omega : 2 < n))
  have : IsPretransitive G (Set.powersetCard (Fin n) 2) := hpre
  have : IsPreprimitive G (Set.powersetCard (Fin n) 2) := hprim
  have : FaithfulSMul G (Set.powersetCard (Fin n) 2) := hfaith
  have hcard : Nat.card (Set.powersetCard (Fin n) 2) = n.choose 2 := by
    rw [Set.powersetCard.card, Nat.card_fin]
  have h52 : 10 ≤ n.choose 2 := by
    have h5 : Nat.choose 5 2 = 10 := by decide
    have := Nat.choose_mono 2 hn
    simp only at this
    omega
  refine isSimpleGroup_of_primitive_coprime_orders (Ω := Set.powersetCard (Fin n) 2)
    (by omega) (gs D a b 0) (gs D a b 1) (closure_gs H) (duad ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp))
    ?_ ?_
  · rw [orderOf_X H hpX, orderOf_Y H hpY]
    exact hXY
  · rw [orderOf_XY H hpXY, card_stabilizer_eq _ (by omega), card_eq H, hcard]
    exact hst

end CFSG.Sporadic.Mathieu
