module

public import CFSG.OddTranspositions.O4PairFixSubgroup
public import CFSG.OddTranspositions.O4PairTenAbstract

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.GorensteinWalter CFSG.PSL2Table

@[expose] def FixK : Subgroup (PSL2 K25) where
  carrier := {q | q = psl2FieldAut K25 frob25 q}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul]
    conv_lhs => rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv]
    exact congrArg Inv.inv ha

theorem map_FixG : FixG.map pslEquiv.toMonoidHom = FixK := by
  ext q
  constructor
  · rintro ⟨g, hg, rfl⟩
    change pslEquiv g = psl2FieldAut K25 frob25 (pslEquiv g)
    rw [← pslEquiv_aut_apply, hg]
  · intro hq
    refine ⟨pslEquiv.symm q, ?_, pslEquiv.apply_symm_apply q⟩
    apply pslEquiv.injective
    rw [pslEquiv_aut_apply, MulEquiv.apply_symm_apply]
    exact hq.symm

theorem card_FixK : Nat.card FixK = 120 := by
  calc
    Nat.card FixK = Nat.card {q : PSL2 K25 // q = psl2FieldAut K25 frob25 q} := rfl
    _ = Nat.card {q : PSL2 F25t // psl2FieldAut F25t frob25t q = q} :=
      (Nat.card_congr fixEquiv).symm
    _ = Nat.card FixG := rfl
    _ = 120 := card_FixG

theorem left_y (i : Fin 10) : (y i).left = pslEquiv (x i) := by
  rw [y, SemidirectProduct.mk_eq_inl_mul_inr, map_mul, psigmaL2Equiv_inl,
    psigmaL2Equiv_inr_frob25t]
  simp [SemidirectProduct.mul_left]

theorem range_left_y : Set.range (fun i : Fin 10 => (y i).left) =
    pslEquiv '' Set.range x := by
  ext q
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨x i, ⟨i, rfl⟩, (left_y i).symm⟩
  · rintro ⟨r, ⟨i, rfl⟩, hq⟩
    refine ⟨i, ?_⟩
    show (y i).left = q
    rw [left_y i]
    exact hq

theorem closure_left_y_eq_FixK :
    Subgroup.closure (Set.range (fun i : Fin 10 => (y i).left)) = FixK := by
  rw [range_left_y]
  change Subgroup.closure ((⇑pslEquiv.toMonoidHom) '' Set.range x) = FixK
  rw [← MonoidHom.map_closure pslEquiv.toMonoidHom (Set.range x)]
  change Subgroup.map pslEquiv.toMonoidHom H = FixK
  rw [H_eq_FixG, map_FixG]

end CFSG.OddTranspositions.QZ
