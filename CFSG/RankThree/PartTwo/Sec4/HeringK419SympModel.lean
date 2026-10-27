module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419SympInner
public import CFSG.RankThree.PartTwo.Sec4.HeringK419Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringK419

open CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

@[expose] noncomputable def statedSpData (n : ℕ) (K : Type) [Field K] :
    SympData K (Fin n ⊕ Fin n → K) (StatedSp n K) where
  F := spForm n K
  σ_eq := rfl
  alt := spForm_self n K
  ρ := natRep (StatedSp n K)
  iso := isIsometric_natRep_statedSp n K
  inj := natRep_injective _
  trans := fun x =>
    exists_natRep_eq_of_isometry n K
      { toFun := fun v => v + (spForm n K).β x v • x
        map_add' := fun u v => by
          simp only [(spForm n K).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
      ((spForm n K).β_transvection rfl (spForm_self n K) x)
  siegel := fun x y hxy =>
    exists_natRep_eq_of_isometry n K
      { toFun := fun v => v + (spForm n K).β x v • y + (spForm n K).β y v • x
        map_add' := fun u v => by
          simp only [(spForm n K).add_right, add_smul]
          abel
        map_smul' := fun a v => by
          simp only [(spForm n K).smul_right, RingHom.id_apply, smul_add, smul_smul] }
      ((spForm n K).β_siegel rfl (spForm_self n K) hxy)

theorem hasTwoWitness_statedSp {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : StatedSp n K} (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) : HasTwoWitness k := by
  refine (statedSpData n K).exists_two_subgroup_of_order_three ?_ hk3 hk1
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

end CFSG.RankThree.PartTwo.Sec4.HeringK419
