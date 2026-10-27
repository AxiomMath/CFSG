module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LDih
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin

theorem nfa2_g4_apply (hG4 : Leaf_G4) {q : ℕ} (hq : q.Prime) (h24 : q % 24 = 11 ∨ q % 24 = 13)
    {Kb : Type} [Group Kb] (hm : StatedClassicalModel Kb .PSL 2 q 1)
    (xb ab sb : Kb) (hx3 : orderOf xb = 3) (ha2 : orderOf ab = 2) (hxa : ab * xb = xb * ab)
    (hsa : sb * ab = ab * sb) (hsx : sb * xb * sb⁻¹ = xb⁻¹) (hs2 : sb * sb = 1) (hs1 : sb ≠ 1)
    (F : Subgroup Kb) (hxF : xb ∈ F) (haF : ab ∈ F) (hsF : sb ∈ F) (hF : F ≠ ⊤) :
    F ≤ Subgroup.centralizer ({ab} : Set Kb) := by
  have hC : Commute ab xb := hxa
  have hab2 : ab * ab = 1 := by
    have h := pow_orderOf_eq_one ab
    rw [ha2, pow_two] at h
    exact h
  have hab_inv : ab⁻¹ = ab := inv_eq_of_mul_eq_one_right hab2
  have hxb3 : xb ^ 3 = 1 := by
    have h := pow_orderOf_eq_one xb
    rw [hx3] at h
    exact h
  have hsq : sb ^ 2 = 1 := by
    rw [pow_two]
    exact hs2
  have hsb_ord : orderOf sb = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hsq hs1
  have ht6 : orderOf (xb * ab) = 6 := by
    have hco : (orderOf xb).Coprime (orderOf ab) := by
      rw [hx3, ha2]
      norm_num
    have h := hC.symm.orderOf_mul_eq_mul_orderOf_of_coprime hco
    rw [hx3, ha2] at h
    exact h
  have hst : sb * (xb * ab) * sb⁻¹ = (xb * ab)⁻¹ := by
    rw [mul_inv_rev, hab_inv, mul_inv_eq_iff_eq_mul]
    calc sb * (xb * ab) = (sb * xb) * ab := by rw [mul_assoc]
      _ = (xb⁻¹ * sb) * ab := by rw [mul_inv_eq_iff_eq_mul.mp hsx]
      _ = xb⁻¹ * (sb * ab) := by rw [mul_assoc]
      _ = xb⁻¹ * (ab * sb) := by rw [hsa]
      _ = (xb⁻¹ * ab) * sb := by rw [mul_assoc]
      _ = (ab * xb⁻¹) * sb := by rw [← hC.inv_right.eq]
  obtain ⟨hcard, hiso⟩ := nfa2_closure_dihedral6 (xb * ab) sb ht6 hsb_ord hst
  have htE : xb * ab ∈ Subgroup.closure ({xb * ab, sb} : Set Kb) :=
    Subgroup.subset_closure (Set.mem_insert (xb * ab) ({sb} : Set Kb))
  have habE : ab ∈ Subgroup.closure ({xb * ab, sb} : Set Kb) := by
    have h3 : (xb * ab) ^ 3 = ab := by
      rw [hC.symm.mul_pow, hxb3, one_mul, pow_three, hab2, mul_one]
    have hmem := pow_mem htE 3
    rwa [h3] at hmem
  have hEc : Subgroup.closure ({xb * ab, sb} : Set Kb) ≤ Subgroup.centralizer ({ab} : Set Kb) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [← mul_assoc, hxa]
    · exact hsa.symm
  have hcomm : ∀ e ∈ Subgroup.closure ({xb * ab, sb} : Set Kb), ab * e = e * ab :=
    fun e he => Subgroup.mem_centralizer_iff.mp (hEc he) ab (Set.mem_singleton ab)
  have hEF : Subgroup.closure ({xb * ab, sb} : Set Kb) ≤ F := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact F.mul_mem hxF haF
    · exact hsF
  exact (hG4 q hq h24 Kb hm (Subgroup.closure ({xb * ab, sb} : Set Kb)) F ab hcard hiso habE hcomm
    ha2 hEF hF).1

end CFSG.Quasithin.H13.NFa2
