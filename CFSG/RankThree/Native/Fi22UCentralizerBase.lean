
module

public import CFSG.RankThree.Native.Fi22UAction
public import CFSG.Monster.B.Fischer.Fi22Centralizer
public import CFSG.RankThree.Native.Fi22UCentralizerCheckInputs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

@[expose] public noncomputable section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Assembly.LowTwoRank CFSG.Fischer
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise commutatorElement

theorem fi22OuterMPointsNat_length : fi22OuterMPointsNat.length = 693 := by
  simp only [fi22OuterMPointsNat, hex3List, List.length_map, List.length_range]

@[expose] def fi22IPt (j : Fin 693) : Fin 3510 :=
  ⟨fi22OuterMPointsNat.getD j 0 % 3510, Nat.mod_lt _ (by norm_num)⟩

theorem fi22OuterMPointsNat_getD_lt (j : Fin 693) : fi22OuterMPointsNat.getD j 0 < 3510 := by
  have hj : (j : ℕ) < fi22OuterMPointsNat.length := by
    rw [fi22OuterMPointsNat_length]
    exact j.2
  rw [List.getD_eq_getElem _ _ hj]
  exact fi22Outer_check.2.2.2.2.2.2.1 _ (List.getElem_mem hj)

theorem fi22IPt_val (j : Fin 693) : (fi22IPt j : ℕ) = fi22OuterMPointsNat.getD j 0 :=
  Nat.mod_eq_of_lt (fi22OuterMPointsNat_getD_lt j)

@[expose] def fi22ISet : Set (Fin 3510) := Set.range fi22IPt

theorem fi22OuterLine3510_three (k : ℕ) : fi22OuterLine3510 3 k = 3 + k := rfl

theorem fi22OuterStrong3510_three_get {k : ℕ} (hk : k < 17) :
    (fi22OuterStrong3510 3)[k]! = fi22OuterArr3510 (3 + k) := by
  rw [fi22OuterStrong3510, getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk),
    Array.getElem_ofFn]
  exact congrArg fi22OuterArr3510 (fi22OuterLine3510_three k)

theorem fi22OuterLine693_three (k : ℕ) : fi22OuterLine693 3 k = 64 + k := rfl

theorem fi22OuterStrong693_three_get {k : ℕ} (hk : k < 15) :
    (fi22OuterStrong693 3)[k]! = fi22OuterArr693 (64 + k) := by
  rw [fi22OuterStrong693, getElem!_pos _ k (by rw [Array.size_ofFn]; exact hk),
    Array.getElem_ofFn]
  exact congrArg fi22OuterArr693 (fi22OuterLine693_three k)

theorem fi22OuterPerm3510_def (L : ℕ) : fi22OuterPerm3510 L = permOfArr 3510 (fi22OuterArr3510 L) :=
  rfl

theorem fi22OuterCu_eq : fi22OuterCu = fi22OuterPerm693 0 := rfl

theorem rep_fi22OuterCu_inv : Rep 693 (invCand 693 (fi22OuterArr693 0)) fi22OuterCu⁻¹ :=
  (rep_permOfArr (fi22Outer_check.2.2.2.2.1 0 (by norm_num))).2

theorem mem_fi22OuterM_gen {i : ℕ} (hi : i < 3) : fi22OuterPerm3510 (3 + i) ∈ fi22OuterM := by
  rw [fi22OuterM, RawSchreierDatum.originalSubgroup]
  refine Subgroup.subset_closure ?_
  rw [Set.mem_ofPred_eq, fi22OuterChainM, RawSchreierDatum.mem_ofArrays_original]
  exact ⟨i, hi, by rw [fi22OuterStrong3510_three_get (by omega), fi22OuterPerm3510_def]⟩

@[expose] def fi22OuterZM : fi22OuterM := ⟨fi22OuterZ, fi22OuterZ_mem_M⟩

theorem orderOf_fi22OuterZM : orderOf fi22OuterZM = 2 := by
  rw [fi22OuterZM, Subgroup.orderOf_mk, orderOf_fi22OuterZ]

theorem fi22OuterZ_eq_perm : fi22OuterZ = fi22OuterPerm3510 1 := rfl

theorem fi22OuterZM_mem_center : fi22OuterZM ∈ Subgroup.center fi22OuterM := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hg := Subgroup.mem_centralizer_singleton_iff.1 (fi22OuterM_le_centralizer g.2)
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, fi22OuterZM, Subgroup.coe_mk]
  exact hg

theorem commutator_fi22OuterX : commutator fi22OuterX = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator fi22OuterX) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := fi22OuterX_not_comm
    have hmem : ⁅a, b⁆ ∈ commutator fi22OuterX :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hab hmem
  · exact h

theorem rep_commA {a b : ℕ} (ha : a < 151) (hb : b < 151) :
    Rep 3510 (commA 3510 (fi22OuterArr3510 a) (fi22OuterArr3510 b))
      (fi22OuterPerm3510 b * fi22OuterPerm3510 a * (fi22OuterPerm3510 b)⁻¹ *
        (fi22OuterPerm3510 a)⁻¹) :=
  rep_compA (rep_compA (rep_compA (rep_fi22OuterPerm3510 hb) (rep_fi22OuterPerm3510 ha))
    (rep_permOfArr (fi22Outer_check.2.2.2.1 b hb)).2)
    (rep_permOfArr (fi22Outer_check.2.2.2.1 a ha)).2

end CFSG.RankThree.Native.Fi22U
