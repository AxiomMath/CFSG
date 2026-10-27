module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section LLocal

variable {G : Type} [Group G] [Finite G]

theorem ggD4OddCent_lLocal {B : Subgroup G} {x y : G} {L D J : Subgroup G}
    (hI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hD : D = Subgroup.closure {x, y}) (hyB : y ∈ B)
    (hNL : B ≤ Subgroup.normalizer (L : Set G)) :
    GGAutLocal (ggAutsOf L B hNL) (L.normalizerMonoidHom ⟨y, hNL hyB⟩) (J.subgroupOf L) := by
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  have hB : IsElemAbelian 3 B := hS.1.1
  have hDJp : LargeEvenStdSubPre 3 B x L D J := hDJ.1
  have hJL : J ≤ L := hDJp.2.2.2.2.2.1.1.trans inf_le_left
  have hJcD : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) := hDJp.2.2.2.2.2.1
  have hCD : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hD, Subgroup.centralizer_closure]
    ext g
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCD, ← inf_assoc, inf_eq_left.mpr hLx]
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := by
    rw [← hLD]; exact hJcD
  refine ⟨isElemAbelian_ggAutsOf hNL hB, (mem_ggAutsOf hNL).2 ⟨y, hyB, rfl⟩, ?_, ?_, ?_⟩
  · intro hδ
    have hyC : y ∈ Subgroup.centralizer (L : Set G) :=
      (normalizerMonoidHom_eq_one_iff (hNL hyB)).1 hδ
    have hyinf : y ∈ B ⊓ Subgroup.centralizer (L : Set G) := ⟨hyB, hyC⟩
    rw [inf_centralizer_eq_zpowers_of_sstar Nat.prime_three hS] at hyinf
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hD]
      exact (Subgroup.closure_le _).mpr (by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with h | h
        · rw [h]; exact Subgroup.mem_zpowers x
        · rw [h]; exact hyinf)
    have hcl := Subgroup.card_le_of_le hDle
    rw [hDJp.2.2.1, Nat.card_zpowers, orderOf_eq_prime (hB.2 x hS.2.1) hS.2.2.1] at hcl
    norm_num at hcl
  · exact isComponentOf_subgroupOf_ggAutFixed (hNL hyB) hJL hJc
  · exact ggAutsOf_apply_mem hNL (le_normalizer_of_stdSub hS hst hDJp)

theorem ggD4OddCent_card_lAuts {B : Subgroup G} {x : G} {L : Subgroup G}
    (hI : GGThmIHyp 3 B x L) (hNL : B ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(ggAutsOf L B hNL) = 3 ^ (LargeEvenTwoLocalRank 3 G - 1) := by
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hm : 4 ≤ LargeEvenTwoLocalRank 3 G := hI.2.2.2.2.2.1.2.2.2
  have hcard := card_ggAutsOf_mul_card hNL
  have hCL : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_sstar Nat.prime_three hS
  have hzx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hS.2.1) hS.2.2.1]
  have hBcard : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hS.1.2.1
  rw [hCL, hzx, hBcard] at hcard
  have hm1 : 1 ≤ LargeEvenTwoLocalRank 3 G := by omega
  have hpow : 3 ^ LargeEvenTwoLocalRank 3 G =
      3 * 3 ^ (LargeEvenTwoLocalRank 3 G - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm1]
    rw [pow_succ]
    ring
  rw [hpow] at hcard
  rw [mul_comm 3 (3 ^ (LargeEvenTwoLocalRank 3 G - 1))] at hcard
  exact Nat.mul_right_cancel (by norm_num) hcard

end LLocal

end CFSG.StandardType
