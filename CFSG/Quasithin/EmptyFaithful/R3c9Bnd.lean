module

public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.Quasithin.EmptyFaithful.SBc2SzLift
public import CFSG.Quasithin.Background.GoldschmidtS146RPair

public section

namespace CFSG.Quasithin.R3c9

open CFSG.Open CFSG.Goldschmidt CFSG.Goldschmidt.G3a CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped MatrixGroups

theorem bender_center_le {X : Type} [Group X] [Finite X]
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X) {E : Subgroup X} (hET : E ≤ (T : Subgroup X))
    (hE1 : E ≠ ⊥)
    (hN : Subgroup.normalizer ((T : Subgroup X) : Set X) ≤ Subgroup.normalizer (E : Set X)) :
    sylowCenter (T : Subgroup X) ≤ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hD⟩ := exists_borelSetup hX T
  have hTE : (T : Subgroup X) ≤ Subgroup.normalizer (E : Set X) := Subgroup.le_normalizer.trans hN
  let E' : Subgroup ↥(T : Subgroup X) := E.subgroupOf (T : Subgroup X)
  have hE'n : E'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hET).mpr hTE
  have hE'1 : E' ≠ ⊥ := by
    intro hb
    apply hE1
    rw [eq_bot_iff]
    intro e he
    have : (⟨e, hET he⟩ : ↥(T : Subgroup X)) ∈ E' := Subgroup.mem_subgroupOf.mpr he
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent ↥(T : Subgroup X) := T.isPGroup'.isNilpotent
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hE'1
  obtain ⟨⟨⟨x, hxT⟩, hxmem⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  have hxE : x ∈ E := Subgroup.mem_subgroupOf.mp hxmem.1
  have hxZ : x ∈ sylowCenter (T : Subgroup X) := by
    rw [mem_sylowCenter]
    refine ⟨hxT, fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.mp hxmem.2 ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hx1' : x ≠ 1 := by
    intro h
    apply hx1
    exact Subtype.ext (Subtype.ext h)
  intro w hw
  by_cases hw1 : w = 1
  · rw [hw1]
    exact E.one_mem
  · obtain ⟨d, hd, hdw⟩ := hD.trans hxZ hw hx1' hw1
    have hdN : d ∈ Subgroup.normalizer (E : Set X) := hN (hD.le hd)
    have hdN' : d⁻¹ ∈ Subgroup.normalizer (E : Set X) := Subgroup.inv_mem _ hdN
    have := (Subgroup.mem_normalizer_iff.mp hdN' x).mp hxE
    rw [inv_inv] at this
    rw [← hdw]
    exact this

theorem exists_psl2_equiv {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    2 ≤ n ∧ Nonempty (X ≃* PSL(2, GaloisField 2 n)) := by
  obtain ⟨hadm, K, _, _, hcard, ⟨e⟩⟩ := h
  have hn1 : 1 ≤ n := hadm.2.1
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact hadm.2.2.2.1 (by simp)
  exact ⟨hn2, ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
      (CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 n (by omega) hcard) (Fin 2)))⟩⟩

theorem exists_psu3_equiv_of_isPSU {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X] (h : IsPSU 3 2 n X) :
    Nonempty (X ≃* PSU3 2 n) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) := e
  exact ⟨e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)⟩

theorem card_sylowCenter_of_isPSL {n : ℕ} {X : Type} [Group X] [Finite X]
    (h : IsPSL 2 2 n X) (T : Sylow 2 X) : Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ n := by
  obtain ⟨hn, ⟨e⟩⟩ := exists_psl2_equiv h
  obtain ⟨D, hD⟩ := exists_borelSetup (A5.C25.fusionIsBenderGroup_of_isPSL h) T
  exact (hD.orders_psl2 hn e).2.2

theorem card_sylowCenter_of_isPSU {n : ℕ} (hn : 2 ≤ n) {X : Type} [Group X]
    [Finite X] (h : IsPSU 3 2 n X) (T : Sylow 2 X) : Nat.card (sylowCenter (T : Subgroup X)) = 2 ^ n := by
  obtain ⟨e⟩ := exists_psu3_equiv_of_isPSU hn h
  obtain ⟨D, hD⟩ := exists_borelSetup (K1.fusionIsBenderGroup_of_stated_psu_three hn h) T
  exact (hD.orders_psu3 hn e).1

section Sub

variable {G : Type} [Group G] [Finite G]

theorem bender_center_card_le {L Q E : Subgroup G}
    (hB : fusionIsBenderGroup ↥L) (hQ : IsSylowTwoOf Q L) (hEQ : E ≤ Q) (hE1 : E ≠ ⊥)
    (hN : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (E : Set G)) :
    ∃ T : Sylow 2 ↥L, (T : Subgroup ↥L) = Q.subgroupOf L ∧
      Nat.card (sylowCenter (T : Subgroup ↥L)) ≤ Nat.card E := by
  have hQL : Q ≤ L := hQ.1
  have hEL : E ≤ L := hEQ.trans hQL
  let T : Sylow 2 ↥L := GoldS146R.sylowOfIsSylowTwoOf hQ
  have hT : (T : Subgroup ↥L) = Q.subgroupOf L := GoldS146R.coe_sylowOfIsSylowTwoOf hQ
  refine ⟨T, hT, ?_⟩
  have hET : E.subgroupOf L ≤ (T : Subgroup ↥L) := by
    rw [hT]
    intro e he
    exact Subgroup.mem_subgroupOf.mpr (hEQ (Subgroup.mem_subgroupOf.mp he))
  have hE1' : E.subgroupOf L ≠ ⊥ := by
    intro hb
    apply hE1
    rw [eq_bot_iff]
    intro e he
    have : (⟨e, hEL he⟩ : ↥L) ∈ E.subgroupOf L := Subgroup.mem_subgroupOf.mpr he
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hN' : Subgroup.normalizer ((T : Subgroup ↥L) : Set ↥L) ≤
      Subgroup.normalizer ((E.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro l hl
    rw [hT] at hl
    have h1 : (l : G) ∈ Subgroup.normalizer (Q : Set G) := (SBc2.mem_normalizer_subgroupOf_iff hQL l).mp hl
    exact (SBc2.mem_normalizer_subgroupOf_iff hEL l).mpr (hN ⟨l.2, h1⟩)
  have hle := bender_center_le hB T hET hE1' hN'
  have hcard : Nat.card (sylowCenter (T : Subgroup ↥L)) ≤ Nat.card (E.subgroupOf L) :=
    Subgroup.card_le_of_le hle
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv] at hcard
  exact hcard

end Sub

end CFSG.Quasithin.R3c9
