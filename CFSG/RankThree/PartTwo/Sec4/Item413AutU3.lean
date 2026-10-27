module

public import CFSG.RankThree.PartTwo.Sec4.Item413AutGen
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem psuConj_eq_one_iff (A : unitaryIsom3 h) :
    psuConj h A = 1 ↔ (A : GL (Fin 3) K) ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K := by
  constructor
  · intro hA
    obtain ⟨-, c, -, hc⟩ :=
      eq_one_of_psuConj_mul_psuField_eq_one A 1 (by rw [map_one, mul_one, hA])
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    ext x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [psuConj_mk, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [coe_suConj, Subgroup.coe_inv, ← hc, ← (commute_scalar c (g : GL (Fin 3) K)).eq,
        mul_inv_cancel_right]

theorem card_le_27_of_mulAut_unitaryPSU [Finite K] (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    (B : Subgroup (MulAut (unitaryPSU h 3))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 27 := by
  have := h.finite
  set N := (psuConj h).range
  set C := (psuField h).range
  have hcycK := (card_ringAut_and_isCyclic h.prime K h.card).2
  have hcyc : IsCyclic C :=
    isCyclic_of_surjective (psuField h).rangeRestrict (psuField h).rangeRestrict_surjective
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨A, rfl⟩ := hx
    exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  set ψ : unitaryIsom3 h →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.mk' _).comp (unitaryIsom3 h).subtype
  have hk : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, psuConj_eq_one_iff]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) K) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.injective)
  set E := ((B ⊓ N).subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h9 : Nat.card (B ⊓ N : Subgroup _) ≤ 9 := by
    rw [← hcardE]
    refine card_le_nine_of_pgl3 h3 E ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hBc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
      rw [this, map_one]
  have h1 := card_le_three_mul_card_inf hB hcyc hCN hBNC
  omega

theorem rankAutU3_holds : ∀ (p f : ℕ) [Fact p.Prime], p ≠ 3 → 1 ≤ f → 2 < p ^ f →
    CFSG.pRank 3 (MulAut (projSU 3 p f)) ≤ 3 := by
  intro p f _ hp3 hf hq
  have hU := unitaryFieldData_galoisField p f hf
  have h3 := three_ne_zero_of_card (Fact.out) hp3 (GaloisField.card p (2 * f) (by omega))
  exact pRank_three_le_of_card_le (card_le_of_mulEquiv_mulAut (projSUEquivUnitaryPSU p f hU)
    (card_le_27_of_mulAut_unitaryPSU h3 hq))

theorem rankAutSU3_holds : ∀ (p f : ℕ) [Fact p.Prime] (K : Type) [Field K] [Finite K], p ≠ 3 →
    Nat.card K = (p ^ f) ^ 2 → 2 < p ^ f →
      CFSG.pRank 3 (MulAut (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) ≤ 3 := by
  intro p f _ K _ _ hp3 hK hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · simp at hq
    · exact hf
  have hU : UnitaryFieldData p f K := ⟨Fact.out, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have h3 := three_ne_zero_of_card (Fact.out) hp3 hU.card
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three hU hq
  have hinj : Function.Injective (centerDescend (unitarySU p f K 3)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    rw [Subgroup.mem_bot]
    refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
    have h1 := congrArg (fun φ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
      φ (s : unitarySU p f K 3 ⧸ Subgroup.center _)) he
    simp only [centerDescend_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have := (Subgroup.center _).inv_mem h1
    simpa using this
  refine pRank_three_le_of_card_le fun B hB => ?_
  have := card_le_27_of_mulAut_unitaryPSU (h := hU) h3 hq
    ((B.map (centerDescend (unitarySU p f K 3))).map
      (MulAut.congr (suCenterEquiv hU hq)).toMonoidHom)
    (isElemAbelian_map _ (isElemAbelian_map _ hB))
  rwa [Subgroup.card_map_of_injective (MulAut.congr (suCenterEquiv hU hq)).injective,
    Subgroup.card_map_of_injective hinj] at this

end CFSG.RankThree.PartTwo.Sec4
