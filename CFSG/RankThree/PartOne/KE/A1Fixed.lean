module

public import CFSG.RankThree.PartOne.KE.SigmaUnion
public import CFSG.RankThree.PartOne.KGD.D4QA3

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL diagUnitOne)
open CFSG.RankThree.PartOne.KGD (glMap_diagUnitOne)
open scoped MatrixGroups Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem diagUnitOne_one_eq : diagUnitOne (1 : Lˣ) = 1 := by
  apply Units.ext
  rw [CFSG.RankThree.Classical.coe_diagUnitOne, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem diagUnitOne_inv_eq (a : Lˣ) : (diagUnitOne a)⁻¹ = diagUnitOne a⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [diagUnitOne_mul, mul_inv_cancel, diagUnitOne_one_eq]

theorem exists_twist_diag [IsAlgClosed L] {K : Type} [Field K] [Finite K] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (s : Lˣ) :
    ∃ P : GL (Fin 2) L, P * Matrix.GeneralLinearGroup.map Fr P⁻¹ = diagUnitOne s := by
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpos : 0 < Nat.card K - 1 := by omega
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq ((s⁻¹ : Lˣ) : L) hpos
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hpos.ne'] at hw
    exact (s⁻¹).ne_zero hw.symm
  set u : Lˣ := Units.mk0 w hw0 with hu
  have hus : u ^ (Nat.card K - 1) = s⁻¹ := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact hw)
  have hFu : Units.map Fr.toMonoidHom u = u ^ Nat.card K := Units.ext (by
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact hFr _)
  refine ⟨diagUnitOne u, ?_⟩
  rw [map_inv, glMap_diagUnitOne, diagUnitOne_inv_eq, diagUnitOne_mul, hFu]
  congr 1
  have hq : Nat.card K = (Nat.card K - 1) + 1 := by omega
  calc u * (u ^ Nat.card K)⁻¹ = u * (u ^ ((Nat.card K - 1) + 1))⁻¹ := by rw [← hq]
    _ = (u ^ (Nat.card K - 1))⁻¹ := by
      rw [pow_succ]
      group
    _ = s := by rw [hus, inv_inv]

theorem a1_fixed_factor [IsAlgClosed L] {K : Type} [Field K] [Finite K] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (hK4 : 4 ≤ Nat.card K)
    {r : Fin τ.rank → ℤ} (hr : IsRoot τ r) (n : ModGL τ L) (s : Lˣ)
    (hn : ∀ A : SL2 L, n * rootSL2 τ L r A * n⁻¹ = rootSL2 τ L r (conjSL (diagUnitOne s) A)) :
    ∃ P : Subgroup (ModGL τ L),
      P = rootSpan τ L {r, -r} ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧
      SigmaFactor n Fr {r, -r} (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan τ L {r, -r} : Set (ModGL τ L))) := by
  classical
  obtain ⟨Pm, hPm⟩ := exists_twist_diag (K := K) Fr hFr s
  set S : Subgroup (SL2 L) := (Matrix.SpecialLinearGroup.map (algebraMap K L)).range.map
    (conjSL Pm) with hSdef
  have hX : ∀ B : SL2 L, n * Units.map (entrywiseHom Fr) (rootSL2 τ L r B) * n⁻¹ =
      rootSL2 τ L r (conjSL (Pm * Matrix.GeneralLinearGroup.map Fr Pm⁻¹)
        (Matrix.SpecialLinearGroup.map Fr B)) := fun B => by
    rw [hPm, entrywise_rootSL2_of_field, hn]
  have hSfix : ∀ B : SL2 L, n * Units.map (entrywiseHom Fr) (rootSL2 τ L r B) * n⁻¹ =
      rootSL2 τ L r B ↔ B ∈ S :=
    a1_hS1_of_action (K := K) Fr hFr Pm hX
  obtain ⟨hfin, hq⟩ := sl2_conj_range_quasisimple (K := K) (L := L) hK4 Pm
  have hz := sl2_conj_range_centralizer (K := K) (L := L) Pm
  have hinj : Function.Injective (rootSL2 τ L r) := rootSL2_injective_of_field r
  have hrange : rootSpan τ L {r, -r} = (rootSL2 τ L r).range := by
    rw [rootSpan, iSup_insert, iSup_singleton, ← range_rootSL2_of_isRoot hr]
  have hroots : ∀ α ∈ ({r, -r} : Set (Fin τ.rank → ℤ)), IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl
    exacts [hr, IsRoot.neg hr]
  refine ⟨rootSpan τ L {r, -r} ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)), rfl, ?_⟩
  have hPeq : rootSpan τ L {r, -r} ⊓ twistedFixedPoints n (Units.map (entrywiseHom Fr)) =
      S.map (rootSL2 τ L r) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgQ, hgR⟩ := Subgroup.mem_inf.1 hg
      rw [hrange] at hgQ
      obtain ⟨A, rfl⟩ := hgQ
      exact ⟨A, (hSfix A).1 hgR, rfl⟩
    · rintro _ ⟨A, hA, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, (hSfix A).2 hA⟩
      rw [hrange]
      exact ⟨A, rfl⟩
  have hfinP : Finite (S.map (rootSL2 τ L r)) := by
    have : Finite S := hfin
    exact Finite.of_equiv S (Subgroup.equivMapOfInjective S (rootSL2 τ L r) hinj)
  have hqP : CFSG.IsQuasisimple (S.map (rootSL2 τ L r)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective S (rootSL2 τ L r) hinj)
      hq
  refine ⟨fun _ => ?_, fun _ => ?_, fun _ => inf_le_left, fun _ => inf_le_right,
    fun _ => inf_le_left.trans (rootSpan_le_adjointGroup L _), fun _ y hy hyR u hu => ?_,
    fun y hy hc => ?_⟩
  · rw [hPeq]
    exact hfinP
  · rw [hPeq]
    exact hqP
  · exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy u).1 hu.1,
      mul_mem (mul_mem hyR hu.2) (inv_mem hyR)⟩
  ·
    have e := Subgroup.coe_mul_of_left_le_normalizer_right (torusGroup τ L)
      (rootSpan τ L {r, -r}) (torusGroup_le_normalizer_rootSpan hroots)
    have hy' : y ∈ ((torusGroup τ L ⊔ rootSpan τ L {r, -r} : Subgroup (ModGL τ L)) :
      Set (ModGL τ L)) := hy
    rw [e] at hy'
    have hy2 : y ∈ (torusGroup τ L : Set (ModGL τ L)) *
        (rootRankOneGroup τ L r : Set (ModGL τ L)) := by
      obtain ⟨t, ht, q, hq', rfl⟩ := hy'
      rw [SetLike.mem_coe, hrange] at hq'
      exact ⟨t, ht, q, hq', rfl⟩
    have hcS : ∀ A ∈ S, y * rootSL2 τ L r A = rootSL2 τ L r A * y := fun A hA =>
      hc () (rootSL2 τ L r A) (by rw [hPeq]; exact ⟨A, hA, rfl⟩)
    have hall := commute_rootSL2_of_commute_fixed hr hz hy2 hcS
    refine ⟨mem_torusGroup_of_centralizes_rootSL2 hr hy2 hall, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, hrange] at hg
    obtain ⟨A, rfl⟩ := hg
    exact (hall A).symm

end CFSG.RankThree.PartOne.KE
