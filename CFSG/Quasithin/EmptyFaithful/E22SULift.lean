module

public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.RankThree.SubgroupLists.CentralThreeLift
public import CFSG.LieType.Universal.Unitary.Model
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU
  CFSG.RankThree.SubgroupLists CFSG.Assembly.LowTwoRank CFSG.Open

variable {K : Type} [Field K] {p f : ℕ}

abbrev suScalars (p f : ℕ) (K : Type) [Field K] : Subgroup ↥(unitarySU p f K 3) :=
  (StatedScalars (Fin 3) K).subgroupOf (unitarySU p f K 3)

theorem suScalars_pow_three (z : ↥(unitarySU p f K 3)) (hz : z ∈ suScalars p f K) :
    z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hz : (z : GL (Fin 3) K) ∈
    (Matrix.GeneralLinearGroup.scalar (Fin 3)).range)
  have hdet : ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    CFSG.LieType.Universal.Unitary.det_eq_one_of_mem_statedSU z.2
  have hc3 : (c : K) ^ 3 = 1 := by
    rw [← hc] at hdet
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] using
      hdet
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hc, ← map_pow]
  have : c ^ 3 = 1 := Units.ext (by simpa using hc3)
  rw [this, map_one]
  rfl

theorem commute_of_proj_commute_two_U {x y : ↥(unitarySU p f K 3)} (hx : x ^ 2 = 1)
    (h : (x : StatedProj (unitarySU p f K 3)) * (y : StatedProj (unitarySU p f K 3)) =
      (y : StatedProj (unitarySU p f K 3)) * (x : StatedProj (unitarySU p f K 3))) :
    x * y = y * x :=
  commute_of_commute_mk (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3
    (p ^ f)) suScalars_pow_three (n := 2) (by norm_num) hx h

@[expose] def invLiftsU (A : Subgroup (StatedProj (unitarySU p f K 3))) (hA : IsElemAbelian 2 A) :
    Subgroup ↥(unitarySU p f K 3) where
  carrier := {x | (x : StatedProj (unitarySU p f K 3)) ∈ A ∧ x ^ 2 = 1}
  one_mem' := ⟨by rw [QuotientGroup.mk_one]; exact A.one_mem, one_pow 2⟩
  mul_mem' := by
    rintro x y ⟨hxA, hx2⟩ ⟨hyA, hy2⟩
    have hc : x * y = y * x := commute_of_proj_commute_two_U hx2 (by
      have := hA.1.is_comm.comm ⟨(x : StatedProj (unitarySU p f K 3)), hxA⟩
        ⟨(y : StatedProj (unitarySU p f K 3)), hyA⟩
      exact congrArg Subtype.val this)
    refine ⟨by rw [QuotientGroup.mk_mul]; exact A.mul_mem hxA hyA, ?_⟩
    calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
          rw [pow_two, pow_two, pow_two, mul_assoc, ← mul_assoc y x y, ← hc]; group
      _ = 1 := by rw [hx2, hy2, one_mul]
  inv_mem' := by
    rintro x ⟨hxA, hx2⟩
    refine ⟨by rw [QuotientGroup.mk_inv]; exact A.inv_mem hxA, ?_⟩
    rw [inv_pow, hx2, inv_one]

theorem exists_invLiftU {A : Subgroup (StatedProj (unitarySU p f K 3))} (hA : IsElemAbelian 2 A)
    {a : StatedProj (unitarySU p f K 3)} (ha : a ∈ A) :
    ∃ x ∈ invLiftsU A hA, (x : StatedProj (unitarySU p f K 3)) = a := by
  obtain ⟨x, hxa, hx2⟩ := exists_lift_pow_eq_one
    (CFSG.LieType.Universal.Unitary.statedScalars_subgroupOf_le_center 3 (p ^ f))
    suScalars_pow_three (n := 2) (by norm_num) a (hA.2 a ha)
  exact ⟨x, ⟨by rw [hxa]; exact ha, hx2⟩, hxa⟩

theorem card_le_card_invLiftsU [Finite K] {A : Subgroup (StatedProj (unitarySU p f K 3))}
    (hA : IsElemAbelian 2 A) : Nat.card A ≤ Nat.card (invLiftsU A hA) := by
  refine Nat.card_le_card_of_surjective
    (fun x => (⟨(x : StatedProj (unitarySU p f K 3)), x.2.1⟩ : A)) fun a => ?_
  obtain ⟨x, hx, hxa⟩ := exists_invLiftU hA a.2
  exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩

end CFSG.Quasithin.E22S
