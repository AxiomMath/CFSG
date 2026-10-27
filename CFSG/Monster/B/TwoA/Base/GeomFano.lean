
module

public import CFSG.Monster.B.TwoA.Base.GeomFanoBase

public import CFSG.Monster.B.TwoA.Base.GeomRes

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.B.Short CFSG.Monster.B Module

open scoped IsMulCommutative

attribute [local instance] parAction

section Interval

variable {G : Type*} [Group G] [Finite G] {E L : Subgroup G} [CFSG.IsElementaryAbelian 2 E]

end Interval

theorem natCard_Echain' :
    ∀ i : ℕ, i ≤ 5 → Nat.card (Echain i) = 2 ^ i := by
  intro i h5
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · rw [Echain_zero, Subgroup.card_bot]
    rfl
  · exact natCard_Echain i h1 h5

theorem mem_res_std_coType
    {j : ℕ} (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (x : ParGeom) :
    x ∈ parRes (stdSub (coType j)) ↔ (parType x = j ∨ parType x = j + 1) ∧
      Echain (j - 1) ≤ x.1.2 ∧ x.1.2 ≤ Echain (j + 2) := by
  change (parType x ∉ parType '' stdSub (coType j) ∧ ∀ y ∈ stdSub (coType j), parInc x y) ↔ _
  rw [parType_stdSub _ (coType_subset j)]
  have hb := parType_bounds x
  constructor
  · rintro ⟨hxt, hinc⟩
    have hjx : parType x = j ∨ parType x = j + 1 := by
      by_contra h
      exact hxt (mem_coType.2 ⟨hb, by omega, by omega⟩)
    refine ⟨hjx, ?_, ?_⟩
    · rcases Nat.lt_or_ge j 2 with hj | hj
      · obtain rfl : j = 1 := by omega
        exact bot_le
      · have h := hinc (stdObj (j - 1) (by omega) (by omega))
          (stdObj_mem_stdSub _ _ (mem_coType.2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩))
        exact le_of_parInc (parInc_symm h) (by change j - 1 ≤ parType x; omega)
    · have h := hinc (stdObj (j + 2) (by omega) (by omega))
        (stdObj_mem_stdSub _ _ (mem_coType.2 ⟨⟨by omega, by omega⟩, by omega, by omega⟩))
      exact le_of_parInc h (by change parType x ≤ j + 2; omega)
  · rintro ⟨hjx, hlo, hhi⟩
    refine ⟨fun h => ?_, fun y hy => ?_⟩
    · rw [mem_coType] at h
      omega
    · obtain ⟨hy1, hyt⟩ := hy
      have hyE : y.1.2 = Echain (parType y) := hy1
      rw [mem_coType] at hyt
      refine (parInc_iff_of_ne (by omega)).2 ?_
      rw [hyE]
      rcases Nat.lt_or_ge (parType y) j with h | h
      · exact .inr ((Echain_mono' (by omega) (by omega)).trans hlo)
      · exact .inl (hhi.trans (Echain_mono' (by omega) hyt.1.2))

@[expose] def stdFanoEquiv
    (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3)
    [CFSG.IsElementaryAbelian 2 (Echain (j + 2))] (d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2) :
    {x : ParGeom // x ∈ parRes (stdSub (coType j)) ∧ parType x = j - 1 + d} ≃
      SubspaceDim (ZMod 2) (Fin 3 → ZMod 2) d where
  toFun x := ⟨intervalSub (Echain_mono' (by omega) (by omega) : Echain (j - 1) ≤ Echain (j + 2))
      (natCard_Echain' (j + 2) (by omega)) (natCard_Echain' (j - 1) (by omega))
      (by omega : j + 2 - (j - 1) = 3) x.1.1.2, by
    have hx := (mem_res_std_coType hj1 hj3 x.1).1 x.2.1
    exact finrank_intervalSub _ _ _ _ hx.2.1 hx.2.2 (by rw [natCard_obj, x.2.2])⟩
  invFun P := ⟨⟨(j - 1 + d, intervalGrp (Echain_mono' (by omega) (by omega) :
      Echain (j - 1) ≤ Echain (j + 2)) (natCard_Echain' (j + 2) (by omega))
      (natCard_Echain' (j - 1) (by omega)) (by omega : j + 2 - (j - 1) = 3) P.1),
    isObj_of_le (i := j + 2) (stdObj (j + 2) (by omega) (by omega)).2 (intervalGrp_le _ _ _ _ _)
      (natCard_intervalGrp _ _ _ _ P.2) (by omega) (by omega)⟩,
    (mem_res_std_coType hj1 hj3 _).2 ⟨by change j - 1 + d = j ∨ j - 1 + d = j + 1; omega,
      le_intervalGrp _ _ _ _ _, intervalGrp_le _ _ _ _ _⟩, rfl⟩
  left_inv x := by
    have hx := (mem_res_std_coType hj1 hj3 x.1).1 x.2.1
    refine Subtype.ext (obj_ext x.2.2.symm ?_)
    exact intervalGrp_intervalSub _ _ _ _ hx.2.1 hx.2.2
  right_inv P := Subtype.ext (intervalSub_intervalGrp _ _ _ _ _)

theorem stdFanoEquiv_le_iff
    (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3)
    [CFSG.IsElementaryAbelian 2 (Echain (j + 2))]
    (a : {x : ParGeom // x ∈ parRes (stdSub (coType j)) ∧ parType x = j - 1 + 1})
    (b : {x : ParGeom // x ∈ parRes (stdSub (coType j)) ∧ parType x = j - 1 + 2}) :
    a.1.1.2 ≤ b.1.1.2 ↔ (stdFanoEquiv j hj1 hj3 1 le_rfl (by norm_num) a).1 ≤
      (stdFanoEquiv j hj1 hj3 2 (by norm_num) le_rfl b).1 := by
  have ha := (mem_res_std_coType hj1 hj3 a.1).1 a.2.1
  have hb := (mem_res_std_coType hj1 hj3 b.1).1 b.2.1
  exact (intervalSub_le_iff _ _ _ _ ha.2.1 ha.2.2 hb.2.1).symm

theorem exists_fano_res
    {F : Set ParGeom} (hF : IsParFlag F) {j : ℕ} (hj1 : 1 ≤ j)
    (hj3 : j ≤ 3) (ht : parType '' F = coType j) :
    ∃ (φ : {x : ParGeom // x ∈ parRes F ∧ parType x = j} ≃
        SubspaceDim (ZMod 2) (Fin 3 → ZMod 2) 1)
      (ψ : {x : ParGeom // x ∈ parRes F ∧ parType x = j + 1} ≃
        SubspaceDim (ZMod 2) (Fin 3 → ZMod 2) 2),
      ∀ a b, a.1.1.2 ≤ b.1.1.2 ↔ (φ a).1 ≤ (ψ b).1 := by
  obtain ⟨hinst, -⟩ := echain_data (j + 2) (by omega) (by omega)
  obtain ⟨g, hg⟩ := flag_eq_smul_std hF
  rw [ht] at hg
  subst hg
  have e1 : ∀ x : ParGeom, parType x = j ↔ parType x = j - 1 + 1 := fun x => by
    constructor <;> intro h <;> omega
  have e2 : ∀ x : ParGeom, parType x = j + 1 ↔ parType x = j - 1 + 2 := fun x => by
    constructor <;> intro h <;> omega
  refine ⟨(Equiv.subtypeEquivRight fun x => and_congr_right fun _ => e1 x).trans
      ((resTransport g _ _).symm.trans (stdFanoEquiv j hj1 hj3 1 le_rfl (by norm_num))),
    (Equiv.subtypeEquivRight fun x => and_congr_right fun _ => e2 x).trans
      ((resTransport g _ _).symm.trans (stdFanoEquiv j hj1 hj3 2 (by norm_num) le_rfl)),
    fun a b => ?_⟩
  simp only [Equiv.trans_apply]
  rw [← stdFanoEquiv_le_iff]
  change a.1.1.2 ≤ b.1.1.2 ↔ conjSub ((g⁻¹ : Shat) : Dfull) a.1.1.2 ≤
    conjSub ((g⁻¹ : Shat) : Dfull) b.1.1.2
  rw [conjSub_le_conjSub_iff]

theorem mem_lowerRes_iff
    (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5) (x : ParGeom) :
    (x ∈ parRes {stdObj i h1 h5} ∧ parType x < i) ↔ parType x < i ∧ x.1.2 ≤ Echain i := by
  constructor
  · rintro ⟨⟨-, hinc⟩, hlt⟩
    exact ⟨hlt, le_of_parInc (hinc _ rfl) hlt.le⟩
  · rintro ⟨hlt, hle⟩
    refine ⟨⟨fun h => ?_, fun y hy => ?_⟩, hlt⟩
    · obtain ⟨y, rfl, hy⟩ := h
      exact absurd hy (Nat.ne_of_lt hlt).symm
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (parInc_iff_of_ne (Nat.ne_of_lt hlt)).2 (.inl hle)

@[expose] def lowerResEquiv
    (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5)
    [CFSG.IsElementaryAbelian 2 (Echain i)] :
    {x : ParGeom // x ∈ parRes {stdObj i h1 h5} ∧ parType x < i} ≃
      {S : Submodule (ZMod 2) (Additive (Echain i)) // 0 < finrank (ZMod 2) S ∧
        finrank (ZMod 2) S < i} where
  toFun x := ⟨subOf (Echain i) x.1.1.2, by
    have hx := (mem_lowerRes_iff i h1 h5 x.1).1 x.2
    rw [finrank_subOf (Echain i) hx.2 (natCard_obj x.1)]
    exact ⟨(parType_bounds x.1).1, hx.1⟩⟩
  invFun S := ⟨⟨(finrank (ZMod 2) S.1, ofSub (Echain i) S.1),
    isObj_of_le (i := i) (stdObj i h1 h5).2 (ofSub_le _)
      ((finrank_subOf_iff (ofSub_le _)).1 (by rw [subOf_ofSub])) S.2.1 S.2.2.le⟩,
    (mem_lowerRes_iff i h1 h5 _).2 ⟨S.2.2, ofSub_le _⟩⟩
  left_inv x := by
    have hx := (mem_lowerRes_iff i h1 h5 x.1).1 x.2
    refine Subtype.ext (obj_ext ?_ (ofSub_subOf hx.2))
    exact finrank_subOf (Echain i) hx.2 (natCard_obj x.1)
  right_inv S := Subtype.ext (subOf_ofSub S.1)

theorem lowerResEquiv_le_iff
    (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5)
    [CFSG.IsElementaryAbelian 2 (Echain i)]
    (x y : {x : ParGeom // x ∈ parRes {stdObj i h1 h5} ∧ parType x < i}) :
    x.1.1.2 ≤ y.1.1.2 ↔ (lowerResEquiv i h1 h5 x).1 ≤ (lowerResEquiv i h1 h5 y).1 :=
  (subOf_le_subOf_iff ((mem_lowerRes_iff i h1 h5 x.1).1 x.2).2).symm

theorem finrank_lowerResEquiv
    (i : ℕ) (h1 : 1 ≤ i) (h5 : i ≤ 5)
    [CFSG.IsElementaryAbelian 2 (Echain i)]
    (x : {x : ParGeom // x ∈ parRes {stdObj i h1 h5} ∧ parType x < i}) :
    finrank (ZMod 2) (lowerResEquiv i h1 h5 x).1 = parType x.1 :=
  finrank_subOf (Echain i) ((mem_lowerRes_iff i h1 h5 x.1).1 x.2).2 (natCard_obj x.1)

end CFSG.Monster.B.TwoA
