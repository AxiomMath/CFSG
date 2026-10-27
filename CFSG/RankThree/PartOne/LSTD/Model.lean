module

public import CFSG.RankThree.PartOne.LSTD.Torus
public import CFSG.RankThree.PartOne.KF.U4Group
public import CFSG.RankThree.PartOne.LSTD.Basic

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K]

@[expose] def tSU (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (v : Fin 5 → Kˣ)
    (hv : v ∈ torusVec 5 5 K) : ↥(unitarySU 2 f K 5) :=
  ⟨diagU v, torusSU_le_unitarySU hU h5 ⟨v, hv, rfl⟩⟩

@[simp] theorem coe_tSU (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) (v : Fin 5 → Kˣ)
    (hv : v ∈ torusVec 5 5 K) : ((tSU hU h5 v hv : ↥(unitarySU 2 f K 5)) : GL (Fin 5) K) =
      diagU v := rfl

theorem mem_torusBar_iff (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    {x : StatedProj (unitarySU 2 f K 5)} :
    x ∈ torusBar K f ↔ ∃ (v : Fin 5 → Kˣ) (hv : v ∈ torusVec 5 5 K),
      x = projU K f (tSU hU h5 v hv) := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨d, hd1, hd2, hd⟩ := mem_torusSU_iff.mp (Subgroup.mem_subgroupOf.mp hs)
    exact ⟨d, ⟨hd1, hd2⟩, by congr 1; exact Subtype.ext hd.symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨tSU hU h5 v hv, Subgroup.mem_subgroupOf.mpr ⟨v, hv, rfl⟩, rfl⟩

@[expose] noncomputable def Bk (hU : UnitaryFieldData 2 f K) {a b : Fin 5} (hab : a ≠ b) :
    Subgroup ↥(unitarySU 2 f K 5) :=
  (blk hU hab).subgroupOf (unitarySU 2 f K 5)

theorem mem_Bk_iff (hU : UnitaryFieldData 2 f K) {a b : Fin 5} (hab : a ≠ b)
    {g : ↥(unitarySU 2 f K 5)} : g ∈ Bk hU hab ↔ (g : GL (Fin 5) K) ∈ blk hU hab :=
  Iff.rfl

@[expose] noncomputable def Jfun (hU : UnitaryFieldData 2 f K) (a b : Fin 5) :
    Subgroup (StatedProj (unitarySU 2 f K 5)) :=
  if h : a = b then ⊥ else (Bk hU h).map (projU K f)

theorem Jfun_of_ne (hU : UnitaryFieldData 2 f K) {a b : Fin 5} (hab : a ≠ b) :
    Jfun hU a b = (Bk hU hab).map (projU K f) := by
  simp [Jfun, hab]

theorem Jfun_symm (hU : UnitaryFieldData 2 f K) (a b : Fin 5) : Jfun hU a b = Jfun hU b a := by
  by_cases hab : a = b
  · subst hab; rfl
  · rw [Jfun_of_ne hU hab, Jfun_of_ne hU (Ne.symm hab)]
    have : Bk hU (Ne.symm hab) = Bk hU hab := by
      unfold Bk
      rw [blk_symm hab]
    rw [this]

theorem Bk_inf_scalars (hU : UnitaryFieldData 2 f K) {a b : Fin 5} (hab : a ≠ b)
    {z : ↥(unitarySU 2 f K 5)} (hz : z ∈ scalarsU K f) (hzB : z ∈ Bk hU hab) : z = 1 := by
  obtain ⟨c, hc⟩ := exists_of_mem_scalarsU hz
  have hB : diagU (fun _ : Fin 5 => c) ∈ blk hU hab := hc ▸ hzB
  have h1 := eq_torusElt_of_diagU_mem_blk hab hB
  have hthird : ∀ a b : Fin 5, ∃ k : Fin 5, k ≠ a ∧ k ≠ b := by decide
  obtain ⟨k, hka, hkb⟩ := hthird a b
  have h2 := congrFun h1 k
  rw [torusElt_apply_other hka hkb] at h2
  have hc1 : c = 1 := h2
  apply Subtype.ext
  rw [hc, hc1]
  exact diagU_one

theorem projU_injOn_Bk (hU : UnitaryFieldData 2 f K) {a b : Fin 5} (hab : a ≠ b) :
    Function.Injective ((projU K f).comp (Bk hU hab).subtype) := by
  intro x y hxy
  have hxy' : projU K f (x : ↥(unitarySU 2 f K 5)) = projU K f (y : ↥(unitarySU 2 f K 5)) := hxy
  obtain ⟨z, hz, hxz⟩ := projU_eq_iff.mp hxy'
  have hzB : z ∈ Bk hU hab := by
    have : z = (y : ↥(unitarySU 2 f K 5))⁻¹ * x := by rw [hxz]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ y.2) x.2
  have := Bk_inf_scalars hU hab hz hzB
  apply Subtype.ext
  rw [hxz, this, mul_one]

end CFSG.RankThree.PartOne.LSTD
