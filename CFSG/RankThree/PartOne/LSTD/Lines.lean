module

public import CFSG.RankThree.PartOne.LSTD.Model

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K]

section Lines

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ 5)

@[expose] def lineElt {a b : Fin 5} (hab : a ≠ b) : ↥(unitarySU 2 f K 5) :=
  tSU hU h5 (torusElt a b ζ) (torusElt_mem hab hζ.pow_eq_one)

theorem lineElt_mem_Bk {a b : Fin 5} (hab : a ≠ b) {u : Kˣ} (hu : u ^ 5 = 1) :
    tSU hU h5 (torusElt a b u) (torusElt_mem hab hu) ∈ Bk hU hab := by
  rw [mem_Bk_iff]
  exact diagU_torusElt_mem_blk hab (bar_mul_eq_one hU h5 hu)

@[expose] noncomputable def lineGen {a b : Fin 5} (hab : a ≠ b) :
    StatedProj (unitarySU 2 f K 5) :=
  projU K f (lineElt hU h5 hζ hab)

theorem lineGen_mem_torusBar {a b : Fin 5} (hab : a ≠ b) : lineGen hU h5 hζ hab ∈ torusBar K f :=
  (mem_torusBar_iff hU h5).mpr ⟨_, torusElt_mem hab hζ.pow_eq_one, rfl⟩

theorem lineGen_mem_Jfun {a b : Fin 5} (hab : a ≠ b) : lineGen hU h5 hζ hab ∈ Jfun hU a b := by
  rw [Jfun_of_ne hU hab]
  exact ⟨_, lineElt_mem_Bk hU h5 hab hζ.pow_eq_one, rfl⟩

theorem lineGen_pow_five {a b : Fin 5} (hab : a ≠ b) : lineGen hU h5 hζ hab ^ 5 = 1 := by
  unfold lineGen
  rw [← map_pow]
  have : lineElt hU h5 hζ hab ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, lineElt, coe_tSU, diagU_pow, ← torusElt_pow, hζ.pow_eq_one,
      torusElt_one, diagU_one]
    rfl
  rw [this, map_one]

theorem lineGen_ne_one {a b : Fin 5} (hab : a ≠ b) : lineGen hU h5 hζ hab ≠ 1 := by
  intro h
  have h1 : lineElt hU h5 hζ hab ∈ scalarsU K f := by
    rw [← ker_projU, MonoidHom.mem_ker]
    exact h
  obtain ⟨c, hc⟩ := exists_of_mem_scalarsU h1
  have h2 : torusElt a b ζ = fun _ => c := diagU_injective hc
  have hthird : ∀ a b : Fin 5, ∃ k : Fin 5, k ≠ a ∧ k ≠ b := by decide
  obtain ⟨k, hka, hkb⟩ := hthird a b
  have h3 := congrFun h2 a
  have h4 := congrFun h2 k
  rw [torusElt_apply_left hab] at h3
  rw [torusElt_apply_other hka hkb] at h4
  apply hζ.pow_ne_one_of_pos_of_lt (by norm_num : (1 : ℕ) ≠ 0) (by norm_num : 1 < 5)
  rw [pow_one, h3, ← h4]

theorem orderOf_lineGen {a b : Fin 5} (hab : a ≠ b) : orderOf (lineGen hU h5 hζ hab) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (lineGen_pow_five hU h5 hζ hab) (lineGen_ne_one hU h5 hζ hab)

theorem pow_five_eq_one_of_mem_scalarsU (hU : UnitaryFieldData 2 f K)
    {z : ↥(unitarySU 2 f K 5)} {c : Kˣ} (hc : (z : GL (Fin 5) K) = diagU (fun _ => c)) :
    c ^ 5 = 1 := by
  have hdet := ((mem_unitarySU_iff hU).mp z.2).1
  rw [hc, det_diagU] at hdet
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  exact Units.ext (by simpa using hdet)

theorem torusBar_inf_Jfun_le {a b : Fin 5} (hab : a ≠ b) :
    torusBar K f ⊓ Jfun hU a b ≤ Subgroup.zpowers (lineGen hU h5 hζ hab) := by
  rintro x ⟨hxT, hxJ⟩
  obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hxT
  rw [Jfun_of_ne hU hab] at hxJ
  obtain ⟨k, hk, hkx⟩ := hxJ
  obtain ⟨z, hz, hkz⟩ := projU_eq_iff.mp hkx
  obtain ⟨c, hc⟩ := exists_of_mem_scalarsU hz
  have hkB : (k : GL (Fin 5) K) ∈ blk hU hab := hk
  have hkGL : (k : GL (Fin 5) K) = diagU (v * fun _ => c) := by
    rw [hkz, Subgroup.coe_mul, coe_tSU, hc, diagU_mul]
  rw [hkGL] at hkB
  have h1 := eq_torusElt_of_diagU_mem_blk hab hkB
  have hc5 : c ^ 5 = 1 := pow_five_eq_one_of_mem_scalarsU hU hc
  have hu : ((v * (fun _ : Fin 5 => c)) a) ^ 5 = 1 := by
    simp only [Pi.mul_apply, mul_pow, hv.1 a, hc5, one_mul]
  obtain ⟨m, -, hm⟩ := exists_pow_eq_of_pow_five hζ hu
  refine Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), ?_⟩
  rw [zpow_natCast]
  have hk' : k = lineElt hU h5 hζ hab ^ m := by
    apply Subtype.ext
    rw [hkGL, h1, ← hm, Subgroup.coe_pow, lineElt, coe_tSU, diagU_pow, torusElt_pow]
  rw [lineGen, ← map_pow, ← hk', hkx]

theorem torusBar_inf_Jfun {a b : Fin 5} (hab : a ≠ b) :
    torusBar K f ⊓ Jfun hU a b = Subgroup.zpowers (lineGen hU h5 hζ hab) :=
  le_antisymm (torusBar_inf_Jfun_le hU h5 hζ hab)
    (Subgroup.zpowers_le.mpr ⟨lineGen_mem_torusBar hU h5 hζ hab, lineGen_mem_Jfun hU h5 hζ hab⟩)

include h5 hζ in
theorem card_torusBar_inf_Jfun {a b : Fin 5} (hab : a ≠ b) :
    Nat.card ↥(torusBar K f ⊓ Jfun hU a b) = 5 := by
  rw [torusBar_inf_Jfun hU h5 hζ hab, Nat.card_zpowers, orderOf_lineGen hU h5 hζ hab]

end Lines

end CFSG.RankThree.PartOne.LSTD
