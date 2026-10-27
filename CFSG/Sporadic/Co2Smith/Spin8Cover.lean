module

public import CFSG.Sporadic.Co2Smith.DichFinal
public import CFSG.Sporadic.Co2Smith.Spin8Check

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.CosetTable

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

@[expose] def toMatZ (A : Array ℤ) : Matrix (Fin 8) (Fin 8) ℤ := fun i j => A[8 * i.val + j.val]!

theorem mulZ_get (A B : Array ℤ) (i j : Fin 8) :
    (Native.mulZ A B)[8 * i.val + j.val]! =
      ∑ t : Fin 8, A[8 * i.val + t.val]! * B[8 * t.val + j.val]! := by
  have h : 8 * i.val + j.val < 64 := by omega
  have hdiv : (8 * i.val + j.val) / 8 = i.val := by omega
  have hmod : (8 * i.val + j.val) % 8 = j.val := by omega
  rw [Native.mulZ, getElem!_pos (Array.ofFn _) _ (by simpa using h), Array.getElem_ofFn]
  simp only [hdiv, hmod, Fin.sum_univ_eight]
  simp

theorem toMatZ_mulZ (A B : Array ℤ) : toMatZ (Native.mulZ A B) = toMatZ A * toMatZ B := by
  ext i j
  rw [Matrix.mul_apply]
  exact mulZ_get A B i j

theorem toMatZ_idZ : toMatZ Native.idZ = 1 := by
  ext i j
  have h : 8 * i.val + j.val < 64 := by omega
  have hdiv : (8 * i.val + j.val) / 8 = i.val := by omega
  have hmod : (8 * i.val + j.val) % 8 = j.val := by omega
  rw [toMatZ, Native.idZ, getElem!_pos (Array.ofFn _) _ (by simpa using h), Array.getElem_ofFn]
  simp only [hdiv, hmod, Matrix.one_apply, Fin.val_inj]

theorem toMatZ_negIdZ : toMatZ Native.negIdZ = -1 := by
  ext i j
  have h : 8 * i.val + j.val < 64 := by omega
  have hdiv : (8 * i.val + j.val) / 8 = i.val := by omega
  have hmod : (8 * i.val + j.val) % 8 = j.val := by omega
  rw [toMatZ, Native.negIdZ, getElem!_pos (Array.ofFn _) _ (by simpa using h),
    Array.getElem_ofFn]
  simp only [hdiv, hmod, Matrix.neg_apply, Matrix.one_apply, Fin.val_inj]
  split_ifs <;> simp

theorem toMatZ_wordZ (w : List ℕ) :
    toMatZ (Native.wordZ w) = (w.map fun k => toMatZ Native.spinMats[k]!).prod := by
  induction w with
  | nil => exact toMatZ_idZ
  | cons k w ih =>
    rw [Native.wordZ, List.foldr_cons, toMatZ_mulZ, List.map_cons, List.prod_cons]
    rw [← ih]
    rfl

theorem spinCheck_parts :
    ((List.range 8).all fun i => Native.wordZ [2 * i, 2 * i + 1] == Native.idZ) = true ∧
      (Native.sp6CoverR.all fun r => Native.wordZ (r.map Native.sCode) == Native.idZ) = true ∧
      (Native.wordZ [0, 0] == Native.negIdZ) = true := by
  have h := spinCheck_ok
  simp only [Native.spinCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem spin_mul_inv (i : ℕ) (hi : i < 8) :
    toMatZ Native.spinMats[2 * i]! * toMatZ Native.spinMats[2 * i + 1]! = 1 := by
  have h := List.all_eq_true.mp spinCheck_parts.1 i (List.mem_range.mpr hi)
  have e := congrArg toMatZ (beq_iff_eq.mp h)
  rw [toMatZ_wordZ, toMatZ_idZ] at e
  simpa using e

@[expose] noncomputable def spinUnit
    (i : Fin 8) : (Matrix (Fin 8) (Fin 8) ℤ)ˣ where
  val := toMatZ Native.spinMats[2 * i.val]!
  inv := toMatZ Native.spinMats[2 * i.val + 1]!
  val_inv := spin_mul_inv i.val i.isLt
  inv_val := mul_eq_one_comm.mp (spin_mul_inv i.val i.isLt)

theorem lift_spinUnit_mk (w : List (Fin 8 × Bool)) :
    ((FreeGroup.lift spinUnit (FreeGroup.mk w) : (Matrix (Fin 8) (Fin 8) ℤ)ˣ) :
      Matrix (Fin 8) (Fin 8) ℤ) = toMatZ (Native.wordZ (w.map Native.sCode)) := by
  rw [FreeGroup.lift_mk, toMatZ_wordZ]
  induction w with
  | nil => rfl
  | cons l w ih =>
    rw [List.map_cons, List.prod_cons, Units.val_mul, ih, List.map_cons, List.map_cons,
      List.prod_cons]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · show ((spinUnit i)⁻¹ : (Matrix (Fin 8) (Fin 8) ℤ)ˣ).val = _
      rfl
    · rfl

theorem lift_spinUnit_cover :
    ∀ r ∈ sp6CoverSet, FreeGroup.lift spinUnit r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
  apply Units.ext
  rw [lift_spinUnit_mk, Units.val_one]
  have h := List.all_eq_true.mp spinCheck_parts.2.1 w hw
  rw [beq_iff_eq.mp h, toMatZ_idZ]

@[expose] noncomputable def spinHom :
    PGcov →* (Matrix (Fin 8) (Fin 8) ℤ)ˣ :=
  PresentedGroup.toGroup lift_spinUnit_cover

@[expose] def coverX0sq : PGcov := PresentedGroup.mk _ (FreeGroup.mk [(0, true), (0, true)])

theorem covMap_coverX0sq :
    covMap coverX0sq = 1 := by
  rw [coverX0sq, covMap_mk]
  exact lift_sp6Gen_rel (by decide)

theorem spinHom_coverX0sq :
    (spinHom coverX0sq : Matrix (Fin 8) (Fin 8) ℤ) = -1 := by
  show ((FreeGroup.lift spinUnit (FreeGroup.mk [(0, true), (0, true)]) :
    (Matrix (Fin 8) (Fin 8) ℤ)ˣ) : Matrix (Fin 8) (Fin 8) ℤ) = -1
  rw [lift_spinUnit_mk,
    show List.map Native.sCode [((0 : Fin 8), true), (0, true)] = [0, 0] from rfl,
    beq_iff_eq.mp spinCheck_parts.2.2, toMatZ_negIdZ]

theorem coverX0sq_ne_one : coverX0sq ≠ 1 := by
  intro h
  have e := spinHom_coverX0sq
  rw [h, map_one, Units.val_one] at e
  have e2 := congrFun (congrFun e 0) 0
  simp at e2

theorem exists_covMap_ne_one :
    ∃ c : PGcov, covMap c = 1 ∧ c ≠ 1 :=
  ⟨coverX0sq, covMap_coverX0sq, coverX0sq_ne_one⟩

theorem covMap_coverZ' :
    covMap coverZ = 1 ∧ coverZ ≠ 1 := by
  have hcz : coverZ = exists_covMap_ne_one.choose := by
    rw [coverZ, dite_eq_left exists_covMap_ne_one]
  rw [hcz]
  exact exists_covMap_ne_one.choose_spec

theorem coverZ_ne_one :
    coverZ ≠ 1 := covMap_coverZ'.2

theorem card_ker_covMap_le :
    Nat.card covMap.ker ≤ 2 := by
  have h := Subgroup.card_mul_index covMap.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr covMap_surjective, Subgroup.card_top,
    card_S0] at h
  have := card_PGcov_le
  have hpos : 0 < Nat.card covMap.ker := Nat.card_pos
  nlinarith

theorem card_ker_covMap :
    Nat.card covMap.ker = 2 := by
  have hnt : Nontrivial covMap.ker :=
    ⟨⟨⟨1, map_one _⟩, ⟨coverZ, covMap_coverZ'.1⟩,
      fun h => coverZ_ne_one (congrArg Subtype.val h).symm⟩⟩
  have h1 := Finite.one_lt_card_iff_nontrivial.mpr hnt
  have := card_ker_covMap_le
  omega

theorem covMap_eq_one_iff
    (c : PGcov) : covMap c = 1 ↔ c = 1 ∨ c = coverZ := by
  constructor
  · intro hc
    by_cases h1 : c = 1
    · exact Or.inl h1
    · right
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : covMap.ker)).mp card_ker_covMap
      have e1 := hy ⟨c, hc⟩ fun h => h1 (congrArg Subtype.val h)
      have e2 := hy ⟨coverZ, covMap_coverZ'.1⟩ fun h => coverZ_ne_one (congrArg Subtype.val h)
      exact congrArg Subtype.val (e1.trans e2.symm)
  · rintro (rfl | rfl)
    · exact map_one _
    · exact covMap_coverZ'.1

theorem covMap_spinHom_injective :
    Function.Injective fun c : PGcov =>
      ((covMap c, spinHom c) : S0 × (Matrix (Fin 8) (Fin 8) ℤ)ˣ) := by
  intro c c' h
  simp only [Prod.mk.injEq] at h
  have h1 : covMap (c'⁻¹ * c) = 1 := by rw [map_mul, map_inv, h.1, inv_mul_cancel]
  have h2 : spinHom (c'⁻¹ * c) = 1 := by rw [map_mul, map_inv, h.2, inv_mul_cancel]
  rcases (covMap_eq_one_iff _).mp h1 with e | e
  · rw [inv_mul_eq_one] at e
    exact e.symm
  · exfalso
    have hz : spinHom coverZ = spinHom coverX0sq := by
      have hx := (covMap_eq_one_iff coverX0sq).mp covMap_coverX0sq
      rcases hx with hx | hx
      · exact absurd hx coverX0sq_ne_one
      · rw [hx]
    rw [e, hz] at h2
    have e2 := spinHom_coverX0sq
    rw [h2, Units.val_one] at e2
    have e3 := congrFun (congrFun e2 0) 0
    simp at e3

end CFSG.Sporadic.Co2Smith
