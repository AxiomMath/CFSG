module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCoresTori

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SeitzReduction.LinearPilot (blockTorusParam rootTorusParam blockSpecialLinear)

section General

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

@[expose] def unitaryTorusParam (I : Finset (Fin n)) : Subgroup (Fin n → Kˣ) where
  carrier := {c | (∀ i, h.norm (c i : K) = 1) ∧ ∏ i, c i = 1 ∧ ∀ i ∈ I, ∀ j ∈ I, c i = c j}
  one_mem' := ⟨fun _ => by simp [UnitaryFieldData.norm], by simp, fun _ _ _ _ => rfl⟩
  mul_mem' := fun {c d} hc hd => ⟨fun i => by
      rw [Pi.mul_apply, Units.val_mul, norm_mul_eq h, hc.1 i, hd.1 i, one_mul],
    by simp only [Pi.mul_apply, Finset.prod_mul_distrib, hc.2.1, hd.2.1, mul_one],
    fun i hi j hj => by simp only [Pi.mul_apply, hc.2.2 i hi j hj, hd.2.2 i hi j hj]⟩
  inv_mem' := fun {c} hc => ⟨fun i => by
      rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv_eq h, hc.1 i, inv_one],
    by simp only [Pi.inv_apply, Finset.prod_inv_distrib, hc.2.1, inv_one],
    fun i hi j hj => by simp only [Pi.inv_apply, hc.2.2 i hi j hj]⟩

theorem mem_unitaryTorusParam {I : Finset (Fin n)} {c : Fin n → Kˣ} :
    c ∈ unitaryTorusParam h I ↔
      (∀ i, h.norm (c i : K) = 1) ∧ ∏ i, c i = 1 ∧ ∀ i ∈ I, ∀ j ∈ I, c i = c j :=
  Iff.rfl

theorem unitaryTorusParam_anti {I I' : Finset (Fin n)} (hII' : I ⊆ I') :
    unitaryTorusParam h I' ≤ unitaryTorusParam h I :=
  fun _ hc => ⟨hc.1, hc.2.1, fun i hi j hj => hc.2.2 i (hII' hi) j (hII' hj)⟩

theorem unitaryTorusParam_le_blockTorusParam (I : Finset (Fin n)) :
    unitaryTorusParam h I ≤ blockTorusParam I :=
  fun _ hc => ⟨hc.2.1, hc.2.2⟩

@[expose] noncomputable def torusDiagSU :
    unitaryTorusParam h (∅ : Finset (Fin n)) →* unitarySU p f K n where
  toFun c := diagSU h (fun i => ((c.1 i : Kˣ) : K)) c.2.1
    (by rw [← Units.coe_prod, c.2.2.1, Units.val_one])
  map_one' := Subtype.ext (Units.ext (by
    change diagonal (fun i => (((1 : Fin n → Kˣ) i : Kˣ) : K)) = 1
    simp))
  map_mul' c d := Subtype.ext (Units.ext (by
    change diagonal (fun i => (((c.1 * d.1) i : Kˣ) : K)) =
      diagonal (fun i => ((c.1 i : Kˣ) : K)) * diagonal (fun i => ((d.1 i : Kˣ) : K))
    rw [diagonal_mul_diagonal]
    simp))

theorem coe_torusDiagSU (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    (((torusDiagSU h c : unitarySU p f K n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => ((c.1 i : Kˣ) : K) :=
  rfl

theorem toSL_torusDiagSU (c : unitaryTorusParam h (∅ : Finset (Fin n))) :
    toSL h n (torusDiagSU h c) =
      LinearPilot.torusDiagSL ⟨c.1, unitaryTorusParam_le_blockTorusParam h ∅ c.2⟩ :=
  rfl

@[expose] noncomputable def unitaryBlockTorus (I : Finset (Fin n)) : Subgroup (unitaryPSU h n) :=
  (((unitaryTorusParam h I).subgroupOf (unitaryTorusParam h ∅)).map (torusDiagSU h)).map
    (unitaryProj h n)

theorem mem_unitaryBlockTorus {I : Finset (Fin n)} {x : unitaryPSU h n} :
    x ∈ unitaryBlockTorus h I ↔ ∃ c : unitaryTorusParam h (∅ : Finset (Fin n)),
      c.1 ∈ unitaryTorusParam h I ∧ unitaryProj h n (torusDiagSU h c) = x := by
  simp only [unitaryBlockTorus, mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩

theorem unitaryProj_torusDiagSU_mem_unitaryBlockTorus {I : Finset (Fin n)}
    {c : unitaryTorusParam h (∅ : Finset (Fin n))} (hc : c.1 ∈ unitaryTorusParam h I) :
    unitaryProj h n (torusDiagSU h c) ∈ unitaryBlockTorus h I :=
  (mem_unitaryBlockTorus h).2 ⟨c, hc, rfl⟩

theorem unitaryBlockTorus_anti {I I' : Finset (Fin n)} (hII' : I ⊆ I') :
    unitaryBlockTorus h I' ≤ unitaryBlockTorus h I := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryBlockTorus h).1 hx
  exact unitaryProj_torusDiagSU_mem_unitaryBlockTorus h (unitaryTorusParam_anti h hII' hc)

theorem torusDiagSU_mul_eq_mul_torusDiagSU {I : Finset (Fin n)}
    {c : unitaryTorusParam h (∅ : Finset (Fin n))} (hc : c.1 ∈ unitaryTorusParam h I)
    {A : unitarySU p f K n} (hA : A ∈ unitaryBlock h I) :
    torusDiagSU h c * A = A * torusDiagSU h c :=
  toSL_injective h (by
    rw [map_mul, map_mul, toSL_torusDiagSU]
    exact LinearPilot.torusDiagSL_mul_eq_mul_torusDiagSL
      (unitaryTorusParam_le_blockTorusParam h I hc) ((mem_unitaryBlock_iff_toSL h).1 hA))

theorem blockSU_le_centralizer_unitaryBlockTorus (I : Finset (Fin n)) :
    blockSU h I ≤ centralizer (unitaryBlockTorus h I : Set (unitaryPSU h n)) := by
  rintro _ ⟨A, hA, rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryBlockTorus h).1 hx
  rw [← map_mul, ← map_mul, torusDiagSU_mul_eq_mul_torusDiagSU h hc hA]

theorem rootTorusParam_mem_unitaryTorusParam {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)}
    (ha : a ∉ I) (hb : b ∉ I) {κ : Kˣ} (hκ : h.norm (κ : K) = 1) :
    rootTorusParam a b κ ∈ unitaryTorusParam h I := by
  refine ⟨fun i => ?_, (LinearPilot.rootTorusParam_mem_blockTorusParam hab ha hb κ).1,
    (LinearPilot.rootTorusParam_mem_blockTorusParam hab ha hb κ).2⟩
  simp only [rootTorusParam]
  split_ifs
  · exact hκ
  · rw [Units.val_inv_eq_inv_val, norm_inv_eq h, hκ, inv_one]
  · simp [UnitaryFieldData.norm]

@[expose] noncomputable def unitaryRootTorusHom {a b : Fin n} (hab : a ≠ b) :
    (Units.map h.normHom).ker →* unitaryTorusParam h (∅ : Finset (Fin n)) where
  toFun κ := ⟨rootTorusParam a b κ, rootTorusParam_mem_unitaryTorusParam h hab
    (Finset.notMem_empty a) (Finset.notMem_empty b) (h.mem_ker_normUnits.1 κ.2)⟩
  map_one' := Subtype.ext (funext fun i => by simp [rootTorusParam])
  map_mul' κ μ := Subtype.ext (funext fun i => by
    change rootTorusParam a b ((κ * μ : (Units.map h.normHom).ker) : Kˣ) i =
      rootTorusParam a b κ i * rootTorusParam a b μ i
    simp only [rootTorusParam, Subgroup.coe_mul]
    split_ifs <;> simp [mul_comm])

theorem coe_torusDiagSU_unitaryRootTorusHom {a b : Fin n} (hab : a ≠ b)
    (κ : (Units.map h.normHom).ker) :
    (((torusDiagSU h (unitaryRootTorusHom h hab κ) : unitarySU p f K n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = diagonal fun i => ((rootTorusParam a b (κ : Kˣ) i : Kˣ) : K) :=
  rfl

@[expose] noncomputable def unitaryRootTorus {a b : Fin n} (hab : a ≠ b) :
    Subgroup (unitaryPSU h n) :=
  ((unitaryProj h n).comp ((torusDiagSU h).comp (unitaryRootTorusHom h hab))).range

theorem mem_unitaryRootTorus {a b : Fin n} (hab : a ≠ b) {x : unitaryPSU h n} :
    x ∈ unitaryRootTorus h hab ↔ ∃ κ : (Units.map h.normHom).ker,
      unitaryProj h n (torusDiagSU h (unitaryRootTorusHom h hab κ)) = x :=
  Iff.rfl

theorem torusDiagSU_unitaryRootTorusHom_mem_unitaryBlock {a b : Fin n} (hab : a ≠ b)
    (κ : (Units.map h.normHom).ker) :
    torusDiagSU h (unitaryRootTorusHom h hab κ) ∈ unitaryBlock h {a, b} := by
  rw [mem_unitaryBlock]
  intro i j hij
  rw [coe_torusDiagSU_unitaryRootTorusHom]
  by_cases hij' : i = j
  · subst hij'
    have hi : i ≠ a ∧ i ≠ b := by
      rcases hij with h1 | h1 <;> simpa [Finset.mem_insert, Finset.mem_singleton, not_or] using h1
    simp [rootTorusParam, hi.1, hi.2]
  · rw [diagonal_apply_ne _ hij', one_apply_ne hij']

theorem unitaryRootTorus_le_rootSU2 {a b : Fin n} (hab : a ≠ b) :
    unitaryRootTorus h hab ≤ rootSU2 h a b := by
  rintro _ ⟨κ, rfl⟩
  exact unitaryProj_mem_blockSU h (torusDiagSU_unitaryRootTorusHom_mem_unitaryBlock h hab κ)

theorem unitaryRootTorus_le_unitaryBlockTorus {a b : Fin n} (hab : a ≠ b) {I : Finset (Fin n)}
    (ha : a ∉ I) (hb : b ∉ I) : unitaryRootTorus h hab ≤ unitaryBlockTorus h I := by
  rintro _ ⟨κ, rfl⟩
  exact unitaryProj_torusDiagSU_mem_unitaryBlockTorus h
    (rootTorusParam_mem_unitaryTorusParam h hab ha hb (h.mem_ker_normUnits.1 κ.2))

theorem blockSU_compl_le_centralizer_unitaryRootTorus {a b : Fin n} (hab : a ≠ b) :
    blockSU h ({a, b}ᶜ : Finset (Fin n)) ≤
      centralizer (unitaryRootTorus h hab : Set (unitaryPSU h n)) := by
  intro d hd
  rw [mem_centralizer_iff]
  intro x hx
  exact (commute_blockSU_of_disjoint h disjoint_compl_left d hd x
    (unitaryRootTorus_le_rootSU2 h hab hx)).symm

theorem injective_unitaryRootTorus (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    Function.Injective
      ((unitaryProj h n).comp ((torusDiagSU h).comp (unitaryRootTorusHom h hab))) := by
  rw [injective_iff_map_eq_one]
  intro κ hκ
  have h1 := eq_one_of_mem_unitaryBlock_of_unitaryProj_eq_one h
    (by rw [Finset.card_pair hab]; omega) (torusDiagSU_unitaryRootTorusHom_mem_unitaryBlock h hab κ)
    hκ
  have h2 := congrArg
    (fun g : unitarySU p f K n => ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a) h1
  simp only [coe_torusDiagSU_unitaryRootTorusHom, diagonal_apply_eq,
    LinearPilot.rootTorusParam_apply_left, OneMemClass.coe_one, Units.val_one, one_apply_eq] at h2
  exact Subtype.ext (Units.ext h2)

theorem card_unitaryRootTorus (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    Nat.card (unitaryRootTorus h hab) = p ^ f + 1 := by
  rw [unitaryRootTorus,
    ← Nat.card_congr (MonoidHom.ofInjective (injective_unitaryRootTorus h hn hab)).toEquiv,
    h.card_ker_normUnits_and_surjective.1]

theorem isCyclic_unitaryRootTorus {a b : Fin n} (hab : a ≠ b) :
    IsCyclic (unitaryRootTorus h hab) := by
  have := h.finite
  exact isCyclic_of_surjective
    ((unitaryProj h n).comp ((torusDiagSU h).comp (unitaryRootTorusHom h hab))).rangeRestrict
    (MonoidHom.rangeRestrict_surjective
      ((unitaryProj h n).comp ((torusDiagSU h).comp (unitaryRootTorusHom h hab))))

theorem unitaryRootTorus_ne_bot (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    unitaryRootTorus h hab ≠ ⊥ := by
  intro hbot
  have h1 := card_unitaryRootTorus h hn hab
  rw [hbot, Subgroup.card_bot] at h1
  have := h.one_lt_pow
  omega

end General

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

include h in
theorem odd_two_pow_add_one_of_unitaryFieldData : Odd (2 ^ f + 1) :=
  (Nat.even_pow.2 ⟨even_two, by have := h.one_le; omega⟩).add_one

theorem odd_card_unitaryRootTorus {a b : Fin n} (hab : a ≠ b) :
    Odd (Nat.card (unitaryRootTorus h hab)) := by
  have hd := Subgroup.card_range_dvd
    ((unitaryProj h n).comp ((torusDiagSU h).comp (unitaryRootTorusHom h hab)))
  rw [h.card_ker_normUnits_and_surjective.1] at hd
  exact (odd_two_pow_add_one_of_unitaryFieldData h).of_dvd_nat hd

theorem exists_mem_unitaryTorusParam_ne {I : Finset (Fin n)} (hI : 2 ≤ Iᶜ.card) {i j : Fin n}
    (hij : i ≠ j) (hIJ : i ∉ I ∨ j ∉ I) : ∃ c ∈ unitaryTorusParam h I, c i ≠ c j := by
  obtain ⟨κ, hκN, hκ1⟩ := exists_norm_eq_one_ne_one h
  have hκ := coe_ne_coe_inv_of_ne_one h hκ1
  have hother : ∀ l : Fin n, ∃ k, k ∉ I ∧ k ≠ l := by
    intro l
    obtain ⟨k₁, h₁, k₂, h₂, h12⟩ := Finset.one_lt_card.1 (by omega : 1 < Iᶜ.card)
    by_cases hk : k₁ = l
    · exact ⟨k₂, Finset.mem_compl.1 h₂, fun h' => h12 (hk.trans h'.symm)⟩
    · exact ⟨k₁, Finset.mem_compl.1 h₁, hk⟩
  by_cases hi : i ∈ I
  · have hj : j ∉ I := hIJ.resolve_left (not_not.2 hi)
    obtain ⟨k, hk, hkj⟩ := hother j
    refine ⟨rootTorusParam j k κ,
      rootTorusParam_mem_unitaryTorusParam h (Ne.symm hkj) hj hk hκN, ?_⟩
    have hik : i ≠ k := fun h' => hk (h' ▸ hi)
    rw [LinearPilot.rootTorusParam_apply_of_ne hij hik, LinearPilot.rootTorusParam_apply_left]
    exact Ne.symm hκ1
  · by_cases hj : j ∈ I
    · obtain ⟨k, hk, hki⟩ := hother i
      refine ⟨rootTorusParam i k κ,
        rootTorusParam_mem_unitaryTorusParam h (Ne.symm hki) hi hk hκN, ?_⟩
      have hjk : j ≠ k := fun h' => hk (h' ▸ hj)
      rw [LinearPilot.rootTorusParam_apply_left,
        LinearPilot.rootTorusParam_apply_of_ne (Ne.symm hij) hjk]
      exact hκ1
    · refine ⟨rootTorusParam i j κ, rootTorusParam_mem_unitaryTorusParam h hij hi hj hκN, ?_⟩
      rw [LinearPilot.rootTorusParam_apply_left, LinearPilot.rootTorusParam_apply_right hij]
      exact fun h' => hκ (congrArg Units.val h')

end Even

end CFSG.SeitzReduction.UnitaryPilot
