module

public import CFSG.Quasithin.Background.SmithB45MatRep
public import Certificates.Certificate260404
public import CFSG.Quasithin.H13.A5M12CentBase

public section

namespace CFSG.Quasithin.B45Mat.M12

open CFSG.CharacterTheory.SteinbergBY CFSG.Sporadic.Mathieu CFSG.Blueprint
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12 CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
  CFSG.Quasithin FieldFour Matrix
open CFSG.Monster.Code (bvec bvec_apply)
open scoped Kronecker

abbrev G12 : Type := ↥NativeSporadic.M12

theorem m12_module_checks :
    subOKM 100 44 (K100 arrA) (K100 arrB) B44 P44 = true ∧
    P44.all (· < 2 ^ 44) = true ∧
    subOKM 440 144 (K440 arrA) (K440 arrB) B144 P144 = true ∧
    subOKM 440 230 (K440 arrA) (K440 arrB) B230 P230 = true ∧
    quotOKM 230 32 (t230 arrA) (t230 arrB) Bsel Psel = true ∧
    subOK (tab32F arrA) (tab32F arrB) B16 P16 = true ∧
    c10.check (tab10 arrA) (tab10 arrB) = true ∧
    c44.check (tab44 arrA) (tab44 arrB) = true ∧
    c144.check (tab144 arrA) (tab144 arrB) = true ∧
    c16a.check (tab16a arrA) (tab16a arrB) = true ∧
    c16b.check (tab16b arrA) (tab16b arrB) = true ∧
    Matrix.trace (untab (mulT (tab16a arrA) (tab16a arrB))) = ω ∧
    Matrix.trace (untab (mulT (tab16b arrA) (tab16b arrB))) = ω₂ :=
  Certificates.certificate260404

section Iso

theorem card_range_res12 : Nat.card res12.range = 95040 ∧ res12.range = NativeSporadic.M12 := by
  have hM12 : Nat.card NativeSporadic.M12 = 95040 := card_M12
  have hle := m12_le_range_res12
  have h1 : Nat.card NativeSporadic.M12 ≤ Nat.card res12.range := Subgroup.card_le_of_le hle
  have h2 : Nat.card res12.range ≤ Nat.card ↥(m24Fix dodecadE) :=
    Nat.card_le_card_of_surjective _ res12.rangeRestrict_surjective
  have h3 := card_m24Fix_le
  exact ⟨by omega, (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm⟩

theorem bijective_res12 : Function.Bijective res12.rangeRestrict := by
  have h2 : Nat.card res12.range ≤ Nat.card ↥(m24Fix dodecadE) :=
    Nat.card_le_card_of_surjective _ res12.rangeRestrict_surjective
  have h3 := card_m24Fix_le
  exact res12.rangeRestrict_surjective.bijective_of_nat_card_le
    (by rw [card_range_res12.1]; omega)

@[expose] noncomputable def e12 : ↥(m24Fix dodecadE) ≃* G12 :=
  (MulEquiv.ofBijective _ bijective_res12).trans (MulEquiv.subgroupCongr card_range_res12.2)

theorem coe_e12 (σ : ↥(m24Fix dodecadE)) : ((e12 σ : G12) : Equiv.Perm (Fin 12)) = res12 σ :=
  rfl

theorem e12_symm_m12a : e12.symm m12a = ⟨m12A, m12A_mem_m24Fix⟩ := by
  apply e12.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (coe_e12 _ ▸ res12_m12A).symm

theorem e12_symm_m12b : e12.symm m12b = ⟨m12B, m12B_mem_m24Fix⟩ := by
  apply e12.injective
  rw [MulEquiv.apply_symm_apply]
  exact Subtype.ext (coe_e12 _ ▸ res12_m12B).symm

end Iso

theorem bvec_two_pow (n : ℕ) (j : Fin n) : bvec n (2 ^ (j : ℕ)) = Pi.single j 1 := by
  funext i
  rw [bvec_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h'.symm)
    simp [h, this]

theorem hasArr_m12A : HasArr m12A arrA := by
  unfold HasArr
  decide

theorem hasArr_m12B : HasArr m12B arrB := by
  unfold HasArr
  decide

theorem closure_m12ab : Subgroup.closure ({m12a, m12b} : Set G12) = ⊤ :=
  closure_pair_eq_top m12_eq _ _

theorem cols10_lt (a : Array ℕ) : ∀ c ∈ cols10 a, c < 2 ^ 10 := by
  intro c hc
  simp only [cols10, List.mem_map] at hc
  obtain ⟨j, -, rfl⟩ := hc
  exact actC12_lt _ _

theorem length_kronM (m n : ℕ) (A C : List ℕ) : (kronM m n A C).length = m * n := by
  simp [kronM]

theorem length_mulM (A B : List ℕ) : (mulM A B).length = B.length := by
  simp [mulM]

theorem rep10_of_arr {σ : ↥(m24Fix dodecadE)} {a : Array ℕ}
    (ha : HasArr (σ : Equiv.Perm (Fin 24)) a) :
    mulAutMat 10 (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair σ) = maskMat 10 10 (cols10 a) := by
  ext i j
  rw [mulAutMat_apply]
  have h1 : Multiplicative.ofAdd (Pi.single j 1 : Fin 10 → ZMod 2) = toW 10 (2 ^ (j : ℕ)) := by
    rw [toW, bvec_two_pow]
  rw [h1, rhoC12_toW _ _ _ ha, toAdd_toW, maskMat_apply, bvec_apply,
    List.getD_eq_getElem _ _ (by simp [cols10])]
  simp only [cols10, List.getElem_map, List.getElem_range]

section Base

noncomputable def rep10 : G12 →* Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  (mulAutMat 10).comp ((rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).comp e12.symm.toMonoidHom)

theorem rep10_apply (g : G12) :
    rep10 g = mulAutMat 10 (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair (e12.symm g)) := by
  rw [rep10, MonoidHom.comp_apply, MonoidHom.comp_apply]
  rfl

theorem rep10_m12a : rep10 m12a = maskMat 10 10 (cols10 arrA) := by
  rw [rep10_apply, e12_symm_m12a]
  exact rep10_of_arr hasArr_m12A

theorem rep10_m12b : rep10 m12b = maskMat 10 10 (cols10 arrB) := by
  rw [rep10_apply, e12_symm_m12b]
  exact rep10_of_arr hasArr_m12B

noncomputable abbrev rep100 : G12 →* Matrix (Fin (10 * 10)) (Fin (10 * 10)) (ZMod 2) :=
  kronRep rep10 rep10

theorem rep100_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep100 s = maskMat (10 * 10) (10 * 10) (K100 a) := by
  rw [kronRep_apply, hs, K100, maskMat_kronM _ _ (cols10_lt a)]

end Base

theorem t44_lt (a : Array ℕ) : ∀ c ∈ t44 a, c < 2 ^ 44 := by
  have hP : ∀ c ∈ P44, c < 2 ^ 44 := by
    intro c hc
    have := List.all_eq_true.1 m12_module_checks.2.1 c hc
    simpa using this
  intro c hc
  simp only [t44, mulM, List.mem_map] at hc
  obtain ⟨x, -, rfl⟩ := hc
  exact actM_lt hP x

section Reps

theorem inv44 : maskMat 44 100 P44 * maskMat 100 44 B44 = 1 ∧
    ∀ g, rep100 g * maskMat 100 44 B44 =
      maskMat 100 44 B44 * (maskMat 44 100 P44 * rep100 g * maskMat 100 44 B44) := by
  obtain ⟨hPB, hgen⟩ := subOKM_spec m12_module_checks.1
  refine ⟨hPB, subInv_of_closure closure_m12ab _ _ _ hPB fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · rw [rep100_gen rep10_m12a]
    exact hgen _ (by simp)
  · rw [rep100_gen rep10_m12b]
    exact hgen _ (by simp)

noncomputable def rep44 : G12 →* Matrix (Fin 44) (Fin 44) (ZMod 2) :=
  subRep rep100 (maskMat 100 44 B44) (maskMat 44 100 P44) inv44.1 inv44.2

theorem rep44_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep44 s = maskMat 44 44 (t44 a) := by
  rw [rep44, subRep_apply, rep100_gen hs, t44,
    maskMat_mulM (m := 44) (k := 100) (n := 44) P44 _ (by decide),
    maskMat_mulM (m := 100) (k := 100) (n := 44) (K100 a) B44 (by simp [K100, length_kronM]),
    Matrix.mul_assoc]

noncomputable abbrev rep440 : G12 →* Matrix (Fin (10 * 44)) (Fin (10 * 44)) (ZMod 2) :=
  kronRep rep10 rep44

theorem rep440_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep440 s = maskMat (10 * 44) (10 * 44) (K440 a) := by
  rw [kronRep_apply, rep44_gen hs, hs, K440, maskMat_kronM _ _ (t44_lt a)]

theorem inv144 : maskMat 144 440 P144 * maskMat 440 144 B144 = 1 ∧
    ∀ g, rep440 g * maskMat 440 144 B144 =
      maskMat 440 144 B144 * (maskMat 144 440 P144 * rep440 g * maskMat 440 144 B144) := by
  obtain ⟨hPB, hgen⟩ := subOKM_spec m12_module_checks.2.2.1
  refine ⟨hPB, subInv_of_closure closure_m12ab _ _ _ hPB fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · rw [rep440_gen rep10_m12a]
    exact hgen _ (by simp)
  · rw [rep440_gen rep10_m12b]
    exact hgen _ (by simp)

noncomputable def rep144 : G12 →* Matrix (Fin 144) (Fin 144) (ZMod 2) :=
  subRep rep440 (maskMat 440 144 B144) (maskMat 144 440 P144) inv144.1 inv144.2

theorem rep144_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep144 s = maskMat 144 144 (t144 a) := by
  rw [rep144, subRep_apply, rep440_gen hs, t144,
    maskMat_mulM (m := 144) (k := 440) (n := 144) P144 _ (by decide +kernel),
    maskMat_mulM (m := 440) (k := 440) (n := 144) (K440 a) B144 (by simp [K440, length_kronM]),
    Matrix.mul_assoc]

theorem inv230 : maskMat 230 440 P230 * maskMat 440 230 B230 = 1 ∧
    ∀ g, rep440 g * maskMat 440 230 B230 =
      maskMat 440 230 B230 * (maskMat 230 440 P230 * rep440 g * maskMat 440 230 B230) := by
  obtain ⟨hPB, hgen⟩ := subOKM_spec m12_module_checks.2.2.2.1
  refine ⟨hPB, subInv_of_closure closure_m12ab _ _ _ hPB fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · rw [rep440_gen rep10_m12a]
    exact hgen _ (by simp)
  · rw [rep440_gen rep10_m12b]
    exact hgen _ (by simp)

noncomputable def rep230 : G12 →* Matrix (Fin 230) (Fin 230) (ZMod 2) :=
  subRep rep440 (maskMat 440 230 B230) (maskMat 230 440 P230) inv230.1 inv230.2

theorem rep230_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep230 s = maskMat 230 230 (t230 a) := by
  rw [rep230, subRep_apply, rep440_gen hs, t230,
    maskMat_mulM (m := 230) (k := 440) (n := 230) P230 _ (by decide +kernel),
    maskMat_mulM (m := 440) (k := 440) (n := 230) (K440 a) B230 (by simp [K440, length_kronM]),
    Matrix.mul_assoc]

theorem inv32 : maskMat 32 230 Psel * maskMat 230 32 Bsel = 1 ∧
    ∀ g, maskMat 32 230 Psel * rep230 g =
      maskMat 32 230 Psel * rep230 g * maskMat 230 32 Bsel * maskMat 32 230 Psel := by
  obtain ⟨hPB, hgen⟩ := quotOKM_spec m12_module_checks.2.2.2.2.1
  refine ⟨hPB, quotInv_of_closure closure_m12ab _ _ _ hPB fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · rw [rep230_gen rep10_m12a]
    exact hgen _ (by simp)
  · rw [rep230_gen rep10_m12b]
    exact hgen _ (by simp)

noncomputable def rep32 : G12 →* Matrix (Fin 32) (Fin 32) (ZMod 2) :=
  quotRep rep230 (maskMat 230 32 Bsel) (maskMat 32 230 Psel) inv32.1 inv32.2

theorem rep32_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep32 s = maskMat 32 32 (t32 a) := by
  rw [rep32, quotRep_apply, rep230_gen hs, t32,
    maskMat_mulM (m := 32) (k := 230) (n := 32) Psel _ (by simp [Psel]),
    maskMat_mulM (m := 230) (k := 230) (n := 32) (t230 a) Bsel
      (by simp [t230, length_mulM, B230, colsOfLimbs]),
    Matrix.mul_assoc]

noncomputable abbrev rep32F : G12 →* Matrix (Fin 32) (Fin 32) FieldFour :=
  (ofPrime.mapMatrix : Matrix (Fin 32) (Fin 32) (ZMod 2) →+* _).toMonoidHom.comp rep32

theorem rep32F_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep32F s = untab (tab32F a) := by
  rw [tab32F, untab_mapTab, untab_tab, MonoidHom.comp_apply, ← rep32_gen hs]
  rfl

theorem inv16 : untab P16 * untab B16 = 1 ∧
    ∀ g, rep32F g * untab B16 = untab B16 * (untab P16 * rep32F g * untab B16) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec m12_module_checks.2.2.2.2.2.1
  refine ⟨hPB, subInv_of_closure closure_m12ab _ _ _ hPB fun s hs => ?_⟩
  rcases hs with rfl | rfl
  · rw [rep32F_gen rep10_m12a]
    exact hgen _ (by simp)
  · rw [rep32F_gen rep10_m12b]
    exact hgen _ (by simp)

noncomputable def rep16a : G12 →* Matrix (Fin 16) (Fin 16) FieldFour :=
  subRep rep32F (untab B16) (untab P16) inv16.1 inv16.2

noncomputable def rep16b : G12 →* Matrix (Fin 16) (Fin 16) FieldFour :=
  (frob.mapMatrix : Matrix (Fin 16) (Fin 16) FieldFour →+* _).toMonoidHom.comp rep16a

theorem rep16b_eq : rep16b =
    (frob.mapMatrix : Matrix (Fin 16) (Fin 16) FieldFour →+* _).toMonoidHom.comp rep16a := by
  rw [rep16b]

theorem rep16a_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep16a s = untab (tab16a a) := by
  rw [rep16a, subRep_apply, rep32F_gen hs, tab16a, untab_mulT, untab_mulT]

theorem rep16b_gen {s : G12} {a : Array ℕ} (hs : rep10 s = maskMat 10 10 (cols10 a)) :
    rep16b s = untab (tab16b a) := by
  rw [tab16b, untab_mapTab, ← rep16a_gen hs]
  rfl

variable {K : Type*} [Field K]

theorem isIrreducible_rep10 (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep10).IsIrreducible :=
  c10.isIrreducible_of_check φ rep10 (a := m12a) (b := m12b)
    (by rw [tab10, untab_tab, rep10_m12a]) (by rw [tab10, untab_tab, rep10_m12b])
    m12_module_checks.2.2.2.2.2.2.1

theorem isIrreducible_rep44 (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep44).IsIrreducible :=
  c44.isIrreducible_of_check φ rep44 (a := m12a) (b := m12b)
    (by rw [tab44, untab_tab, rep44_gen rep10_m12a])
    (by rw [tab44, untab_tab, rep44_gen rep10_m12b]) m12_module_checks.2.2.2.2.2.2.2.1

theorem isIrreducible_rep144 (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep144).IsIrreducible :=
  c144.isIrreducible_of_check φ rep144 (a := m12a) (b := m12b)
    (by rw [tab144, untab_tab, rep144_gen rep10_m12a])
    (by rw [tab144, untab_tab, rep144_gen rep10_m12b]) m12_module_checks.2.2.2.2.2.2.2.2.1

theorem isIrreducible_rep16a (φ : FieldFour →+* K) : (matrixBaseChange φ rep16a).IsIrreducible :=
  c16a.isIrreducible_of_check φ rep16a (a := m12a) (b := m12b)
    (rep16a_gen rep10_m12a).symm (rep16a_gen rep10_m12b).symm
    m12_module_checks.2.2.2.2.2.2.2.2.2.1

theorem isIrreducible_rep16b (φ : FieldFour →+* K) : (matrixBaseChange φ rep16b).IsIrreducible :=
  c16b.isIrreducible_of_check φ rep16b (a := m12a) (b := m12b)
    (rep16b_gen rep10_m12a).symm (rep16b_gen rep10_m12b).symm
    m12_module_checks.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep16a : Matrix.trace (rep16a (m12a * m12b)) = ω := by
  rw [map_mul, rep16a_gen rep10_m12a, rep16a_gen rep10_m12b, ← untab_mulT]
  exact m12_module_checks.2.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep16b : Matrix.trace (rep16b (m12a * m12b)) = ω₂ := by
  rw [map_mul, rep16b_gen rep10_m12a, rep16b_gen rep10_m12b, ← untab_mulT]
  exact m12_module_checks.2.2.2.2.2.2.2.2.2.2.2.2

end Reps

end CFSG.Quasithin.B45Mat.M12
