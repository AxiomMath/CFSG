module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrSpJClass

public section

namespace CFSG.StandardType

namespace CoordSp

open Multiplicative CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic
open Matrix CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

private theorem a8js_pow_two_le_natCard {G : Type} [Group G] [Finite G] {p : ℕ} {H : Subgroup G}
    (f : ZMod p × ZMod p → G) (hf : Function.Injective f) (hH : ∀ a, f a ∈ H) :
    p ^ 2 ≤ Nat.card H := by
  have h := Nat.card_le_card_of_injective (fun a => (⟨f a, hH a⟩ : H))
    (fun a b hab => hf (congrArg Subtype.val hab))
  rw [Nat.card_prod, Nat.card_zmod] at h
  rwa [pow_two]

private theorem a8js_elt_sq_eq_one {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (r : RootSubgroupIndex n) (c : F) : elt r c * elt r c = 1 := by
  rw [← elt_add, CharTwo.add_self_eq_zero, elt_zero]

private theorem a8js_ofAdd_injective {α : Type*} [Add α] :
    Function.Injective (Multiplicative.ofAdd : α → Multiplicative α) :=
  fun _ _ h => by simpa using congrArg Multiplicative.toAdd h

private noncomputable def a8js_eltHom' {F : Type} [Field F] {n : ℕ}
    (r : RootSubgroupIndex n) : Multiplicative F →* StatedSp n F where
  toFun d := elt r (Multiplicative.toAdd d)
  map_one' := by rw [toAdd_one, elt_zero]
  map_mul' a b := by rw [toAdd_mul, elt_add]

private theorem a8js_mat_elt_positiveLong {F : Type} [Field F] {n : ℕ} (j : Fin n) (c : F) :
    mat n F (elt (.positiveLong j) c) = 1 + Matrix.single (Sum.inl j) (Sum.inr j) c := by
  rw [mat_elt]
  ext x y
  simp only [Matrix.add_apply, Matrix.smul_apply, E, Matrix.single_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> ring

private theorem a8js_mat_elt_difference {F : Type} [Field F] {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (c : F) :
    mat n F (elt (.difference i j hij) c) =
      1 + c • (Matrix.single (Sum.inl i) (Sum.inl j) 1 -
        Matrix.single (Sum.inr j) (Sum.inr i) 1) := by
  rw [mat_elt]
  rfl

private theorem a8js_mul_single_mul_apply {F : Type} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (P R : Matrix ι ι F) (a b : ι) (c : F) (x y : ι) :
    (P * Matrix.single a b c * R) x y = P x a * c * R b y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single b]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [Matrix.single_apply_same]
    · intro k _ hk
      rw [Matrix.single_apply_of_row_ne hk.symm, mul_zero]
    · simp
  · intro k _ hk
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro l _
    rw [Matrix.single_apply_of_col_ne _ _ hk.symm, mul_zero]
  · simp

private theorem a8js_diagonal_conj_apply {F : Type} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d d' : ι → F) (M : Matrix ι ι F) (x y : ι) :
    (diagonal d * M * diagonal d') x y = d x * M x y * d' y := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem a8js_diagonal_conj_single' {F : Type} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d d' : ι → F) (a b : ι) (c : F) :
    diagonal d * Matrix.single a b c * diagonal d' = Matrix.single a b (c * d a * d' b) := by
  ext x y
  rw [a8js_mul_single_mul_apply]
  simp only [Matrix.diagonal_apply, Matrix.single_apply]
  by_cases hx : x = a
  · rw [hx]
    by_cases hy : b = y
    · rw [← hy]
      rw [if_pos rfl, if_pos rfl, if_pos (show a = a ∧ b = b from ⟨rfl, rfl⟩)]
      ring
    · rw [if_pos rfl, if_neg hy, if_neg (fun hh => hy hh.2)]
      ring
  · by_cases hy : b = y
    · rw [if_neg hx, if_pos hy, if_neg (fun hh : a = x ∧ b = y => hx hh.1.symm)]
      ring
    · rw [if_neg hx, if_neg hy, if_neg (fun hh : a = x ∧ b = y => hx hh.1.symm)]
      ring

private theorem a8js_diagonal_conj_single {F : Type} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d d' : ι → F} (hdd' : ∀ x, d x * d' x = 1) (a b : ι) (c : F) :
    diagonal d * (1 + Matrix.single a b c) * diagonal d' =
      1 + Matrix.single a b (c * d a * d' b) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.diagonal_mul_diagonal,
    show (fun x => d x * d' x) = 1 by funext x; exact hdd' x, Matrix.diagonal_one',
    a8js_diagonal_conj_single']

private theorem a8js_diagonal_conj_diff {F : Type} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {d d' : ι → F} (hdd' : ∀ x, d x * d' x = 1) {a b a' b' : ι}
    (hab : a ≠ b) (ha'b' : a' ≠ b') (hne : (a, b) ≠ (a', b'))
    (h : d a * d' b = d a' * d' b') (c : F) :
    diagonal d * (1 + c • (Matrix.single a b 1 - Matrix.single a' b' 1)) * diagonal d' =
      1 + (c * (d a * d' b)) • (Matrix.single a b 1 - Matrix.single a' b' 1) := by
  ext x y
  rw [a8js_diagonal_conj_apply]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases h1 : a = x ∧ b = y
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬ (a' = a ∧ b' = b) := fun hh => hne (Prod.ext hh.1.symm hh.2.symm)
    simp [h2, hab]
    ring
  · by_cases h2 : a' = x ∧ b' = y
    · obtain ⟨rfl, rfl⟩ := h2
      have h3 : ¬ (a = a' ∧ b = b') := fun hh => hne (Prod.ext hh.1 hh.2)
      simp [h3, ha'b', h]
      ring
    · by_cases h3 : x = y
      · subst h3
        have e1 : ¬ (a = x ∧ b = x) := fun hh => hab ((hh.2.trans hh.1.symm).symm)
        have e2 : ¬ (a' = x ∧ b' = x) := fun hh => ha'b' ((hh.2.trans hh.1.symm).symm)
        simp [e1, e2, hdd' x]
      · have e1 : ¬ (x = y) := h3
        have e2 : ¬ (a = x ∧ b = y) := h1
        have e3 : ¬ (a' = x ∧ b' = y) := h2
        simp [e1, e2, e3]

private theorem a8js_pairedUnits_val_mul_inv {F : Type} [Field F] {n : ℕ} (u : Fin n → Fˣ)
    (x : Fin n ⊕ Fin n) :
    ((TableBSymp.pairedUnits u x : Fˣ) : F) * ((TableBSymp.pairedUnits u⁻¹ x : Fˣ) : F) = 1 := by
  rcases x with k | k
  · simp only [TableBSymp.pairedUnits, Sum.elim_inl, Pi.inv_apply]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · simp only [TableBSymp.pairedUnits, Sum.elim_inr, Pi.inv_apply, inv_inv]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem a8js_spDiag_conj_elt_long {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (u : Fin n → Fˣ) (j : Fin n) (c : F) :
    spDiag u * elt (.positiveLong j) c * (spDiag u)⁻¹ =
      elt (.positiveLong j) (c * ((u j * u j : Fˣ) : F)) := by
  have hinv : (spDiag u)⁻¹ = spDiag u⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← spDiag_mul, mul_inv_cancel, spDiag_one])
  apply mat_injective
  rw [hinv, map_mul, map_mul, mat_spDiag, mat_spDiag, a8js_mat_elt_positiveLong,
    a8js_mat_elt_positiveLong]
  let d : Fin n ⊕ Fin n → F := fun x => ((TableBSymp.pairedUnits u x : Fˣ) : F)
  let d' : Fin n ⊕ Fin n → F := fun x => ((TableBSymp.pairedUnits u⁻¹ x : Fˣ) : F)
  have hdd' : ∀ x, d x * d' x = 1 := fun x => a8js_pairedUnits_val_mul_inv u x
  have hd1 : d (Sum.inl j) = ((u j : Fˣ) : F) := rfl
  have hd2 : d' (Sum.inr j) = ((u j : Fˣ) : F) := by
    simp only [d', TableBSymp.pairedUnits, Sum.elim_inr, Pi.inv_apply, inv_inv]
  have hval : d (Sum.inl j) * d' (Sum.inr j) = ((u j * u j : Fˣ) : F) := by
    rw [hd1, hd2, ← Units.val_mul]
  rw [a8js_diagonal_conj_single hdd' (Sum.inl j) (Sum.inr j) c]
  congr 1
  rw [mul_assoc, hval]

private theorem a8js_spDiag_conj_elt_diff {F : Type} [Field F] [CharP F 2] {n : ℕ}
    (u : Fin n → Fˣ) {i j : Fin n} (hij : i ≠ j) (c : F) :
    spDiag u * elt (.difference i j hij) c * (spDiag u)⁻¹ =
      elt (.difference i j hij) (c * ((u i * (u j)⁻¹ : Fˣ) : F)) := by
  have hinv : (spDiag u)⁻¹ = spDiag u⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← spDiag_mul, mul_inv_cancel, spDiag_one])
  apply mat_injective
  rw [hinv, map_mul, map_mul, mat_spDiag, mat_spDiag, a8js_mat_elt_difference,
    a8js_mat_elt_difference]
  let d : Fin n ⊕ Fin n → F := fun x => ((TableBSymp.pairedUnits u x : Fˣ) : F)
  let d' : Fin n ⊕ Fin n → F := fun x => ((TableBSymp.pairedUnits u⁻¹ x : Fˣ) : F)
  have hdd' : ∀ x, d x * d' x = 1 := fun x => a8js_pairedUnits_val_mul_inv u x
  have hne : (Sum.inl i, Sum.inl j) ≠ (Sum.inr j, Sum.inr i) := by
    intro hh
    exact Sum.inl_ne_inr (Prod.mk.inj hh).1
  have hval1 : d (Sum.inl i) = ((u i : Fˣ) : F) := rfl
  have hval2 : d' (Sum.inl j) = (((u j)⁻¹ : Fˣ) : F) := by
    simp only [d', TableBSymp.pairedUnits, Sum.elim_inl, Pi.inv_apply]
  have hval3 : d (Sum.inr j) = (((u j)⁻¹ : Fˣ) : F) := rfl
  have hval4 : d' (Sum.inr i) = ((u i : Fˣ) : F) := by
    simp only [d', TableBSymp.pairedUnits, Sum.elim_inr, Pi.inv_apply, inv_inv]
  have hfac : d (Sum.inl i) * d' (Sum.inl j) = d (Sum.inr j) * d' (Sum.inr i) := by
    rw [hval1, hval2, hval3, hval4, mul_comm]
  have hval : d (Sum.inl i) * d' (Sum.inl j) = ((u i * (u j)⁻¹ : Fˣ) : F) := by
    rw [hval1, hval2, ← Units.val_mul]
  rw [a8js_diagonal_conj_diff hdd' (fun h => hij (Sum.inl.inj h))
    (fun h => hij (Sum.inr.inj h).symm) hne hfac c, hval]

private theorem a8js_elt_long_mem_suppGroup {F : Type} [Field F] {n : ℕ} {s : Finset (Fin n)}
    {j : Fin n} (hj : j ∈ s) (c : F) :
    elt (F := F) (.positiveLong j) c ∈ suppGroup (planeSet s) := by
  rw [mem_suppGroup, a8js_mat_elt_positiveLong]
  intro a b hab
  rw [Matrix.add_apply, Matrix.single_apply]
  by_cases h : Sum.inl j = a ∧ Sum.inr j = b
  · obtain ⟨rfl, rfl⟩ := h
    exact absurd ⟨inl_mem_planeSet.mpr hj, inr_mem_planeSet.mpr hj⟩ hab
  · rw [if_neg h, add_zero]

private theorem a8js_mem_range_classHom_of_no_ef {F : Type} [Field F] {n p : ℕ} [Fact p.Prime]
    {β : Fin n → ZMod p} {c : ZMod p} (hc : c ≠ 0) {M : StatedSp n F}
    (hS : M ∈ suppGroup (planeSet (spClass β c)))
    (hdet : (eBlock (spClass β c) (mat n F M)).det = 1)
    (hef : ∀ k l, mat n F M (Sum.inl (enum (spClass β c) k))
      (Sum.inr (enum (spClass β c) l)) = 0)
    (hfe : ∀ k l, mat n F M (Sum.inr (enum (spClass β c) k))
      (Sum.inl (enum (spClass β c) l)) = 0) :
    M ∈ (classHom (F := F) (spClass β c)).range := by
  have hk : ∀ k, β (enum (spClass β c) k) = c := spClass_enum β c
  rw [← range_blockSp] at hS
  obtain ⟨M', rfl⟩ := hS
  have hent : ∀ x y, mat (spClass β c).card F M' x y =
      mat n F (blockSp (spClass β c) M') (Sum.map (enum (spClass β c)) (enum (spClass β c)) x)
        (Sum.map (enum (spClass β c)) (enum (spClass β c)) y) :=
    fun x y => (mat_blockSp_apply_image _ M' x y).symm
  have h12 : ∀ k l, mat (spClass β c).card F M' (Sum.inl k) (Sum.inr l) = 0 := fun k l => by
    rw [hent]
    exact hef k l
  have h21 : ∀ k l, mat (spClass β c).card F M' (Sum.inr k) (Sum.inl l) = 0 := fun k l => by
    rw [hent]
    exact hfe k l
  set A : Matrix (Fin (spClass β c).card) (Fin (spClass β c).card) F :=
    Matrix.of fun k l => mat (spClass β c).card F M' (Sum.inl k) (Sum.inl l) with hA
  set D : Matrix (Fin (spClass β c).card) (Fin (spClass β c).card) F :=
    Matrix.of fun k l => mat (spClass β c).card F M' (Sum.inr k) (Sum.inr l) with hD
  have hM' : mat (spClass β c).card F M' = fromBlocks A 0 0 D := by
    ext x y
    rcases x with k | k <;> rcases y with l | l
    · rfl
    · exact h12 k l
    · exact h21 k l
    · rfl
  have hdetA : A.det = 1 := by
    have hAe : A = eBlock (spClass β c) (mat n F (blockSp (spClass β c) M')) := by
      ext k l
      exact hent (Sum.inl k) (Sum.inl l)
    rw [hAe]
    exact hdet
  have hsymp := mat_transpose_mul_gram_mul M'
  rw [hM', CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply] at hsymp
  have hAD : Aᵀ * D = 1 := by
    have h := (fromBlocks_inj.mp hsymp).2.1
    simpa using h
  let A' : Matrix.SpecialLinearGroup (Fin (spClass β c).card) F := ⟨A, hdetA⟩
  refine ⟨A', ?_⟩
  change blockSp (spClass β c) (leviEmbedSL F _ A') = blockSp (spClass β c) M'
  congr 1
  apply mat_injective
  rw [mat_leviEmbedSL, hM']
  have hinv : ((A'⁻¹ : Matrix.SpecialLinearGroup (Fin (spClass β c).card) F) :
      Matrix (Fin (spClass β c).card) (Fin (spClass β c).card) F)ᵀ = D := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
    have hadj : adjugate A = A⁻¹ := by
      rw [Matrix.inv_def, hdetA, Ring.inverse_one, one_smul]
    change (adjugate A)ᵀ = D
    rw [hadj, Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv hAD]
  rw [hinv]

private theorem a8js_elt_diff_mem_classBlock {F : Type} [Field F] {n p : ℕ} [Fact p.Prime]
    {β : Fin n → ZMod p} {c : ZMod p} (hc : c ≠ 0) {i j : Fin n} (hij : i ≠ j)
    (hi : β i = c) (hj : β j = c) (a : F) :
    elt (.difference i j hij) a ∈ (classHom (F := F) (spClass β c)).range := by
  have hS : elt (.difference i j hij) a ∈ suppGroup (planeSet (spClass β c)) := by
    rw [mem_suppGroup]
    intro r t hrt
    rw [a8js_mat_elt_difference]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.single_apply,
      Matrix.single_apply, smul_eq_mul]
    have hX : (if Sum.inl i = r ∧ Sum.inl j = t then (1 : F) else 0) = 0 := by
      by_cases h : Sum.inl i = r ∧ Sum.inl j = t
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd ⟨inl_mem_planeSet.mpr (mem_spClass.mpr hi),
          inl_mem_planeSet.mpr (mem_spClass.mpr hj)⟩ hrt
      · rw [if_neg h]
    have hY : (if Sum.inr j = r ∧ Sum.inr i = t then (1 : F) else 0) = 0 := by
      by_cases h : Sum.inr j = r ∧ Sum.inr i = t
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd ⟨inr_mem_planeSet.mpr (mem_spClass.mpr hj),
          inr_mem_planeSet.mpr (mem_spClass.mpr hi)⟩ hrt
      · rw [if_neg h]
    rw [hX, hY, sub_zero, mul_zero, add_zero]
  have hef : ∀ k l, mat n F (elt (.difference i j hij) a)
      (Sum.inl (enum (spClass β c) k)) (Sum.inr (enum (spClass β c) l)) = 0 := by
    intro k l
    rw [a8js_mat_elt_difference]
    simp [Matrix.single_apply, Matrix.one_apply]
  have hfe : ∀ k l, mat n F (elt (.difference i j hij) a)
      (Sum.inr (enum (spClass β c) k)) (Sum.inl (enum (spClass β c) l)) = 0 := by
    intro k l
    rw [a8js_mat_elt_difference]
    simp [Matrix.single_apply, Matrix.one_apply]
  have hdet : (eBlock (spClass β c) (mat n F (elt (.difference i j hij) a))).det = 1 := by
    obtain ⟨k, hk⟩ := exists_enum_eq (mem_spClass.mpr hi)
    obtain ⟨l, hl⟩ := exists_enum_eq (mem_spClass.mpr hj)
    have hkl : k ≠ l := fun h => hij (by rw [← hk, ← hl, h])
    have he : eBlock (spClass β c) (mat n F (elt (.difference i j hij) a)) =
        Matrix.transvection k l a := by
      rw [a8js_mat_elt_difference]
      ext k' l'
      simp only [eBlock_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
        Matrix.single_apply, Matrix.transvection, Matrix.one_apply, smul_eq_mul, Sum.inl.injEq,
        reduceCtorEq, false_and, ite_false, sub_zero, ← hk, ← hl, (enum_injective _).eq_iff,
        mul_ite, mul_one, mul_zero]
    rw [he, Matrix.det_transvection_of_ne (h := hkl)]
  exact a8js_mem_range_classHom_of_no_ef hc hS hdet hef hfe

theorem spCompShape_exists_twoSubgroup {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ}
    {hζ : ζ ^ p = 1} (hψ : Function.Injective ψ) {β : Fin n → ZMod p}
    {J : Subgroup G} (hJ : SpCompShape ψ A₀ β J) :
    ∃ T : Subgroup G, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T ≤ J ∧
      (frameHom ψ A₀ hζ).range ≤ Subgroup.normalizer (T : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hφinj : Function.Injective (frameConj ψ A₀) := frameConj_injective hψ A₀
  rcases hJ with ⟨hJeq, hZ1⟩ | ⟨c, hc, hJeq, hS2⟩
  ·
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (spClass β 0).card)
    let r : RootSubgroupIndex n := .positiveLong j
    let T₀ : Subgroup (StatedSp n F) := (a8js_eltHom' r).range
    let T : Subgroup G := T₀.map (frameConj ψ A₀)
    have hT0_le : T₀ ≤ suppGroup (planeSet (spClass β 0)) := by
      intro y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      change elt r (Multiplicative.toAdd d) ∈ suppGroup (planeSet (spClass β 0))
      exact a8js_elt_long_mem_suppGroup hj _
    have hT0sq : ∀ y ∈ T₀, y * y = 1 := by
      intro y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      change elt r (Multiplicative.toAdd d) * elt r (Multiplicative.toAdd d) = 1
      exact a8js_elt_sq_eq_one r _
    have hconj_u : ∀ (v : Fin n → Fˣ) (y : StatedSp n F), y ∈ T₀ →
        spDiag v * y * (spDiag v)⁻¹ ∈ T₀ := by
      intro v y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      change spDiag v * elt r (Multiplicative.toAdd d) * (spDiag v)⁻¹ ∈ T₀
      rw [a8js_spDiag_conj_elt_long]
      exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd _, rfl⟩
    have hT2 : IsPGroup 2 T := by
      intro g
      refine ⟨1, ?_⟩
      rw [pow_one]
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
      have hgg : (g : G) * (g : G) = 1 := by
        rw [← hyg, ← map_mul, hT0sq y hy, map_one]
      exact Subtype.ext (by simpa [pow_two] using hgg)
    have hTne : T ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr
        ⟨⟨frameConj ψ A₀ (elt r 1), ?_⟩, ?_⟩
      · exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, rfl⟩)
      · intro h
        have hval : frameConj ψ A₀ (elt r 1) = 1 := by
          have := congrArg Subtype.val h
          simpa using this
        have h1 : elt r (1 : F) = 1 := hφinj (by rw [hval, map_one])
        have h0 : elt r (1 : F) = elt r (0 : F) := by rw [h1, elt_zero]
        exact one_ne_zero (elt_injective r h0)
    have hTJ : T ≤ J := by
      rw [hJeq, range_blockSp]
      exact Subgroup.map_mono hT0_le
    have hnorm : (frameHom ψ A₀ hζ).range ≤ Subgroup.normalizer (T : Set G) := by
      rintro e ⟨t, rfl⟩
      let u : Fin n → Fˣ := fun i => ζ ^ ((Multiplicative.toAdd t) i).val
      have hfr : frameHom ψ A₀ hζ t = frameConj ψ A₀ (spDiag u) := by
        conv_lhs => rw [← ofAdd_toAdd t]
        exact frameHom_eq_frameConj ψ A₀ hζ (Multiplicative.toAdd t)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        rw [hfr, ← map_mul, ← map_inv, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (hconj_u u y hy)
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        rw [hfr] at hyx
        have hx' : x = frameConj ψ A₀ ((spDiag u)⁻¹ * y * spDiag u) := by
          have h1 : x = (frameConj ψ A₀ (spDiag u))⁻¹ *
              frameConj ψ A₀ y * frameConj ψ A₀ (spDiag u) := by
            rw [hyx]; group
          rw [h1, ← map_inv, ← map_mul, ← map_mul]
        rw [hx']
        have hsinv : spDiag (F := F) (fun i => (u i)⁻¹) = (spDiag (F := F) u)⁻¹ :=
          eq_inv_of_mul_eq_one_right (by
            rw [← spDiag_mul (F := F) (u := u) (v := fun i => (u i)⁻¹),
              show u * (fun i => (u i)⁻¹) = 1 by funext i; exact mul_inv_cancel (u i),
              spDiag_one])
        exact Subgroup.mem_map_of_mem _
          (by simpa [hsinv] using hconj_u (fun i => (u i)⁻¹) y hy)
    exact ⟨T, hTne, hT2, hTJ, hnorm⟩
  ·
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (spClass β c).card)
    let r : RootSubgroupIndex n := .difference i j hij
    let T₀ : Subgroup (StatedSp n F) := (a8js_eltHom' r).range
    let T : Subgroup G := T₀.map (frameConj ψ A₀)
    have hT0_le : T₀ ≤ (classHom (F := F) (spClass β c)).range := by
      intro y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      change elt r (Multiplicative.toAdd d) ∈ (classHom (F := F) (spClass β c)).range
      exact a8js_elt_diff_mem_classBlock hc hij (mem_spClass.mp hi) (mem_spClass.mp hj) _
    have hT0sq : ∀ y ∈ T₀, y * y = 1 := by
      intro y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      change elt r (Multiplicative.toAdd d) * elt r (Multiplicative.toAdd d) = 1
      exact a8js_elt_sq_eq_one r _
    have hconj_u : ∀ (v : Fin n → Fˣ) (y : StatedSp n F), y ∈ T₀ →
        spDiag v * y * (spDiag v)⁻¹ ∈ T₀ := by
      intro v y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      change spDiag v * elt r (Multiplicative.toAdd d) * (spDiag v)⁻¹ ∈ T₀
      rw [a8js_spDiag_conj_elt_diff (u := v) hij]
      exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd _, rfl⟩
    have hT2 : IsPGroup 2 T := by
      intro g
      refine ⟨1, ?_⟩
      rw [pow_one]
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp g.2
      have hgg : (g : G) * (g : G) = 1 := by
        rw [← hyg, ← map_mul, hT0sq y hy, map_one]
      exact Subtype.ext (by simpa [pow_two] using hgg)
    have hTne : T ≠ ⊥ := by
      refine Subgroup.ne_bot_iff_exists_ne_one.mpr
        ⟨⟨frameConj ψ A₀ (elt r 1), ?_⟩, ?_⟩
      · exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd 1, rfl⟩)
      · intro h
        have hval : frameConj ψ A₀ (elt r 1) = 1 := by
          have := congrArg Subtype.val h
          simpa using this
        have h1 : elt r (1 : F) = 1 := hφinj (by rw [hval, map_one])
        have h0 : elt r (1 : F) = elt r (0 : F) := by rw [h1, elt_zero]
        exact one_ne_zero (elt_injective r h0)
    have hTJ : T ≤ J := by
      rw [hJeq]
      exact Subgroup.map_mono hT0_le
    have hnorm : (frameHom ψ A₀ hζ).range ≤ Subgroup.normalizer (T : Set G) := by
      rintro e ⟨t, rfl⟩
      let u : Fin n → Fˣ := fun i => ζ ^ ((Multiplicative.toAdd t) i).val
      have hfr : frameHom ψ A₀ hζ t = frameConj ψ A₀ (spDiag u) := by
        conv_lhs => rw [← ofAdd_toAdd t]
        exact frameHom_eq_frameConj ψ A₀ hζ (Multiplicative.toAdd t)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        rw [hfr, ← map_mul, ← map_inv, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (hconj_u u y hy)
      · intro hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        rw [hfr] at hyx
        have hx' : x = frameConj ψ A₀ ((spDiag u)⁻¹ * y * spDiag u) := by
          have h1 : x = (frameConj ψ A₀ (spDiag u))⁻¹ *
              frameConj ψ A₀ y * frameConj ψ A₀ (spDiag u) := by
            rw [hyx]; group
          rw [h1, ← map_inv, ← map_mul, ← map_mul]
        rw [hx']
        have hsinv : spDiag (F := F) (fun i => (u i)⁻¹) = (spDiag (F := F) u)⁻¹ :=
          eq_inv_of_mul_eq_one_right (by
            rw [← spDiag_mul (F := F) (u := u) (v := fun i => (u i)⁻¹),
              show u * (fun i => (u i)⁻¹) = 1 by funext i; exact mul_inv_cancel (u i),
              spDiag_one])
        exact Subgroup.mem_map_of_mem _
          (by simpa [hsinv] using hconj_u (fun i => (u i)⁻¹) y hy)
    exact ⟨T, hTne, hT2, hTJ, hnorm⟩

theorem spCompShape_exists_orderOf {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ}
    (hψ : Function.Injective ψ) (hζo : orderOf ζ = p)
    {β : Fin n → ZMod p} {J : Subgroup G} (hJ : SpCompShape ψ A₀ β J) :
    ∃ w ∈ J, orderOf w = p := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hinj : Function.Injective (frameHom ψ A₀ hζ) := frameHom_injective ψ A₀ hζ hψ hζo
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : ζ ^ 2 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
    have hv : (ζ : F) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    have h1 : (ζ : F) ^ 2 = (1 : F) ^ 2 := by rw [hv, one_pow]
    have hζ1 : ζ = 1 := Units.ext (CharTwo.sq_inj.mp h1)
    rw [hζ1, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  rcases hJ with ⟨hJeq, hZ1⟩ | ⟨c, hc, hJeq, hS2⟩
  · obtain ⟨j, hj⟩ := Finset.card_pos.mp (by omega : 0 < (spClass β 0).card)
    set t : Fin n → ZMod p := Pi.single j 1 with ht
    refine ⟨frameHom ψ A₀ hζ (ofAdd t), ?_, ?_⟩
    · rw [hJeq, frameHom_eq_frameConj]
      exact Subgroup.mem_map_of_mem _ (by
        rw [range_blockSp]
        refine torusElt_mem_suppGroup hζ (fun i hi => ?_)
        have hij : i ≠ j := fun h => hi (h ▸ hj)
        simp [ht, hij])
    · refine orderOf_eq_prime (frameHom_pow_p ψ A₀ hζ (ofAdd t)) ?_
      intro h1
      have ht0 : t = 0 := a8js_ofAdd_injective
        (by rw [ofAdd_zero]; exact hinj (h1.trans (map_one (frameHom ψ A₀ hζ)).symm))
      have htj : t j = 1 := by simp [ht]
      rw [ht0] at htj
      exact one_ne_zero htj.symm
  · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (spClass β c).card)
    set t : Fin n → ZMod p := (Pi.single i (1 : ZMod p) : Fin n → ZMod p) -
      (Pi.single j (1 : ZMod p) : Fin n → ZMod p) with ht
    refine ⟨frameHom ψ A₀ hζ (ofAdd t), ?_, ?_⟩
    · rw [hJeq, frameHom_eq_frameConj]
      exact Subgroup.mem_map_of_mem _
        (torusElt_mem_range_classHom hp2 hζ hc (fun k hk => by
          have hki : k ≠ i := fun h => hk (h ▸ mem_spClass.mp hi)
          have hkj : k ≠ j := fun h => hk (h ▸ mem_spClass.mp hj)
          simp [ht, hki, hkj])
          (by
            rw [ht]
            simp only [Pi.sub_apply]
            have hsub : (∑ x, (Pi.single i (1 : ZMod p) x - Pi.single j (1 : ZMod p) x)) =
                (∑ x, Pi.single i (1 : ZMod p) x) - (∑ x, Pi.single j (1 : ZMod p) x) :=
              Finset.sum_sub_distrib (s := Finset.univ)
                (f := fun x => Pi.single i (1 : ZMod p) x)
                (g := fun x => Pi.single j (1 : ZMod p) x)
            rw [hsub, Fintype.sum_pi_single', Fintype.sum_pi_single', sub_self]))
    · refine orderOf_eq_prime (frameHom_pow_p ψ A₀ hζ (ofAdd t)) ?_
      intro h1
      have ht0 : t = 0 := a8js_ofAdd_injective
        (by rw [ofAdd_zero]; exact hinj (h1.trans (map_one (frameHom ψ A₀ hζ)).symm))
      have hti : t i = 1 := by simp [ht, hij]
      rw [ht0] at hti
      exact one_ne_zero hti.symm

theorem spCompShape_refine {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
    {n p : ℕ} [Fact p.Prime] {ψ : StatedSp n F →* G} {A₀ : StatedSp n F} {ζ : Fˣ}
    {hζ : ζ ^ p = 1} (hψ : Function.Injective ψ) (hζo : orderOf ζ = p)
    {β : Fin n → ZMod p} (hβ : β ≠ 0) {J : Subgroup G} (hJ : SpCompShape ψ A₀ β J)
    (hcent : Nat.card ((frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (J : Set G) :
      Subgroup G) ≤ p) :
    (J = ((blockSp (F := F) (spClass β 0)).range).map (frameConj ψ A₀) ∧
        (spClass β 0).card + 1 = n) ∨
      (∃ c : ZMod p, c ≠ 0 ∧
        J = ((classHom (F := F) (spClass β c)).range).map (frameConj ψ A₀) ∧
          spClass β c = Finset.univ) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hinj : Function.Injective (frameHom ψ A₀ hζ) := frameHom_injective ψ A₀ hζ hψ hζo
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : ζ ^ 2 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
    have hv : (ζ : F) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    have h1 : (ζ : F) ^ 2 = (1 : F) ^ 2 := by rw [hv, one_pow]
    have hζ1 : ζ = 1 := Units.ext (CharTwo.sq_inj.mp h1)
    rw [hζ1, orderOf_one] at hζo
    exact absurd hζo (by norm_num)
  rcases hJ with ⟨hJeq, hZ1⟩ | ⟨c, hc, hJeq, hS2⟩
  ·
    left
    refine ⟨hJeq, ?_⟩
    have hcomm : ∀ t : Fin n → ZMod p, (∀ i, β i = 0 → t i = 0) →
        frameHom ψ A₀ hζ (ofAdd t) ∈ Subgroup.centralizer (J : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hJeq] at hx
      obtain ⟨M, hM, rfl⟩ := hx
      rw [range_blockSp] at hM
      rw [frameHom_eq_frameConj, ← map_mul, ← map_mul, torusElt_comm_zeroBlock hζ ht hM]
    have htwo : ∀ i₁ i₂ : Fin n, i₁ ≠ i₂ → β i₁ ≠ 0 → β i₂ ≠ 0 → False := by
      intro i₁ i₂ h12 h1 h2
      set v : ZMod p × ZMod p → (Fin n → ZMod p) := fun a =>
        Pi.single i₁ a.1 + Pi.single i₂ a.2 with hv
      have hv_inj : Function.Injective v := by
        intro a b hab
        have e1 := congrFun hab i₁
        have e2 := congrFun hab i₂
        simp only [hv, Pi.add_apply, Pi.single_apply, h12, Ne.symm h12, ↓reduceIte, add_zero,
          zero_add] at e1 e2
        exact Prod.ext e1 e2
      have hle := a8js_pow_two_le_natCard
        (H := (frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (J : Set G))
        (fun a => frameHom ψ A₀ hζ (ofAdd (v a)))
        (hinj.comp (a8js_ofAdd_injective.comp hv_inj)) (fun a => Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
          hcomm (v a) fun i hi => by
            have hi1 : i ≠ i₁ := fun h => h1 (h ▸ hi)
            have hi2 : i ≠ i₂ := fun h => h2 (h ▸ hi)
            simp [hv, hi1, hi2]⟩)
      exact absurd (hle.trans hcent)
        (not_le.mpr (by simpa using Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)))
    have hZlt : (spClass β 0).card < n := by
      rcases Function.ne_iff.mp hβ with ⟨i, hi⟩
      by_contra hlt
      rw [not_lt] at hlt
      have hcard : (spClass β 0).card = n :=
        le_antisymm (by simpa [Fintype.card_fin] using Finset.card_le_univ (spClass β 0)) hlt
      have hZuniv : spClass β 0 = Finset.univ :=
        Finset.eq_univ_of_card _ (by simpa using hcard)
      have hZi : i ∈ spClass β 0 := by
        rw [hZuniv]
        exact Finset.mem_univ i
      exact hi (mem_spClass.mp hZi)
    have hnot2 : ¬ 2 ≤ n - (spClass β 0).card := by
      intro h2
      have hZc : ((spClass β 0)ᶜ).card = n - (spClass β 0).card := by
        rw [Finset.card_compl, Fintype.card_fin]
      have hlt : 1 < ((spClass β 0)ᶜ).card := by omega
      obtain ⟨i₁, hi₁, i₂, hi₂, h12⟩ := Finset.one_lt_card.mp hlt
      exact htwo i₁ i₂ h12 (fun h => (Finset.mem_compl.mp hi₁) (mem_spClass.mpr h))
        (fun h => (Finset.mem_compl.mp hi₂) (mem_spClass.mpr h))
    have hZle : (spClass β 0).card ≤ n :=
      by simpa [Fintype.card_fin] using Finset.card_le_univ (spClass β 0)
    omega
  ·
    right
    refine ⟨c, hc, hJeq, ?_⟩
    have hcomm : ∀ t : Fin n → ZMod p, (∀ i j, β i = c → β j = c → t i = t j) →
        frameHom ψ A₀ hζ (ofAdd t) ∈ Subgroup.centralizer (J : Set G) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hJeq] at hx
      obtain ⟨M, hM, rfl⟩ := hx
      obtain ⟨A, rfl⟩ := hM
      rw [frameHom_eq_frameConj, ← map_mul, ← map_mul,
        torusElt_comm_classBlock hp2 hζ hc ht (wtPres_classHom β c A)
          (classHom_mem_suppGroup _ A)]
    by_contra hne
    have hex : ∃ k, k ∉ spClass β c := by
      by_contra h
      push Not at h
      exact hne (Finset.eq_univ_of_forall h)
    obtain ⟨k, hk⟩ := hex
    have hkβ : β k ≠ c := fun h => hk (mem_spClass.mpr h)
    obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < (spClass β c).card)
    set v : ZMod p × ZMod p → (Fin n → ZMod p) := fun a =>
      Pi.single k a.1 + fun i => if β i = c then a.2 else 0 with hv
    have hik : i₀ ≠ k := fun h => hkβ (h ▸ mem_spClass.mp hi₀)
    have hv_inj : Function.Injective v := by
      intro a b hab
      have e1 := congrFun hab k
      have e2 := congrFun hab i₀
      simp only [hv, Pi.add_apply, Pi.single_apply, hkβ, hik, mem_spClass.mp hi₀, ↓reduceIte,
        zero_add, add_zero] at e1 e2
      exact Prod.ext e1 e2
    have hconst : ∀ a, ∀ i j, β i = c → β j = c → v a i = v a j := by
      intro a i j hi hj
      have hik' : i ≠ k := fun h => hkβ (h ▸ hi)
      have hjk' : j ≠ k := fun h => hkβ (h ▸ hj)
      simp [hv, hik', hjk', hi, hj]
    have hle := a8js_pow_two_le_natCard
      (H := (frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (J : Set G))
      (fun a => frameHom ψ A₀ hζ (ofAdd (v a)))
      (hinj.comp (a8js_ofAdd_injective.comp hv_inj)) (fun a => Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
        hcomm (v a) (hconst a)⟩)
    exact absurd (hle.trans hcent)
      (not_le.mpr (by simpa using Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 2)))

end CoordSp

end CFSG.StandardType

end
