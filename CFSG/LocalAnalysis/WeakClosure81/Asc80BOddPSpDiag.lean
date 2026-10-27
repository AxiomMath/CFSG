module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpDiagComm
public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSpDiagAnti
import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent

public section

namespace CFSG.LocalAnalysis.WeakClosure81.PSpOuter

open Subgroup Matrix CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spForm)
open CFSG.RankThree.Classical.SteinbergBY (scalarGsp conjAut_scalarGsp coe_scalarGsp)

private lemma multiplier_scalarGsp {r : ℕ} {F : Type} [Field F] [NeZero r] (b : Fˣ) :
    multiplier r F (scalarGsp b) = b * b := by
  apply multiplier_eq
  rw [coe_scalarGsp, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_transpose, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
    Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_mul]

private lemma exists_scalar_of_conjAut_eq_one {r : ℕ} {F : Type} [Field F] [Finite F]
    (hr : 1 ≤ r) {A : gsp r F} (h : conjAut r F A = 1) :
    ∃ lam : F, ((A : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = lam • 1 := by
  have h' : conjAut r F A * fieldAut r F (1 : F ≃+* F) = 1 := by
    rw [map_one, mul_one, h]
  obtain ⟨-, c, hc⟩ :=
    (CFSG.ComponentClassification.CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff
      (K := F) hr A 1).mp h'
  have hsc : ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = (c : F) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.scalar, hij]
  refine ⟨(c : F), ?_⟩
  have hc' : ((A : GL (Fin r ⊕ Fin r) F) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) :=
    congrArg (fun g : GL (Fin r ⊕ Fin r) F =>
      ((g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) hc
  rw [hc', hsc]

private lemma conjAut_mem_range_of_isSquare {r : ℕ} {F : Type} [Field F] [Finite F]
    [NeZero r] (hr : 1 ≤ r) {A : gsp r F} (hs : IsSquare ((multiplier r F A : Fˣ) : F)) :
    conjAut r F A ∈ (MulAut.conj : StatedProj (StatedSp r F) →*
      MulAut (StatedProj (StatedSp r F))).range := by
  obtain ⟨s, hs⟩ := hs
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hs
    exact (multiplier r F A).ne_zero hs
  set u : Fˣ := Units.mk0 s hs0 with hu
  set A' : gsp r F := scalarGsp u⁻¹ * A with hA'def
  have hmul : multiplier r F A' = 1 := by
    rw [hA'def, map_mul, multiplier_scalarGsp]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val, hu, Units.val_mk0]
    rw [hs]
    field_simp
  have hA'mem : A' ∈ (StatedSp r F).subgroupOf (gsp r F) := by
    rw [← ker_multiplier]
    exact hmul
  have hceq : conjAut r F A' = conjAut r F A := by
    rw [hA'def, map_mul, conjAut_scalarGsp (r := r) (K := F) (by omega : 1 ≤ r), one_mul]
  refine ⟨proj r F ⟨(A' : GL (Fin r ⊕ Fin r) F), hA'mem⟩, ?_⟩
  rw [← conjAut_statedSp]
  exact hceq

private lemma isSquare_mul_of_not_isSquare {F : Type} [Field F] [Finite F] {a b : F}
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) : IsSquare (a * b) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h => ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h => hb (h ▸ IsSquare.zero)
  have h1 : quadraticChar F a = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have h2 : quadraticChar F b = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  have h3 : quadraticChar F (a * b) = 1 := by
    rw [map_mul, h1, h2]
    norm_num
  exact (quadraticChar_one_iff_isSquare (mul_ne_zero ha0 hb0)).mp h3

private theorem mem_four' {G : Type*} [Group G] {E : Subgroup G} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {x y z : G} (hx : x ∈ E) (hy : y ∈ E) (hz : z ∈ E) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) : z = 1 ∨ z = x ∨ z = y ∨ z = x * y := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hz1, hzx, hzy, hzxy⟩ := hcon
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have hxx : x * x = 1 := by rw [← sq]; exact hE.2 x hx
  have hxy1 : x * y ≠ 1 := fun h => hxy (mul_left_cancel (hxx.trans h.symm))
  have hxyx : x * y ≠ x := fun h => hy1 (mul_eq_left.mp h)
  have hxyy : x * y ≠ y := fun h => hx1 (mul_eq_right.mp h)
  set S : Finset G := {1, x, y, x * y, z} with hS
  have hcard : S.card = 5 := by
    rw [hS, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]; exact Ne.symm hzxy
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hxyy, Ne.symm hzy⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, Ne.symm hxyx, Ne.symm hzx⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hx1, Ne.symm hy1, Ne.symm hxy1, Ne.symm hz1⟩
  have hsub : (S : Set G) ⊆ E := by
    intro w hw
    simp only [hS, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hx
    · exact hy
    · exact E.mul_mem hx hy
    · exact hz
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq] at hle
  change 5 ≤ Nat.card E at hle
  omega

private lemma transpose_smul_one_mul_formJ {F : Type} [Field F] {r : ℕ} (c : F) :
    (c • 1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * formJ r F * (c • 1) =
      (c * c) • formJ r F := by
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul]

private lemma smul_formJ_eq {F : Type} [Field F] {r : ℕ} (i : Fin r) {c c' : F}
    (h : c • formJ r F = c' • formJ r F) : c = c' := by
  have h' := congrFun (congrFun h (Sum.inl i)) (Sum.inr i)
  simpa [formJ] using h'

private lemma beta_eq_or_neg {F : Type} [Field F] {r : ℕ} (i : Fin r)
    {B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F}
    {ν β : F} (hB : Bᵀ * formJ r F * B = ν • formJ r F) (hBB : B * B = β • 1)
    (hν : ¬ IsSquare ν) : ν ≠ 0 ∧ β ≠ 0 ∧ (β = ν ∨ β = -ν) := by
  have hν0 : ν ≠ 0 := fun h => hν (by rw [h]; exact IsSquare.zero)
  have hβ2 : β * β = ν * ν := by
    have h1 : (B * B)ᵀ * formJ r F * (B * B) = (β * β) • formJ r F := by
      rw [hBB, transpose_smul_one_mul_formJ]
    have h2 : (B * B)ᵀ * formJ r F * (B * B) = (ν * ν) • formJ r F := by
      rw [mul_transpose_formJ_mul hB B, hB, smul_smul]
    exact smul_formJ_eq i (h1.symm.trans h2)
  have hβν : β = ν ∨ β = -ν := by
    have hfac : (β - ν) * (β + ν) = 0 := by linear_combination hβ2
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  refine ⟨hν0, ?_, hβν⟩
  rcases hβν with h | h
  · rw [h]; exact hν0
  · rw [h]; exact neg_ne_zero.mpr hν0

theorem exists_lifts_of_spLinear_of_not_inner {F : Type} [Field F] [Finite F] {r : ℕ}
    (hr : 1 ≤ r) {E : Subgroup (MulAut (StatedProj (StatedSp r F)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (hlin : E ≤ spLinearAutGroup r F)
    (hout : ¬ E ≤ (MulAut.conj : StatedProj (StatedSp r F) →* MulAut _).range) :
    ∃ (a : StatedSp r F) (B : gsp r F) (ε ν β lam : F),
      MulAut.conj (proj r F a) ∈ E ∧ MulAut.conj (proj r F a) ≠ 1 ∧ conjAut r F B ∈ E ∧
      conjAut r F B ≠ 1 ∧ MulAut.conj (proj r F a) ≠ conjAut r F B ∧
      ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = ε • 1 ∧
      (ε = 1 ∨ ε = -1) ∧
      ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ * formJ r F *
        ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = ν • formJ r F ∧
      ¬ IsSquare ν ∧
      ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = β • 1 ∧
      (β = ν ∨ β = -ν) ∧
      ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
          lam • (((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) ∧
      (lam = 1 ∨ lam = -1) := by
  classical
  have : NeZero r := ⟨by omega⟩
  obtain ⟨b, hbE, hbout⟩ := Set.not_subset.mp hout
  have hbD : b ∈ spLinearAutGroup r F := hlin hbE
  obtain ⟨B, hB⟩ := mem_spLinearAutGroup_iff.mp hbD
  have hb1 : b ≠ 1 := by
    intro h
    rw [h] at hbout
    exact hbout (Subgroup.one_mem _)
  have hBform : ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
      formJ r F * ((B : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      ((multiplier r F B : Fˣ) : F) • formJ r F := multiplier_spec B
  have hν : ¬ IsSquare ((multiplier r F B : Fˣ) : F) := by
    intro hs
    exact hbout (hB ▸ conjAut_mem_range_of_isSquare (r := r) (F := F)
      hr hs)
  have hb2 : b * b = 1 := by
    rw [← sq]
    exact hE.2 b hbE
  have hB2conj : conjAut r F (B * B) = 1 := by
    calc conjAut r F (B * B) = conjAut r F B * conjAut r F B := map_mul _ _ _
      _ = 1 := by rw [hB, hb2]
  obtain ⟨β, hβ⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F) hr hB2conj
  have hBB : ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
      ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = β • 1 := by
    simpa [Subgroup.coe_mul, Units.val_mul] using hβ
  have hBne : ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) ≠ 0 := by
    intro h
    have h1 : ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        (((B : GL (Fin r ⊕ Fin r) F)⁻¹ : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hzord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  have hzcard : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers, hzord]
  have hzle : Subgroup.zpowers b ≤ E := Subgroup.zpowers_le.mpr hbE
  have hzlt : Subgroup.zpowers b < E := by
    rw [lt_iff_le_and_ne]
    refine ⟨hzle, fun hEq => ?_⟩
    have hc := congrArg (fun H : Subgroup (MulAut (StatedProj (StatedSp r F))) => Nat.card H) hEq
    rw [hzcard, h4] at hc
    exact absurd hc (by norm_num)
  obtain ⟨e, heE, hez⟩ := Set.exists_of_ssubset hzlt
  have he1 : e ≠ 1 := fun h => hez (by rw [h]; exact Subgroup.one_mem _)
  have heb : e ≠ b := fun h => hez (by rw [h]; exact Subgroup.mem_zpowers b)
  have heD : e ∈ spLinearAutGroup r F := hlin heE
  obtain ⟨C, hC⟩ := mem_spLinearAutGroup_iff.mp heD
  have hA0exists : ∃ A₀ : gsp r F, ∃ a : MulAut (StatedProj (StatedSp r F)),
      a = conjAut r F A₀ ∧ a ∈ E ∧ a ≠ 1 ∧
      IsSquare ((multiplier r F A₀ : Fˣ) : F) := by
    by_cases hsq : IsSquare ((multiplier r F C : Fˣ) : F)
    · exact ⟨C, e, hC.symm, heE, he1, hsq⟩
    · refine ⟨C * B, e * b, ?_, E.mul_mem heE hbE, ?_, ?_⟩
      · rw [map_mul, hC, hB]
      · intro h
        apply heb
        exact mul_right_cancel (h.trans hb2.symm)
      · rw [map_mul, Units.val_mul]
        exact isSquare_mul_of_not_isSquare hsq hν
  obtain ⟨A₀, a, ha, haE, ha1, hsq⟩ := hA0exists
  obtain ⟨s, hs⟩ := hsq
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hs
    exact (multiplier r F A₀).ne_zero hs
  set A : gsp r F := scalarGsp (Units.mk0 s hs0)⁻¹ * A₀ with hAdef
  have hmulA : multiplier r F A = 1 := by
    rw [hAdef, map_mul, multiplier_scalarGsp]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [hs]
    field_simp
  have hAsp : (A : GL (Fin r ⊕ Fin r) F) ∈ StatedSp r F := by
    have hmem : A ∈ (StatedSp r F).subgroupOf (gsp r F) := by
      rw [← ker_multiplier]
      exact hmulA
    exact Subgroup.mem_subgroupOf.mp hmem
  have hAa : conjAut r F A = a := by
    rw [hAdef, map_mul, conjAut_scalarGsp (r := r) (K := F) hr, one_mul, ← ha]
  have ha_range : a ∈ (MulAut.conj : StatedProj (StatedSp r F) →*
      MulAut (StatedProj (StatedSp r F))).range := by
    rw [ha]
    exact conjAut_mem_range_of_isSquare (r := r) (F := F) hr ⟨s, hs⟩
  have hab : a ≠ b := fun h => hbout (h ▸ ha_range)
  have ha2 : a * a = 1 := by
    rw [← sq]
    exact hE.2 a haE
  have hA2conj : conjAut r F (A * A) = 1 := by
    calc conjAut r F (A * A) = conjAut r F A * conjAut r F A := map_mul _ _ _
      _ = 1 := by rw [hAa, ha2]
  obtain ⟨ε, hε⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F) hr hA2conj
  have hA2 : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
      ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = ε • 1 := by
    simpa [Subgroup.coe_mul, Units.val_mul] using hε
  have hmul2 : multiplier r F (A * A) = 1 := by
    calc multiplier r F (A * A) = multiplier r F A * multiplier r F A := map_mul _ _ _
      _ = 1 := by rw [hmulA]; simp
  have hA2form : ((((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
      ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))ᵀ *
      formJ r F * ((((A : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
      ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) = formJ r F := by
    have hmem : A * A ∈ (StatedSp r F).subgroupOf (gsp r F) := by
      rw [← ker_multiplier]
      exact hmul2
    have h := SymplecticTorusWeyl.mem_statedSp_iff.mp (Subgroup.mem_subgroupOf.mp hmem)
    simpa [Subgroup.coe_mul, Units.val_mul] using h
  have hε2 : ε * ε = 1 := by
    rw [hA2] at hA2form
    have h3 : (ε * ε) • formJ r F = (1 : F) • formJ r F := by
      simpa [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, smul_smul] using hA2form
    have hentry := congrFun (congrFun h3 (Sum.inl 0)) (Sum.inr 0)
    simpa [formJ] using hentry
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, mul_zero] at hε2
    exact zero_ne_one hε2
  have hεpm : ε = 1 ∨ ε = -1 := by
    have h : ε ^ 2 = 1 := by rwa [sq]
    exact sq_eq_one_iff.mp h
  have hcommE : a * b = b * a :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)
  have hcAB : conjAut r F (A * B) = conjAut r F (B * A) := by
    calc conjAut r F (A * B) = conjAut r F A * conjAut r F B := map_mul _ _ _
      _ = a * b := by rw [hAa, hB]
      _ = b * a := hcommE
      _ = conjAut r F B * conjAut r F A := by rw [hB, hAa]
      _ = conjAut r F (B * A) := (map_mul _ _ _).symm
  have hker : conjAut r F (A * B * (B * A)⁻¹) = 1 := by
    calc conjAut r F (A * B * (B * A)⁻¹)
        = conjAut r F (A * B) * conjAut r F ((B * A)⁻¹) := map_mul _ _ _
      _ = conjAut r F (A * B) * (conjAut r F (B * A))⁻¹ := by rw [map_inv]
      _ = conjAut r F (B * A) * (conjAut r F (B * A))⁻¹ := by rw [hcAB]
      _ = 1 := mul_inv_cancel _
  obtain ⟨lam, hlam⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F)
    hr hker
  have hABlam : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
      ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
      lam • (((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := by
    have := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
      M * ((((B * A : gsp r F) : GL (Fin r ⊕ Fin r) F)) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) hlam
    simpa [Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, Subgroup.coe_mul,
      Units.val_mul, mul_inv_cancel, Units.val_one] using this
  have hlam2 : lam * lam = 1 := by
    have h1 : (((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
        ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
        ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        (lam * lam) • (((B : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
          (((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            ((A : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) := by
      calc (((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
            ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
          = ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            (((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((B : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := by rw [Matrix.mul_assoc]
        _ = ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            (lam • (((B : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) := by rw [hABlam]
        _ = lam • (((A : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            (((B : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) := by rw [Matrix.mul_smul]
        _ = lam • ((((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((B : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := by rw [Matrix.mul_assoc]
        _ = lam • ((lam • (((B : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := by rw [hABlam]
        _ = lam • (lam • ((((B : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) := by rw [Matrix.smul_mul]
        _ = (lam * lam) • (((B : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
            (((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))) := by
            rw [smul_smul, Matrix.mul_assoc]
    have h2 : ε • ((B : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        ((lam * lam) * ε) • ((B : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
      calc ε • ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)
          = (ε • 1) * ((B : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
            rw [Matrix.smul_mul, Matrix.one_mul]
        _ = (((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
              ((A : GL (Fin r ⊕ Fin r) F) :
                Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) *
              ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
            rw [hA2]
        _ = _ := h1
        _ = (lam * lam) • (((B : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) * (ε • 1)) := by rw [hA2]
        _ = (lam * lam) • (ε • ((B : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = ((lam * lam) * ε) • ((B : GL (Fin r ⊕ Fin r) F) :
              Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by rw [smul_smul]
    obtain ⟨i, j, hij⟩ : ∃ i j, ((B : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hBne (funext fun i => funext fun j => h i j)
    have hentry := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hentry
    have h4 : ε = (lam * lam) * ε := mul_right_cancel₀ hij hentry
    have h5 : (lam * lam) * ε = 1 * ε := by rw [one_mul]; exact h4.symm
    exact mul_right_cancel₀ hε0 h5
  have hlampm : lam = 1 ∨ lam = -1 := by
    have h : lam ^ 2 = 1 := by rwa [sq]
    exact sq_eq_one_iff.mp h

  have hβν : β = ((multiplier r F B : Fˣ) : F) ∨
      β = -((multiplier r F B : Fˣ) : F) := by
    have hi : Fin r := ⟨0, by omega⟩
    exact (beta_eq_or_neg (r := r) (F := F)
      (B := ((B : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))
      (ν := ((multiplier r F B : Fˣ) : F)) (β := β) hi hBform hBB hν).2.2
  let aSp : StatedSp r F := ⟨(A : GL (Fin r ⊕ Fin r) F), hAsp⟩
  have hconj : MulAut.conj (proj r F aSp) = a := by
    rw [← conjAut_statedSp aSp]
    have hg : (⟨aSp, statedSp_le_gsp aSp.2⟩ : gsp r F) = A := Subtype.ext rfl
    rw [hg]
    exact hAa
  refine ⟨aSp, B, ε, ((multiplier r F B : Fˣ) : F), β, lam, ?_, ?_, ?_, ?_, ?_, ?_, hεpm,
    hBform, hν, hBB, hβν, ?_, hlampm⟩
  · rw [hconj]; exact haE
  · rw [hconj]; exact ha1
  · rw [hB]; exact hbE
  · rw [hB]; exact hb1
  · rw [hconj, hB]; exact hab
  · simpa using hA2
  · simpa using hABlam

theorem lift_mulVec_mem_of_stable {F : Type} [Field F] [Finite F] {r : ℕ} (hr : 1 ≤ r)
    {E : Subgroup (MulAut (StatedProj (StatedSp r F)))} (hE : IsElemAbelian 2 E)
    (h4 : Nat.card E = 4) {a : StatedSp r F} {B : gsp r F}
    (ha : MulAut.conj (proj r F a) ∈ E) (ha1 : MulAut.conj (proj r F a) ≠ 1)
    (hb : conjAut r F B ∈ E) (hb1 : conjAut r F B ≠ 1)
    (hab : MulAut.conj (proj r F a) ≠ conjAut r F B) {W : Submodule F (Fin r ⊕ Fin r → F)}
    (hWa : ∀ w ∈ W,
      ((a : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W)
    (hWB : ∀ w ∈ W,
      ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W) :
    ∀ A : gsp r F, conjAut r F A ∈ E →
      ∀ w ∈ W,
        ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W := by
  classical
  let Aa : gsp r F := ⟨a, statedSp_le_gsp a.2⟩
  have hAaa : conjAut r F Aa = MulAut.conj (proj r F a) := conjAut_statedSp a
  intro A hAE w hw
  have hfour := mem_four' hE h4 (x := MulAut.conj (proj r F a)) (y := conjAut r F B)
    (z := conjAut r F A) ha hb hAE ha1 hb1 hab
  rcases hfour with h1 | ha' | hb' | hab'
  · obtain ⟨mu, hmu⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F) hr h1
    rw [hmu, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact Submodule.smul_mem W mu hw
  · have hc : conjAut r F (A * Aa⁻¹) = 1 := by
      calc conjAut r F (A * Aa⁻¹) = conjAut r F A * conjAut r F (Aa⁻¹) := map_mul _ _ _
        _ = conjAut r F A * (conjAut r F Aa)⁻¹ := by rw [map_inv]
        _ = MulAut.conj (proj r F a) * (MulAut.conj (proj r F a))⁻¹ := by rw [ha', hAaa]
        _ = 1 := mul_inv_cancel _
    obtain ⟨mu, hmu⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F) hr hc
    have hmat : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        mu • ((Aa : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
      have := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
        M * ((Aa : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) hmu
      simpa [Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, Subgroup.coe_mul,
        Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_cancel, Units.val_one] using this
    rw [hmat, Matrix.smul_mulVec]
    exact Submodule.smul_mem W mu (by simpa [Aa] using hWa w hw)
  · have hc : conjAut r F (A * B⁻¹) = 1 := by
      calc conjAut r F (A * B⁻¹) = conjAut r F A * conjAut r F (B⁻¹) := map_mul _ _ _
        _ = conjAut r F A * (conjAut r F B)⁻¹ := by rw [map_inv]
        _ = conjAut r F B * (conjAut r F B)⁻¹ := by rw [hb']
        _ = 1 := mul_inv_cancel _
    obtain ⟨mu, hmu⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F) hr hc
    have hmat : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        mu • ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) := by
      have := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
        M * ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) hmu
      simpa [Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, Subgroup.coe_mul,
        Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_cancel, Units.val_one] using this
    rw [hmat, Matrix.smul_mulVec]
    exact Submodule.smul_mem W mu (hWB w hw)
  · have hABconj : conjAut r F (Aa * B) =
        MulAut.conj (proj r F a) * conjAut r F B := by
      calc conjAut r F (Aa * B) = conjAut r F Aa * conjAut r F B := map_mul _ _ _
        _ = MulAut.conj (proj r F a) * conjAut r F B := by rw [hAaa]
    have hc : conjAut r F (A * (Aa * B)⁻¹) = 1 := by
      calc conjAut r F (A * (Aa * B)⁻¹)
          = conjAut r F A * conjAut r F ((Aa * B)⁻¹) := map_mul _ _ _
        _ = conjAut r F A * (conjAut r F (Aa * B))⁻¹ := by rw [map_inv]
        _ = (MulAut.conj (proj r F a) * conjAut r F B) *
            (MulAut.conj (proj r F a) * conjAut r F B)⁻¹ := by rw [hab', hABconj]
        _ = 1 := mul_inv_cancel _
    obtain ⟨mu, hmu⟩ := exists_scalar_of_conjAut_eq_one (r := r) (F := F) hr hc
    have hmat : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) =
        mu • (((Aa : GL (Fin r ⊕ Fin r) F) :
            Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
          ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) := by
      have := congrArg (fun M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F =>
        M * (((Aa * B : gsp r F) : GL (Fin r ⊕ Fin r) F) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)) hmu
      simpa [Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul, Subgroup.coe_mul,
        Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_cancel, Units.val_one] using this
    rw [hmat, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    exact Submodule.smul_mem W mu (by simpa [Aa] using hWa _ (hWB w hw))

theorem exists_isotropic_of_spLinear_of_not_inner {F : Type} [Field F] [Finite F] {r : ℕ}
    (hr : 3 ≤ r) (hF : ringChar F ≠ 2) {E : Subgroup (MulAut (StatedProj (StatedSp r F)))}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4) (hlin : E ≤ spLinearAutGroup r F)
    (hout : ¬ E ≤ (MulAut.conj : StatedProj (StatedSp r F) →* MulAut _).range) :
    ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      ∀ A : gsp r F, conjAut r F A ∈ E →
        ∀ w ∈ W,
          ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W := by
  classical
  obtain ⟨a, B, ε, ν, β, lam, hconjE, hne1, hBE, hB1, hne, ha2, hε, hBform, hν, hBB,
    hβν, hAB, hlampm⟩ :=
    exists_lifts_of_spLinear_of_not_inner (F := F) (r := r) (E := E)
      (by omega : 1 ≤ r) hE h4 hlin hout
  let A : gsp r F := ⟨a, statedSp_le_gsp a.2⟩
  have hAaut : conjAut r F A = MulAut.conj (proj r F a) := conjAut_statedSp a
  have hAiso : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F)ᵀ *
      formJ r F * ((A : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = formJ r F := by
    have h := SymplecticTorusWeyl.mem_statedSp_iff.mp a.2
    simpa [A] using h
  have hAA : ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *
      ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) = ε • 1 := by
    simpa [A] using ha2
  obtain ⟨W, hW0, hWiso, hWA, hWB⟩ : ∃ W : Submodule F (Fin r ⊕ Fin r → F), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm r F x y = 0) ∧
      (∀ w ∈ W, ((A : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W) ∧
      ∀ w ∈ W, ((B : GL (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) *ᵥ w ∈ W := by
    rcases hlampm with hl1 | hlm1
    · refine exists_isotropic_of_commute (F := F) (r := r)
        (A := ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))
        (B := ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))
        (ε := ε) (ν := ν) (β := β)
        hF hr hAiso hAA hε hBform hν hBB ?_
      rw [hAB, hl1, one_smul]
    · refine exists_isotropic_of_anticommute (F := F) (r := r)
        (A := ((A : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))
        (B := ((B : GL (Fin r ⊕ Fin r) F) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F))
        (ε := ε) (ν := ν) (β := β)
        hF hr hAiso hAA hε hBform hν hBB ?_
      rw [hAB, hlm1, neg_one_smul]
  refine ⟨W, hW0, hWiso, ?_⟩
  exact lift_mulVec_mem_of_stable (F := F) (r := r) (E := E) (a := a) (B := B) (W := W)
    (by omega : 1 ≤ r) hE h4 hconjE hne1 hBE hB1 hne
    (fun w hw => by simpa [A] using hWA w hw) hWB

end CFSG.LocalAnalysis.WeakClosure81.PSpOuter
