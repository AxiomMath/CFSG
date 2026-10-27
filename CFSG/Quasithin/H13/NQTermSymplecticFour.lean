module

public import CFSG.Quasithin.H13.NQTermAmbientQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualSp
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.Quasithin.H13.LocDblMatrix

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped Matrix

theorem pow_apply_eq_zero_of_lt_height {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (N : Matrix n n R) (h : n → ℕ) (hN : ∀ x y, N x y ≠ 0 → h x < h y) :
    ∀ m x y, ¬ h x + m ≤ h y → (N ^ m) x y = 0 := by
  intro m
  induction m with
  | zero =>
    intro x y hxy
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    exact hxy (by omega)
  | succ m ih =>
    intro x y hxy
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : h x + m ≤ h z
    · have hzy : N z y = 0 := by
        by_contra hne
        have := hN z y hne
        omega
      rw [hzy, mul_zero]
    · rw [ih x z hz, zero_mul]

theorem pow_four_eq_one_of_height {n R : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    [CommRing R] [CharP R 2] (G : Matrix n n R) (h : n → ℕ) (hh : ∀ x, h x < 4)
    (hN : ∀ x y, (G - 1) x y ≠ 0 → h x < h y) : G ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : (G - 1) ^ 4 = 0 := by
    ext x y
    rw [Matrix.zero_apply]
    exact pow_apply_eq_zero_of_lt_height (G - 1) h hN 4 x y (by have := hh y; omega)
  have h1 := add_pow_char_pow_of_commute 2 2 (Commute.one_right (G - 1))
  rw [sub_add_cancel, show (2 : ℕ) ^ 2 = 4 by norm_num, h4, one_pow, zero_add] at h1
  exact h1

theorem isQuasisimple_quotient_pCore_two {X : Type*} [Group X] [Finite X]
    (hq : CFSG.IsQuasisimple X) : CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq
      (CFSG.pCore_normal (p := 2) (G := X)) with h | h
  · exfalso
    have hP2 : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
    rw [h] at hP2
    have : Group.IsNilpotent X := (hP2.of_equiv Subgroup.topEquiv).isNilpotent
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq inferInstance
  · exact (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hq h).1

theorem isQuasisimple_pCore_quotient_of_GL_two {k : Type} [Field k] [Finite k] [CharP k 2]
    {X : Type} [Group X] [Finite X] (hX : (⊤ : Subgroup X) ∈ cComp (⊤ : Subgroup X))
    (ρ : X →* GL (Fin 2) k) (hρ : ∀ x, ρ x = 1 → x ^ 4 = 1) :
    CFSG.IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set σ : X →* LinearMap.GeneralLinearGroup k (Fin 2 → k) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ with hσ
  have hker : IsPGroup 2 σ.ker := by
    intro x
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ 2 = 4 by norm_num]
    apply hρ
    have h1 : σ x = 1 := x.2
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_one]
    exact h1
  have hsolv : Group.IsSolvable σ.ker := by
    have : Group.IsNilpotent σ.ker := hker.isNilpotent
    infer_instance
  have : Finite (LinearMap.GeneralLinearGroup k (Fin 2 → k)) :=
    CFSG.Quasithin.H13.LocDbl.finite_GL
  have hJ := map_mem_cComp_of_isSolvable_ker σ hsolv hX
  rw [← MonoidHom.range_eq_map] at hJ
  have hJq := (CFSG.Quasithin.H13.LocDbl.cComp_quasisimple_and_subsingleton_of_finrank_two
    (p := 2) (Module.finrank_fin_fun k) σ.range).1 _ hJ
  rw [isQuasisimple_pCore_quotient_iff σ.rangeRestrict σ.rangeRestrict_surjective
    (by rwa [MonoidHom.ker_rangeRestrict])]
  exact isQuasisimple_quotient_pCore_two hJq

section Entries

variable {k : Type} [Field k]

@[expose] def spMat : StatedSp 2 k →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k :=
  (Units.coeHom _).comp (StatedSp 2 k).subtype

theorem spMat_apply (g : StatedSp 2 k) :
    spMat g = ((g : GL (Fin 2 ⊕ Fin 2) k) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) k) := rfl

theorem spMat_injective : Function.Injective (spMat (k := k)) := fun _ _ hgh =>
  Subtype.ext (Units.ext hgh)

theorem spMat_mulVec_single (g : StatedSp 2 k) (j : Fin 2 ⊕ Fin 2) :
    spMat g *ᵥ Pi.single j 1 = fun x => spMat g x j := by
  rw [Matrix.mulVec_single_one]
  rfl

theorem spMat_mulVec_mem {W : Submodule k (Fin 2 ⊕ Fin 2 → k)} {g : StatedSp 2 k}
    (hg : g ∈ stabilizer 2 k W) {v : Fin 2 ⊕ Fin 2 → k} (hv : v ∈ W) : spMat g *ᵥ v ∈ W := by
  rw [← mem_stabilizer.mp hg]
  exact ⟨v, hv, rfl⟩

theorem single_inl_zero_mem_flag_one :
    (Pi.single (Sum.inl 0) (1 : k) : Fin 2 ⊕ Fin 2 → k) ∈ flag 2 k 1 := by
  rw [mem_flag_of_le (by norm_num), mem_isoFlag]
  refine ⟨fun j => by simp, fun j hj => ?_⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hj
  simp [hj0]

theorem single_inl_mem_flag_two (j : Fin 2) :
    (Pi.single (Sum.inl j) (1 : k) : Fin 2 ⊕ Fin 2 → k) ∈ flag 2 k 2 := by
  rw [mem_flag_of_le le_rfl, mem_isoFlag]
  refine ⟨fun i => by simp, fun i hi => ?_⟩
  exact absurd i.isLt (by omega)

theorem spMat_eq_zero_of_mem_stabilizer_one {g : StatedSp 2 k}
    (hg : g ∈ stabilizer 2 k (flag 2 k 1)) {x : Fin 2 ⊕ Fin 2} (hx : x ≠ Sum.inl 0) :
    spMat g x (Sum.inl 0) = 0 := by
  have h := spMat_mulVec_mem hg single_inl_zero_mem_flag_one
  rw [spMat_mulVec_single, mem_flag_of_le (by norm_num), mem_isoFlag] at h
  rcases x with i | i
  · have hi : i = 1 := by
      fin_cases i
      · exact absurd rfl hx
      · rfl
    subst hi
    exact h.2 1 (by decide)
  · exact h.1 i

theorem spMat_line_row {g : StatedSp 2 k} (hg : g ∈ stabilizer 2 k (flag 2 k 1))
    (y : Fin 2 ⊕ Fin 2) :
    spMat g (Sum.inl 0) (Sum.inl 0) * spMat g (Sum.inr 0) y =
      (Pi.single y (1 : k) : Fin 2 ⊕ Fin 2 → k) (Sum.inr 0) := by
  have hcol : spMat g *ᵥ Pi.single (Sum.inl 0) 1 =
      spMat g (Sum.inl 0) (Sum.inl 0) • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → k) := by
    rw [spMat_mulVec_single]
    funext x
    by_cases hx : x = Sum.inl 0
    · subst hx
      simp
    · rw [spMat_eq_zero_of_mem_stabilizer_one hg hx]
      simp [hx]
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_mulVec g
    (Pi.single (Sum.inl 0) 1) (Pi.single y 1)
  rw [← spMat_apply, hcol, spMat_mulVec_single, map_smul, LinearMap.smul_apply, smul_eq_mul,
    pairedSympForm_single_inl, pairedSympForm_single_inl] at h
  exact h

theorem spMat_line_corner_ne_zero {g : StatedSp 2 k} (hg : g ∈ stabilizer 2 k (flag 2 k 1)) :
    spMat g (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
  intro h0
  have h := spMat_line_row hg (Sum.inr 0)
  rw [h0, zero_mul] at h
  simp at h

theorem spMat_line_row_eq_zero {g : StatedSp 2 k} (hg : g ∈ stabilizer 2 k (flag 2 k 1))
    {y : Fin 2 ⊕ Fin 2} (hy : y ≠ Sum.inr 0) : spMat g (Sum.inr 0) y = 0 := by
  have h := spMat_line_row hg y
  have h0 : (Pi.single y (1 : k) : Fin 2 ⊕ Fin 2 → k) (Sum.inr 0) = 0 := by
    simp [Ne.symm hy]
  rw [h0] at h
  exact (mul_eq_zero.mp h).resolve_left (spMat_line_corner_ne_zero hg)

theorem spMat_eq_zero_of_mem_stabilizer_two {g : StatedSp 2 k}
    (hg : g ∈ stabilizer 2 k (flag 2 k 2)) (a b : Fin 2) :
    spMat g (Sum.inr a) (Sum.inl b) = 0 := by
  have h := spMat_mulVec_mem hg (single_inl_mem_flag_two b)
  rw [spMat_mulVec_single, mem_flag_of_le le_rfl, mem_isoFlag] at h
  exact h.1 a

theorem spMat_lag_row {g : StatedSp 2 k} (hg : g ∈ stabilizer 2 k (flag 2 k 2))
    (h1 : ∀ a b : Fin 2, spMat g (Sum.inl a) (Sum.inl b) = (1 : Matrix (Fin 2) (Fin 2) k) a b)
    (a b : Fin 2) :
    spMat g (Sum.inr a) (Sum.inr b) = (1 : Matrix (Fin 2) (Fin 2) k) a b := by
  have hcol : spMat g *ᵥ Pi.single (Sum.inl a) 1 =
      (Pi.single (Sum.inl a) 1 : Fin 2 ⊕ Fin 2 → k) := by
    rw [spMat_mulVec_single]
    funext x
    rcases x with i | i
    · rw [h1 i a]
      simp [Matrix.one_apply, Pi.single_apply]
    · rw [spMat_eq_zero_of_mem_stabilizer_two hg]
      simp
  have h := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_mulVec g
    (Pi.single (Sum.inl a) 1) (Pi.single (Sum.inr b) 1)
  rw [← spMat_apply, hcol, spMat_mulVec_single, pairedSympForm_single_inl,
    pairedSympForm_single_inl] at h
  refine h.trans ?_
  simp [Matrix.one_apply, Pi.single_apply]

end Entries

section Reps

variable {k : Type} [Field k]

@[expose] def lineIdx : Fin 2 → Fin 2 ⊕ Fin 2 := ![Sum.inl 1, Sum.inr 1]

theorem lineIdx_ne_inl_zero (a : Fin 2) : lineIdx a ≠ Sum.inl 0 := by
  fin_cases a <;> simp [lineIdx]

theorem lineIdx_ne_inr_zero (a : Fin 2) : lineIdx a ≠ Sum.inr 0 := by
  fin_cases a <;> simp [lineIdx]

@[expose] def lineRep : stabilizer 2 k (flag 2 k 1) →* Matrix (Fin 2) (Fin 2) k where
  toFun g := Matrix.of fun a b => spMat (g : StatedSp 2 k) (lineIdx a) (lineIdx b)
  map_one' := by
    ext a b
    simp only [OneMemClass.coe_one, map_one, Matrix.of_apply]
    fin_cases a <;> fin_cases b <;> simp [lineIdx, Matrix.one_apply]
  map_mul' g h := by
    ext a b
    simp only [Matrix.of_apply, Subgroup.coe_mul, map_mul, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two]
    rw [spMat_eq_zero_of_mem_stabilizer_one g.2 (lineIdx_ne_inl_zero a),
      spMat_line_row_eq_zero h.2 (lineIdx_ne_inr_zero b)]
    simp [lineIdx]

@[expose] def lineChar : stabilizer 2 k (flag 2 k 1) →* k where
  toFun g := spMat (g : StatedSp 2 k) (Sum.inl 0) (Sum.inl 0)
  map_one' := by simp
  map_mul' g h := by
    simp only [Subgroup.coe_mul, map_mul, Matrix.mul_apply, Fintype.sum_sum_type,
      Fin.sum_univ_two]
    rw [spMat_eq_zero_of_mem_stabilizer_one h.2 (x := Sum.inl 1) (by simp),
      spMat_eq_zero_of_mem_stabilizer_one h.2 (x := Sum.inr 0) (by simp),
      spMat_eq_zero_of_mem_stabilizer_one h.2 (x := Sum.inr 1) (by simp)]
    ring

@[expose] def lagRep : stabilizer 2 k (flag 2 k 2) →* Matrix (Fin 2) (Fin 2) k where
  toFun g := Matrix.of fun a b => spMat (g : StatedSp 2 k) (Sum.inl a) (Sum.inl b)
  map_one' := by
    ext a b
    simp [Matrix.one_apply]
  map_mul' g h := by
    ext a b
    simp only [Matrix.of_apply, Subgroup.coe_mul, map_mul, Matrix.mul_apply,
      Fintype.sum_sum_type, spMat_eq_zero_of_mem_stabilizer_two h.2, mul_zero,
      Finset.sum_const_zero, add_zero]

theorem pow_four_eq_one_of_line [CharP k 2] {g : StatedSp 2 k}
    (hg : g ∈ stabilizer 2 k (flag 2 k 1)) (hc : spMat g (Sum.inl 0) (Sum.inl 0) = 1)
    (hρ : ∀ a b, spMat g (lineIdx a) (lineIdx b) = (1 : Matrix (Fin 2) (Fin 2) k) a b) :
    g ^ 4 = 1 := by
  apply spMat_injective
  rw [map_pow, map_one]
  have m00 : spMat g (Sum.inl 1) (Sum.inl 1) = 1 := by simpa [lineIdx] using hρ 0 0
  have m01 : spMat g (Sum.inl 1) (Sum.inr 1) = 0 := by simpa [lineIdx] using hρ 0 1
  have m10 : spMat g (Sum.inr 1) (Sum.inl 1) = 0 := by simpa [lineIdx] using hρ 1 0
  have m11 : spMat g (Sum.inr 1) (Sum.inr 1) = 1 := by simpa [lineIdx] using hρ 1 1
  have c1 : spMat g (Sum.inl 1) (Sum.inl 0) = 0 :=
    spMat_eq_zero_of_mem_stabilizer_one hg (by simp)
  have c2 : spMat g (Sum.inr 0) (Sum.inl 0) = 0 :=
    spMat_eq_zero_of_mem_stabilizer_one hg (by simp)
  have c3 : spMat g (Sum.inr 1) (Sum.inl 0) = 0 :=
    spMat_eq_zero_of_mem_stabilizer_one hg (by simp)
  have r1 : spMat g (Sum.inr 0) (Sum.inl 1) = 0 := spMat_line_row_eq_zero hg (by simp)
  have r2 : spMat g (Sum.inr 0) (Sum.inr 1) = 0 := spMat_line_row_eq_zero hg (by simp)
  have r0 : spMat g (Sum.inr 0) (Sum.inr 0) = 1 := by
    have h := spMat_line_row hg (Sum.inr 0)
    rw [hc, one_mul] at h
    simpa using h
  refine pow_four_eq_one_of_height (spMat g) (Sum.elim (fun i => (i : ℕ)) (fun i => 2 - (i : ℕ)))
    ?_ ?_
  · rintro (i | i) <;> simp <;> omega
  · intro x y hxy
    by_contra hlt
    apply hxy
    rw [Matrix.sub_apply, sub_eq_zero]
    revert x y
    simp only [Sum.forall, Fin.forall_fin_two]
    simp [hc, m00, m01, m10, m11, c1, c2, c3, r0, r1, r2]

theorem pow_four_eq_one_of_lag [CharP k 2] {g : StatedSp 2 k}
    (hg : g ∈ stabilizer 2 k (flag 2 k 2))
    (hρ : ∀ a b, spMat g (Sum.inl a) (Sum.inl b) = (1 : Matrix (Fin 2) (Fin 2) k) a b) :
    g ^ 4 = 1 := by
  apply spMat_injective
  rw [map_pow, map_one]
  have hD := spMat_lag_row hg hρ
  have hC := spMat_eq_zero_of_mem_stabilizer_two hg
  refine pow_four_eq_one_of_height (spMat g) (Sum.elim (fun _ => 0) (fun _ => 1)) ?_ ?_
  · rintro (i | i) <;> simp
  · intro x y hxy
    by_contra hlt
    apply hxy
    rw [Matrix.sub_apply, sub_eq_zero]
    revert x y
    simp only [Sum.forall, Fin.forall_fin_two]
    simp [hρ, hD, hC]

end Reps

section Cases

variable {k : Type} [Field k] [Finite k] [CharP k 2]

theorem top_mem_cComp_top {G : Type*} [Group G] [Finite G] {A : Subgroup G} (hA : A ∈ cComp A) :
    (⊤ : Subgroup A) ∈ cComp (⊤ : Subgroup A) := by
  have h := subgroupOf_mem_cComp hA
  rwa [Subgroup.subgroupOf_self] at h

theorem isQuasisimple_of_le_stabilizer_line {A : Subgroup (StatedSp 2 k)} (hA : A ∈ cComp A)
    (hAQ : A ≤ stabilizer 2 k (flag 2 k 1)) : CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A) := by
  have hperf : commutator A = ⊤ :=
    (Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hA)).commutator_eq_top
  have hχ : ∀ x : A, lineChar (Subgroup.inclusion hAQ x) = 1 := by
    intro x
    have h := Abelianization.commutator_subset_ker
      (lineChar.toHomUnits.comp (Subgroup.inclusion hAQ)) (hperf ▸ Subgroup.mem_top x)
    exact congrArg Units.val (MonoidHom.mem_ker.mp h)
  refine isQuasisimple_pCore_quotient_of_GL_two (top_mem_cComp_top hA)
    (lineRep.toHomUnits.comp (Subgroup.inclusion hAQ)) fun x hx => ?_
  have hρ : lineRep (Subgroup.inclusion hAQ x) = 1 := congrArg Units.val hx
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_four_eq_one_of_line (hAQ x.2) (hχ x) fun a b => congrFun (congrFun hρ a) b

theorem isQuasisimple_of_le_stabilizer_lag {A : Subgroup (StatedSp 2 k)} (hA : A ∈ cComp A)
    (hAQ : A ≤ stabilizer 2 k (flag 2 k 2)) : CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A) := by
  refine isQuasisimple_pCore_quotient_of_GL_two (top_mem_cComp_top hA)
    (lagRep.toHomUnits.comp (Subgroup.inclusion hAQ)) fun x hx => ?_
  have hρ : lagRep (Subgroup.inclusion hAQ x) = 1 := congrArg Units.val hx
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_four_eq_one_of_lag (hAQ x.2) fun a b => congrFun (congrFun hρ a) b

end Cases

theorem characteristic_two_symplectic_four_Ccomponents_have_quasisimple_two_core_quotient
    {k : Type} [Field k] [Finite k] [CharP k 2] {T A : Subgroup (StatedSp 2 k)}
    (hT : CFSG.Open.quasithinIsSylowTwo T) (hA : A ∈ cComp A) (hAT : A ⊔ T < ⊤) :
    CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := k) 2 2
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (StatedSp 2 k) (hT.1.toSylow hT.2) P
  set c : MulAut (StatedSp 2 k) := MulAut.conj g with hc
  have hTU : T.map c.toMonoidHom = unipotent 2 k := by
    rw [← hP, ← hg]
    rfl
  have hne : (A ⊔ T).map c.toMonoidHom ≠ ⊤ := by
    intro h
    apply hAT.ne
    have hsurj : Function.Surjective c.toMonoidHom := c.surjective
    rw [← Subgroup.map_top_of_surjective c.toMonoidHom hsurj] at h
    exact Subgroup.map_injective c.injective h
  have hUle : unipotent 2 k ≤ (A ⊔ T).map c.toMonoidHom := by
    rw [← hTU]
    exact Subgroup.map_mono le_sup_right
  have hA' : A.map c.toMonoidHom ∈ cComp (A.map c.toMonoidHom) := cComp_map_mulEquiv c hA
  rw [isQuasisimple_pCore_quotient_congr (A.equivMapOfInjective c.toMonoidHom c.injective)]
  rcases CFSG.QuasithinUnique.Setup.X7a.contained_in_Q2 hUle hne with hQ | hQ
  · exact isQuasisimple_of_le_stabilizer_line hA' ((Subgroup.map_mono le_sup_left).trans hQ)
  · exact isQuasisimple_of_le_stabilizer_lag hA' ((Subgroup.map_mono le_sup_left).trans hQ)

end CFSG.Quasithin.H13.NQTerm
