module

public import CFSG.RankThree.PartOne.KF4.Lattice4
public import CFSG.RankThree.PartOne.KF4.F4ThreeBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Polynomial


open Polynomial in
@[expose] def f4FourP : ℤ[X] := X ^ 2 + 1

theorem f4FourP_monic : f4FourP.Monic := by
  unfold f4FourP
  monicity!

theorem f4FourP_natDegree : f4FourP.natDegree = 2 := by
  unfold f4FourP
  compute_degree!

theorem f4FourP_coeff_zero : f4FourP.coeff 0 = 1 := by
  simp [f4FourP, Polynomial.coeff_add, Polynomial.coeff_X_pow]

theorem f4FourP_eval (q : ℤ) : f4FourP.eval q = q ^ 2 + 1 := by
  simp [f4FourP]

theorem aeval_f4FourP_eq_zero : Polynomial.aeval (weylMatrix f4W4) f4FourP = 0 := by
  simp only [f4FourP, map_add, map_pow, Polynomial.aeval_X, map_one]
  rw [weylMatrix_f4W4, pow_two, f4W4Mat_sq]
  simp

theorem f4Four_P_zero (x : Fin Tag.F4.rank → ℤ) :
    (Polynomial.aeval (weylMatrix f4W4) f4FourP) *ᵥ x = 0 := by
  rw [aeval_f4FourP_eq_zero, Matrix.zero_mulVec]

@[expose] def f4FourA : Fin Tag.F4.rank → ℤ := ![0, 0, 1, 0]

@[expose] def f4FourA' : Fin Tag.F4.rank → ℤ := ![0, -1, -1, 0]

@[expose] def f4FourB : Fin Tag.F4.rank → ℤ := ![0, 0, 0, 1]

@[expose] def f4FourB' : Fin Tag.F4.rank → ℤ := ![-1, -1, -2, -1]

theorem f4W4_blockA : f4W4 • f4FourA = f4FourA' ∧ f4W4 • f4FourA' = -f4FourA := by
  rw [f4W4_smul, f4W4_smul]
  decide +kernel

theorem f4W4_blockB : f4W4 • f4FourB = f4FourB' ∧ f4W4 • f4FourB' = -f4FourB := by
  rw [f4W4_smul, f4W4_smul]
  decide +kernel

theorem f4Four_blocks_span (i : Fin Tag.F4.rank) :
    (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {f4FourA, f4FourA', f4FourB, f4FourB'} := by
  have mA := Submodule.subset_span (R := ℤ) (Set.mem_insert f4FourA
    {f4FourA', f4FourB, f4FourB'})
  have mA' := Submodule.subset_span (R := ℤ) (Set.mem_insert_of_mem f4FourA
    (Set.mem_insert f4FourA' {f4FourB, f4FourB'}))
  have mB := Submodule.subset_span (R := ℤ) (Set.mem_insert_of_mem f4FourA
    (Set.mem_insert_of_mem f4FourA' (Set.mem_insert f4FourB {f4FourB'})))
  have mB' := Submodule.subset_span (R := ℤ) (Set.mem_insert_of_mem f4FourA
    (Set.mem_insert_of_mem f4FourA' (Set.mem_insert_of_mem f4FourB
      (Set.mem_singleton f4FourB'))))
  have h0 : (Pi.single (f4Index 0) 1 : Fin Tag.F4.rank → ℤ) =
      -f4FourB' + f4FourA' - f4FourA - f4FourB := by decide +kernel
  have h1 : (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = -f4FourA' - f4FourA := by
    decide +kernel
  have h2 : (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4FourA := by decide +kernel
  have h3 : (Pi.single (f4Index 3) 1 : Fin Tag.F4.rank → ℤ) = f4FourB := by decide +kernel
  have key : ∀ k : Fin 4, (Pi.single (f4Index k) 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {f4FourA, f4FourA', f4FourB, f4FourB'} := by
    intro k
    match k with
    | 0 =>
      rw [h0]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.add_mem _
        (Submodule.neg_mem _ mB') mA') mA) mB
    | 1 =>
      rw [h1]
      exact Submodule.sub_mem _ (Submodule.neg_mem _ mA') mA
    | 2 => rw [h2]; exact mA
    | 3 => rw [h3]; exact mB
  exact key i

@[expose] def f4FourCols (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ := fun j =>
  if (j : ℕ) < 2 then (weylMatrix f4W4 ^ (j : ℕ)) *ᵥ β₁
  else (weylMatrix f4W4 ^ ((j : ℕ) - 2)) *ᵥ β₂

theorem f4FourCols_zero (β₁ β₂ : Fin Tag.F4.rank → ℤ) : f4FourCols β₁ β₂ (f4Index 0) = β₁ := by
  simp [f4FourCols, f4Index]

theorem f4FourCols_one (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    f4FourCols β₁ β₂ (f4Index 1) = weylMatrix f4W4 *ᵥ β₁ := by
  simp [f4FourCols, f4Index]

theorem f4FourCols_two (β₁ β₂ : Fin Tag.F4.rank → ℤ) : f4FourCols β₁ β₂ (f4Index 2) = β₂ := by
  simp [f4FourCols, f4Index]

theorem f4FourCols_three (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    f4FourCols β₁ β₂ (f4Index 3) = weylMatrix f4W4 *ᵥ β₂ := by
  simp [f4FourCols, f4Index]

theorem f4Four_block_rel {β β' : Fin Tag.F4.rank → ℤ} (h1 : f4W4 • β = β')
    (h2 : f4W4 • β' = -β) :
    weylMatrix f4W4 *ᵥ β = β' ∧ (weylMatrix f4W4 ^ 2) *ᵥ β = -β := by
  refine ⟨by rw [weylMatrix_mulVec, h1], ?_⟩
  rw [pow_two, ← Matrix.mulVec_mulVec, weylMatrix_mulVec, weylMatrix_mulVec, h1, h2]

section Basis

variable {β₁ β₁' β₂ β₂' : Fin Tag.F4.rank → ℤ}

theorem f4FourCols_basis (h1 : f4W4 • β₁ = β₁') (h2 : f4W4 • β₂ = β₂')
    (hsp : ∀ i : Fin Tag.F4.rank, (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {β₁, β₁', β₂, β₂'}) :
    LinearIndependent ℤ (f4FourCols β₁ β₂) ∧
      Submodule.span ℤ (Set.range (f4FourCols β₁ β₂)) = ⊤ := by
  set c := f4FourCols β₁ β₂ with hc
  have hmem : ∀ v ∈ ({β₁, β₁', β₂, β₂'} : Set (Fin Tag.F4.rank → ℤ)),
      v ∈ Submodule.span ℤ (Set.range c) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv | hv | hv
    · have : v = c (f4Index 0) := by rw [hc, f4FourCols_zero, hv]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : v = c (f4Index 1) := by rw [hc, f4FourCols_one, weylMatrix_mulVec, h1, hv]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : v = c (f4Index 2) := by rw [hc, f4FourCols_two, hv]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : v = c (f4Index 3) := by rw [hc, f4FourCols_three, weylMatrix_mulVec, h2, hv]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range c) := by
    rw [← (Pi.basisFun ℤ (Fin Tag.F4.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact (Submodule.span_le.2 hmem) (hsp i)
  exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp),
    top_le_iff.1 hspan⟩

theorem f4Four_first_block_mem (h1 : f4W4 • β₁ = β₁') :
    β₁ ∈ Submodule.span ℤ (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) ∧
      β₁' ∈ Submodule.span ℤ (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) := by
  have m0 : f4FourCols β₁ β₂ (f4Index 0) ∈
      Submodule.span ℤ (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) :=
    Submodule.subset_span ⟨f4Index 0, (by decide : ((f4Index 0 : Fin Tag.F4.rank) : ℕ) < 2), rfl⟩
  have m1 : f4FourCols β₁ β₂ (f4Index 1) ∈
      Submodule.span ℤ (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) :=
    Submodule.subset_span ⟨f4Index 1, (by decide : ((f4Index 1 : Fin Tag.F4.rank) : ℕ) < 2), rfl⟩
  rw [f4FourCols_zero] at m0
  rw [f4FourCols_one, weylMatrix_mulVec, h1] at m1
  exact ⟨m0, m1⟩

theorem f4Four_stab (h1 : f4W4 • β₁ = β₁') (h1' : f4W4 • β₁' = -β₁) :
    ∀ j : Fin Tag.F4.rank, (j : ℕ) < 2 →
      weylMatrix f4W4 *ᵥ f4FourCols β₁ β₂ j ∈
        Submodule.span ℤ (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) := by
  obtain ⟨m0, m1⟩ := f4Four_first_block_mem (β₂ := β₂) h1
  intro j hj
  have hj' : j = f4Index 0 ∨ j = f4Index 1 := by
    have : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases this with h | h
    · exact Or.inl (Fin.ext (by simpa [f4Index] using h))
    · exact Or.inr (Fin.ext (by simpa [f4Index] using h))
  rcases hj' with rfl | rfl
  · rw [f4FourCols_zero, ← f4FourCols_one]
    exact Submodule.subset_span
      ⟨f4Index 1, (by decide : ((f4Index 1 : Fin Tag.F4.rank) : ℕ) < 2), rfl⟩
  · rw [f4FourCols_one, Matrix.mulVec_mulVec, ← pow_two, (f4Four_block_rel h1 h1').2]
    exact Submodule.neg_mem _ m0

end Basis

theorem f4FourP_eval_ne_zero {q : ℕ} (hq : 2 ≤ q) : f4FourP.eval (q : ℤ) ≠ 0 := by
  rw [f4FourP_eval]
  positivity

theorem f4Four_blocks_top (u : Fin Tag.F4.rank → ℤ) :
    u ∈ Submodule.span ℤ {f4FourA, f4FourA', f4FourB, f4FourB'} := by
  have : ⊤ ≤ Submodule.span ℤ ({f4FourA, f4FourA', f4FourB, f4FourB'} :
      Set (Fin Tag.F4.rank → ℤ)) := by
    rw [← (Pi.basisFun ℤ (Fin Tag.F4.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact f4Four_blocks_span i
  exact this Submodule.mem_top

theorem f4Four_blocks_span' (i : Fin Tag.F4.rank) :
    (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {f4FourB, f4FourB', f4FourA, f4FourA'} :=
  Submodule.span_mono (fun v hv => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
    tauto) (f4Four_blocks_span i)

section Fixed

variable {L : Type} [Field L] [IsAlgClosed L]

theorem f4Four_block_cyclic {β₁ β₁' β₂ β₂' : Fin Tag.F4.rank → ℤ}
    (h1 : f4W4 • β₁ = β₁') (h1' : f4W4 • β₁' = -β₁) (h2 : f4W4 • β₂ = β₂')
    (hsp : ∀ i : Fin Tag.F4.rank, (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {β₁, β₁', β₂, β₂'})
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples (weylMatrix f4W4) Fr
        (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) ∧
      Nat.card (fixedBlockTuples (weylMatrix f4W4) Fr
        (f4FourCols β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) = q ^ 2 + 1 := by
  obtain ⟨hlin, hspan⟩ := f4FourCols_basis h1 h2 hsp
  have h := isCyclic_and_card_fixedBlockTuples (L := L) (weylMatrix f4W4) (f4FourCols β₁ β₂)
    (k := 2) (by decide) β₂ hlin hspan
    (fun j hj => by simp [f4FourCols, not_lt.2 hj]) (f4Four_stab h1 h1')
    f4FourP f4FourP_monic (by rw [f4FourP_natDegree]; rfl)
    (by rw [f4Four_P_zero]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (Or.inl f4FourP_coeff_zero) (f4FourP_eval_ne_zero hq)
  refine ⟨h.1, ?_⟩
  rw [h.2, f4FourP_eval]
  have e : ((q : ℤ) ^ 2 + 1) = ((q ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, Int.natAbs_natCast]

omit [IsAlgClosed L] in
theorem f4Four_inf_eq_bot (Fr : L →+* L) :
    fixedBlockTuples (weylMatrix f4W4) Fr
        (f4FourCols f4FourA f4FourB '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) ⊓
      fixedBlockTuples (weylMatrix f4W4) Fr
        (f4FourCols f4FourB f4FourA '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  obtain ⟨mA, mA'⟩ := f4Four_first_block_mem (β₂ := f4FourB) f4W4_blockA.1
  obtain ⟨mB, mB'⟩ := f4Four_first_block_mem (β₂ := f4FourA) f4W4_blockB.1
  have h1 := (mem_fixedBlockTuples.1 ha1).2
  have h2 := (mem_fixedBlockTuples.1 ha2).2
  have hS : ∀ u ∈ ({f4FourA, f4FourA', f4FourB, f4FourB'} : Set (Fin Tag.F4.rank → ℤ)),
      rootChar a u = 1 := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with hu | hu | hu | hu
    · rw [hu]; exact CTTorus.rootChar_eq_one_of_mem_span h1 mA
    · rw [hu]; exact CTTorus.rootChar_eq_one_of_mem_span h1 mA'
    · rw [hu]; exact CTTorus.rootChar_eq_one_of_mem_span h2 mB
    · rw [hu]; exact CTTorus.rootChar_eq_one_of_mem_span h2 mB'
  have h : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u =>
    CTTorus.rootChar_eq_one_of_mem_span hS (f4Four_blocks_top u)
  exact h ▸ Subgroup.one_mem _

@[expose] def f4FourZ (Fr : L →+* L) : Subgroup (Fin Tag.F4.rank → Lˣ) :=
  fixedBlockTuples (weylMatrix f4W4) Fr
      (f4FourCols f4FourA f4FourB '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) ⊔
    fixedBlockTuples (weylMatrix f4W4) Fr
      (f4FourCols f4FourB f4FourA '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})

theorem f4Four_card_Z (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ]
    (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    Nat.card ↥(f4FourZ Fr) = (q ^ 2 + 1) ^ 2 := by
  obtain ⟨-, hA⟩ := f4Four_block_cyclic f4W4_blockA.1 f4W4_blockA.2 f4W4_blockB.1
    f4Four_blocks_span Fr hFr hℓ hℓq hq
  obtain ⟨-, hB⟩ := f4Four_block_cyclic f4W4_blockB.1 f4W4_blockB.2 f4W4_blockA.1
    f4Four_blocks_span' Fr hFr hℓ hℓq hq
  have hne : q ^ 2 + 1 ≠ 0 := by positivity
  have : Finite ↥(fixedBlockTuples (weylMatrix f4W4) Fr
      (f4FourCols f4FourA f4FourB '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) :=
    Nat.finite_of_card_ne_zero (by rw [hA]; exact hne)
  have : Finite ↥(fixedBlockTuples (weylMatrix f4W4) Fr
      (f4FourCols f4FourB f4FourA '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact hne)
  rw [f4FourZ, card_sup_of_inf_eq_bot' (f4Four_inf_eq_bot Fr), hA, hB]
  exact (sq _).symm

omit [IsAlgClosed L] in
theorem f4Four_zpow_eq_one (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    {a : Fin Tag.F4.rank → Lˣ} (ha : a ∈ fixedCharTuples (weylMatrix f4W4) Fr)
    (i : Fin Tag.F4.rank) : a i ^ ((q : ℤ) ^ 2 + 1) = 1 := by
  have h := rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr ha f4FourP (Pi.single i 1)
  rw [f4Four_P_zero, rootChar_zero, CTTorus.rootChar_single, f4FourP_eval] at h
  exact h.symm

omit [IsAlgClosed L] in
theorem f4Four_orderOf_dvd (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    {a : Fin Tag.F4.rank → Lˣ} (ha : a ∈ fixedCharTuples (weylMatrix f4W4) Fr) :
    orderOf a ∣ q ^ 2 + 1 := by
  apply orderOf_dvd_of_pow_eq_one
  funext i
  have h := f4Four_zpow_eq_one Fr hFr ha i
  rw [Pi.pow_apply, Pi.one_apply]
  have e : ((q : ℤ) ^ 2 + 1) = ((q ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e, zpow_natCast] at h
  exact h

omit [IsAlgClosed L] in
theorem f4Four_eigencolumn (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {p : ℕ}
    (hp : p.Prime) {a : Fin Tag.F4.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (weylMatrix f4W4) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ z : Fin Tag.F4.rank → ZMod p, z ≠ 0 ∧
      (dualMatrix (ZMod p) f4W4).mulVec z = (q : ZMod p) • z ∧
        rootCharKernel a = rootKernel z := by
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (weylMatrix f4W4) Fr hFr hp ha hap ha1
  exact ⟨z, hz0, hzM, by rw [hzk]; rfl⟩

omit [IsAlgClosed L] in
theorem f4Four_two_torsion_card (Fr : L →+* L) :
    Finite {a : Fin Tag.F4.rank → Lˣ // a ∈ fixedCharTuples (weylMatrix f4W4) Fr ∧ a ^ 2 = 1} ∧
      Nat.card {a : Fin Tag.F4.rank → Lˣ //
        a ∈ fixedCharTuples (weylMatrix f4W4) Fr ∧ a ^ 2 = 1} ≤ 4 := by
  classical
  have hsq : ∀ a : Fin Tag.F4.rank → Lˣ, a ^ 2 = 1 → ∀ i, a i ^ 2 = 1 := fun a ha i => by
    simpa using congrFun ha i
  let φ : {a : Fin Tag.F4.rank → Lˣ // a ∈ fixedCharTuples (weylMatrix f4W4) Fr ∧ a ^ 2 = 1} →
      rootsOfUnity 2 L × rootsOfUnity 2 L := fun a =>
    (⟨rootChar a.1 f4FourA, (mem_rootsOfUnity 2 _).2
        (CTTorus.rootChar_pow_eq_one (hsq a.1 a.2.2) _)⟩,
      ⟨rootChar a.1 f4FourB, (mem_rootsOfUnity 2 _).2
        (CTTorus.rootChar_pow_eq_one (hsq a.1 a.2.2) _)⟩)
  have hinj : Function.Injective φ := by
    intro a b hab
    have hA : rootChar a.1 f4FourA = rootChar b.1 f4FourA :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => (x.1 : Lˣ)) hab
    have hB : rootChar a.1 f4FourB = rootChar b.1 f4FourB :=
      congrArg (fun x : rootsOfUnity 2 L × rootsOfUnity 2 L => (x.2 : Lˣ)) hab
    apply Subtype.ext
    have hc : a.1 * b.1 ∈ fixedCharTuples (weylMatrix f4W4) Fr :=
      mul_mem a.2.1 b.2.1
    have hcA : rootChar (a.1 * b.1) f4FourA = 1 := by
      rw [CTTorus.rootChar_mul, ← hA, ← sq]
      exact CTTorus.rootChar_pow_eq_one (hsq a.1 a.2.2) _
    have hcB : rootChar (a.1 * b.1) f4FourB = 1 := by
      rw [CTTorus.rootChar_mul, ← hB, ← sq]
      exact CTTorus.rootChar_pow_eq_one (hsq a.1 a.2.2) _
    have hfix := mem_fixedCharTuples_iff.1 hc
    have hcA' : rootChar (a.1 * b.1) f4FourA' = 1 := by
      have := hfix f4FourA
      rw [weylMatrix_mulVec, f4W4_blockA.1, hcA, map_one] at this
      exact this
    have hcB' : rootChar (a.1 * b.1) f4FourB' = 1 := by
      have := hfix f4FourB
      rw [weylMatrix_mulVec, f4W4_blockB.1, hcB, map_one] at this
      exact this
    have hS : ∀ u ∈ ({f4FourA, f4FourA', f4FourB, f4FourB'} : Set (Fin Tag.F4.rank → ℤ)),
        rootChar (a.1 * b.1) u = 1 := by
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with hu | hu | hu | hu
      · rw [hu]; exact hcA
      · rw [hu]; exact hcA'
      · rw [hu]; exact hcB
      · rw [hu]; exact hcB'
    have h1 : a.1 * b.1 = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u =>
      CTTorus.rootChar_eq_one_of_mem_span hS (f4Four_blocks_top u)
    have hb2 : b.1 * b.1 = 1 := by rw [← sq]; exact b.2.2
    calc a.1 = a.1 * (b.1 * b.1) := by rw [hb2, mul_one]
      _ = (a.1 * b.1) * b.1 := by rw [mul_assoc]
      _ = b.1 := by rw [h1, one_mul]
  have hcard : Nat.card (rootsOfUnity 2 L × rootsOfUnity 2 L) ≤ 4 := by
    rw [Nat.card_prod]
    have h2 := card_rootsOfUnity L 2
    nlinarith
  exact ⟨Finite.of_injective φ hinj, (Nat.card_le_card_of_injective φ hinj).trans hcard⟩

end Fixed

end CFSG.RankThree.PartOne.KF4
