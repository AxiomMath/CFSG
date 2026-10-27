module

public import CFSG.RankThree.PartOne.KF4.Lattice3
public import CFSG.RankThree.PartOne.KE.CTBlock

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE
open scoped Matrix Polynomial


@[expose] def f4ThreeM (δ : ℤ) : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  δ • weylMatrix f4W3

theorem f4ThreeM_mulVec (δ : ℤ) (x : Fin Tag.F4.rank → ℤ) :
    f4ThreeM δ *ᵥ x = δ • (f4W3 • x) := by
  rw [f4ThreeM, Matrix.smul_mulVec, weylMatrix_mulVec]

theorem f4ThreeM_pow_mulVec (δ : ℤ) (i : ℕ) (x : Fin Tag.F4.rank → ℤ) :
    (f4ThreeM δ ^ i) *ᵥ x = (δ ^ i) • ((f4W3 ^ i) • x) := by
  rw [f4ThreeM, smul_pow, Matrix.smul_mulVec, ← weylMatrix_pow, weylMatrix_mulVec]

open Polynomial in
@[expose] def f4ThreeP (δ : ℤ) : ℤ[X] := X ^ 2 + C δ * X + 1

theorem f4ThreeP_monic (δ : ℤ) : (f4ThreeP δ).Monic := by
  unfold f4ThreeP
  monicity!

theorem f4ThreeP_natDegree (δ : ℤ) : (f4ThreeP δ).natDegree = 2 := by
  unfold f4ThreeP
  compute_degree!

theorem f4ThreeP_coeff_zero (δ : ℤ) : (f4ThreeP δ).coeff 0 = 1 := by
  simp [f4ThreeP, Polynomial.coeff_add, Polynomial.coeff_X_pow]

theorem f4ThreeP_eval (δ q : ℤ) : (f4ThreeP δ).eval q = q ^ 2 + δ * q + 1 := by
  simp [f4ThreeP]

theorem aeval_f4ThreeP (δ : ℤ) : Polynomial.aeval (f4ThreeM δ) (f4ThreeP δ) =
    f4ThreeM δ ^ 2 + δ • f4ThreeM δ + 1 := by
  simp only [f4ThreeP, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    map_one, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem f4W3Mat_one_sq_add : f4W3Mat ^ 2 + f4W3Mat + 1 = 0 := by
  rw [pow_two]
  exact f4W3Mat_sq

theorem aeval_f4ThreeP_eq_zero (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) :
    Polynomial.aeval (f4ThreeM δ) (f4ThreeP δ) = 0 := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hδ2' : δ ^ 2 = 1 := by rcases hδ with rfl | rfl <;> norm_num
  have hM : f4ThreeM δ = δ • f4W3Mat := by
    rw [f4ThreeM, weylMatrix_f4W3]
  rw [aeval_f4ThreeP, hM, smul_pow, smul_smul, hδ2', hδ2, one_smul, one_smul]
  exact f4W3Mat_one_sq_add

theorem f4Three_P_zero (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (x : Fin Tag.F4.rank → ℤ) :
    (Polynomial.aeval (f4ThreeM δ) (f4ThreeP δ)) *ᵥ x = 0 := by
  rw [aeval_f4ThreeP_eq_zero δ hδ, Matrix.zero_mulVec]

@[expose] def f4ThreeA : Fin Tag.F4.rank → ℤ := ![1, 0, 0, 0]

@[expose] def f4ThreeA' : Fin Tag.F4.rank → ℤ := ![0, 1, 2, 0]

@[expose] def f4ThreeB : Fin Tag.F4.rank → ℤ := ![0, 0, 1, 0]

@[expose] def f4ThreeB' : Fin Tag.F4.rank → ℤ := ![-1, -1, -2, -1]

theorem f4W3_blockA : f4W3 • f4ThreeA = f4ThreeA' ∧ f4W3 • f4ThreeA' = -(f4ThreeA + f4ThreeA') := by
  rw [f4W3_smul, f4W3_smul]
  decide +kernel

theorem f4W3_blockB : f4W3 • f4ThreeB = f4ThreeB' ∧ f4W3 • f4ThreeB' = -(f4ThreeB + f4ThreeB') := by
  rw [f4W3_smul, f4W3_smul]
  decide +kernel

theorem f4Three_blocks_span (i : Fin Tag.F4.rank) :
    (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {f4ThreeA, f4ThreeA', f4ThreeB, f4ThreeB'} := by
  have mA := Submodule.subset_span (R := ℤ) (Set.mem_insert f4ThreeA
    {f4ThreeA', f4ThreeB, f4ThreeB'})
  have mA' := Submodule.subset_span (R := ℤ) (Set.mem_insert_of_mem f4ThreeA
    (Set.mem_insert f4ThreeA' {f4ThreeB, f4ThreeB'}))
  have mB := Submodule.subset_span (R := ℤ) (Set.mem_insert_of_mem f4ThreeA
    (Set.mem_insert_of_mem f4ThreeA' (Set.mem_insert f4ThreeB {f4ThreeB'})))
  have mB' := Submodule.subset_span (R := ℤ) (Set.mem_insert_of_mem f4ThreeA
    (Set.mem_insert_of_mem f4ThreeA' (Set.mem_insert_of_mem f4ThreeB
      (Set.mem_singleton f4ThreeB'))))
  have h0 : (Pi.single (f4Index 0) 1 : Fin Tag.F4.rank → ℤ) = f4ThreeA := by decide +kernel
  have h1 : (Pi.single (f4Index 1) 1 : Fin Tag.F4.rank → ℤ) = f4ThreeA' - (2 : ℤ) • f4ThreeB := by
    decide +kernel
  have h2 : (Pi.single (f4Index 2) 1 : Fin Tag.F4.rank → ℤ) = f4ThreeB := by decide +kernel
  have h3 : (Pi.single (f4Index 3) 1 : Fin Tag.F4.rank → ℤ) =
      -(f4ThreeA + f4ThreeA' + f4ThreeB') := by decide +kernel
  have key : ∀ k : Fin 4, (Pi.single (f4Index k) 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {f4ThreeA, f4ThreeA', f4ThreeB, f4ThreeB'} := by
    intro k
    match k with
    | 0 => rw [h0]; exact mA
    | 1 =>
      rw [h1]
      exact Submodule.sub_mem _ mA' (Submodule.smul_mem _ _ mB)
    | 2 => rw [h2]; exact mB
    | 3 =>
      rw [h3]
      exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.add_mem _ mA mA') mB')
  exact key i

@[expose] def f4ThreeCols (δ : ℤ) (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    Fin Tag.F4.rank → Fin Tag.F4.rank → ℤ := fun j =>
  if (j : ℕ) < 2 then (f4ThreeM δ ^ (j : ℕ)) *ᵥ β₁ else (f4ThreeM δ ^ ((j : ℕ) - 2)) *ᵥ β₂

theorem f4ThreeCols_zero (δ : ℤ) (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    f4ThreeCols δ β₁ β₂ (f4Index 0) = β₁ := by
  simp [f4ThreeCols, f4Index]

theorem f4ThreeCols_one (δ : ℤ) (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    f4ThreeCols δ β₁ β₂ (f4Index 1) = f4ThreeM δ *ᵥ β₁ := by
  simp [f4ThreeCols, f4Index]

theorem f4ThreeCols_two (δ : ℤ) (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    f4ThreeCols δ β₁ β₂ (f4Index 2) = β₂ := by
  simp [f4ThreeCols, f4Index]

theorem f4ThreeCols_three (δ : ℤ) (β₁ β₂ : Fin Tag.F4.rank → ℤ) :
    f4ThreeCols δ β₁ β₂ (f4Index 3) = f4ThreeM δ *ᵥ β₂ := by
  simp [f4ThreeCols, f4Index]

theorem f4Three_block_rel (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {β β' : Fin Tag.F4.rank → ℤ}
    (h1 : f4W3 • β = β') (h2 : f4W3 • β' = -(β + β')) :
    f4ThreeM δ *ᵥ β = δ • β' ∧ (f4ThreeM δ ^ 2) *ᵥ β = -(β + β') := by
  refine ⟨by rw [f4ThreeM_mulVec, h1], ?_⟩
  have hδ2 : δ ^ 2 = 1 := by rcases hδ with rfl | rfl <;> norm_num
  rw [f4ThreeM_pow_mulVec, hδ2, one_smul, pow_two, mul_smul, h1, h2]

theorem f4Three_block_inv (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {β β' : Fin Tag.F4.rank → ℤ}
    (h1 : f4W3 • β = β') (h2 : f4W3 • β' = -(β + β')) : δ • (f4ThreeM δ *ᵥ β) = β' := by
  have hδ2 : δ * δ = 1 := by rcases hδ with rfl | rfl <;> norm_num
  rw [(f4Three_block_rel δ hδ h1 h2).1, smul_smul, hδ2, one_smul]

section Basis

variable {β₁ β₁' β₂ β₂' : Fin Tag.F4.rank → ℤ}

theorem f4ThreeCols_basis (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (h1 : f4W3 • β₁ = β₁')
    (h1' : f4W3 • β₁' = -(β₁ + β₁')) (h2 : f4W3 • β₂ = β₂') (h2' : f4W3 • β₂' = -(β₂ + β₂'))
    (hsp : ∀ i : Fin Tag.F4.rank, (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {β₁, β₁', β₂, β₂'}) :
    LinearIndependent ℤ (f4ThreeCols δ β₁ β₂) ∧
      Submodule.span ℤ (Set.range (f4ThreeCols δ β₁ β₂)) = ⊤ := by
  set c := f4ThreeCols δ β₁ β₂ with hc
  have hmem : ∀ v ∈ ({β₁, β₁', β₂, β₂'} : Set (Fin Tag.F4.rank → ℤ)),
      v ∈ Submodule.span ℤ (Set.range c) := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · rw [← f4ThreeCols_zero δ v β₂]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [← f4Three_block_inv δ hδ h1 h1']
      refine Submodule.smul_mem _ _ ?_
      rw [← f4ThreeCols_one δ β₁ β₂]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [← f4ThreeCols_two δ β₁ v]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [← f4Three_block_inv δ hδ h2 h2']
      refine Submodule.smul_mem _ _ ?_
      rw [← f4ThreeCols_three δ β₁ β₂]
      exact Submodule.subset_span ⟨_, rfl⟩
  have hspan : ⊤ ≤ Submodule.span ℤ (Set.range c) := by
    rw [← (Pi.basisFun ℤ (Fin Tag.F4.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact (Submodule.span_le.2 hmem) (hsp i)
  exact ⟨linearIndependent_of_top_le_span_of_card_eq_finrank hspan (by simp),
    top_le_iff.1 hspan⟩

theorem f4Three_first_block_mem (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (h1 : f4W3 • β₁ = β₁')
    (h1' : f4W3 • β₁' = -(β₁ + β₁')) :
    β₁ ∈ Submodule.span ℤ (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) ∧
      β₁' ∈ Submodule.span ℤ (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) := by
  have m0 : f4ThreeCols δ β₁ β₂ (f4Index 0) ∈
      Submodule.span ℤ (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) :=
    Submodule.subset_span ⟨f4Index 0, (by decide : ((f4Index 0 : Fin Tag.F4.rank) : ℕ) < 2), rfl⟩
  have m1 : f4ThreeCols δ β₁ β₂ (f4Index 1) ∈
      Submodule.span ℤ (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) :=
    Submodule.subset_span ⟨f4Index 1, (by decide : ((f4Index 1 : Fin Tag.F4.rank) : ℕ) < 2), rfl⟩
  rw [f4ThreeCols_zero] at m0
  rw [f4ThreeCols_one] at m1
  refine ⟨m0, ?_⟩
  rw [← f4Three_block_inv δ hδ h1 h1']
  exact Submodule.smul_mem _ _ m1

theorem f4Three_stab (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (h1 : f4W3 • β₁ = β₁')
    (h1' : f4W3 • β₁' = -(β₁ + β₁')) :
    ∀ j : Fin Tag.F4.rank, (j : ℕ) < 2 →
      f4ThreeM δ *ᵥ f4ThreeCols δ β₁ β₂ j ∈
        Submodule.span ℤ (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) := by
  obtain ⟨m0, m1⟩ := f4Three_first_block_mem (β₂ := β₂) δ hδ h1 h1'
  intro j hj
  have hj' : j = f4Index 0 ∨ j = f4Index 1 := by
    have : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
    rcases this with h | h
    · exact Or.inl (Fin.ext (by simpa [f4Index] using h))
    · exact Or.inr (Fin.ext (by simpa [f4Index] using h))
  rcases hj' with rfl | rfl
  · rw [f4ThreeCols_zero, ← f4ThreeCols_one]
    exact Submodule.subset_span
      ⟨f4Index 1, (by decide : ((f4Index 1 : Fin Tag.F4.rank) : ℕ) < 2), rfl⟩
  · rw [f4ThreeCols_one, Matrix.mulVec_mulVec, ← pow_two, (f4Three_block_rel δ hδ h1 h1').2]
    exact Submodule.neg_mem _ (Submodule.add_mem _ m0 m1)

end Basis

theorem f4ThreeP_eval_ne_zero (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {q : ℕ} (hq : 2 ≤ q) :
    (f4ThreeP δ).eval (q : ℤ) ≠ 0 := by
  rw [f4ThreeP_eval]
  have hq' : (2 : ℤ) ≤ q := by exact_mod_cast hq
  rcases hδ with rfl | rfl <;> nlinarith

theorem f4Three_blocks_top (u : Fin Tag.F4.rank → ℤ) :
    u ∈ Submodule.span ℤ {f4ThreeA, f4ThreeA', f4ThreeB, f4ThreeB'} := by
  have : ⊤ ≤ Submodule.span ℤ ({f4ThreeA, f4ThreeA', f4ThreeB, f4ThreeB'} :
      Set (Fin Tag.F4.rank → ℤ)) := by
    rw [← (Pi.basisFun ℤ (Fin Tag.F4.rank)).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact f4Three_blocks_span i
  exact this Submodule.mem_top

theorem f4Three_blocks_span' (i : Fin Tag.F4.rank) :
    (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {f4ThreeB, f4ThreeB', f4ThreeA, f4ThreeA'} :=
  Submodule.span_mono (fun v hv => by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv ⊢
    tauto) (f4Three_blocks_span i)

section Fixed

variable {L : Type} [Field L] [IsAlgClosed L]

theorem f4Three_block_cyclic (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) {β₁ β₁' β₂ β₂' : Fin Tag.F4.rank → ℤ}
    (h1 : f4W3 • β₁ = β₁') (h1' : f4W3 • β₁' = -(β₁ + β₁')) (h2 : f4W3 • β₂ = β₂')
    (h2' : f4W3 • β₂' = -(β₂ + β₂'))
    (hsp : ∀ i : Fin Tag.F4.rank, (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈
      Submodule.span ℤ {β₁, β₁', β₂, β₂'})
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    IsCyclic (fixedBlockTuples (f4ThreeM δ) Fr
        (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) ∧
      Nat.card (fixedBlockTuples (f4ThreeM δ) Fr
        (f4ThreeCols δ β₁ β₂ '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) =
          ((q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs := by
  obtain ⟨hlin, hspan⟩ := f4ThreeCols_basis δ hδ h1 h1' h2 h2' hsp
  have h := isCyclic_and_card_fixedBlockTuples (L := L) (f4ThreeM δ) (f4ThreeCols δ β₁ β₂)
    (k := 2) (by decide) β₂ hlin hspan
    (fun j hj => by simp [f4ThreeCols, not_lt.2 hj]) (f4Three_stab δ hδ h1 h1')
    (f4ThreeP δ) (f4ThreeP_monic δ) (by rw [f4ThreeP_natDegree]; rfl)
    (by rw [f4Three_P_zero δ hδ]; exact Submodule.zero_mem _)
    Fr hFr hℓ hℓq (Or.inl (f4ThreeP_coeff_zero δ)) (f4ThreeP_eval_ne_zero δ hδ hq)
  refine ⟨h.1, ?_⟩
  rw [h.2, f4ThreeP_eval]

omit [IsAlgClosed L] in
theorem f4Three_inf_eq_bot (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (Fr : L →+* L) :
    fixedBlockTuples (f4ThreeM δ) Fr
        (f4ThreeCols δ f4ThreeA f4ThreeB '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) ⊓
      fixedBlockTuples (f4ThreeM δ) Fr
        (f4ThreeCols δ f4ThreeB f4ThreeA '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) = ⊥ := by
  rw [eq_bot_iff]
  intro a ⟨ha1, ha2⟩
  obtain ⟨mA, mA'⟩ := f4Three_first_block_mem (β₂ := f4ThreeB) δ hδ f4W3_blockA.1 f4W3_blockA.2
  obtain ⟨mB, mB'⟩ := f4Three_first_block_mem (β₂ := f4ThreeA) δ hδ f4W3_blockB.1 f4W3_blockB.2
  have h1 := (mem_fixedBlockTuples.1 ha1).2
  have h2 := (mem_fixedBlockTuples.1 ha2).2
  have hS : ∀ u ∈ ({f4ThreeA, f4ThreeA', f4ThreeB, f4ThreeB'} : Set (Fin Tag.F4.rank → ℤ)),
      rootChar a u = 1 := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact CTTorus.rootChar_eq_one_of_mem_span h1 mA
    · exact CTTorus.rootChar_eq_one_of_mem_span h1 mA'
    · exact CTTorus.rootChar_eq_one_of_mem_span h2 mB
    · exact CTTorus.rootChar_eq_one_of_mem_span h2 mB'
  have h : a = 1 := CTTorus.eq_one_of_rootChar_eq_one fun u =>
    CTTorus.rootChar_eq_one_of_mem_span hS (f4Three_blocks_top u)
  exact h ▸ Subgroup.one_mem _

theorem card_sup_of_inf_eq_bot' {G : Type*} [CommGroup G] {A B : Subgroup G} [Finite A] [Finite B]
    (h : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let φ : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype fun _ _ => Commute.all _ _
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := by simpa [φ] using hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : G) ∈ A ⊓ B :=
      ⟨x.2, by rw [hx]; exact B.inv_mem y.2⟩
    rw [h, Subgroup.mem_bot] at hmem
    have hy : (y : G) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = A ⊔ B := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofInjective φ hinj)).symm

@[expose] def f4ThreeZ (δ : ℤ) (Fr : L →+* L) : Subgroup (Fin Tag.F4.rank → Lˣ) :=
  fixedBlockTuples (f4ThreeM δ) Fr
      (f4ThreeCols δ f4ThreeA f4ThreeB '' {i : Fin Tag.F4.rank | (i : ℕ) < 2}) ⊔
    fixedBlockTuples (f4ThreeM δ) Fr
      (f4ThreeCols δ f4ThreeB f4ThreeA '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})

theorem f4Three_card_Z (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q) (hq : 2 ≤ q) :
    Nat.card ↥(f4ThreeZ δ Fr) = ((q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs ^ 2 := by
  obtain ⟨-, hA⟩ := f4Three_block_cyclic δ hδ f4W3_blockA.1 f4W3_blockA.2 f4W3_blockB.1
    f4W3_blockB.2 f4Three_blocks_span Fr hFr hℓ hℓq hq
  obtain ⟨-, hB⟩ := f4Three_block_cyclic δ hδ f4W3_blockB.1 f4W3_blockB.2 f4W3_blockA.1
    f4W3_blockA.2 f4Three_blocks_span' Fr hFr hℓ hℓq hq
  have hne : ((q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs ≠ 0 := by
    have := f4ThreeP_eval_ne_zero δ hδ hq
    rw [f4ThreeP_eval] at this
    exact Int.natAbs_ne_zero.2 this
  have : Finite ↥(fixedBlockTuples (f4ThreeM δ) Fr
      (f4ThreeCols δ f4ThreeA f4ThreeB '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) :=
    Nat.finite_of_card_ne_zero (by rw [hA]; exact hne)
  have : Finite ↥(fixedBlockTuples (f4ThreeM δ) Fr
      (f4ThreeCols δ f4ThreeB f4ThreeA '' {i : Fin Tag.F4.rank | (i : ℕ) < 2})) :=
    Nat.finite_of_card_ne_zero (by rw [hB]; exact hne)
  rw [f4ThreeZ, card_sup_of_inf_eq_bot' (f4Three_inf_eq_bot δ hδ Fr), hA, hB]
  exact (sq _).symm

omit [IsAlgClosed L] in
theorem f4Three_zpow_eq_one (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.F4.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (f4ThreeM δ) Fr) (i : Fin Tag.F4.rank) :
    a i ^ ((q : ℤ) ^ 2 + δ * (q : ℤ) + 1) = 1 := by
  have h := rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr ha (f4ThreeP δ) (Pi.single i 1)
  rw [f4Three_P_zero δ hδ, rootChar_zero, CTTorus.rootChar_single, f4ThreeP_eval] at h
  exact h.symm

omit [IsAlgClosed L] in
theorem f4Three_orderOf_dvd (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {a : Fin Tag.F4.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (f4ThreeM δ) Fr) :
    orderOf a ∣ ((q : ℤ) ^ 2 + δ * (q : ℤ) + 1).natAbs := by
  apply orderOf_dvd_of_pow_eq_one
  funext i
  have h := f4Three_zpow_eq_one δ hδ Fr hFr ha i
  rw [Pi.pow_apply, Pi.one_apply]
  rcases Int.natAbs_eq ((q : ℤ) ^ 2 + δ * (q : ℤ) + 1) with hF | hF
  · rw [hF] at h
    simpa using h
  · rw [hF, zpow_neg, inv_eq_one] at h
    simpa using h

omit
  [IsAlgClosed L] in
theorem f4Three_eigencolumn (δ : ℤ) (hδ : δ = 1 ∨ δ = -1) (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ x, Fr x = x ^ q) {p : ℕ} (hp : p.Prime) {a : Fin Tag.F4.rank → Lˣ}
    (ha : a ∈ fixedCharTuples (f4ThreeM δ) Fr) (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ z : Fin Tag.F4.rank → ZMod p, z ≠ 0 ∧
      (dualMatrix (ZMod p) f4W3).mulVec z = ((δ : ZMod p) * (q : ZMod p)) • z ∧
        rootCharKernel a = rootKernel z := by
  obtain ⟨z, hz0, hzM, hzk⟩ :=
    exists_eigencolumn_of_mem_fixedCharTuples (f4ThreeM δ) Fr hFr hp ha hap ha1
  refine ⟨z, hz0, ?_, by rw [hzk]; rfl⟩
  have hM : ((f4ThreeM δ).map (Int.cast : ℤ → ZMod p))ᵀ =
      (δ : ZMod p) • dualMatrix (ZMod p) f4W3 := by
    ext i j
    simp only [f4ThreeM, dualMatrix, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      smul_eq_mul, Int.cast_mul]
  rw [hM, Matrix.smul_mulVec] at hzM
  have hδ2 : (δ : ZMod p) * (δ : ZMod p) = 1 := by
    rcases hδ with h | h <;> rw [h] <;> simp
  calc (dualMatrix (ZMod p) f4W3).mulVec z
      = ((δ : ZMod p) * (δ : ZMod p)) • (dualMatrix (ZMod p) f4W3).mulVec z := by
        rw [hδ2, one_smul]
    _ = (δ : ZMod p) • ((δ : ZMod p) • (dualMatrix (ZMod p) f4W3).mulVec z) := by
        rw [mul_smul]
    _ = (δ : ZMod p) • ((q : ZMod p) • z) := by rw [hzM]
    _ = ((δ : ZMod p) * (q : ZMod p)) • z := by rw [mul_smul]

end Fixed

end CFSG.RankThree.PartOne.KF4
