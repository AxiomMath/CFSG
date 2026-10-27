module

public import CFSG.RankThree.PartOne.TCX.E.AnModel
public import CFSG.RankThree.Classical2.TwistedE6Phi3A2A2
public import CFSG.RankThree.PartOne.KE.ConjRootSpan

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Matrix CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.KLCE
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open CFSG.RankThree.E6 (chain13 chain56 support13 support56 mem_support13 mem_support56 e6Index
  a2Equiv₁ a2Equiv₂ a2Rep₁ a2Rep₂ a2Mat₁ a2Mat₂ coe_a2Rep₁ coe_a2Rep₂ a2Equiv₁_apply
  a2Equiv₂_apply e6TorusPair e6TorusPair_mem_subsystemGroup e6TorusPair_mem_torusGroup
  a2Mat₁_torus a2Mat₂_torus e6RootVec isRoot_iff_exists_e6RootVec chainRoot chainRoot_swap)

open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Weights

variable {τ : Tag}

@[expose] def chainWeight {n : ℕ} (ι : Fin n → Fin τ.rank) (i : Fin (n + 1)) :
    Fin τ.rank → ℤ :=
  fun l => -∑ k : Fin n, (if (k : ℕ) < i then 1 else 0) * (if ι k = l then 1 else 0)

theorem chainRoot_eq_weight_sub {n : ℕ} (ι : Fin n → Fin τ.rank) (i j : Fin (n + 1)) :
    chainRoot ι i j = chainWeight ι i - chainWeight ι j := by
  funext l
  simp only [chainRoot, chainWeight, Pi.sub_apply]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : ι k = l
  · simp only [h, ite_true, mul_one]
    split_ifs <;> simp_all <;> omega
  · simp [h]

end Weights

section Roots

theorem exists_chainRoot13_of_support : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2) → e6RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot chain13 k l = e6RootVec m := by
  decide +kernel

theorem exists_chainRoot56_of_support : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 4 ∨ i = e6Index 5) → e6RootVec m i = 0) →
      ∃ k l : Fin 3, k ≠ l ∧ chainRoot chain56 k l = e6RootVec m := by
  decide +kernel

end Roots

section Std


structure A2Std (J : Set (Fin Tag.E6.rank)) (ι : Fin 2 → Fin Tag.E6.rank) where
  ρ : ∀ (L : Type) [Field L], SL(3, L) →* ModGL Tag.E6 L
  inj : ∀ (L : Type) [Field L], Function.Injective (ρ L)
  range : ∀ (L : Type) [Field L], (ρ L).range = subsystemGroup Tag.E6 L J
  roots : ∀ α : Fin Tag.E6.rank → ℤ, α ∈ parabolicRoots Tag.E6 J ↔
    ∃ i j : Fin 3, i ≠ j ∧ α = chainRoot ι i j
  gen : ∀ (L : Type) [Field L] (i j : Fin 3) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
    ρ L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot ι i j) ((ε : L) * t)
  diag : ∀ (L : Type) [Field L] (A : SL(3, L)),
    (∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) → ρ L A ∈ torusGroup Tag.E6 L

section Std13

variable (L : Type) [Field L]

@[expose] def e6rhoA2₁ : SL(3, L) →* ModGL Tag.E6 L :=
  (subsystemGroup Tag.E6 L support13).subtype.comp (a2Equiv₁ L).symm.toMonoidHom

variable {L}

theorem e6rhoA2₁_injective : Function.Injective (e6rhoA2₁ L) :=
  Subtype.val_injective.comp (a2Equiv₁ L).symm.injective

theorem e6rhoA2₁_range : (e6rhoA2₁ L).range = subsystemGroup Tag.E6 L support13 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₁ L).symm X).2
  · intro hg
    exact ⟨a2Equiv₁ L ⟨g, hg⟩, by simp [e6rhoA2₁]⟩

theorem e6rhoA2₁_transvection {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, e6rhoA2₁ L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot chain13 i j) ((ε : L) * t) := by
  obtain ⟨s, hs, hρ⟩ := a2Mat₁_pinnedX_chainRoot13 (Ω := L) hij
  have hss : (s : L) * s = 1 := sign_mul_self hs
  refine ⟨⟨(s : L), (s : L), hss, hss⟩, fun t => ?_⟩
  have h : (a2Equiv₁ L).symm (Matrix.SpecialLinearGroup.transvection hij t) =
      ⟨pinnedX Tag.E6 L (chainRoot chain13 i j) ((s : L) * t),
        pinnedX_chainRoot13_mem hij _⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ, ← mul_assoc, hss, one_mul]
    rfl
  simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [h]

theorem e6rhoA2₁_diagonal (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    e6rhoA2₁ L A ∈ torusGroup Tag.E6 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
      ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  have hrep : a2Equiv₁ L ⟨e6TorusPair (e6Index 0) (e6Index 2) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ = A := by
    rw [a2Equiv₁_apply]
    apply Subtype.ext
    rw [coe_a2Rep₁]
    change a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) ua ub) = _
    rw [a2Mat₁_torus, hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hsymm : (a2Equiv₁ L).symm A = ⟨e6TorusPair (e6Index 0) (e6Index 2) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ := by
    rw [MulEquiv.symm_apply_eq, hrep]
  simp only [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [hsymm]
  exact e6TorusPair_mem_torusGroup _ _ ua ub

end Std13

section Std56

variable (L : Type) [Field L]

@[expose] def e6rhoA2₂ : SL(3, L) →* ModGL Tag.E6 L :=
  (subsystemGroup Tag.E6 L support56).subtype.comp (a2Equiv₂ L).symm.toMonoidHom

variable {L}

theorem e6rhoA2₂_injective : Function.Injective (e6rhoA2₂ L) :=
  Subtype.val_injective.comp (a2Equiv₂ L).symm.injective

theorem e6rhoA2₂_range : (e6rhoA2₂ L).range = subsystemGroup Tag.E6 L support56 := by
  ext g
  constructor
  · rintro ⟨X, rfl⟩
    exact ((a2Equiv₂ L).symm X).2
  · intro hg
    exact ⟨a2Equiv₂ L ⟨g, hg⟩, by simp [e6rhoA2₂]⟩

theorem e6rhoA2₂_transvection {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, e6rhoA2₂ L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (chainRoot chain56 i j) ((ε : L) * t) := by
  obtain ⟨s, hss, hρ⟩ := a2Mat₂_pinnedX_chainRoot56 (Ω := L) hij
  refine ⟨⟨s, s, hss, hss⟩, fun t => ?_⟩
  have h : (a2Equiv₂ L).symm (Matrix.SpecialLinearGroup.transvection hij t) =
      ⟨pinnedX Tag.E6 L (chainRoot chain56 i j) (s * t), pinnedX_chainRoot56_mem hij _⟩ := by
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₂_apply, coe_a2Rep₂, hρ, ← mul_assoc, hss, one_mul]
    rfl
  simp only [e6rhoA2₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [h]

theorem e6rhoA2₂_diagonal (A : SL(3, L))
    (hA : ∀ i j : Fin 3, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    e6rhoA2₂ L A ∈ torusGroup Tag.E6 L := by
  have hdiag : (A : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (A : Matrix (Fin 3) (Fin 3) L) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hA i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (A : Matrix (Fin 3) (Fin 3) L).det = 1 := A.2
  rw [hdiag, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
  have h0 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 ≠ 0 := fun h => by
    rw [h, zero_mul, zero_mul] at hdet
    exact zero_ne_one hdet
  have h01 : (A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1 ≠ 0 :=
    fun h => by
      rw [h, zero_mul] at hdet
      exact zero_ne_one hdet
  set ua : Lˣ := Units.mk0 _ h0 with hua
  set ub : Lˣ := Units.mk0 _ h01 with hub
  have h22 : (A : Matrix (Fin 3) (Fin 3) L) 2 2 =
      ((A : Matrix (Fin 3) (Fin 3) L) 0 0 * (A : Matrix (Fin 3) (Fin 3) L) 1 1)⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  have hrep : a2Equiv₂ L ⟨e6TorusPair (e6Index 4) (e6Index 5) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ = A := by
    rw [a2Equiv₂_apply]
    apply Subtype.ext
    rw [coe_a2Rep₂]
    change a2Mat₂ (e6TorusPair (e6Index 4) (e6Index 5) ua ub) = _
    rw [a2Mat₂_torus, hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hua, hub, Matrix.diagonal_apply_ne]
    rw [h22, _root_.mul_inv_rev]
  have hsymm : (a2Equiv₂ L).symm A = ⟨e6TorusPair (e6Index 4) (e6Index 5) ua ub,
      e6TorusPair_mem_subsystemGroup _ _ ua ub⟩ := by
    rw [MulEquiv.symm_apply_eq, hrep]
  simp only [e6rhoA2₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [hsymm]
  exact e6TorusPair_mem_torusGroup _ _ ua ub

end Std56

@[expose] def a2Std₁ : A2Std support13 chain13 where
  ρ L _ := e6rhoA2₁ L
  inj _ _ := e6rhoA2₁_injective
  range _ _ := e6rhoA2₁_range
  roots α := ⟨fun hα => by
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
    obtain ⟨k, l, hkl, h⟩ := exists_chainRoot13_of_support m
      (fun i hi => hα.2 i ((mem_support13 i).not.2 hi))
    exact ⟨k, l, hkl, h.symm⟩,
    fun ⟨i, j, hij, h⟩ => h ▸ chainRoot13_mem_parabolicRoots hij⟩
  gen _ _ _ _ hij := e6rhoA2₁_transvection hij
  diag _ _ A hA := e6rhoA2₁_diagonal A hA

@[expose] def a2Std₂ : A2Std support56 chain56 where
  ρ L _ := e6rhoA2₂ L
  inj _ _ := e6rhoA2₂_injective
  range _ _ := e6rhoA2₂_range
  roots α := ⟨fun hα => by
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
    obtain ⟨k, l, hkl, h⟩ := exists_chainRoot56_of_support m
      (fun i hi => hα.2 i ((mem_support56 i).not.2 hi))
    exact ⟨k, l, hkl, h.symm⟩,
    fun ⟨i, j, hij, h⟩ => h ▸ chainRoot56_mem_parabolicRoots hij⟩
  gen _ _ _ _ hij := e6rhoA2₂_transvection hij
  diag _ _ A hA := e6rhoA2₂_diagonal A hA

end Std

section Embedding

variable {J : Set (Fin Tag.E6.rank)} {ι : Fin 2 → Fin Tag.E6.rank}

@[expose] def A2Std.rhoV (std : A2Std J ι) (L : Type) [Field L] (v : WeylGroup Tag.E6) :
    SL(3, L) →* ModGL Tag.E6 L :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L v)).toMonoidHom.comp (std.ρ L)

theorem A2Std.rhoV_transvection (std : A2Std J ι) (L : Type) [Field L] (v : WeylGroup Tag.E6)
    {i j : Fin 3} (hij : i ≠ j) :
    ∃ ε : Lˣ, ∀ t : L, std.rhoV L v (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E6 L (v • chainRoot ι i j) ((ε : L) * t) := by
  obtain ⟨ε₀, h₀⟩ := std.gen L i j hij
  have hα : IsRoot Tag.E6 (chainRoot ι i j) := ((std.roots _).2 ⟨i, j, hij, rfl⟩).1
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v) hα
  have hπ : weylQuotientHom Tag.E6 L ⟨canonicalRep (coxeterSystem Tag.E6) L v,
      canonicalRep_mem_monomialSubgroup L v⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  refine ⟨μ * ε₀, fun t => ?_⟩
  simp only [A2Std.rhoV, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h₀, hμ, hπ, Units.val_mul, mul_assoc]

theorem A2Std.rhoV_torus (std : A2Std J ι) (L : Type) [Field L] (v : WeylGroup Tag.E6)
    (b : Fin Tag.E6.rank → Lˣ) (A : SL(3, L)) :
    rootDiagUnit Tag.E6 b * std.rhoV L v A * (rootDiagUnit Tag.E6 b)⁻¹ =
      std.rhoV L v (conjDiagn (fun i : Fin 3 => rootChar b (v • chainWeight ι i)) A) := by
  set d : Fin 3 → Lˣ := fun i => rootChar b (v • chainWeight ι i) with hd
  have h : (MulAut.conj (rootDiagUnit Tag.E6 b)).toMonoidHom.comp (std.rhoV L v) =
      (std.rhoV L v).comp (conjDiagnHom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := std.rhoV_transvection L v hij
    have hvα : IsRoot Tag.E6 (v • chainRoot ι i j) :=
      IsRoot.smul ((std.roots _).2 ⟨i, j, hij, rfl⟩).1 v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [hε, conjDiagn_transvection, hε, rootDiagUnit_conj_pinnedX b hvα]
    congr 1
    rw [chainRoot_eq_weight_sub, smul_sub, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun h A

@[expose] def A2Std.embedding (std : A2Std J ι) (v : WeylGroup Tag.E6) :
    AnEmbedding Tag.E6 (0 + 3) ((fun γ => v • γ) '' parabolicRoots Tag.E6 J) where
  ρ L _ := std.rhoV L v
  r i j := v • chainRoot ι i j
  mem x := ⟨fun ⟨α, hα, h⟩ => by
      obtain ⟨i, j, hij, rfl⟩ := (std.roots α).1 hα
      exact ⟨i, j, hij, h.symm⟩,
    fun ⟨i, j, hij, h⟩ => ⟨chainRoot ι i j, (std.roots _).2 ⟨i, j, hij, rfl⟩, h.symm⟩⟩
  isRoot i j hij := IsRoot.smul ((std.roots _).2 ⟨i, j, hij, rfl⟩).1 v
  neg i j := by rw [← smul_neg, chainRoot_swap ι i j]
  inj L _ := (MulAut.conj _).injective.comp (std.inj L)
  range L _ := by
    rw [A2Std.rhoV, MonoidHom.range_comp, std.range, subsystemGroup_eq_rootSpan,
      map_conj_rootSpan v (fun γ hγ => hγ.1)]
  gen L _ i j hij := std.rhoV_transvection L v hij
  tor L _ b := ⟨fun i => rootChar b (v • chainWeight ι i), fun A => std.rhoV_torus L v b A⟩
  diag L _ A hA := by
    simp only [A2Std.rhoV, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1 (std.diag L A hA)

end Embedding

end CFSG.RankThree.PartOne.TCX.E
