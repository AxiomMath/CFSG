module

public import CFSG.RankThree.Lattice.SteinbergBITrialityCoxeter
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.RelativeWeylTwist

public section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix

@[expose] def trialityRho : Equiv.Perm (Fin Tag.D4.rank) := TwistTag.D4.perm

@[expose] def trialityP : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ := trialityPermMat

@[expose] def trialityC : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ := trialityCoxeter

@[expose] def trialityA : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ := trialityC ^ 4

@[expose] def trialityAMat : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  !![0, 0, 0, -1; 0, -1, 1, -1; 1, -1, 0, -1; 1, 0, 0, -1]

@[expose] def trialityU : Fin 4 → Fin Tag.D4.rank → ℤ :=
  ![![-1, -1, -2, -1], ![-1, -1, -1, -1], ![-1, 0, -1, -1], ![0, -1, -1, 0]]

@[expose] def trialitySigma (i : Fin 4) : Set (Fin Tag.D4.rank → ℤ) :=
  {v | ∃ k < 3, v = (trialityA ^ k) *ᵥ trialityU i ∨ v = -((trialityA ^ k) *ᵥ trialityU i)}

@[expose] def trialityStdA2 : Set (Fin Tag.D4.rank → ℤ) :=
  {Pi.single 0 1, Pi.single 2 1, Pi.single 0 1 + Pi.single 2 1, -Pi.single 0 1, -Pi.single 2 1,
    -(Pi.single 0 1 + Pi.single 2 1)}

@[expose] def trialityColMat (x₁ x₂ x₃ x₄ : Fin Tag.D4.rank → ℤ) :
    Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ :=
  Matrix.of fun r k => (![x₁, x₂, x₃, x₄] : Fin 4 → Fin Tag.D4.rank → ℤ) k r

@[expose] def trialityRefl (β x : Fin Tag.D4.rank → ℤ) : Fin Tag.D4.rank → ℤ :=
  x - corootPair β x • β

@[expose] def trialityRot (i : Fin 4) (x : Fin Tag.D4.rank → ℤ) : Fin Tag.D4.rank → ℤ :=
  trialityRefl (trialityU i) (trialityRefl (trialityAMat *ᵥ trialityU i) x)

@[expose] def trialitySigmaList (i : Fin 4) : List (Fin Tag.D4.rank → ℤ) :=
  [trialityU i, trialityAMat *ᵥ trialityU i, trialityAMat *ᵥ (trialityAMat *ᵥ trialityU i),
    -trialityU i, -(trialityAMat *ᵥ trialityU i), -(trialityAMat *ᵥ (trialityAMat *ᵥ trialityU i))]

@[expose] def trialityWord : Fin 4 → List (Fin Tag.D4.rank) :=
  ![[2, 3, 1, 2, 0], [1, 2, 3, 2, 0], [3, 2, 0], [1, 0, 2, 1, 0]]

@[expose] def trialityWordFour : List (Fin Tag.D4.rank) := [2, 0, 2, 1, 2, 3, 2, 0]

@[expose] def trialityWordSix : List (Fin Tag.D4.rank) := [2, 0, 2, 1, 2, 3, 2, 0, 2, 1, 2, 3]

theorem trialityP_mulVec (v : Fin Tag.D4.rank → ℤ) :
    trialityP *ᵥ v = permLattice trialityRho v :=
  trialityPermMat_mulVec v

theorem trialityC_eq_mul : trialityC = reflMat Tag.D4 2 * reflMat Tag.D4 0 * trialityP :=
  rfl

theorem trialityC_eq : trialityC = toMat Tag.D4.rank trialityCoxeterList :=
  trialityCoxeter_eq

theorem trialityC_pow_six : trialityC ^ 6 = -1 :=
  trialityCoxeter_pow_six

theorem trialityC_relation : trialityC ^ 4 - trialityC ^ 2 + 1 = 0 :=
  trialityCoxeter_relation

theorem trialityA_eq : trialityA = trialityAMat := by
  rw [trialityA, trialityC_eq, ← toMat_lpow]
  decide +kernel

theorem trialityA_sq_add : trialityA ^ 2 + trialityA + 1 = 0 := by
  have h8 : trialityA ^ 2 = -trialityC ^ 2 := by
    rw [trialityA, ← pow_mul, show 4 * 2 = 6 + 2 from rfl, pow_add, trialityC_pow_six,
      neg_one_mul]
  rw [h8, ← trialityC_relation, trialityA]
  abel

theorem trialityC_pow_ten : trialityC ^ 10 = -trialityA := by
  rw [show 10 = 6 + 4 from rfl, pow_add, trialityC_pow_six, neg_one_mul, trialityA]

theorem wordMat_mulVec_eq_foldr (τ : Tag) (ω : List (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    wordMat τ ω *ᵥ v = ω.foldr (reflect τ) v := by
  induction ω with
  | nil => rw [wordMat_nil, one_mulVec, List.foldr_nil]
  | cons i ω ih => rw [wordMat_cons, ← mulVec_mulVec, ih, reflMat_mulVec, List.foldr_cons]

theorem trialityAMat_eq_wordMat :
    wordMat Tag.D4 trialityWordFour * trialityP = trialityAMat ∧
      wordMat Tag.D4 (trialityWordSix ++ trialityWordFour) * trialityP = -trialityAMat := by
  rw [wordMat_eq_toMat Tag.D4 trialityWordFour rfl,
    wordMat_eq_toMat Tag.D4 (trialityWordSix ++ trialityWordFour) rfl,
    show trialityP = toMat Tag.D4.rank [[0, 0, 0, 1], [1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0]] by
      decide +kernel, ← toMat_lmul, ← toMat_lmul]
  decide +kernel

theorem exists_smul_trialityRho {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ w : WeylGroup Tag.D4, ∀ v, (ε • trialityA) *ᵥ v = w • permLattice trialityRho v := by
  have key : ∀ (ω : List (Fin Tag.D4.rank)) (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ),
      wordMat Tag.D4 ω * trialityP = M →
        ∀ v, M *ᵥ v = (coxeterSystem Tag.D4).wordProd ω • permLattice trialityRho v := by
    intro ω M hM v
    rw [← hM, ← mulVec_mulVec, trialityP_mulVec, wordMat_mulVec_eq_foldr, wordProd_smul]
  rcases hε with rfl | rfl
  · refine ⟨(coxeterSystem Tag.D4).wordProd trialityWordFour, fun v => ?_⟩
    rw [one_smul, trialityA_eq]
    exact key _ _ trialityAMat_eq_wordMat.1 v
  · refine ⟨(coxeterSystem Tag.D4).wordProd (trialityWordSix ++ trialityWordFour), fun v => ?_⟩
    rw [neg_one_smul, trialityA_eq]
    exact key _ _ trialityAMat_eq_wordMat.2 v

theorem mem_trialitySigma {i : Fin 4} {v : Fin Tag.D4.rank → ℤ} :
    v ∈ trialitySigma i ↔ v ∈ trialitySigmaList i := by
  have h0 : (trialityA ^ 0) *ᵥ trialityU i = trialityU i := by rw [pow_zero, one_mulVec]
  have h1 : (trialityA ^ 1) *ᵥ trialityU i = trialityAMat *ᵥ trialityU i := by
    rw [pow_one, trialityA_eq]
  have h2 : (trialityA ^ 2) *ᵥ trialityU i = trialityAMat *ᵥ (trialityAMat *ᵥ trialityU i) := by
    rw [pow_two, trialityA_eq, mulVec_mulVec]
  simp only [trialitySigma, Set.mem_ofPred_eq, trialitySigmaList, List.mem_cons, List.mem_nil_iff,
    or_false]
  constructor
  · rintro ⟨k, hk, h⟩
    interval_cases k
    · rw [h0] at h
      tauto
    · rw [h1] at h
      tauto
    · rw [h2] at h
      tauto
  · rintro (h | h | h | h | h | h)
    · exact ⟨0, by norm_num, Or.inl (h.trans h0.symm)⟩
    · exact ⟨1, by norm_num, Or.inl (h.trans h1.symm)⟩
    · exact ⟨2, by norm_num, Or.inl (h.trans h2.symm)⟩
    · exact ⟨0, by norm_num, Or.inr (by rw [h, h0])⟩
    · exact ⟨1, by norm_num, Or.inr (by rw [h, h1])⟩
    · exact ⟨2, by norm_num, Or.inr (by rw [h, h2])⟩

theorem trialitySigma_cover :
    ∀ l ∈ Tag.D4.artifactRoots, ∃ i : Fin 4, toVec Tag.D4.rank l ∈ trialitySigmaList i := by
  decide +kernel

theorem trialitySigma_isRoot :
    ∀ i : Fin 4, ∀ v ∈ trialitySigmaList i, List.ofFn v ∈ Tag.D4.artifactRoots := by
  decide +kernel

theorem trialitySigma_disjoint :
    ∀ i j : Fin 4, i ≠ j → ∀ v ∈ trialitySigmaList i, v ∉ trialitySigmaList j := by
  decide +kernel

theorem trialitySigma_add : ∀ i : Fin 4, ∀ α ∈ trialitySigmaList i, ∀ β ∈ trialitySigmaList i,
    List.ofFn (α + β) ∈ Tag.D4.artifactRoots → α + β ∈ trialitySigmaList i := by
  decide +kernel

theorem trialitySigma_refl : ∀ i : Fin 4, ∀ α ∈ trialitySigmaList i, ∀ β ∈ trialitySigmaList i,
    trialityRefl β α ∈ trialitySigmaList i := by
  decide +kernel

theorem trialitySigma_iform_ne : ∀ i : Fin 4, ∀ α ∈ trialitySigmaList i,
    ∀ β ∈ trialitySigmaList i, iform α β ≠ 0 := by
  decide +kernel

theorem trialityU_data : ∀ i : Fin 4,
    iform (trialityU i) (trialityU i) = 2 ∧
      iform (trialityAMat *ᵥ trialityU i) (trialityAMat *ᵥ trialityU i) = 2 ∧
      iform (trialityU i) (trialityAMat *ᵥ trialityU i) = -1 ∧
      trialityAMat *ᵥ (trialityAMat *ᵥ trialityU i) =
        -(trialityU i + trialityAMat *ᵥ trialityU i) := by
  decide +kernel

theorem trialityWord_single : ∀ i : Fin 4,
    (trialityWord i).foldr (reflect Tag.D4) (Pi.single 0 1) = trialityU i ∧
      (trialityWord i).foldr (reflect Tag.D4) (Pi.single 2 1) = trialityAMat *ᵥ trialityU i := by
  decide +kernel

theorem trialityRot_check : ∀ i : Fin 4,
    (∀ j : Fin Tag.D4.rank,
      trialityRot i (trialityRot i (trialityRot i (Pi.single j 1))) = Pi.single j 1) ∧
      trialityRot i (trialityU i) ≠ trialityU i := by
  decide +kernel

theorem trialitySigma_rot_check : ∀ ε ∈ [(1 : ℤ), -1], ∀ i : Fin 4, ∀ x ∈ trialitySigmaList i,
    (ε • trialityAMat) *ᵥ x ∈ trialitySigmaList i ∧
      (ε • trialityAMat) *ᵥ x = ε • trialityRot i x := by
  decide +kernel

theorem trialityColMat_det_e₁e₂ : ∀ ε ∈ [(1 : ℤ), -1],
    laplaceDet Tag.D4.rank (trialityColMat (Pi.single 0 1) ((ε • trialityAMat) *ᵥ Pi.single 0 1)
      (Pi.single 1 1) ((ε • trialityAMat) *ᵥ Pi.single 1 1)) = -1 := by
  decide +kernel

theorem trialityColMat_det_check : ∀ ε ∈ [(1 : ℤ), -1], ∀ l ∈ Tag.D4.artifactRoots,
    ∀ l' ∈ Tag.D4.artifactRoots,
      laplaceDet Tag.D4.rank (trialityColMat (toVec _ l) ((ε • trialityAMat) *ᵥ toVec _ l)
          (toVec _ l') ((ε • trialityAMat) *ᵥ toVec _ l')) =
        if ∃ i : Fin 4, toVec Tag.D4.rank l ∈ trialitySigmaList i ∧
          toVec Tag.D4.rank l' ∈ trialitySigmaList i then 0 else -1 := by
  decide +kernel

theorem isRoot_of_mem_trialitySigmaList {i : Fin 4} {v : Fin Tag.D4.rank → ℤ}
    (h : v ∈ trialitySigmaList i) : IsRoot Tag.D4 v :=
  isRoot_iff_mem_artifactRoots.2 (trialitySigma_isRoot i v h)

theorem isRoot_trialityU (i : Fin 4) :
    IsRoot Tag.D4 (trialityU i) ∧ IsRoot Tag.D4 (trialityA *ᵥ trialityU i) := by
  rw [trialityA_eq]
  exact ⟨isRoot_of_mem_trialitySigmaList (i := i) List.mem_cons_self,
    isRoot_of_mem_trialitySigmaList (i := i) (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem isRoot_eq_iUnion_trialitySigma : {v | IsRoot Tag.D4 v} = ⋃ i, trialitySigma i := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hv
    obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hv
    obtain ⟨i, hi⟩ := trialitySigma_cover l hl
    exact ⟨i, mem_trialitySigma.2 hi⟩
  · rintro ⟨i, hi⟩
    exact isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hi)

theorem pairwise_disjoint_trialitySigma :
    Pairwise fun i j => Disjoint (trialitySigma i) (trialitySigma j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro v hvi hvj
  exact trialitySigma_disjoint i j hij v (mem_trialitySigma.1 hvi) (mem_trialitySigma.1 hvj)

theorem isRootComponent_trialitySigma (i : Fin 4) : IsRootComponent (trialitySigma i) where
  isRoot α hα := isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hα)
  neg_mem α hα := by
    obtain ⟨k, hk, h | h⟩ := hα
    · exact ⟨k, hk, Or.inr (by rw [h])⟩
    · exact ⟨k, hk, Or.inl (by rw [h, neg_neg])⟩
  add_mem α hα β hβ hroot := mem_trialitySigma.2 (trialitySigma_add i α
    (mem_trialitySigma.1 hα) β (mem_trialitySigma.1 hβ) (isRoot_iff_mem_artifactRoots.1 hroot))
  reflection_mem α hα β hβ := by
    rw [rootReflection_smul (isRoot_of_mem_trialitySigmaList (mem_trialitySigma.1 hβ))]
    exact mem_trialitySigma.2
      (trialitySigma_refl i α (mem_trialitySigma.1 hα) β (mem_trialitySigma.1 hβ))
  irreducible S hS hperp := by
    by_cases hne : S = ∅
    · exact Or.inl hne
    right
    obtain ⟨α, hα⟩ := Set.nonempty_iff_ne_empty.2 hne
    refine Set.Subset.antisymm hS fun β hβ => ?_
    by_contra hβS
    exact trialitySigma_iform_ne i α (mem_trialitySigma.1 (hS hα)) β (mem_trialitySigma.1 hβ)
      (hperp α hα β hβ hβS)

theorem trialitySigma_eq_A2 (i : Fin 4) :
    trialitySigma i = {trialityU i, trialityA *ᵥ trialityU i,
      trialityU i + trialityA *ᵥ trialityU i, -trialityU i, -(trialityA *ᵥ trialityU i),
      -(trialityU i + trialityA *ᵥ trialityU i)} := by
  ext v
  rw [mem_trialitySigma, trialityA_eq]
  simp only [trialitySigmaList, List.mem_cons, List.mem_nil_iff, or_false, Set.mem_insert_iff,
    Set.mem_singleton_iff, (trialityU_data i).2.2.2, neg_neg]
  tauto

theorem exists_smul_trialityStdA2 (i : Fin 4) :
    ∃ w : WeylGroup Tag.D4, w • Pi.single 0 1 = trialityU i ∧
      w • Pi.single 2 1 = trialityA *ᵥ trialityU i ∧
        (w • ·) '' trialityStdA2 = trialitySigma i := by
  have h₁ : (coxeterSystem Tag.D4).wordProd (trialityWord i) •
      (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) = trialityU i := by
    rw [wordProd_smul]
    exact (trialityWord_single i).1
  have h₃ : (coxeterSystem Tag.D4).wordProd (trialityWord i) •
      (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) = trialityA *ᵥ trialityU i := by
    rw [wordProd_smul, trialityA_eq]
    exact (trialityWord_single i).2
  refine ⟨_, h₁, h₃, ?_⟩
  rw [trialitySigma_eq_A2, trialityStdA2]
  simp only [Set.image_insert_eq, Set.image_singleton, smul_add, smul_neg, h₁, h₃]

theorem trialityColMat_det {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {u v : Fin Tag.D4.rank → ℤ}
    (hu : IsRoot Tag.D4 u) (hv : IsRoot Tag.D4 v) :
    ((∃ i, u ∈ trialitySigma i ∧ v ∈ trialitySigma i) →
        (trialityColMat u ((ε • trialityA) *ᵥ u) v ((ε • trialityA) *ᵥ v)).det = 0) ∧
      ((¬∃ i, u ∈ trialitySigma i ∧ v ∈ trialitySigma i) →
        (trialityColMat u ((ε • trialityA) *ᵥ u) v ((ε • trialityA) *ᵥ v)).det = -1) := by
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hu
  obtain ⟨l', hl', rfl⟩ := isRoot_iff_exists_mem.1 hv
  have hε' : ε ∈ [(1 : ℤ), -1] := by rcases hε with rfl | rfl <;> simp
  have h := trialityColMat_det_check ε hε' l hl l' hl'
  simp only [mem_trialitySigma]
  rw [← laplaceDet_eq_det, trialityA_eq, h]
  exact ⟨fun hi => by simp [hi], fun hi => by simp [hi]⟩

theorem trialityColMat_det_single {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (trialityColMat (Pi.single 0 1) ((ε • trialityA) *ᵥ Pi.single 0 1) (Pi.single 1 1)
      ((ε • trialityA) *ᵥ Pi.single 1 1)).det = -1 := by
  have hε' : ε ∈ [(1 : ℤ), -1] := by rcases hε with rfl | rfl <;> simp
  rw [← laplaceDet_eq_det, trialityA_eq]
  exact trialityColMat_det_e₁e₂ ε hε'

theorem trialityA_eps_sq_add {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    (ε • trialityA) ^ 2 + ε • (ε • trialityA) + 1 = 0 := by
  rcases hε with rfl | rfl
  · rw [one_smul, one_smul, trialityA_sq_add]
  · rw [neg_one_smul, neg_one_smul, neg_neg, neg_sq, trialityA_sq_add]

theorem rootReflection_mul_smul_eq_trialityRot (i : Fin 4) (x : Fin Tag.D4.rank → ℤ) :
    (rootReflection (trialityU i) * rootReflection (trialityA *ᵥ trialityU i)) • x =
      trialityRot i x := by
  rw [mul_smul, rootReflection_smul (isRoot_trialityU i).2,
    rootReflection_smul (isRoot_trialityU i).1, trialityA_eq]
  rfl

theorem orderOf_trialityRotation (i : Fin 4) :
    orderOf (rootReflection (trialityU i) * rootReflection (trialityA *ᵥ trialityU i)) = 3 := by
  have key : ∀ g : WeylGroup Tag.D4, (∀ x, g • x = trialityRot i x) → orderOf g = 3 := by
    intro g hg
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · refine ext_single fun j => ?_
      rw [pow_three, mul_smul, mul_smul, hg, hg, hg, one_smul]
      exact (trialityRot_check i).1 j
    · apply (trialityRot_check i).2
      rw [← hg, h1, one_smul]
  exact key _ (rootReflection_mul_smul_eq_trialityRot i)

theorem trialitySigma_smul {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (i : Fin 4)
    {x : Fin Tag.D4.rank → ℤ} (hx : x ∈ trialitySigma i) :
    (ε • trialityA) *ᵥ x ∈ trialitySigma i ∧
      (ε • trialityA) *ᵥ x =
        ε • ((rootReflection (trialityU i) * rootReflection (trialityA *ᵥ trialityU i)) • x) := by
  have hε' : ε ∈ [(1 : ℤ), -1] := by rcases hε with rfl | rfl <;> simp
  rw [mem_trialitySigma] at hx ⊢
  rw [rootReflection_mul_smul_eq_trialityRot, trialityA_eq]
  exact trialitySigma_rot_check ε hε' i x hx

theorem triality_three_six_unimodular_A2_root_partition :
    trialityC = reflMat Tag.D4 2 * reflMat Tag.D4 0 * trialityP ∧
    (∀ v, trialityP *ᵥ v = permLattice trialityRho v) ∧ trialityA = trialityC ^ 4 ∧
    trialityA = !![0, 0, 0, -1; 0, -1, 1, -1; 1, -1, 0, -1; 1, 0, 0, -1] ∧
    trialityA ^ 2 + trialityA + 1 = 0 ∧
    (1 : ℤ) • trialityA = trialityC ^ 4 ∧ (-1 : ℤ) • trialityA = trialityC ^ 10 ∧
    {v | IsRoot Tag.D4 v} = ⋃ i, trialitySigma i ∧
    (Pairwise fun i j => Disjoint (trialitySigma i) (trialitySigma j)) ∧
    (∀ i, IsRootComponent (trialitySigma i) ∧
      trialitySigma i = {trialityU i, trialityA *ᵥ trialityU i,
        trialityU i + trialityA *ᵥ trialityU i, -trialityU i, -(trialityA *ᵥ trialityU i),
        -(trialityU i + trialityA *ᵥ trialityU i)} ∧
      iform (trialityU i) (trialityU i) = 2 ∧
      iform (trialityA *ᵥ trialityU i) (trialityA *ᵥ trialityU i) = 2 ∧
      iform (trialityU i) (trialityA *ᵥ trialityU i) = -1 ∧
      ∃ w : WeylGroup Tag.D4, w • Pi.single 0 1 = trialityU i ∧
        w • Pi.single 2 1 = trialityA *ᵥ trialityU i ∧
          (w • ·) '' trialityStdA2 = trialitySigma i) ∧
    (∀ u v, IsRoot Tag.D4 u → IsRoot Tag.D4 v →
      ((∃ i, u ∈ trialitySigma i ∧ v ∈ trialitySigma i) →
          (trialityColMat u (trialityA *ᵥ u) v (trialityA *ᵥ v)).det = 0) ∧
        ((¬∃ i, u ∈ trialitySigma i ∧ v ∈ trialitySigma i) →
          (trialityColMat u (trialityA *ᵥ u) v (trialityA *ᵥ v)).det = -1)) ∧
    ∀ ε : ℤ, ε = 1 ∨ ε = -1 →
      (∃ w : WeylGroup Tag.D4, ∀ v, (ε • trialityA) *ᵥ v = w • permLattice trialityRho v) ∧
      (ε • trialityA) ^ 2 + ε • (ε • trialityA) + 1 = 0 ∧
      (trialityColMat (Pi.single 0 1) ((ε • trialityA) *ᵥ Pi.single 0 1) (Pi.single 1 1)
        ((ε • trialityA) *ᵥ Pi.single 1 1)).det = -1 ∧
      (∀ u v, IsRoot Tag.D4 u → IsRoot Tag.D4 v →
        ((∃ i, u ∈ trialitySigma i ∧ v ∈ trialitySigma i) →
            (trialityColMat u ((ε • trialityA) *ᵥ u) v ((ε • trialityA) *ᵥ v)).det = 0) ∧
          ((¬∃ i, u ∈ trialitySigma i ∧ v ∈ trialitySigma i) →
            (trialityColMat u ((ε • trialityA) *ᵥ u) v ((ε • trialityA) *ᵥ v)).det = -1)) ∧
      ∀ i, (∀ x ∈ trialitySigma i, (ε • trialityA) *ᵥ x ∈ trialitySigma i ∧
          (ε • trialityA) *ᵥ x =
            ε • ((rootReflection (trialityU i) * rootReflection (trialityA *ᵥ trialityU i)) • x)) ∧
        orderOf (rootReflection (trialityU i) * rootReflection (trialityA *ᵥ trialityU i)) = 3 := by
  refine ⟨trialityC_eq_mul, trialityP_mulVec, rfl, trialityA_eq, trialityA_sq_add,
    by rw [one_smul, trialityA], by rw [neg_one_smul, trialityC_pow_ten],
    isRoot_eq_iUnion_trialitySigma, pairwise_disjoint_trialitySigma, fun i => ?_,
    fun u v hu hv => ?_, fun ε hε => ⟨exists_smul_trialityRho hε, trialityA_eps_sq_add hε,
      trialityColMat_det_single hε, fun u v hu hv => trialityColMat_det hε hu hv, fun i =>
        ⟨fun x hx => trialitySigma_smul hε i hx, orderOf_trialityRotation i⟩⟩⟩
  · obtain ⟨h₁, h₂, h₃, -⟩ := trialityU_data i
    rw [trialityA_eq]
    refine ⟨isRootComponent_trialitySigma i, ?_, h₁, h₂, h₃, ?_⟩
    · rw [← trialityA_eq]
      exact trialitySigma_eq_A2 i
    · rw [← trialityA_eq]
      exact exists_smul_trialityStdA2 i
  · simpa only [one_smul] using trialityColMat_det (Or.inl rfl) hu hv

end CFSG.RankThree.Lattice
