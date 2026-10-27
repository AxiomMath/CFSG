module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import CFSG.Open.StatedDefs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.RCKRP

open CFSG.StandardType.ClassicalPosition

open scoped Matrix

private lemma rck_commute_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {g : Matrix ι ι F}
    (hg : ∀ s ∈ S, (s : Matrix ι ι F) * g = g * (s : Matrix ι ι F))
    {ε : Matrix ι ι F} (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) :
    g * ε = ε * g := by
  have hgen : ∀ x ∈ (Units.val '' S : Set (Matrix ι ι F)), Commute g x := by
    rintro _ ⟨s, hs, rfl⟩
    change g * (s : Matrix ι ι F) = (s : Matrix ι ι F) * g
    exact (hg s hs).symm
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hε hgen).eq

private lemma rck_one_sub {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) :
    ε * (1 - ε) = 0 ∧ (1 - ε) * ε = 0 ∧ (1 - ε) * (1 - ε) = 1 - ε := by
  have h1 : ε * (1 - ε) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, h.eq, sub_self]
  have h2 : (1 - ε) * ε = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, h.eq, sub_self]
  have h3 : (1 - ε) * (1 - ε) = 1 - ε := by
    rw [Matrix.mul_sub, Matrix.mul_one, h2, sub_zero]
  exact ⟨h1, h2, h3⟩

private lemma rck_block_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {ε : Matrix ι ι F} (h : IsIdempotentElem ε) {p q : Matrix ι ι F}
    (hq : q * ε = ε * q) :
    (p * ε + (1 - ε)) * (q * ε + (1 - ε)) = (p * q) * ε + (1 - ε) := by
  obtain ⟨h1, h2, h3⟩ := rck_one_sub h
  have hq1 : (1 - ε) * q = q * (1 - ε) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hq]
  have hp1 : p * ε * (1 - ε) = 0 := by
    rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  have h1q : (1 - ε) * (q * ε) = 0 := by
    rw [← Matrix.mul_assoc, hq1, Matrix.mul_assoc, h2, Matrix.mul_zero]
  have hpq : (p * ε) * (q * ε) = (p * q) * ε := by
    rw [Matrix.mul_assoc p ε, ← Matrix.mul_assoc ε q ε, ← hq,
      Matrix.mul_assoc q ε ε, h.eq, ← Matrix.mul_assoc p q ε]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hpq, hp1, h1q, h3]
  abel

private lemma rck_inv_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (m : GL ι F) {ε : Matrix ι ι F}
    (hm : (m : Matrix ι ι F) * ε = ε * (m : Matrix ι ι F)) :
    ((m⁻¹ : GL ι F) : Matrix ι ι F) * ε =
      ε * ((m⁻¹ : GL ι F) : Matrix ι ι F) := by
  have hmm' : (m : Matrix ι ι F) * ((m⁻¹ : GL ι F) : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : ((m⁻¹ : GL ι F) : Matrix ι ι F) * (m : Matrix ι ι F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc ((m⁻¹ : GL ι F) : Matrix ι ι F) * ε
      = ((m⁻¹ : GL ι F) : Matrix ι ι F) * ε *
          ((m : Matrix ι ι F) * ((m⁻¹ : GL ι F) : Matrix ι ι F)) := by
        rw [hmm', Matrix.mul_one]
    _ = ((m⁻¹ : GL ι F) : Matrix ι ι F) * (ε * (m : Matrix ι ι F)) *
          ((m⁻¹ : GL ι F) : Matrix ι ι F) := by simp only [Matrix.mul_assoc]
    _ = ((m⁻¹ : GL ι F) : Matrix ι ι F) * ((m : Matrix ι ι F) * ε) *
          ((m⁻¹ : GL ι F) : Matrix ι ι F) := by rw [← hm]
    _ = ε * ((m⁻¹ : GL ι F) : Matrix ι ι F) := by
        rw [← Matrix.mul_assoc ((m⁻¹ : GL ι F) : Matrix ι ι F)
          (m : Matrix ι ι F) ε, hm'm, Matrix.one_mul]

private lemma rck_block_unit {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (hεi : IsIdempotentElem ε) (s' : GL ι F)
    (hcomm : (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F)) :
    ∃ s₁ : GL ι F, (s₁ : Matrix ι ι F) = (s' : Matrix ι ι F) * ε + (1 - ε) ∧
      ((s₁⁻¹ : GL ι F) : Matrix ι ι F) =
        ((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε) := by
  have hinv : ((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε =
      ε * ((s'⁻¹ : GL ι F) : Matrix ι ι F) := rck_inv_comm s' hcomm
  let M : Matrix ι ι F := (s' : Matrix ι ι F) * ε + (1 - ε)
  let M' : Matrix ι ι F := ((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε)
  have hMM' : M * M' = 1 := by
    dsimp only [M, M']
    rw [rck_block_mul hεi hinv, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    abel
  have hM'M : M' * M = 1 := by
    dsimp only [M, M']
    rw [rck_block_mul hεi hcomm, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    abel
  exact ⟨Units.mk M M' hMM' hM'M, rfl, rfl⟩

private lemma rck_block_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s'' ∈ S, Commute s s'') {ε : Matrix ι ι F}
    (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) (hεi : IsIdempotentElem ε)
    (s' : GL ι F) (hs' : ∀ s ∈ S, Commute s' s) {s₁ : GL ι F}
    (h₁ : (s₁ : Matrix ι ι F) = (s' : Matrix ι ι F) * ε + (1 - ε)) :
    s₁ ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) := by
  have hSε : ∀ s ∈ S, (s : Matrix ι ι F) * ε = ε * (s : Matrix ι ι F) := by
    intro s hs
    exact rck_commute_adjoin (g := (s : Matrix ι ι F))
      (fun t ht => (congrArg Units.val (hS s hs t ht).eq).symm) hε
  obtain ⟨h1, h2, h3⟩ := rck_one_sub hεi
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply Units.ext
    change (t : Matrix ι ι F) * (s₁ : Matrix ι ι F) =
      (s₁ : Matrix ι ι F) * (t : Matrix ι ι F)
    have hts' : (t : Matrix ι ι F) * (s' : Matrix ι ι F) =
        (s' : Matrix ι ι F) * (t : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg Units.val (hs' t ht).eq.symm
    have ht1 : (t : Matrix ι ι F) * (1 - ε) = (1 - ε) * (t : Matrix ι ι F) := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hSε t ht]
    rw [h₁]
    calc (t : Matrix ι ι F) * ((s' : Matrix ι ι F) * ε + (1 - ε))
        = ((t : Matrix ι ι F) * (s' : Matrix ι ι F)) * ε +
            (1 - ε) * (t : Matrix ι ι F) := by
          rw [Matrix.mul_add, Matrix.mul_assoc, ht1]
      _ = ((s' : Matrix ι ι F) * (t : Matrix ι ι F)) * ε +
            (1 - ε) * (t : Matrix ι ι F) := by rw [hts']
      _ = (s' : Matrix ι ι F) * ((t : Matrix ι ι F) * ε) +
            (1 - ε) * (t : Matrix ι ι F) := by rw [← Matrix.mul_assoc]
      _ = (s' : Matrix ι ι F) * (ε * (t : Matrix ι ι F)) +
            (1 - ε) * (t : Matrix ι ι F) := by rw [hSε t ht]
      _ = ((s' : Matrix ι ι F) * ε + (1 - ε)) * (t : Matrix ι ι F) := by
          rw [← Matrix.mul_assoc, Matrix.add_mul]
  · change (s₁ : Matrix ι ι F) * (1 - ε) = 1 - ε
    rw [h₁, Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_zero, zero_add, h3]

private lemma rck_block_order {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {ε : Matrix ι ι F} (hεi : IsIdempotentElem ε) (s' : GL ι F)
    (hcomm : (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F)) {s₁ : GL ι F}
    (h₁ : (s₁ : Matrix ι ι F) = (s' : Matrix ι ι F) * ε + (1 - ε)) :
    orderOf s₁ ∣ orderOf s' := by
  have hpow : ∀ k : ℕ, ((s₁ ^ k : GL ι F) : Matrix ι ι F) =
      (s' : Matrix ι ι F) ^ k * ε + (1 - ε) := by
    intro k
    induction k with
    | zero =>
        rw [pow_zero, Units.val_one, pow_zero, Matrix.one_mul]
        abel
    | succ k ih =>
        rw [pow_succ, Units.val_mul, ih, h₁, rck_block_mul hεi hcomm, ← pow_succ]
  have hval : (s' : Matrix ι ι F) ^ orderOf s' = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hord : s₁ ^ orderOf s' = 1 := by
    apply Units.ext
    rw [hpow (orderOf s'), hval, Matrix.one_mul]
    abel
  exact orderOf_dvd_of_pow_eq_one hord

private lemma rck_block_r_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {ε : Matrix ι ι F}
    (hε : ε ∈ Algebra.adjoin F (Units.val '' S)) (hεi : IsIdempotentElem ε)
    {s' : GL ι F} (hs'ε : (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F))
    {s₁ : GL ι F}
    (hinv : ((s₁⁻¹ : GL ι F) : Matrix ι ι F) =
      ((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε))
    {g : GL ι F} (hgcent : g ∈ Subgroup.centralizer S)
    (hgfix : (g : Matrix ι ι F) * (1 - ε) = 1 - ε) :
    Commute (s₁⁻¹ * s') g := by
  have hgε : (g : Matrix ι ι F) * ε = ε * (g : Matrix ι ι F) :=
    rck_commute_adjoin (g := (g : Matrix ι ι F))
      (fun t ht => congrArg Units.val (Subgroup.mem_centralizer_iff.mp hgcent t ht)) hε
  have hg1g : (1 - ε) * (g : Matrix ι ι F) = 1 - ε := by
    calc (1 - ε) * (g : Matrix ι ι F)
        = 1 * (g : Matrix ι ι F) - ε * (g : Matrix ι ι F) := by
          rw [Matrix.sub_mul]
      _ = (g : Matrix ι ι F) - ε * (g : Matrix ι ι F) := by rw [Matrix.one_mul]
      _ = (g : Matrix ι ι F) - (g : Matrix ι ι F) * ε := by rw [← hgε]
      _ = (g : Matrix ι ι F) * (1 - ε) := by rw [Matrix.mul_sub, Matrix.mul_one]
      _ = 1 - ε := hgfix
  have hs'ε1 : (1 - ε) * (s' : Matrix ι ι F) = (s' : Matrix ι ι F) * (1 - ε) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, ← hs'ε]
  let r : GL ι F := s₁⁻¹ * s'
  have hrval : (r : Matrix ι ι F) = ε + (s' : Matrix ι ι F) * (1 - ε) := by
    have h1 : (r : Matrix ι ι F) =
        ((s₁⁻¹ : GL ι F) : Matrix ι ι F) * (s' : Matrix ι ι F) := rfl
    rw [h1, hinv]
    calc (((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε + (1 - ε)) *
          (s' : Matrix ι ι F)
        = ((s'⁻¹ : GL ι F) : Matrix ι ι F) * (ε * (s' : Matrix ι ι F)) +
            (1 - ε) * (s' : Matrix ι ι F) := by
          rw [Matrix.add_mul, Matrix.mul_assoc]
      _ = ((s'⁻¹ : GL ι F) : Matrix ι ι F) *
            ((s' : Matrix ι ι F) * ε) + (1 - ε) * (s' : Matrix ι ι F) := by
          rw [← hs'ε]
      _ = (((s'⁻¹ : GL ι F) * s' : GL ι F) : Matrix ι ι F) * ε +
            (1 - ε) * (s' : Matrix ι ι F) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul]
      _ = ε + (1 - ε) * (s' : Matrix ι ι F) := by
          rw [inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = ε + (s' : Matrix ι ι F) * (1 - ε) := by rw [hs'ε1]
  have hs'11 : (s' : Matrix ι ι F) * (1 - ε) =
      (1 - ε) * ((s' : Matrix ι ι F) * (1 - ε)) := by
    rw [← Matrix.mul_assoc, hs'ε1, Matrix.mul_assoc, (rck_one_sub hεi).2.2]
  have hgs' : (g : Matrix ι ι F) * ((s' : Matrix ι ι F) * (1 - ε)) =
      (s' : Matrix ι ι F) * (1 - ε) := by
    have h := congrArg (fun x => (g : Matrix ι ι F) * x) hs'11
    rw [h, ← Matrix.mul_assoc, hgfix, ← hs'11]
  have hs'g : ((s' : Matrix ι ι F) * (1 - ε)) * (g : Matrix ι ι F) =
      (s' : Matrix ι ι F) * (1 - ε) := by
    rw [Matrix.mul_assoc, hg1g]
  change r * g = g * r
  apply Units.ext
  change (r : Matrix ι ι F) * (g : Matrix ι ι F) =
    (g : Matrix ι ι F) * (r : Matrix ι ι F)
  rw [hrval, Matrix.add_mul, Matrix.mul_add, hs'g, hgs', hgε]

theorem rckGLBlock_restrict {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} (hS : ∀ s ∈ S, ∀ s'' ∈ S, Commute s s'') {ε : Matrix ι ι F}
    (hε : ε ∈ Algebra.adjoin F (Units.val '' S))
    (hεi : IsIdempotentElem ε) (s' : GL ι F) (hs' : ∀ s ∈ S, Commute s' s) :
    (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F) ∧
      ∃ s₁ : GL ι F, (s₁ : Matrix ι ι F) = (s' : Matrix ι ι F) * ε + (1 - ε) ∧
        s₁ ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) ∧ orderOf s₁ ∣ orderOf s' ∧
        ∀ g ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε), s' * g * s'⁻¹ = s₁ * g * s₁⁻¹ := by
  have hs'ε : (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F) :=
    rck_commute_adjoin (g := (s' : Matrix ι ι F))
      (fun s hs => (congrArg Units.val (hs' s hs).eq).symm) hε
  obtain ⟨s₁, h₁, hinv⟩ := rck_block_unit hεi s' hs'ε
  have hmem : s₁ ∈ Subgroup.centralizer S ⊓ glFixing (1 - ε) :=
    rck_block_mem hS hε hεi s' hs' h₁
  refine ⟨hs'ε, s₁, h₁, hmem, rck_block_order hεi s' hs'ε h₁, ?_⟩
  intro g hg
  have hgcent : g ∈ Subgroup.centralizer S := (Subgroup.mem_inf.mp hg).1
  have hgfix : (g : Matrix ι ι F) * (1 - ε) = 1 - ε := (Subgroup.mem_inf.mp hg).2
  let r : GL ι F := s₁⁻¹ * s'
  have hcommr : Commute r g := rck_block_r_comm hε hεi hs'ε hinv hgcent hgfix
  have hs'eq : s' = s₁ * r := by
    dsimp only [r]
    group
  calc s' * g * s'⁻¹
      = (s₁ * r) * g * (r⁻¹ * s₁⁻¹) := by rw [hs'eq, mul_inv_rev]
    _ = s₁ * (r * g * r⁻¹) * s₁⁻¹ := by group
    _ = s₁ * g * s₁⁻¹ := by rw [hcommr.eq]; group

private lemma rck_J_isUnit_det {n : ℕ} {F : Type} [Field F] :
    IsUnit (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).det := by
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0
  have hJJ : J * J = -1 := by
    dsimp only [J]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
      Matrix.mul_neg, Matrix.neg_mul, neg_zero]
    rw [show (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Matrix.fromBlocks (-1) 0 0 (-1) by
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
      simp]
  have hunit : IsUnit J :=
    isUnit_iff_exists.mpr ⟨-J, by rw [Matrix.mul_neg, hJJ, neg_neg],
      by rw [Matrix.neg_mul, hJJ, neg_neg]⟩
  exact (Matrix.isUnit_iff_isUnit_det J).mp hunit

private lemma rck_adj_transpose_of {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {ε : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) G ε = ε) :
    εᵀ * G = G * ε := by
  have hGinv : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G hG
  have h := congrArg (fun x => G * x) hadj
  rw [formAdj] at h
  change G * (G⁻¹ * Matrix.transpose (ε.map (RingHom.id F)) * G) = G * ε at h
  have hmapid : ε.map (RingHom.id F) = ε := by
    ext i j
    simp
  rw [hmapid] at h
  have h2 : (G * G⁻¹) * (εᵀ * G) = G * ε := by
    calc (G * G⁻¹) * (εᵀ * G)
        = G * (G⁻¹ * εᵀ * G) := by noncomm_ring
      _ = G * ε := h
  rwa [hGinv, Matrix.one_mul] at h2

private lemma rck_adj_transpose {n : ℕ} {F : Type} [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hadj : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ε = ε) :
    εᵀ * (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε :=
  rck_adj_transpose_of rck_J_isUnit_det hadj

private lemma rck_block_symplectic {n : ℕ} {F : Type} [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hadj : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ε = ε)
    (hεi : IsIdempotentElem ε) {s' s₁ : GL (Fin n ⊕ Fin n) F}
    (hs' : s' ∈ CFSG.Open.StatedSp n F)
    (hcomm : (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (h₁ : (s₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) :
    s₁ ∈ CFSG.Open.StatedSp n F := by
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0
  let S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := (s' : Matrix _ _ F)
  let E : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := ε
  have htrans : Eᵀ * J = J * E := rck_adj_transpose hadj
  have hsub : (1 - E)ᵀ * J = J * (1 - E) := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.one_mul,
      htrans, Matrix.mul_sub, Matrix.mul_one]
  have hA : Sᵀ * J * S = J := by
    change (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
        (Matrix.fromBlocks 0 1 (-1) 0) * (s' : Matrix _ _ F) = Matrix.fromBlocks 0 1 (-1) 0
    exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp hs'
  obtain ⟨hE1, h1E, h11⟩ := rck_one_sub hεi
  have hA1 : S * (1 - E) = (1 - E) * S := by
    dsimp only [S, E]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hcomm]
  have ht1 : Eᵀ * Sᵀ * J * (S * E) = J * E := by
    rw [show Eᵀ * Sᵀ * J * (S * E) = Eᵀ * (Sᵀ * J * S) * E by noncomm_ring,
      hA, htrans, Matrix.mul_assoc]
    dsimp only [E]
    rw [hεi.eq]
  have ht2 : Eᵀ * Sᵀ * J * (1 - E) = 0 := by
    rw [show Eᵀ * Sᵀ * J * (1 - E) = Sᵀ * (Eᵀ * J) * (1 - E) by
      dsimp only [S, E]
      rw [← Matrix.transpose_mul, hcomm, Matrix.transpose_mul]
      noncomm_ring, htrans]
    rw [show Sᵀ * (J * E) * (1 - E) = Sᵀ * J * (E * (1 - E)) by noncomm_ring]
    dsimp only [E]
    rw [hE1, Matrix.mul_zero]
  have ht3 : (1 - E)ᵀ * J * (S * E) = 0 := by
    calc (1 - E)ᵀ * J * (S * E)
        = J * ((1 - E) * S) * E := by rw [hsub]; noncomm_ring
      _ = J * (S * (1 - E)) * E := by rw [← hA1]
      _ = J * S * ((1 - E) * E) := by noncomm_ring
      _ = 0 := by dsimp only [E]; rw [h1E, Matrix.mul_zero]
  have ht4 : (1 - E)ᵀ * J * (1 - E) = J * (1 - E) := by
    rw [hsub, show J * (1 - E) * (1 - E) = J * (1 - E) by
      rw [Matrix.mul_assoc]
      dsimp only [E]
      rw [h11]]
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, h₁]
  change (S * E + (1 - E))ᵀ * J * (S * E + (1 - E)) = J
  calc (S * E + (1 - E))ᵀ * J * (S * E + (1 - E))
      = (Eᵀ * Sᵀ + (1 - E)ᵀ) * J * (S * E + (1 - E)) := by
        rw [Matrix.transpose_add, Matrix.transpose_mul]
    _ = Eᵀ * Sᵀ * J * (S * E) + Eᵀ * Sᵀ * J * (1 - E) +
        (1 - E)ᵀ * J * (S * E) + (1 - E)ᵀ * J * (1 - E) := by noncomm_ring
    _ = J * E + 0 + 0 + J * (1 - E) := by rw [ht1, ht2, ht3, ht4]
    _ = J := by rw [add_zero, add_zero, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]

theorem rckGLBlock_restrict_mem_statedSp {n : ℕ} {F : Type} [Field F]
    {ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hadj : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) ε = ε)
    (hεi : IsIdempotentElem ε) {s' s₁ : GL (Fin n ⊕ Fin n) F}
    (hs' : s' ∈ CFSG.Open.StatedSp n F)
    (hcomm : (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (h₁ : (s₁ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (s' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) :
    s₁ ∈ CFSG.Open.StatedSp n F :=
  rck_block_symplectic hadj hεi hs' hcomm h₁


theorem rckGLBlock_restrict_isometry {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {σ : F →+* F} {G : Matrix ι ι F} (hG : IsUnit G.det) {ε : Matrix ι ι F}
    (hadj : formAdj σ G ε = ε) (hεi : IsIdempotentElem ε) {s' s₁ : GL ι F}
    (hs' : Matrix.transpose ((s' : Matrix ι ι F).map σ) * G * (s' : Matrix ι ι F) = G)
    (hcomm : (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F))
    (h₁ : (s₁ : Matrix ι ι F) = (s' : Matrix ι ι F) * ε + (1 - ε)) :
    Matrix.transpose ((s₁ : Matrix ι ι F).map σ) * G * (s₁ : Matrix ι ι F) = G := by
  have hεadj : formAdj σ G (1 - ε) = 1 - ε := by
    have h := Geo.formAdj_add σ G ε (1 - ε)
    rw [add_sub_cancel, Geo.formAdj_one σ hG, hadj] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h.symm
  have hinv : ((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε =
      ε * ((s'⁻¹ : GL ι F) : Matrix ι ι F) := rck_inv_comm s' hcomm
  have hs'inv : formAdj σ G (s' : Matrix ι ι F) = ((s'⁻¹ : GL ι F) : Matrix ι ι F) :=
    Geo.formAdj_eq_inv_of_isometry σ hG s' hs'
  have hform : formAdj σ G (s₁ : Matrix ι ι F) =
      ε * ((s'⁻¹ : GL ι F) : Matrix ι ι F) + (1 - ε) := by
    rw [h₁, Geo.formAdj_add, Geo.formAdj_mul σ hG, hs'inv, hadj, hεadj]
  have hmul : (formAdj σ G (s₁ : Matrix ι ι F)) * (s₁ : Matrix ι ι F) = 1 := by
    rw [hform, show ε * ((s'⁻¹ : GL ι F) : Matrix ι ι F) =
        ((s'⁻¹ : GL ι F) : Matrix ι ι F) * ε from hinv.symm,
      h₁, rck_block_mul hεi hcomm, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
    abel
  let A : Matrix ι ι F := Matrix.transpose (((s₁ : GL ι F) : Matrix ι ι F).map σ)
  have h := congrArg (fun x => G * x) hmul
  rw [Matrix.mul_one] at h
  rw [formAdj] at h
  change G * (G⁻¹ * A * G * (s₁ : Matrix ι ι F)) = G at h
  have hA : G * (G⁻¹ * A * G * (s₁ : Matrix ι ι F)) =
      A * G * (s₁ : Matrix ι ι F) := by
    calc G * (G⁻¹ * A * G * (s₁ : Matrix ι ι F))
        = (G * G⁻¹) * (A * G * (s₁ : Matrix ι ι F)) := by noncomm_ring
      _ = A * G * (s₁ : Matrix ι ι F) := by
          rw [Matrix.mul_nonsing_inv G hG, Matrix.one_mul]
  rw [hA] at h
  simpa only [A] using h

theorem rckGLBlock_restrict_quad {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {ε : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) G ε = ε) (hεi : IsIdempotentElem ε)
    {Q : (ι → F) → F} (hQ : ∀ u v, Q (u + v) = Q u + Q v + dotProduct u (G.mulVec v))
    {s' s₁ : GL ι F} (hs' : ∀ v, Q ((s' : Matrix ι ι F).mulVec v) = Q v)
    (hcomm : (s' : Matrix ι ι F) * ε = ε * (s' : Matrix ι ι F))
    (h₁ : (s₁ : Matrix ι ι F) = (s' : Matrix ι ι F) * ε + (1 - ε)) :
    ∀ v, Q ((s₁ : Matrix ι ι F).mulVec v) = Q v := by
  let E : Matrix ι ι F := ε
  let M : Matrix ι ι F := (s' : Matrix ι ι F)
  let S : Matrix ι ι F := (s₁ : Matrix ι ι F)
  have hadjT : Eᵀ * G = G * E := rck_adj_transpose_of hG hadj
  have hE1 : E * (1 - E) = 0 := (rck_one_sub hεi).1
  have hdot : ∀ (M : Matrix ι ι F) (x y : ι → F),
      dotProduct (M.mulVec x) y = dotProduct x (Mᵀ.mulVec y) := by
    intro M x y
    exact ((Matrix.dotProduct_mulVec x Mᵀ y).trans
      (by rw [Matrix.vecMul_transpose])).symm
  have hpair : ∀ x y, dotProduct (E.mulVec x) (G.mulVec ((1 - E).mulVec y)) = 0 := by
    intro x y
    have hzero : G * E * (1 - E) = 0 := by
      rw [Matrix.mul_assoc, hE1, Matrix.mul_zero]
    rw [hdot E x (G.mulVec ((1 - E).mulVec y)), Matrix.mulVec_mulVec, hadjT,
      Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec, dotProduct_zero]
  intro v
  have hv : v = E.mulVec v + (1 - E).mulVec v := by
    rw [← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hs₁v : S.mulVec v = M.mulVec (E.mulVec v) + (1 - E).mulVec v := by
    dsimp only [S, M, E]
    rw [h₁, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
  have hs'E : M.mulVec (E.mulVec v) = E.mulVec (M.mulVec v) := by
    dsimp only [M]
    rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec]
  calc Q (S.mulVec v)
      = Q (M.mulVec (E.mulVec v)) + Q ((1 - E).mulVec v) +
          dotProduct (M.mulVec (E.mulVec v)) (G.mulVec ((1 - E).mulVec v)) := by
        rw [hs₁v, hQ (M.mulVec (E.mulVec v)) ((1 - E).mulVec v)]
    _ = Q (E.mulVec v) + Q ((1 - E).mulVec v) := by
        rw [hs' (E.mulVec v), hs'E, hpair (M.mulVec v) v]
        abel
    _ = Q v := by
        rw [show Q v = Q (E.mulVec v + (1 - E).mulVec v) from congrArg Q hv,
          hQ (E.mulVec v) ((1 - E).mulVec v), hpair v v]
        abel

end CFSG.StandardType.RCKRP
