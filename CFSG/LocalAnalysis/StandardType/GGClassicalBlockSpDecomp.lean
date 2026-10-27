module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDecomp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix

private lemma ggJS3_pair_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ x ∈ Units.val '' S, ∀ y ∈ Units.val '' S, x * y = y * x := by
  intro x hx y hy
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨s', hs', rfl⟩
  simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F))
    (hS s hs s' hs')

private lemma ggJS3_adjoin_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S), ∀ b ∈ Algebra.adjoin F (Units.val '' S),
      a * b = b * a := by
  intro a ha b hb
  exact Algebra.adjoin_induction₂ (R := F) (A := Matrix ι ι F) (s := Units.val '' S)
    (p := fun a b _ _ => a * b = b * a)
    (fun x y hx hy => ggJS3_pair_comm S hS x hx y hy)
    (fun r₁ r₂ => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, mul_comm])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun r x hx => by
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one])
    (fun x y z hx hy hz hxz hyz => by rw [add_mul, mul_add, hxz, hyz])
    (fun x y z hx hy hz hxy hxz => by rw [mul_add, add_mul, hxy, hxz])
    (fun x y z hx hy hz hxz hyz => by
      rw [mul_assoc, hyz, ← mul_assoc, hxz, mul_assoc])
    (fun x y z hx hy hz hxy hxz => by
      rw [← mul_assoc, hxy, mul_assoc, hxz, ← mul_assoc])
    (x := a) (y := b) ha hb

private lemma ggJS3_adjoin_commute_S {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (S : Set (GL ι F)) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (a : Matrix ι ι F) (ha : a ∈ Algebra.adjoin F (Units.val '' S))
    (s : GL ι F) (hs : s ∈ S) :
    a * (s : Matrix ι ι F) = (s : Matrix ι ι F) * a :=
  ggJS3_adjoin_comm S hS a ha (s : Matrix ι ι F)
    (Algebra.subset_adjoin ⟨s, hs, rfl⟩)

private lemma ggJS3_mem_adjoin_commute {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (x : U) (hx : x ∈ (Subgroup.centralizer S).comap j) :
    ∀ a ∈ Algebra.adjoin F (Units.val '' S),
      (j x : Matrix ι ι F) * a = a * (j x : Matrix ι ι F) := by
  have hgen : Units.val '' S ⊆ Subalgebra.centralizer F {(j x : Matrix ι ι F)} := by
    intro y hy
    change y ∈ Subalgebra.centralizer F {(j x : Matrix ι ι F)}
    rw [Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rcases hy with ⟨t, ht, rfl⟩
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) t ht
    have hm : (t : Matrix ι ι F) * (j x : Matrix ι ι F) =
        (j x : Matrix ι ι F) * (t : Matrix ι ι F) := by
      simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
    exact hm.symm
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F {(j x : Matrix ι ι F)} :=
    Algebra.adjoin_le hgen
  intro a ha
  exact (Subalgebra.mem_centralizer_iff F).mp (hA ha) (j x) (Set.mem_singleton _)

private lemma ggJS3_inv_comm {R : Type} [Ring R] {x xi e : R} (hx : x * xi = 1)
    (hxi : xi * x = 1) (hc : x * e = e * x) : xi * e = e * xi := by
  calc xi * e = xi * e * (x * xi) := by rw [hx, mul_one]
    _ = xi * (e * x) * xi := by noncomm_ring
    _ = xi * (x * e) * xi := by rw [hc]
    _ = xi * x * e * xi := by noncomm_ring
    _ = e * xi := by rw [hxi]; noncomm_ring

private lemma ggJS3_blk_val_mul_inv {R : Type} [Ring R] (x xi e : R) (hx : x * xi = 1)
    (hid : e * e = e) (hci : xi * e = e * xi) :
    (x * e + (1 - e)) * (xi * e + (1 - e)) = 1 := by
  have hxe : x * (xi * e) = e := by rw [← mul_assoc, hx, one_mul]
  have hexi : e * (xi * e) = xi * e := by
    calc e * (xi * e) = (e * xi) * e := by rw [mul_assoc]
      _ = (xi * e) * e := by rw [← hci]
      _ = xi * (e * e) := by rw [mul_assoc]
      _ = xi * e := by rw [hid]
  have hxe' : (x * e) * (xi * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private lemma ggJS3_blk_inv_mul {R : Type} [Ring R] (x xi e : R) (hxi : xi * x = 1)
    (hid : e * e = e) (hc : x * e = e * x) :
    (xi * e + (1 - e)) * (x * e + (1 - e)) = 1 := by
  have hxe : xi * (x * e) = e := by rw [← mul_assoc, hxi, one_mul]
  have hexi : e * (x * e) = x * e := by
    calc e * (x * e) = (e * x) * e := by rw [mul_assoc]
      _ = (x * e) * e := by rw [← hc]
      _ = x * (e * e) := by rw [mul_assoc]
      _ = x * e := by rw [hid]
  have hxe' : (xi * e) * (x * e) = e := by rw [mul_assoc, hexi, hxe]
  noncomm_ring [hxe', hexi, hid]

private noncomputable def ggJS3_blkAux {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) : GL ι F :=
  Units.mk ((x : Matrix ι ι F) * e + (1 - e))
    (((x⁻¹ : GL ι F) : Matrix ι ι F) * e + (1 - e))
    (ggJS3_blk_val_mul_inv (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.mul_inv x) hid.eq
      (ggJS3_inv_comm (Units.mul_inv x) (Units.inv_mul x) hcomm))
    (ggJS3_blk_inv_mul (x : Matrix ι ι F) ((x⁻¹ : GL ι F) : Matrix ι ι F) e
      (Units.inv_mul x) hid.eq hcomm)

private noncomputable def ggJS3_blk {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) : GL ι F := by
  classical
  exact if h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e)
    then Classical.choose h else 1

private lemma ggJS3_blk_val {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hcomm : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    (ggJS3_blk x e : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) := by
  have h : ∃ u : GL ι F, (u : Matrix ι ι F) = (x : Matrix ι ι F) * e + (1 - e) :=
    ⟨ggJS3_blkAux x e hid hcomm, rfl⟩
  rw [ggJS3_blk, dif_pos h]
  exact Classical.choose_spec h

private lemma ggJS3_blk_mem_centralizer {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι]
    [Field F] (j : U →* GL ι F) (S : Set (GL ι F))
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (x : U)
    (hx : x ∈ (Subgroup.centralizer S).comap j) (e : Matrix ι ι F)
    (heA : e ∈ Algebra.adjoin F (Units.val '' S)) (hid : IsIdempotentElem e)
    (hxe : (j x : Matrix ι ι F) * e = e * (j x : Matrix ι ι F)) :
    ggJS3_blk (j x) e ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ggJS3_blk_val (j x) e hid hxe]
  have hxs : (s : Matrix ι ι F) * (j x : Matrix ι ι F) =
      (j x : Matrix ι ι F) * (s : Matrix ι ι F) := by
    have hmem := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp hx)) s hs
    simpa only [Units.val_mul] using congrArg (fun u : GL ι F => (u : Matrix ι ι F)) hmem
  have hes : e * (s : Matrix ι ι F) = (s : Matrix ι ι F) * e :=
    ggJS3_adjoin_commute_S S hS e heA s hs
  have h1 : (s : Matrix ι ι F) * ((j x : Matrix ι ι F) * e) =
      (j x : Matrix ι ι F) * ((s : Matrix ι ι F) * e) := by
    rw [← mul_assoc, hxs, mul_assoc]
  noncomm_ring [hxs, hes, h1]

private lemma ggJS3_blk_mem_glFixing {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (x : GL ι F) (e : Matrix ι ι F) (hid : IsIdempotentElem e)
    (hxe : (x : Matrix ι ι F) * e = e * (x : Matrix ι ι F)) :
    ggJS3_blk x e ∈ glFixing (1 - e) := by
  change ((ggJS3_blk x e : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
  rw [ggJS3_blk_val x e hid hxe]
  have h1 : e * (e * (x : Matrix ι ι F)) = e * (x : Matrix ι ι F) := by
    rw [← mul_assoc, hid.eq]
  noncomm_ring [hid.eq, hxe, h1]

private abbrev ggJS3_J (n : ℕ) (F : Type) [Field F] :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.fromBlocks 0 1 (-1) 0

private lemma ggJS3_J_mul_self {n : ℕ} {F : Type} [Field F] :
    ggJS3_J n F * ggJS3_J n F = -1 := by
  unfold ggJS3_J
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero]
  rw [show (-1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.fromBlocks (-1) 0 0 (-1) by
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
    simp]

private lemma ggJS3_J_isUnit_det {n : ℕ} {F : Type} [Field F] :
    IsUnit (ggJS3_J n F).det := by
  have h1 : ggJS3_J n F * (-(ggJS3_J n F)) = 1 := by
    rw [Matrix.mul_neg, ggJS3_J_mul_self, neg_neg]
  have h2 : (-(ggJS3_J n F)) * ggJS3_J n F = 1 := by
    rw [Matrix.neg_mul, ggJS3_J_mul_self, neg_neg]
  exact (Matrix.isUnit_iff_isUnit_det (ggJS3_J n F)).mp
    (isUnit_iff_exists.mpr ⟨-(ggJS3_J n F), h1, h2⟩)

private lemma ggJS3_blk_mem_statedSp {n : ℕ} {F : Type} [Field F]
    (m : GL (Fin n ⊕ Fin n) F) (hm : m ∈ CFSG.Open.StatedSp n F)
    (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (hid : IsIdempotentElem ε)
    (hcomm : (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F))
    (hst : formAdj (RingHom.id F) (ggJS3_J n F) ε = ε) :
    ggJS3_blk m ε ∈ CFSG.Open.StatedSp n F := by
  have hJdet : IsUnit (ggJS3_J n F).det := ggJS3_J_isUnit_det
  have hcomm' : (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε =
      ε * (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    ggJS3_inv_comm (Units.mul_inv m) (Units.inv_mul m) hcomm
  have hm_inv : formAdj (RingHom.id F) (ggJS3_J n F) (m : Matrix _ _ F) =
      (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) := by
    refine Geo.formAdj_eq_inv_of_isometry (RingHom.id F) hJdet m ?_
    simpa [ggJS3_J] using (CFSG.Open.StatedAPI.mem_statedSp_iff.mp hm)
  have h1e : formAdj (RingHom.id F) (ggJS3_J n F) (1 - ε) = 1 - ε := by
    have h := Geo.formAdj_add (RingHom.id F) (ggJS3_J n F) (1 - ε) ε
    rw [sub_add_cancel, Geo.formAdj_one (RingHom.id F) hJdet, hst] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  have hformX : formAdj (RingHom.id F) (ggJS3_J n F)
      ((m : Matrix _ _ F) * ε + (1 - ε)) =
      (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) * ε + (1 - ε) := by
    rw [Geo.formAdj_add, Geo.formAdj_mul (RingHom.id F) hJdet, hm_inv, hst, h1e]
    rw [← hcomm']
  have hm'm : (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hinv_val : ((((m⁻¹ : GL (Fin n ⊕ Fin n) F)) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) *
      ((m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * ε + (1 - ε)) = 1 :=
    ggJS3_blk_inv_mul (m : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      ε hm'm hid.eq hcomm
  have hJJ : ggJS3_J n F * (ggJS3_J n F)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJdet
  have hJform : (ggJS3_J n F)⁻¹ * Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) *
      ggJS3_J n F = (((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) * ε + (1 - ε) := by
    exact hformX
  rw [CFSG.Open.StatedAPI.mem_statedSp_iff, ggJS3_blk_val m ε hid hcomm]
  show Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F *
      ((m : Matrix _ _ F) * ε + (1 - ε)) = ggJS3_J n F
  have h1 : Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F =
      ggJS3_J n F * ((((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) * ε + (1 - ε)) := by
    calc Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F
        = 1 * (Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F) :=
          (Matrix.one_mul _).symm
      _ = (ggJS3_J n F * (ggJS3_J n F)⁻¹) *
            (Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F) := by rw [hJJ]
      _ = ggJS3_J n F * ((ggJS3_J n F)⁻¹ *
            Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F) := by
          simp only [Matrix.mul_assoc]
      _ = ggJS3_J n F * ((((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) * ε + (1 - ε)) := by
          rw [hJform]
  calc Matrix.transpose ((m : Matrix _ _ F) * ε + (1 - ε)) * ggJS3_J n F *
        ((m : Matrix _ _ F) * ε + (1 - ε))
      = (ggJS3_J n F * ((((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) * ε + (1 - ε))) *
          ((m : Matrix _ _ F) * ε + (1 - ε)) := by rw [h1]
    _ = ggJS3_J n F * (((((m⁻¹ : GL (Fin n ⊕ Fin n) F)) : Matrix _ _ F) * ε + (1 - ε)) *
          ((m : Matrix _ _ F) * ε + (1 - ε))) := by rw [Matrix.mul_assoc]
    _ = ggJS3_J n F * 1 := by rw [hinv_val]
    _ = ggJS3_J n F := Matrix.mul_one _
private lemma ggJS3_blk_commute_matrices {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (A : Subalgebra F (Matrix ι ι F)) (P : Finset (Matrix ι ι F))
    (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hid : ∀ p ∈ P, IsIdempotentElem p)
    (hpA : ∀ p ∈ P, p ∈ A)
    {M N ε ε' : Matrix ι ι F} (hε : ε ∈ P) (hε' : ε' ∈ P) (hne : ε ≠ ε')
    (hMA : ∀ a ∈ A, M * a = a * M) (hNA : ∀ a ∈ A, N * a = a * N)
    (hMfix : M * (1 - ε) = 1 - ε) (hNfix : N * (1 - ε') = 1 - ε') :
    M * N = N * M := by
  have hMNp : ∀ p ∈ P, M * N * p = N * M * p := by
    intro p hp
    by_cases hpε : p = ε
    · rw [hpε]
      have hNε : N * ε = ε := by
        have h1 : (1 - ε') * ε = ε := by
          rw [Matrix.sub_mul, Matrix.one_mul, horth ε' hε' ε hε hne.symm, sub_zero]
        calc N * ε = N * ((1 - ε') * ε) := by rw [h1]
          _ = (N * (1 - ε')) * ε := by rw [Matrix.mul_assoc]
          _ = (1 - ε') * ε := by rw [hNfix]
          _ = ε := h1
      calc M * N * ε = M * (N * ε) := by rw [Matrix.mul_assoc]
        _ = M * ε := by rw [hNε]
        _ = ε * M := hMA ε (hpA ε hε)
        _ = (N * ε) * M := by rw [hNε]
        _ = N * (ε * M) := by rw [Matrix.mul_assoc]
        _ = N * (M * ε) := by rw [hMA ε (hpA ε hε)]
        _ = N * M * ε := by rw [Matrix.mul_assoc]
    · by_cases hpε' : p = ε'
      · rw [hpε']
        have hMε' : M * ε' = ε' := by
          have h1 : (1 - ε) * ε' = ε' := by
            rw [Matrix.sub_mul, Matrix.one_mul, horth ε hε ε' hε' hne, sub_zero]
          calc M * ε' = M * ((1 - ε) * ε') := by rw [h1]
            _ = (M * (1 - ε)) * ε' := by rw [Matrix.mul_assoc]
            _ = (1 - ε) * ε' := by rw [hMfix]
            _ = ε' := h1
        have hNε'comm : N * ε' = ε' * N := hNA ε' (hpA ε' hε')
        calc M * N * ε' = M * (N * ε') := by rw [Matrix.mul_assoc]
          _ = M * (ε' * N) := by rw [hNε'comm]
          _ = (M * ε') * N := by rw [Matrix.mul_assoc]
          _ = ε' * N := by rw [hMε']
          _ = N * ε' := by rw [hNε'comm]
          _ = N * (M * ε') := by rw [hMε']
          _ = N * M * ε' := by rw [Matrix.mul_assoc]
      · have hMp : M * p = p := by
          have h1 : (1 - ε) * p = p := by
            rw [Matrix.sub_mul, Matrix.one_mul, horth ε hε p hp (fun h => hpε h.symm), sub_zero]
          calc M * p = M * ((1 - ε) * p) := by rw [h1]
            _ = (M * (1 - ε)) * p := by rw [Matrix.mul_assoc]
            _ = (1 - ε) * p := by rw [hMfix]
            _ = p := h1
        have hNp : N * p = p := by
          have h1 : (1 - ε') * p = p := by
            rw [Matrix.sub_mul, Matrix.one_mul, horth ε' hε' p hp (fun h => hpε' h.symm), sub_zero]
          calc N * p = N * ((1 - ε') * p) := by rw [h1]
            _ = (N * (1 - ε')) * p := by rw [Matrix.mul_assoc]
            _ = (1 - ε') * p := by rw [hNfix]
            _ = p := h1
        calc M * N * p = M * (N * p) := by rw [Matrix.mul_assoc]
          _ = M * p := by rw [hNp]
          _ = p := hMp
          _ = N * p := by rw [hNp]
          _ = N * (M * p) := by rw [hMp]
          _ = N * M * p := by rw [Matrix.mul_assoc]
  have hsum : M * N * (∑ p ∈ P, p) = N * M * (∑ p ∈ P, p) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hMNp p hp)
  rwa [hPsum, Matrix.mul_one, Matrix.mul_one] at hsum

private lemma ggJS3_exists_prod {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (G : Matrix ι ι F → Subgroup U)
    (P : Finset (Matrix ι ι F)) (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hfix : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * (1 - p) = 1 - p)
    (hcomm : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * p = p * (j x : Matrix ι ι F))
    (g : ∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) :
    ∃ w : U, w ∈ (⨆ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) ∧
      ∀ ε : {p // p ∈ P},
        (j w : Matrix ι ι F) * (ε : Matrix ι ι F) =
        (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F) := by
  classical
  have key : ∀ sT : Finset {p // p ∈ P},
      ∃ w ∈ (⨆ ε ∈ sT, G (ε : Matrix ι ι F)),
        (∀ ε ∈ sT, (j w : Matrix ι ι F) * (ε : Matrix ι ι F) =
          (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F)) ∧
        (∀ ε : {p // p ∈ P}, ε ∉ sT →
          (j w : Matrix ι ι F) * (ε : Matrix ι ι F) = (ε : Matrix ι ι F)) := by
    intro sT
    induction sT using Finset.induction_on with
    | empty =>
        refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
        · intro ε hε; simp at hε
        · intro ε _; show (j 1 : Matrix ι ι F) * (ε : Matrix ι ι F) = (ε : Matrix ι ι F)
          rw [map_one, Units.val_one, Matrix.one_mul]
    | insert a sT ha ih =>
        obtain ⟨w, hw_mem, hw_in, hw_out⟩ := ih
        have hga_fix : (j (g a) : Matrix ι ι F) * (1 - (a : Matrix ι ι F)) =
            1 - (a : Matrix ι ι F) := hfix a a.2 (g a) (g a).2
        have hga_fix_ne : ∀ ε : Matrix ι ι F, ε ∈ P → ε ≠ (a : Matrix ι ι F) →
            (j (g a) : Matrix ι ι F) * ε = ε := by
          intro ε hεP hne
          have h1 : (1 - (a : Matrix ι ι F)) * ε = ε := by
            rw [Matrix.sub_mul, Matrix.one_mul,
              horth a a.2 ε hεP (fun h => hne h.symm), sub_zero]
          calc (j (g a) : Matrix ι ι F) * ε
              = (j (g a) : Matrix ι ι F) * ((1 - (a : Matrix ι ι F)) * ε) := by rw [h1]
            _ = ((j (g a) : Matrix ι ι F) * (1 - (a : Matrix ι ι F))) * ε := by
                rw [Matrix.mul_assoc]
            _ = (1 - (a : Matrix ι ι F)) * ε := by rw [hga_fix]
            _ = ε := h1
        have hle_a : G (a : Matrix ι ι F) ≤ ⨆ p ∈ insert a sT, G (p : Matrix ι ι F) := by
          apply le_iSup_of_le (f := fun p => ⨆ (_ : p ∈ insert a sT), G (p : Matrix ι ι F)) a
          apply le_iSup_of_le (f := fun _ : a ∈ insert a sT =>
            G (a : Matrix ι ι F)) (Finset.mem_insert_self a sT)
          exact le_rfl
        have hle_T : (⨆ p ∈ sT, G (p : Matrix ι ι F)) ≤
            ⨆ p ∈ insert a sT, G (p : Matrix ι ι F) := by
          apply iSup_le; intro p; apply iSup_le; intro hp
          apply le_iSup_of_le (f := fun q =>
            ⨆ (_ : q ∈ insert a sT), G (q : Matrix ι ι F)) p
          apply le_iSup_of_le (f := fun _ : p ∈ insert a sT => G (p : Matrix ι ι F))
            (Finset.mem_insert_of_mem hp)
          exact le_rfl
        refine ⟨(g a) * w, ?_, ?_, ?_⟩
        · exact (⨆ p ∈ insert a sT, G (p : Matrix ι ι F)).mul_mem (hle_a (g a).2) (hle_T hw_mem)
        · intro ε hε
          rw [Finset.mem_insert] at hε
          rcases hε with hεa | hε
          · rw [hεa]
            have hw_a : (j w : Matrix ι ι F) * (a : Matrix ι ι F) = (a : Matrix ι ι F) :=
              hw_out a ha
            rw [map_mul, Units.val_mul, Matrix.mul_assoc, hw_a]
          · have hw_e := hw_in ε hε
            have hcomm_e : (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F) =
                (ε : Matrix ι ι F) * (j (g ε) : Matrix ι ι F) := hcomm ε ε.2 (g ε) (g ε).2
            have hga_e : (j (g a) : Matrix ι ι F) * (ε : Matrix ι ι F) = (ε : Matrix ι ι F) :=
              hga_fix_ne (ε : Matrix ι ι F) ε.2 (fun hmat => ha (by
                have hsub : ε = a := Subtype.ext hmat
                exact hsub ▸ hε))
            calc (j ((g a) * w) : Matrix ι ι F) * (ε : Matrix ι ι F)
                = (j (g a) : Matrix ι ι F) *
                    ((j w : Matrix ι ι F) * (ε : Matrix ι ι F)) := by
                  rw [map_mul, Units.val_mul, Matrix.mul_assoc]
              _ = (j (g a) : Matrix ι ι F) *
                    ((j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F)) := by rw [hw_e]
              _ = (j (g a) : Matrix ι ι F) *
                    ((ε : Matrix ι ι F) * (j (g ε) : Matrix ι ι F)) := by rw [hcomm_e]
              _ = ((j (g a) : Matrix ι ι F) * (ε : Matrix ι ι F)) *
                    (j (g ε) : Matrix ι ι F) := by rw [Matrix.mul_assoc]
              _ = (ε : Matrix ι ι F) * (j (g ε) : Matrix ι ι F) := by rw [hga_e]
              _ = (j (g ε) : Matrix ι ι F) * (ε : Matrix ι ι F) := hcomm_e.symm
        · intro ε hε
          have hne : (ε : Matrix ι ι F) ≠ (a : Matrix ι ι F) := fun hmat =>
            hε ((Subtype.ext hmat).symm ▸ Finset.mem_insert_self a sT)
          have hw_e := hw_out ε (fun hmem => hε (Finset.mem_insert_of_mem hmem))
          rw [map_mul, Units.val_mul, Matrix.mul_assoc, hw_e, hga_fix_ne (ε : Matrix ι ι F) ε.2 hne]
  obtain ⟨w, hw_mem, hw_in, _⟩ := key Finset.univ
  exact ⟨w, by simpa using hw_mem, fun ε => hw_in ε (Finset.mem_univ ε)⟩

private lemma ggJS3_eq_of_blocks {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j)
    (P : Finset (Matrix ι ι F)) (hPsum : ∑ p ∈ P, p = 1)
    {x y : U}
    (h : ∀ ε : {p // p ∈ P}, (j x : Matrix ι ι F) * (ε : Matrix ι ι F) =
        (j y : Matrix ι ι F) * (ε : Matrix ι ι F)) :
    x = y := by
  apply hj
  apply Units.ext
  have hsum1 : (∑ ε : {p : Matrix ι ι F // p ∈ P}, (ε : Matrix ι ι F)) = 1 := by
    rw [Finset.sum_coe_sort P (fun i : Matrix ι ι F => i), hPsum]
  calc (j x : Matrix ι ι F)
      = (j x : Matrix ι ι F) * 1 := (Matrix.mul_one _).symm
    _ = (j x : Matrix ι ι F) * (∑ ε : {p : Matrix ι ι F // p ∈ P}, (ε : Matrix ι ι F)) := by
        rw [hsum1]
    _ = ∑ ε : {p : Matrix ι ι F // p ∈ P}, (j x : Matrix ι ι F) * (ε : Matrix ι ι F) := by
        rw [Finset.mul_sum]
    _ = ∑ ε : {p : Matrix ι ι F // p ∈ P}, (j y : Matrix ι ι F) * (ε : Matrix ι ι F) :=
        Finset.sum_congr rfl (fun ε _ => h ε)
    _ = (j y : Matrix ι ι F) * (∑ ε : {p : Matrix ι ι F // p ∈ P}, (ε : Matrix ι ι F)) := by
        rw [Finset.mul_sum]
    _ = (j y : Matrix ι ι F) * 1 := by rw [hsum1]
    _ = (j y : Matrix ι ι F) := Matrix.mul_one _

private lemma ggJS3_eq_of_blk {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j)
    {G : Matrix ι ι F → Subgroup U} {ε : Matrix ι ι F} {x y : G ε}
    (hfixx : (j x : Matrix ι ι F) * (1 - ε) = 1 - ε)
    (hfixy : (j y : Matrix ι ι F) * (1 - ε) = 1 - ε)
    (h : (j x : Matrix ι ι F) * ε = (j y : Matrix ι ι F) * ε) :
    x = y := by
  apply Subtype.ext
  apply hj
  apply Units.ext
  calc (j x : Matrix ι ι F)
      = (j x : Matrix ι ι F) * ε + (j x : Matrix ι ι F) * (1 - ε) := by
        rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
    _ = (j x : Matrix ι ι F) * ε + (1 - ε) := by rw [hfixx]
    _ = (j y : Matrix ι ι F) * ε + (1 - ε) := by rw [h]
    _ = (j y : Matrix ι ι F) * ε + (j y : Matrix ι ι F) * (1 - ε) := by rw [hfixy]
    _ = (j y : Matrix ι ι F) := by rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]

private lemma ggJS3_card_eq_prod {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (hj : Function.Injective j) (G : Matrix ι ι F → Subgroup U)
    (P : Finset (Matrix ι ι F)) (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hfix : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * (1 - p) = 1 - p)
    (hcomm : ∀ p ∈ P, ∀ x ∈ G p, (j x : Matrix ι ι F) * p = p * (j x : Matrix ι ι F))
    (C : Subgroup U) (hGleC : ∀ p, G p ≤ C)
    (toBlock : ↥C → ∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F))
    (htoBlock : ∀ u : ↥C, ∀ ε : {p // p ∈ P},
      (j (toBlock u ε) : Matrix ι ι F) * (ε : Matrix ι ι F) =
      (j (u : U) : Matrix ι ι F) * (ε : Matrix ι ι F)) :
    Nat.card ↥C = ∏ p ∈ P, Nat.card ↥(G p) := by
  classical
  let Ψ : (∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) → ↥C := fun g =>
    ⟨Classical.choose (ggJS3_exists_prod j G P hPsum horth hfix hcomm g),
      (iSup_le (fun ε : {p // p ∈ P} => hGleC (ε : Matrix ι ι F)))
        (Classical.choose_spec (ggJS3_exists_prod j G P hPsum horth hfix hcomm g)).1⟩
  have hsurj : Function.Surjective Ψ := by
    intro u
    refine ⟨toBlock u, ?_⟩
    apply Subtype.ext
    apply ggJS3_eq_of_blocks j hj P hPsum
    intro ε
    rw [(Classical.choose_spec
      (ggJS3_exists_prod j G P hPsum horth hfix hcomm (toBlock u))).2 ε]
    exact htoBlock u ε
  have hinj : Function.Injective Ψ := by
    intro g h hgh
    funext ε
    apply ggJS3_eq_of_blk j hj
      (hfix (ε : Matrix ι ι F) ε.2 (g ε) (g ε).2)
      (hfix (ε : Matrix ι ι F) ε.2 (h ε) (h ε).2)
    have hb : (j ((Ψ g : ↥C) : U) : Matrix ι ι F) * (ε : Matrix ι ι F) =
        (j ((Ψ h : ↥C) : U) : Matrix ι ι F) * (ε : Matrix ι ι F) := by rw [hgh]
    rw [(Classical.choose_spec (ggJS3_exists_prod j G P hPsum horth hfix hcomm g)).2 ε,
      (Classical.choose_spec (ggJS3_exists_prod j G P hPsum horth hfix hcomm h)).2 ε] at hb
    exact hb
  calc Nat.card ↥C = Nat.card (∀ ε : {p // p ∈ P}, G (ε : Matrix ι ι F)) :=
        (Nat.card_congr (Equiv.ofBijective Ψ ⟨hinj, hsurj⟩)).symm
    _ = ∏ ε : {p // p ∈ P}, Nat.card ↥(G (ε : Matrix ι ι F)) := Nat.card_pi
    _ = ∏ p ∈ P, Nat.card ↥(G p) :=
        Finset.prod_coe_sort P (fun p : Matrix ι ι F => Nat.card ↥(G p))

private lemma ggJS3_toBlock_exists {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K)
    (P : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (hpid : ∀ p ∈ P, IsIdempotentElem p)
    (hpA : ∀ p ∈ P, p ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K))))
    (hpstar : ∀ p ∈ P, formAdj (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) p = p)
    (hS : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)), Commute s s') :
    ∃ toBlock : ↥((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype) →
        (∀ ε : {p : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K // p ∈ P},
          glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
            (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)),
      ∀ (u : ↥((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
          (StatedSp n K).subtype))
        (ε : {p : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K // p ∈ P}),
        ((StatedSp n K).subtype (toBlock u ε) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        ((StatedSp n K).subtype (u : ↥(StatedSp n K)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
  classical
  have hblk_sp : ∀ (u : ↥(StatedSp n K))
      (hu : u ∈ (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype) (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hε : ε ∈ P),
      ggJS3_blk ((u : GL (Fin n ⊕ Fin n) K)) ε ∈ StatedSp n K := by
    intro u hu ε hε
    refine ggJS3_blk_mem_statedSp ((u : GL (Fin n ⊕ Fin n) K)) u.2 ε (hpid ε hε) ?_
      (by simpa [ggJS3_J] using hpstar ε hε)
    exact ggJS3_mem_adjoin_commute (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
      u hu ε (hpA ε hε)
  have hblk_mem : ∀ (u : ↥(StatedSp n K))
      (hu : u ∈ (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype) (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (hε : ε ∈ P),
      (⟨ggJS3_blk ((u : GL (Fin n ⊕ Fin n) K)) ε, hblk_sp u hu ε hε⟩ : ↥(StatedSp n K)) ∈
        glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε := by
    intro u hu ε hε
    show (⟨ggJS3_blk ((u : GL (Fin n ⊕ Fin n) K)) ε, hblk_sp u hu ε hε⟩ : ↥(StatedSp n K)) ∈
      (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) ⊓ glFixing (1 - ε)).comap
        (StatedSp n K).subtype
    rw [Subgroup.mem_comap]
    exact Subgroup.mem_inf.mpr ⟨
      ggJS3_blk_mem_centralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) hS u hu
        ε (hpA ε hε) (hpid ε hε)
        (ggJS3_mem_adjoin_commute (StatedSp n K).subtype
          ({b} : Set (GL (Fin n ⊕ Fin n) K)) u hu ε (hpA ε hε)),
      ggJS3_blk_mem_glFixing ((u : GL (Fin n ⊕ Fin n) K)) ε (hpid ε hε)
        (ggJS3_mem_adjoin_commute (StatedSp n K).subtype
          ({b} : Set (GL (Fin n ⊕ Fin n) K)) u hu ε (hpA ε hε))⟩
  let toBlockFun : ↥((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype) →
        (∀ ε : {p : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K // p ∈ P},
          glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
            (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) :=
    fun u ε => ⟨⟨ggJS3_blk (((u : ↥(StatedSp n K)) : GL (Fin n ⊕ Fin n) K))
      (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
      hblk_sp (u : ↥(StatedSp n K)) u.2 (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε.2⟩,
      hblk_mem (u : ↥(StatedSp n K)) u.2 (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε.2⟩
  refine ⟨toBlockFun, ?_⟩
  intro u ε
  have hv : ((StatedSp n K).subtype (toBlockFun u ε) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
      ggJS3_blk (((u : ↥(StatedSp n K)) : GL (Fin n ⊕ Fin n) K))
        (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := rfl
  rw [hv, ggJS3_blk_val (((u : ↥(StatedSp n K)) : GL (Fin n ⊕ Fin n) K))
      (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
      (hpid (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε.2)
      (ggJS3_mem_adjoin_commute (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
        (u : ↥(StatedSp n K)) u.2 (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (hpA (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε.2)),
    Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    (hpid (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) ε.2).eq, sub_self, add_zero]
  rfl

private lemma ggJS3_iSup_eq_centralizer {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K)
    (P : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))
    (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    (hpA : ∀ p ∈ P, p ∈ Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K))))
    (toBlock : ↥((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype) →
        (∀ ε : {p : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K // p ∈ P},
          glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
            (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)))
    (htoBlock : ∀ (u : ↥((Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
          (StatedSp n K).subtype))
        (ε : {p : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K // p ∈ P}),
        ((StatedSp n K).subtype (toBlock u ε) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        ((StatedSp n K).subtype (u : ↥(StatedSp n K)) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          (ε : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) :
    (⨆ ε ∈ P, glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε) =
      (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap
        (StatedSp n K).subtype := by
  apply le_antisymm
  · apply iSup_le; intro ε; apply iSup_le; intro hε; intro x hx
    exact Subgroup.mem_comap.mpr (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1
  · intro u hu
    obtain ⟨w, hw_mem, hw_prop⟩ := ggJS3_exists_prod (StatedSp n K).subtype
      (fun ε => glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε)
      P hPsum horth
      (fun p hp x hx => (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2)
      (fun p hp x hx => ggJS3_mem_adjoin_commute (StatedSp n K).subtype
        ({b} : Set (GL (Fin n ⊕ Fin n) K)) x
        (Subgroup.mem_comap.mpr (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1) p (hpA p hp))
      (toBlock ⟨u, hu⟩)
    have hw_mem' : w ∈ (⨆ ε ∈ P, glBlockCentralizer (StatedSp n K).subtype
        ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε) := by
      simpa only [iSup_subtype] using hw_mem
    have hw_eq : w = u :=
      ggJS3_eq_of_blocks (StatedSp n K).subtype (Subgroup.subtype_injective _) P hPsum
        (fun ε => by rw [hw_prop ε, htoBlock ⟨u, hu⟩ ε])
    rw [← hw_eq]; exact hw_mem'

theorem centralizer_block_decomp_Sp {K : Type} [Field K] [Fintype K] [CharP K 2] {n : ℕ}
    (b : GL (Fin n ⊕ Fin n) K) (hb : b ∈ StatedSp n K) (hodd : Odd (orderOf b)) :
    ∃ P : Finset (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K),
      (∀ ε ∈ P, IsPrimAdjIdemIn (RingHom.id K)
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
        (Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))) ε) ∧
      (∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' → ε * ε' = 0) ∧ ∑ ε ∈ P, ε = 1 ∧
      (∀ ε ∈ P, ∀ ε' ∈ P, ε ≠ ε' →
        ∀ x ∈ glBlockCentralizer (StatedSp n K).subtype {b} ε,
        ∀ y ∈ glBlockCentralizer (StatedSp n K).subtype {b} ε', Commute x y) ∧
      (⨆ ε ∈ P, glBlockCentralizer (StatedSp n K).subtype {b} ε) =
        (Subgroup.centralizer {b}).comap (StatedSp n K).subtype ∧
      Nat.card ↥((Subgroup.centralizer {b}).comap (StatedSp n K).subtype) =
        ∏ ε ∈ P, Nat.card ↥(glBlockCentralizer (StatedSp n K).subtype {b} ε) := by
  classical
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := Matrix.fromBlocks 0 1 (-1) 0
  let A : Subalgebra K (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
    Algebra.adjoin K (Units.val '' ({b} : Set (GL (Fin n ⊕ Fin n) K)))
  let star : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K →
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := formAdj (RingHom.id K) J
  let G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K → Subgroup ↥(StatedSp n K) :=
    fun ε => glBlockCentralizer (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) ε
  let C : Subgroup ↥(StatedSp n K) :=
    (Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K))).comap (StatedSp n K).subtype
  have hJdet : IsUnit J.det := by simpa [J] using ggJS3_J_isUnit_det (n := n) (F := K)
  have hS : ∀ s ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)),
      ∀ s' ∈ ({b} : Set (GL (Fin n ⊕ Fin n) K)), Commute s s' := by
    intro s hs s' hs'
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  have hAcomm : ∀ a ∈ A, ∀ b' ∈ A, a * b' = b' * a :=
    ggJS3_adjoin_comm ({b} : Set (GL (Fin n ⊕ Fin n) K)) hS
  have hone : star 1 = 1 := by
    simpa [star] using Geo.formAdj_one (RingHom.id K) hJdet
  have hadd : ∀ a ∈ A, ∀ b' ∈ A, star (a + b') = star a + star b' := by
    intro a _ b' _; exact Geo.formAdj_add (RingHom.id K) J a b'
  obtain ⟨P, hPprim, hPorth, hPsum⟩ :=
    Block.exists_finset_isPrimStarIdemIn_sum_eq star A hAcomm hadd
      (Subalgebra.one_mem A) IsIdempotentElem.one hone
  have hpA : ∀ p ∈ P, p ∈ A := fun p hp => (hPprim p hp).1.1
  have hpid : ∀ p ∈ P, IsIdempotentElem p := fun p hp => (hPprim p hp).1.2.1
  have hpstar : ∀ p ∈ P, star p = p := fun p hp => (hPprim p hp).1.2.2.2.1
  obtain ⟨toBlock, htoBlock⟩ := ggJS3_toBlock_exists b P hpid hpA
    (fun p hp => by simpa [star, J] using hpstar p hp) hS
  have hfix : ∀ p ∈ P, ∀ x ∈ G p,
      ((StatedSp n K).subtype x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * (1 - p) =
        1 - p := by
    intro p hp x hx
    exact (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2
  have hcommG : ∀ p ∈ P, ∀ x ∈ G p,
      ((StatedSp n K).subtype x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) * p =
        p * ((StatedSp n K).subtype x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) := by
    intro p hp x hx
    exact ggJS3_mem_adjoin_commute (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K)) x
      (Subgroup.mem_comap.mpr (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).1) p (hpA p hp)
  have hGleC : ∀ p : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K, G p ≤ C :=
    fun p => Subgroup.comap_mono inf_le_left
  refine ⟨P, ?_, ?_, hPsum, ?_, ?_, ?_⟩
  · intro ε hε
    exact (Block.isPrimStarIdemIn_formAdj_iff (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0) A ε).mp (by simpa [star, J] using (hPprim ε hε).1)
  · intro ε hε ε' hε' hne
    exact hPorth ε hε ε' hε' hne
  · intro ε hε ε' hε' hne x hx y hy
    have hx_inf : (x : GL (Fin n ⊕ Fin n) K) ∈
        Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) ⊓ glFixing (1 - ε) :=
      Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)
    have hy_inf : (y : GL (Fin n ⊕ Fin n) K) ∈
        Subgroup.centralizer ({b} : Set (GL (Fin n ⊕ Fin n) K)) ⊓ glFixing (1 - ε') :=
      Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hy)
    have hMA : ∀ a ∈ A, (x : GL (Fin n ⊕ Fin n) K) * a = a * (x : GL (Fin n ⊕ Fin n) K) :=
      ggJS3_mem_adjoin_commute (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
        x (Subgroup.mem_comap.mpr hx_inf.1)
    have hNA : ∀ a ∈ A, (y : GL (Fin n ⊕ Fin n) K) * a = a * (y : GL (Fin n ⊕ Fin n) K) :=
      ggJS3_mem_adjoin_commute (StatedSp n K).subtype ({b} : Set (GL (Fin n ⊕ Fin n) K))
        y (Subgroup.mem_comap.mpr hy_inf.1)
    have key : ((x : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          ((y : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) =
        ((y : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
          ((x : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
      ggJS3_blk_commute_matrices A P hPsum hPorth hpid hpA hε hε' hne hMA hNA
        hx_inf.2 hy_inf.2
    change x * y = y * x
    apply Subtype.ext
    apply Units.ext
    exact key
  · show (⨆ ε ∈ P, G ε) = C
    exact ggJS3_iSup_eq_centralizer b P hPsum hPorth hpA toBlock htoBlock
  · show Nat.card ↥C = ∏ p ∈ P, Nat.card ↥(G p)
    exact ggJS3_card_eq_prod (StatedSp n K).subtype (Subgroup.subtype_injective _) G P hPsum
      hPorth hfix hcommG C hGleC toBlock htoBlock

end CFSG.StandardType.ClassicalBlocks
