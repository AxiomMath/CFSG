module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphAlgebra

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma pslB2a_mem_sup_of_comm {G : Type*} [Group G] {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let T : Subgroup G :=
    { carrier := {z | ∃ a ∈ A, ∃ b ∈ B, a * b = z}
      mul_mem' := by
        rintro z w ⟨a1, ha1, b1, hb1, rfl⟩ ⟨a2, ha2, b2, hb2, rfl⟩
        exact ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, by
          calc (a1 * a2) * (b1 * b2) = a1 * (a2 * (b1 * b2)) := by rw [mul_assoc]
            _ = a1 * ((a2 * b1) * b2) := by rw [mul_assoc]
            _ = a1 * ((b1 * a2) * b2) := by rw [hcomm a2 ha2 b1 hb1]
            _ = a1 * (b1 * (a2 * b2)) := by rw [mul_assoc]
            _ = (a1 * b1) * (a2 * b2) := by rw [mul_assoc]⟩
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by rw [mul_one]⟩
      inv_mem' := by
        rintro z ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, by
          rw [_root_.mul_inv_rev]
          exact hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)⟩ }
  have hAT : A ≤ T := fun z hz => ⟨z, hz, 1, B.one_mem, mul_one z⟩
  have hBT : B ≤ T := fun z hz => ⟨1, A.one_mem, z, hz, one_mul z⟩
  have hTAB : T ≤ A ⊔ B := fun z hz => by
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact Subgroup.mul_mem_sup ha hb
  have hEq : A ⊔ B = T := le_antisymm (sup_le hAT hBT) hTAB
  rw [hEq] at hx
  exact hx

private lemma pslB2a_sup_solvable {G : Type*} [Group G] (A B : Subgroup G)
    (hA : Group.IsSolvable ↥A) (hB : Group.IsSolvable ↥B)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Group.IsSolvable ↥(A ⊔ B) := by
  haveI : Group.IsSolvable ↥A := hA
  haveI : Group.IsSolvable ↥B := hB
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        change (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G)) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * ((p.2 : G) * (q.2 : G))) := by rw [mul_assoc]
          _ = (p.1 : G) * (((q.1 : G) * (p.2 : G)) * (q.2 : G)) := by rw [mul_assoc]
          _ = (p.1 : G) * (((p.2 : G) * (q.1 : G)) * (q.2 : G)) := by
              rw [(hcomm (q.1 : G) q.1.2 (p.2 : G) p.2.2).symm]
          _ = (p.1 : G) * ((p.2 : G) * ((q.1 : G) * (q.2 : G))) := by rw [mul_assoc]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by rw [mul_assoc] }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ := pslB2a_mem_sup_of_comm hcomm x.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  exact solvable_of_surjective hf

private lemma pslB2a_commuting_join {ι G : Type*} [Group G] (s : Finset ι) (H : ι → Subgroup G)
    (hsol : ∀ i ∈ s, Group.IsSolvable ↥(H i))
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ H i, ∀ y ∈ H j, x * y = y * x) :
    Group.IsSolvable ↥(⨆ i ∈ s, H i) := by
  classical
  revert hsol hcomm
  refine Finset.induction ?_ ?_ s
  · intro hsol hcomm
    have h : (⨆ i ∈ (∅ : Finset ι), H i) = ⊥ := by simp
    rw [h]
    infer_instance
  · intro a t ha ih hsol hcomm
    rw [Finset.iSup_insert]
    apply pslB2a_sup_solvable
    · exact hsol a (Finset.mem_insert_self a t)
    · apply ih
      · intro i hi; exact hsol i (Finset.mem_insert_of_mem hi)
      · intro i hi j hj hij
        exact hcomm i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    · intro u hu v hv
      have hle : (⨆ i ∈ t, H i) ≤ Subgroup.centralizer ({u} : Set G) := by
        apply iSup_le; intro i
        apply iSup_le; intro hi
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hcomm a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
          (fun hae => ha (hae.symm ▸ hi)) u hu z hz
      exact (Subgroup.mem_centralizer_iff.mp (hle hv)) u (Set.mem_singleton u)

private lemma pslB2a_comm_of_comm {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {x : Matrix (Fin n) (Fin n) K}
    (hx : (B : Matrix (Fin n) (Fin n) K) * x = x * (B : Matrix (Fin n) (Fin n) K)) :
    ∀ a ∈ pslAlg B, x * a = a * x := by
  intro a ha
  refine Algebra.adjoin_induction (p := fun y _ => x * y = y * x) ?_ ?_ ?_ ?_ ha
  · rintro y ⟨s, hs, rfl⟩
    rw [Set.mem_singleton_iff] at hs
    subst hs
    exact hx.symm
  · intro r
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  · intro y z _ _ hy hz
    rw [Matrix.mul_add, Matrix.add_mul, hy, hz]
  · intro y z _ _ hy hz
    calc x * (y * z) = (x * y) * z := by rw [Matrix.mul_assoc]
      _ = (y * x) * z := by rw [hy]
      _ = y * (x * z) := by rw [Matrix.mul_assoc]
      _ = y * (z * x) := by rw [hz]
      _ = (y * z) * x := by rw [Matrix.mul_assoc]

private def pslB2a_C {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    Subgroup (SpecialLinearGroup (Fin n) K) :=
  (Subgroup.centralizer ({B} : Set (GL (Fin n) K))).comap (SpecialLinearGroup.toGL)

private lemma pslB2a_C_comm_B {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    (x : ↥(pslB2a_C B)) :
    (B : Matrix (Fin n) (Fin n) K) * ((x : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (B : Matrix (Fin n) (Fin n) K) := by
  have hx := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_comap.mp x.2)
  have hB := hx B (Set.mem_singleton B)
  have hB' := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hB
  simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using hB'

private lemma pslB2a_mem_block_comm_B {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ pslBlock B e) :
    (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) := by
  rw [pslBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hx
  have hB := (Subgroup.mem_centralizer_iff.mp hx.1) B (Set.mem_singleton B)
  have hB' := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hB
  simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using hB'

private lemma pslB2a_mem_block_fix {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {e : Matrix (Fin n) (Fin n) K} {x : SpecialLinearGroup (Fin n) K}
    (hx : x ∈ pslBlock B e) :
    (x : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e := by
  rw [pslBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf] at hx
  have h := hx.2
  change (SpecialLinearGroup.toGL x : Matrix (Fin n) (Fin n) K) * (1 - e) = 1 - e at h
  rw [SpecialLinearGroup.coe_GL_coe_matrix] at h
  exact h

private def pslB2a_extMat {n : ℕ} {K : Type} [Field K] (x : SpecialLinearGroup (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  (x : Matrix (Fin n) (Fin n) K) * e + (1 - e)

private lemma pslB2a_extMat_one {n : ℕ} {K : Type} [Field K]
    (e : Matrix (Fin n) (Fin n) K) :
    pslB2a_extMat (1 : SpecialLinearGroup (Fin n) K) e = 1 := by
  unfold pslB2a_extMat
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
  abel

private lemma pslB2a_extMat_mul_ring {R : Type} [Ring R] (x y e : R)
    (hye : y * e = e * y) (hidem : e * e = e) :
    (x * y) * e + (1 - e) = (x * e + (1 - e)) * (y * e + (1 - e)) := by
  have h1 : e * y = y * e := hye.symm
  have hxy : x * e * (y * e) = x * y * e := by
    rw [mul_assoc, ← mul_assoc e y e, h1, mul_assoc y e e, hidem, ← mul_assoc x y e]
  have hxe1 : x * e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, mul_assoc, hidem, sub_self]
  have h1ye : (1 - e) * (y * e) = 0 := by
    rw [sub_mul, one_mul, ← mul_assoc, h1, mul_assoc, hidem, sub_self]
  have h11 : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hidem]
    abel
  rw [add_mul, mul_add, mul_add, hxy, hxe1, h1ye, h11, add_zero, zero_add]

private lemma pslB2a_extMat_mul {n : ℕ} {K : Type} [Field K]
    {x y : SpecialLinearGroup (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    (hye : (y : Matrix (Fin n) (Fin n) K) * e = e * (y : Matrix (Fin n) (Fin n) K))
    (hidem : e * e = e) :
    pslB2a_extMat (x * y) e = pslB2a_extMat x e * pslB2a_extMat y e := by
  unfold pslB2a_extMat
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact pslB2a_extMat_mul_ring (x : Matrix (Fin n) (Fin n) K) (y : Matrix (Fin n) (Fin n) K)
    e hye hidem

private lemma pslB2a_extMat_mul_inv {n : ℕ} {K : Type} [Field K]
    {x : SpecialLinearGroup (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    (hxe : (x : Matrix (Fin n) (Fin n) K) * e = e * (x : Matrix (Fin n) (Fin n) K))
    (hidem : e * e = e) :
    pslB2a_extMat x e * pslB2a_extMat (x⁻¹) e = 1 := by
  unfold pslB2a_extMat
  have hx : (x : Matrix (Fin n) (Fin n) K) * ((x⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hxi : ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (x : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hci : ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
      e * ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    calc ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e
        = ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e *
            ((x : Matrix (Fin n) (Fin n) K) *
              ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [hx, mul_one]
      _ = ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            (e * (x : Matrix (Fin n) (Fin n) K)) *
            ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          noncomm_ring
      _ = ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((x : Matrix (Fin n) (Fin n) K) * e) *
            ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hxe]
      _ = e * ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [← Matrix.mul_assoc, hxi, Matrix.one_mul]
  have hxe1 : (x : Matrix (Fin n) (Fin n) K) *
      (((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e) = e := by
    rw [← Matrix.mul_assoc, hx, Matrix.one_mul]
  have hexi : e * (((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e) =
      ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e := by
    calc e * (((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e)
        = (e * ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) * e := by
          rw [Matrix.mul_assoc]
      _ = (((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e) * e := by
          rw [← hci]
      _ = ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * (e * e) := by
          rw [Matrix.mul_assoc]
      _ = ((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e := by
          rw [hidem]
  have hxe' : ((x : Matrix (Fin n) (Fin n) K) * e) *
      (((x⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e) = e := by
    rw [Matrix.mul_assoc, hexi, hxe1]
  noncomm_ring [hxe', hexi, hidem]

private noncomputable def pslB2a_extUnit {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (x : ↥(pslB2a_C B)) (e : Matrix (Fin n) (Fin n) K) (he : e ∈ pslAlg B)
    (hidem : e * e = e) : Kˣ :=
  Units.mk0 (pslB2a_extMat (x : SpecialLinearGroup (Fin n) K) e).det (by
    have hxe : ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * e =
        e * ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) :=
      pslB2a_comm_of_comm (pslB2a_C_comm_B x) e he
    have h := pslB2a_extMat_mul_inv hxe hidem
    intro hdet
    have hd : (pslB2a_extMat (x : SpecialLinearGroup (Fin n) K) e *
        pslB2a_extMat ((x : SpecialLinearGroup (Fin n) K))⁻¹ e).det = 1 := by
      rw [h, Matrix.det_one]
    rw [Matrix.det_mul, hdet, zero_mul] at hd
    exact zero_ne_one hd)

private lemma pslB2a_extUnit_one {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (e : Matrix (Fin n) (Fin n) K) (he : e ∈ pslAlg B) (hidem : e * e = e) :
    pslB2a_extUnit B 1 e he hidem = 1 := by
  apply Units.ext
  show (pslB2a_extMat (1 : SpecialLinearGroup (Fin n) K) e).det = (1 : Kˣ)
  rw [pslB2a_extMat_one, Matrix.det_one]
  simp

private lemma pslB2a_extUnit_mul {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (x y : ↥(pslB2a_C B)) (e : Matrix (Fin n) (Fin n) K) (he : e ∈ pslAlg B)
    (hidem : e * e = e) :
    pslB2a_extUnit B (x * y) e he hidem =
      pslB2a_extUnit B x e he hidem * pslB2a_extUnit B y e he hidem := by
  apply Units.ext
  show (pslB2a_extMat (((x * y : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K)) e).det =
    (pslB2a_extMat ((x : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) e).det *
    (pslB2a_extMat ((y : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) e).det
  have hxe : (((x : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * e =
      e * (((x : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) :=
    pslB2a_comm_of_comm (pslB2a_C_comm_B x) e he
  have hye : (((y : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * e =
      e * (((y : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) :=
    pslB2a_comm_of_comm (pslB2a_C_comm_B y) e he
  have hxy : ((x * y : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) =
      ((x : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) *
        ((y : ↥(pslB2a_C B)) : SpecialLinearGroup (Fin n) K) :=
    Subgroup.coe_mul (pslB2a_C B) x y
  rw [hxy, pslB2a_extMat_mul hye hidem, Matrix.det_mul]

private noncomputable def pslB2a_Phi {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P) :
    ↥(pslB2a_C B) →* (P → Kˣ) where
  toFun x := fun e =>
    pslB2a_extUnit B x (e : Matrix (Fin n) (Fin n) K)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).1)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).2.1.eq)
  map_one' := by
    funext e
    exact pslB2a_extUnit_one B (e : Matrix (Fin n) (Fin n) K)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).1)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).2.1.eq)
  map_mul' := by
    intro x y
    funext e
    exact pslB2a_extUnit_mul B x y (e : Matrix (Fin n) (Fin n) K)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).1)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).2.1.eq)

private noncomputable def pslB2a_extSL {n : ℕ} {K : Type} [Field K]
    (x : SpecialLinearGroup (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (hdet : (pslB2a_extMat x e).det = 1) : SpecialLinearGroup (Fin n) K :=
  ⟨pslB2a_extMat x e, hdet⟩

private lemma pslB2a_extSL_mem_block {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {x : SpecialLinearGroup (Fin n) K} {e : Matrix (Fin n) (Fin n) K}
    (he : e ∈ pslAlg B) (hidem : e * e = e)
    (hxB : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K))
    (hdet : (pslB2a_extMat x e).det = 1) :
    pslB2a_extSL x e hdet ∈ pslBlock B e := by
  rw [pslBlock, glBlockCentralizer, Subgroup.mem_comap, Subgroup.mem_inf]
  constructor
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    apply Units.ext
    show (B : Matrix (Fin n) (Fin n) K) * pslB2a_extMat x e =
      pslB2a_extMat x e * (B : Matrix (Fin n) (Fin n) K)
    have heB : e * (B : Matrix (Fin n) (Fin n) K) = (B : Matrix (Fin n) (Fin n) K) * e :=
      (pslB2a_comm_of_comm (B := B) (x := (B : Matrix (Fin n) (Fin n) K)) rfl e he).symm
    have h1 : (B : Matrix (Fin n) (Fin n) K) * ((x : Matrix (Fin n) (Fin n) K) * e) =
        ((x : Matrix (Fin n) (Fin n) K) * e) * (B : Matrix (Fin n) (Fin n) K) := by
      rw [← Matrix.mul_assoc, hxB, Matrix.mul_assoc, ← heB, ← Matrix.mul_assoc]
    have h2 : (B : Matrix (Fin n) (Fin n) K) * (1 - e) =
        (1 - e) * (B : Matrix (Fin n) (Fin n) K) := by
      rw [Matrix.mul_sub, Matrix.mul_one, ← heB, Matrix.sub_mul, Matrix.one_mul]
    unfold pslB2a_extMat
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2]
  · show pslB2a_extMat x e * (1 - e) = 1 - e
    unfold pslB2a_extMat
    noncomm_ring [hidem]

private lemma pslB2a_toGL_injective {n : ℕ} {K : Type} [Field K] :
    Function.Injective (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K → GL (Fin n) K) := by
  intro a b h
  apply Subtype.ext
  have h' := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) h
  simpa only [SpecialLinearGroup.coe_GL_coe_matrix] using h'

private lemma pslB2a_mat_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (P : Finset (Matrix ι ι F)) (hPsum : ∑ p ∈ P, p = 1)
    (horth : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p * q = 0)
    {M N e e' : Matrix ι ι F} (he : e ∈ P) (he' : e' ∈ P) (hne : e ≠ e')
    (hMP : ∀ p ∈ P, M * p = p * M) (hNP : ∀ p ∈ P, N * p = p * N)
    (hMfix : M * (1 - e) = 1 - e) (hNfix : N * (1 - e') = 1 - e') :
    M * N = N * M := by
  have hMNp : ∀ p ∈ P, M * N * p = N * M * p := by
    intro p hp
    by_cases hpe : p = e
    · rw [hpe]
      have hNe : N * e = e := by
        calc N * e = N * ((1 - e') * e) := by
              rw [sub_mul, one_mul, horth e' he' e he hne.symm, sub_zero]
          _ = (N * (1 - e')) * e := by rw [mul_assoc]
          _ = (1 - e') * e := by rw [hNfix]
          _ = e := by rw [sub_mul, one_mul, horth e' he' e he hne.symm, sub_zero]
      have hNMe : N * (M * e) = M * e := by
        have h1 : (1 - e') * (M * e) = M * e := by
          rw [sub_mul, one_mul, ← mul_assoc, ← hMP e' he', mul_assoc,
            horth e' he' e he hne.symm, mul_zero, sub_zero]
        calc N * (M * e) = N * ((1 - e') * (M * e)) := by rw [h1]
          _ = (N * (1 - e')) * (M * e) := by rw [mul_assoc]
          _ = (1 - e') * (M * e) := by rw [hNfix]
          _ = M * e := h1
      calc M * N * e = M * (N * e) := by rw [mul_assoc]
        _ = M * e := by rw [hNe]
        _ = N * (M * e) := hNMe.symm
        _ = N * M * e := by rw [mul_assoc]
    · by_cases hpe' : p = e'
      · rw [hpe']
        have hMe' : M * e' = e' := by
          calc M * e' = M * ((1 - e) * e') := by
                rw [sub_mul, one_mul, horth e he e' he' hne, sub_zero]
            _ = (M * (1 - e)) * e' := by rw [mul_assoc]
            _ = (1 - e) * e' := by rw [hMfix]
            _ = e' := by rw [sub_mul, one_mul, horth e he e' he' hne, sub_zero]
        have hMNe' : M * (N * e') = N * e' := by
          have h1 : (1 - e) * (N * e') = N * e' := by
            rw [sub_mul, one_mul, ← mul_assoc, ← hNP e he, mul_assoc,
              horth e he e' he' hne, mul_zero, sub_zero]
          calc M * (N * e') = M * ((1 - e) * (N * e')) := by rw [h1]
            _ = (M * (1 - e)) * (N * e') := by rw [mul_assoc]
            _ = (1 - e) * (N * e') := by rw [hMfix]
            _ = N * e' := h1
        calc M * N * e' = M * (N * e') := by rw [mul_assoc]
          _ = N * e' := hMNe'
          _ = N * (M * e') := by rw [hMe']
          _ = N * M * e' := by rw [mul_assoc]
      · have hMp : M * p = p := by
          have h1 : (1 - e) * p = p := by
            rw [sub_mul, one_mul, horth e he p hp (fun h => hpe h.symm), sub_zero]
          calc M * p = M * ((1 - e) * p) := by rw [h1]
            _ = (M * (1 - e)) * p := by rw [mul_assoc]
            _ = (1 - e) * p := by rw [hMfix]
            _ = p := h1
        have hNp : N * p = p := by
          have h1 : (1 - e') * p = p := by
            rw [sub_mul, one_mul, horth e' he' p hp (fun h => hpe' h.symm), sub_zero]
          calc N * p = N * ((1 - e') * p) := by rw [h1]
            _ = (N * (1 - e')) * p := by rw [mul_assoc]
            _ = (1 - e') * p := by rw [hNfix]
            _ = p := h1
        calc M * N * p = M * (N * p) := by rw [mul_assoc]
          _ = M * p := by rw [hNp]
          _ = p := hMp
          _ = N * p := hNp.symm
          _ = N * (M * p) := by rw [hMp]
          _ = N * M * p := by rw [mul_assoc]
  have hsum : M * N * (∑ p ∈ P, p) = N * M * (∑ p ∈ P, p) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hMNp p hp)
  rwa [hPsum, mul_one, mul_one] at hsum

private lemma pslB2a_blocks_commute {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {P : Finset (Matrix (Fin n) (Fin n) K)} (hP : PrimFamily (pslAlg B) P)
    {e e' : Matrix (Fin n) (Fin n) K} (he : e ∈ P) (he' : e' ∈ P) (hne : e ≠ e')
    (x : SpecialLinearGroup (Fin n) K) (hx : x ∈ pslBlock B e)
    (y : SpecialLinearGroup (Fin n) K) (hy : y ∈ pslBlock B e') :
    x * y = y * x := by
  have hxP : ∀ p ∈ P, (x : Matrix (Fin n) (Fin n) K) * p =
      p * (x : Matrix (Fin n) (Fin n) K) := by
    intro p hp
    exact pslB2a_comm_of_comm (pslB2a_mem_block_comm_B hx) p (((hP.1 p).1 hp).1)
  have hyP : ∀ p ∈ P, (y : Matrix (Fin n) (Fin n) K) * p =
      p * (y : Matrix (Fin n) (Fin n) K) := by
    intro p hp
    exact pslB2a_comm_of_comm (pslB2a_mem_block_comm_B hy) p (((hP.1 p).1 hp).1)
  have hxy := pslB2a_mat_commute P hP.2.2 hP.2.1 he he' hne hxP hyP
    (pslB2a_mem_block_fix hx) (pslB2a_mem_block_fix hy)
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_mul] using hxy

private lemma pslB2a_exists_prod {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
    (j : U →* GL ι F) (G : Matrix ι ι F → Subgroup U)
    (P : Finset (Matrix ι ι F))
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

private lemma pslB2a_eq_of_blocks {U ι F : Type} [Group U] [Fintype ι] [DecidableEq ι] [Field F]
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

private lemma pslB2a_extMat_mul_self {n : ℕ} {K : Type} [Field K]
    (x : SpecialLinearGroup (Fin n) K) (e : Matrix (Fin n) (Fin n) K)
    (hidem : e * e = e) :
    pslB2a_extMat x e * e = (x : Matrix (Fin n) (Fin n) K) * e := by
  unfold pslB2a_extMat
  rw [add_mul, mul_assoc, hidem, sub_mul, one_mul, hidem, sub_self, add_zero]

private lemma pslB2a_Phi_ker_le_join {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (pslAlg B) P) :
    ∀ x : ↥(pslB2a_C B), pslB2a_Phi B P hP x = 1 →
      (x : SpecialLinearGroup (Fin n) K) ∈ ⨆ e ∈ P, pslBlock B e := by
  intro x hx
  have hdet : ∀ e : {p // p ∈ P},
      (pslB2a_extMat (x : SpecialLinearGroup (Fin n) K)
        (e : Matrix (Fin n) (Fin n) K)).det = 1 := by
    intro e
    have h := congrFun hx e
    have h2 : pslB2a_extUnit B x (e : Matrix (Fin n) (Fin n) K)
        (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).1)
        (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).2.1.eq) = 1 := h
    have h' := congrArg (fun u : Kˣ => (u : K)) h2
    simpa only [pslB2a_extUnit, Units.val_mk0, Units.val_one] using h'
  let g : ∀ e : {p // p ∈ P}, pslBlock B (e : Matrix (Fin n) (Fin n) K) := fun e =>
    ⟨pslB2a_extSL (x : SpecialLinearGroup (Fin n) K) (e : Matrix (Fin n) (Fin n) K) (hdet e),
      pslB2a_extSL_mem_block
        (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).1)
        (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).2.1.eq)
        (pslB2a_C_comm_B x) (hdet e)⟩
  obtain ⟨w, hw_mem, hw_eq⟩ := pslB2a_exists_prod (SpecialLinearGroup.toGL) (pslBlock B) P
    hP.2.1
    (fun p hp y hy => pslB2a_mem_block_fix hy)
    (fun p hp y hy => pslB2a_comm_of_comm (pslB2a_mem_block_comm_B hy) p (((hP.1 p).1 hp).1))
    g
  have hwx : w = (x : SpecialLinearGroup (Fin n) K) := by
    apply pslB2a_eq_of_blocks (SpecialLinearGroup.toGL) pslB2a_toGL_injective P hP.2.2
    intro e
    rw [hw_eq e]
    show pslB2a_extMat (x : SpecialLinearGroup (Fin n) K) (e : Matrix (Fin n) (Fin n) K) *
        (e : Matrix (Fin n) (Fin n) K) =
      ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (e : Matrix (Fin n) (Fin n) K)
    exact pslB2a_extMat_mul_self (x : SpecialLinearGroup (Fin n) K)
      (e : Matrix (Fin n) (Fin n) K)
      (((hP.1 (e : Matrix (Fin n) (Fin n) K)).1 e.2).2.1.eq)
  rw [← hwx]
  simpa only [iSup_subtype] using hw_mem

private lemma pslB2a_centralizer_solvable {n : ℕ} {K : Type} [Field K]
    (B : GL (Fin n) K) (P : Finset (Matrix (Fin n) (Fin n) K))
    (hP : PrimFamily (pslAlg B) P)
    (hblock : ∀ e ∈ P, Group.IsSolvable ↥(pslBlock B e)) :
    Group.IsSolvable ↥(pslB2a_C B) := by
  have hJsolv : Group.IsSolvable ↥(⨆ e ∈ P, pslBlock B e) :=
    pslB2a_commuting_join P (fun e => pslBlock B e) hblock
      (fun i hi j hj hij x hx y hy => pslB2a_blocks_commute hP hi hj hij x hx y hy)
  have hJC : (⨆ e ∈ P, pslBlock B e) ≤ pslB2a_C B := by
    apply iSup_le; intro e
    apply iSup_le; intro he
    intro x hx
    simp only [pslB2a_C]
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    rw [hs]
    apply Units.ext
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using
      pslB2a_mem_block_comm_B hx
  haveI : Group.IsSolvable (P → Kˣ) := by
    apply isSolvable_of_comm
    intro a b
    exact mul_comm a b
  have hker : (pslB2a_Phi B P hP).ker ≤ (Subgroup.inclusion hJC).range := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' := pslB2a_Phi_ker_le_join B P hP x hx
    have hrange : (Subgroup.inclusion hJC).range =
        (⨆ e ∈ P, pslBlock B e).subgroupOf (pslB2a_C B) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        rw [Subgroup.mem_subgroupOf]
        simpa using z.2
      · intro hy
        rw [Subgroup.mem_subgroupOf] at hy
        exact ⟨⟨(y : SpecialLinearGroup (Fin n) K), hy⟩, Subtype.ext rfl⟩
    rw [hrange, Subgroup.mem_subgroupOf]
    exact hx'
  exact solvable_of_ker_le_range (Subgroup.inclusion hJC) (pslB2a_Phi B P hP) hker

private lemma pslB2a_scalars_central {n : ℕ} {K : Type} [Field K]
    {a : SpecialLinearGroup (Fin n) K} (ha : a ∈ scalars n K) :
    ∀ b : SpecialLinearGroup (Fin n) K, a * b = b * a := by
  have hcenter : a ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    rw [← scalars_eq_center]
    exact ha
  intro b
  exact (Subgroup.mem_center_iff.mp hcenter b).symm

private noncomputable abbrev pslB2a_slConj {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    SpecialLinearGroup (Fin n) K →* SpecialLinearGroup (Fin n) K :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B

private lemma pslB2a_delta_mem {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) (x : ↥(pslChat B)) :
    (pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
        (x : SpecialLinearGroup (Fin n) K) ∈ scalars n K := by
  have hx : (conjAut n K B) ((proj n K) (x : SpecialLinearGroup (Fin n) K)) =
      (proj n K) (x : SpecialLinearGroup (Fin n) K) := by
    simpa [pslChat, pslCent] using x.2
  rw [conjAut_proj] at hx
  exact (proj_eq_proj_iff).mp hx

private noncomputable def pslB2a_deltaFun {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) (x : ↥(pslChat B)) : ↥(scalars n K) :=
  ⟨(pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
      (x : SpecialLinearGroup (Fin n) K), pslB2a_delta_mem B x⟩

private lemma pslB2a_delta_mul {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) (x y : ↥(pslChat B)) :
    pslB2a_deltaFun B (x * y) = pslB2a_deltaFun B x * pslB2a_deltaFun B y := by
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  simp only [pslB2a_deltaFun, Subgroup.coe_mul]
  have hxmem : (pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
      (x : SpecialLinearGroup (Fin n) K) ∈ scalars n K := pslB2a_delta_mem B x
  have hcent := pslB2a_scalars_central hxmem
  rw [map_mul, _root_.mul_inv_rev]
  have h1 : (pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
      (pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
      ((x : SpecialLinearGroup (Fin n) K) * (y : SpecialLinearGroup (Fin n) K)) =
      (pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
      ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
        (x : SpecialLinearGroup (Fin n) K)) * (y : SpecialLinearGroup (Fin n) K) := by
    group
  rw [h1]
  have h2 : (pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
      ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
        (x : SpecialLinearGroup (Fin n) K)) * (y : SpecialLinearGroup (Fin n) K) =
      ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
        (x : SpecialLinearGroup (Fin n) K)) *
      ((pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
        (y : SpecialLinearGroup (Fin n) K)) := by
    calc (pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
          ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
            (x : SpecialLinearGroup (Fin n) K)) * (y : SpecialLinearGroup (Fin n) K)
        = (pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
            (((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
              (x : SpecialLinearGroup (Fin n) K)) *
              (y : SpecialLinearGroup (Fin n) K)) := by rw [mul_assoc]
      _ = (pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
            ((y : SpecialLinearGroup (Fin n) K) *
              ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
                (x : SpecialLinearGroup (Fin n) K))) := by
            rw [hcent (y : SpecialLinearGroup (Fin n) K)]
      _ = ((pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
            (y : SpecialLinearGroup (Fin n) K)) *
            ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
              (x : SpecialLinearGroup (Fin n) K)) := by rw [mul_assoc]
      _ = ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
            (x : SpecialLinearGroup (Fin n) K)) *
            ((pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
              (y : SpecialLinearGroup (Fin n) K)) := by
            rw [(hcent ((pslB2a_slConj B (y : SpecialLinearGroup (Fin n) K))⁻¹ *
              (y : SpecialLinearGroup (Fin n) K))).symm]
  exact h2

private noncomputable def pslB2a_delta {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) : ↥(pslChat B) →* ↥(scalars n K) :=
  MonoidHom.mk' (pslB2a_deltaFun B) (pslB2a_delta_mul B)

private lemma pslB2a_slConj_eq_self {n : ℕ} {K : Type} [Field K] {B : GL (Fin n) K}
    {x : SpecialLinearGroup (Fin n) K}
    (hxB : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) :
    pslB2a_slConj B x = x := by
  apply Subtype.ext
  change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B) x :
    Matrix (Fin n) (Fin n) K) = (x : Matrix (Fin n) (Fin n) K)
  rw [coe_slConjugation, hxB, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.mul_one]

private lemma pslB2a_C_le_chat {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) : pslB2a_C B ≤ pslChat B := by
  intro x hx
  have hx' : (conjAut n K B) ((proj n K) (x : SpecialLinearGroup (Fin n) K)) =
      (proj n K) (x : SpecialLinearGroup (Fin n) K) := by
    rw [conjAut_proj]
    apply proj_eq_proj_iff.mpr
    change ((pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
      (x : SpecialLinearGroup (Fin n) K)) ∈ scalars n K
    have hxB := pslB2a_C_comm_B ⟨(x : SpecialLinearGroup (Fin n) K), hx⟩
    rw [pslB2a_slConj_eq_self hxB]
    have h1 : (x : SpecialLinearGroup (Fin n) K)⁻¹ * (x : SpecialLinearGroup (Fin n) K) = 1 := by
      group
    rw [h1]
    exact Subgroup.one_mem _
  simpa [pslChat, pslCent] using hx'

private lemma pslB2a_delta_ker {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (B : GL (Fin n) K) :
    (pslB2a_delta B).ker = (pslB2a_C B).subgroupOf (pslChat B) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hval : (pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K))⁻¹ *
        (x : SpecialLinearGroup (Fin n) K) = 1 := by
      have h := congrArg (fun y : ↥(scalars n K) =>
        (y : SpecialLinearGroup (Fin n) K)) hx
      simpa [pslB2a_delta, pslB2a_deltaFun] using h
    have hsl : pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K) =
        (x : SpecialLinearGroup (Fin n) K) := by
      have h := congrArg (fun z => pslB2a_slConj B (x : SpecialLinearGroup (Fin n) K) * z) hval
      rw [mul_one] at h
      rw [← mul_assoc, mul_inv_cancel, one_mul] at h
      exact h.symm
    have hxB : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) := by
      have h2 : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
          (B : Matrix (Fin n) (Fin n) K)⁻¹ = (x : Matrix (Fin n) (Fin n) K) := by
        have h := congrArg (fun y : SpecialLinearGroup (Fin n) K =>
          (y : Matrix (Fin n) (Fin n) K)) hsl
        change ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K B)
          (x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (x : Matrix (Fin n) (Fin n) K) at h
        rw [coe_slConjugation] at h
        rwa [Matrix.GeneralLinearGroup.coe_inv] at h
      have hBinv : (B : Matrix (Fin n) (Fin n) K)⁻¹ * (B : Matrix (Fin n) (Fin n) K) = 1 := by
        rw [← Matrix.GeneralLinearGroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K)
          = (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) *
              (B : Matrix (Fin n) (Fin n) K)⁻¹ * (B : Matrix (Fin n) (Fin n) K) := by
            noncomm_ring [hBinv]
        _ = (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) := by rw [h2]
    simp only [pslB2a_C]
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    apply Units.ext
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using hxB
  · intro hx
    have hxB : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
        (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) :=
      pslB2a_C_comm_B ⟨(x : SpecialLinearGroup (Fin n) K), hx⟩
    have hsl := pslB2a_slConj_eq_self hxB
    change pslB2a_deltaFun B x = 1
    apply Subtype.ext
    simp only [pslB2a_deltaFun, Subgroup.coe_one]
    rw [hsl, inv_mul_cancel]

theorem pslGraph_exists_nonsolvable_block {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {B : GL (Fin n) K}
    (P : Finset (Matrix (Fin n) (Fin n) K)) (hP : PrimFamily (pslAlg B) P)
    (hns : ¬ Group.IsSolvable ↥(pslChat B)) :
    ∃ e ∈ P, ¬ Group.IsSolvable ↥(pslBlock B e) := by
  by_contra hcon
  push Not at hcon
  haveI : Group.IsSolvable ↥(pslB2a_C B) := pslB2a_centralizer_solvable B P hP hcon
  haveI : Group.IsSolvable ↥(scalars n K) := by
    apply isSolvable_of_comm
    intro a b
    exact Subtype.ext (pslB2a_scalars_central a.2 b)
  have hCle : pslB2a_C B ≤ pslChat B := pslB2a_C_le_chat B
  have hker : (pslB2a_delta B).ker ≤ (Subgroup.inclusion hCle).range := by
    intro x hx
    rw [pslB2a_delta_ker B] at hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact ⟨⟨(x : SpecialLinearGroup (Fin n) K), hx⟩, Subtype.ext rfl⟩
  exact hns (solvable_of_ker_le_range (Subgroup.inclusion hCle) (pslB2a_delta B) hker)

end CFSG.StandardType
