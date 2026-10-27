module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelCoordinates

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail QuadraticMap Matrix
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

abbrev Vt (K : Type) [Field K] : Type := (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)

instance instFiniteVtEquiv {K : Type} [Field K] [Finite K] : Finite (Vt K ≃ₗ[K] Vt K) :=
  Finite.of_injective (fun f : Vt K ≃ₗ[K] Vt K => (f : Vt K → Vt K))
    (fun _ _ h => LinearEquiv.ext fun v => congrFun h v)

section Setup

variable {K : Type} [Field K] (b c : K)

noncomputable abbrev U0 : Subgroup (Vt K ≃ₗ[K] Vt K) :=
  tailUnipotent 3 (minusTailForm K b c)

variable {b c}

structure IsPar (g : Vt K ≃ₗ[K] Vt K) (D : GL (Fin 3) K) (L : Fin 3 → Fin 2 → K)
    (C : Matrix (Fin 3) (Fin 3) K) : Prop where
  upper : (D : Matrix (Fin 3) (Fin 3) K).IsUpperTriangular
  diag : ∀ i, (D : Matrix (Fin 3) (Fin 3) K) i i = 1
  alt : Cᵀ = -C
  diag0 : ∀ i, C i i = 0
  eq : g = dMap D 1 * uMap (minusTailForm K b c) L C

theorem exists_par [Finite K] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {g : Vt K ≃ₗ[K] Vt K}
    (hg : g ∈ U0 b c) : ∃ D L C, IsPar (b := b) (c := c) g D L C := by
  obtain ⟨D, L, C, hD, h1, hC, hd, he⟩ :=
    (mem_tailUnipotent_iff (anisotropic_minusTailForm hirr)).1 hg
  exact ⟨D, L, C, ⟨hD, h1, hC, hd, he⟩⟩

theorem IsPar.unique {g : Vt K ≃ₗ[K] Vt K} {D D' : GL (Fin 3) K} {L L' : Fin 3 → Fin 2 → K}
    {C C' : Matrix (Fin 3) (Fin 3) K} (h : IsPar (b := b) (c := c) g D L C)
    (h' : IsPar (b := b) (c := c) g D' L' C') : D = D' ∧ L = L' ∧ C = C' := by
  have := dMap_uMap_injective (h.eq.symm.trans h'.eq)
  exact ⟨this.1, this.2.2.1, this.2.2.2⟩

class AnisoPair (b c : K) : Prop where
  hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0

theorem one_mem_orth : ((1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))) ∈
    TauCeti.QuadraticMap.orthogonalGroup (minusTailForm K b c) := one_mem _

theorem IsPar.mul {g g' : Vt K ≃ₗ[K] Vt K} {D D' : GL (Fin 3) K} {L L' : Fin 3 → Fin 2 → K}
    {C C' : Matrix (Fin 3) (Fin 3) K} (h : IsPar (b := b) (c := c) g D L C)
    (h' : IsPar (b := b) (c := c) g' D' L' C') :
    IsPar (b := b) (c := c) (g * g') (D * D') (conjL D'⁻¹ 1 L + L')
      (mulParam (minusTailForm K b c) (conjL D'⁻¹ 1 L) L'
        (conjC (minusTailForm K b c) D'⁻¹ 1 L C) C') := by
  have hcA := conjC_alternating (one_mem_orth (b := b) (c := c)) D'⁻¹ L h.alt h.diag0
  have hmA := mulParam_alternating (qA := minusTailForm K b c) (conjL D'⁻¹ 1 L) L' hcA.1 hcA.2
    h'.alt h'.diag0
  refine ⟨?_, ?_, hmA.1, hmA.2, ?_⟩
  · rw [Units.val_mul]
    exact Matrix.BlockTriangular.mul h.upper h'.upper
  · intro i
    rw [Units.val_mul, mul_apply_self_of_upperTriangular h.upper h'.upper i, h.diag, h'.diag,
      one_mul]
  · have := dMap_uMap_mul_dMap_uMap (qA := minusTailForm K b c) D D' 1
      (one_mem_orth (b := b) (c := c)) L L' C C'
    rw [h.eq, h'.eq, this]
    simp only [inv_one, mul_one]

end Setup

section Choose

variable {K : Type} [Field K] [Finite K] {b c : K} [AnisoPair b c]

@[expose] noncomputable def par (g : ↥(U0 b c)) :
    GL (Fin 3) K × (Fin 3 → Fin 2 → K) × Matrix (Fin 3) (Fin 3) K :=
  Classical.choose (show ∃ p : GL (Fin 3) K × (Fin 3 → Fin 2 → K) × Matrix (Fin 3) (Fin 3) K,
      IsPar (b := b) (c := c) (g : Vt K ≃ₗ[K] Vt K) p.1 p.2.1 p.2.2 from by
    obtain ⟨D, L, C, h⟩ := exists_par (AnisoPair.hirr (b := b) (c := c)) g.2
    exact ⟨(D, L, C), h⟩)

noncomputable abbrev Dm (g : ↥(U0 b c)) : GL (Fin 3) K := (par g).1

noncomputable abbrev Lp (g : ↥(U0 b c)) : Fin 3 → Fin 2 → K := (par g).2.1

noncomputable abbrev Cp (g : ↥(U0 b c)) : Matrix (Fin 3) (Fin 3) K := (par g).2.2

theorem par_spec (g : ↥(U0 b c)) :
    IsPar (b := b) (c := c) (g : Vt K ≃ₗ[K] Vt K) (Dm g) (Lp g) (Cp g) :=
  Classical.choose_spec (show ∃ p : GL (Fin 3) K × (Fin 3 → Fin 2 → K) × Matrix (Fin 3) (Fin 3) K,
      IsPar (b := b) (c := c) (g : Vt K ≃ₗ[K] Vt K) p.1 p.2.1 p.2.2 from by
    obtain ⟨D, L, C, h⟩ := exists_par (AnisoPair.hirr (b := b) (c := c)) g.2
    exact ⟨(D, L, C), h⟩)

theorem par_eq {g : ↥(U0 b c)} {D : GL (Fin 3) K} {L : Fin 3 → Fin 2 → K}
    {C : Matrix (Fin 3) (Fin 3) K} (h : IsPar (b := b) (c := c) (g : Vt K ≃ₗ[K] Vt K) D L C) :
    Dm g = D ∧ Lp g = L ∧ Cp g = C :=
  IsPar.unique (par_spec g) h

theorem Dm_mul (g g' : ↥(U0 b c)) : Dm (g * g') = Dm g * Dm g' :=
  (par_eq (by
    have := IsPar.mul (par_spec g) (par_spec g')
    exact this : IsPar (b := b) (c := c) ((g * g' : ↥(U0 b c)) : Vt K ≃ₗ[K] Vt K) _ _ _)).1

@[expose] noncomputable def Dhom : ↥(U0 b c) →* GL (Fin 3) K := MonoidHom.mk' Dm Dm_mul

theorem Dhom_apply (g : ↥(U0 b c)) : Dhom g = Dm g := rfl

theorem Dm_diag (g : ↥(U0 b c)) (i : Fin 3) : (Dm g : Matrix (Fin 3) (Fin 3) K) i i = 1 :=
  (par_spec g).diag i

theorem Dm_lower (g : ↥(U0 b c)) {i j : Fin 3} (h : j < i) :
    (Dm g : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
  (par_spec g).upper h

@[expose] noncomputable def da (g : ↥(U0 b c)) : K := (Dm g : Matrix (Fin 3) (Fin 3) K) 0 1

@[expose] noncomputable def db (g : ↥(U0 b c)) : K := (Dm g : Matrix (Fin 3) (Fin 3) K) 1 2

@[expose] noncomputable def dc (g : ↥(U0 b c)) : K := (Dm g : Matrix (Fin 3) (Fin 3) K) 0 2

theorem db_mul (g g' : ↥(U0 b c)) : db (g * g') = db g + db g' := by
  simp only [db, Dm_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  rw [Dm_diag g 1, Dm_diag g' 2, Dm_lower g (show (0 : Fin 3) < 1 by decide)]
  ring

theorem dc_mul (g g' : ↥(U0 b c)) : dc (g * g') = dc g + dc g' + da g * db g' := by
  simp only [dc, da, db, Dm_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
  rw [Dm_diag g 0, Dm_diag g' 2]
  ring

end Choose

end CFSG.RankThree.PartOne.KF1514B
