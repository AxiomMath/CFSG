module

public import CFSG.Milestones.ASVolI.A3Lie
public import CFSG.Milestones.ASVolI.A3L3.Sylow

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.ASVolI.ChA
open scoped MatrixGroups

section L3

variable {F : Type} [Field F]

@[expose] noncomputable def burnsideA315y_l3c (F : Type) [Field F] :
    ↥(⊤ : Subgroup (GL (Fin 3) F)) →* MulAut PSL(3, F) where
  toFun g := psl3DiagAut (g : GL (Fin 3) F)
  map_one' := burnsideA315h_diag_one F
  map_mul' a b := burnsideA315h_diag_mul (a : GL (Fin 3) F) b

theorem burnsideA315y_l3c_apply (g : ↥(⊤ : Subgroup (GL (Fin 3) F))) :
    burnsideA315y_l3c F g = psl3DiagAut (g : GL (Fin 3) F) :=
  rfl

theorem burnsideA315y_l3_diag_scalar (μ : Fˣ) :
    psl3DiagAut (Matrix.GeneralLinearGroup.scalar (Fin 3) μ) = 1 := by
  apply (burnsideA315h_Phi F).injective
  rw [burnsideA315h_Phi_diag, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_scalar,
    map_one]

theorem burnsideA315y_l3_ker [Finite F] (g : ↥(⊤ : Subgroup (GL (Fin 3) F))) :
    burnsideA315y_l3c F g = 1 ↔
      ∃ μ : Fˣ, (g : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ := by
  rw [burnsideA315y_l3c_apply]
  constructor
  · intro h
    have h1 : psl3DiagAut (g : GL (Fin 3) F) * psl3FieldAut (1 : RingAut F) = 1 := by
      rw [burnsideA315h_field_one, mul_one]
      exact h
    obtain ⟨-, μ, hμ⟩ := burnsideA315h_diagfield_eq_one h1
    exact ⟨μ, hμ.symm⟩
  · rintro ⟨μ, hμ⟩
    rw [hμ]
    exact burnsideA315y_l3_diag_scalar μ

@[expose] noncomputable def burnsideA315y_blkGL (A : Matrix (Fin 2) (Fin 2) F) (hA : A.det = 1) :
    GL (Fin 3) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (blkMat A 1) (by
    rw [det_blkMat, hA, mul_one]
    exact one_ne_zero)

theorem burnsideA315y_l3_charP [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    CharP F p := by
  have := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF, pow_one])

theorem burnsideA315y_l3_exists_xy [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p) :
    ∃ x y : F, x ^ 2 + y ^ 2 = -1 := by
  haveI := burnsideA315y_l3_charP hF
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  refine ⟨ZMod.castHom (dvd_refl p) F a, ZMod.castHom (dvd_refl p) F b, ?_⟩
  rw [← map_pow, ← map_pow, ← map_add, hab, map_neg, map_one]

theorem burnsideA315y_l3_two_ne [Finite F] {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (hp2 : p ≠ 2) : (2 : F) ≠ 0 := by
  haveI := burnsideA315y_l3_charP hF
  intro h
  have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff F p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem burnsideA315y_l3_det_qb {x y : F} (hxy : x ^ 2 + y ^ 2 = -1) :
    ((1 : F) • burnsideA315y_qb x y).det = 1 := by
  rw [burnsideA315y_det_qb, one_pow, one_mul, hxy, neg_neg]

@[expose] noncomputable def burnsideA315y_l3Model [Finite F] (x y : F) (hxy : x ^ 2 + y ^ 2 = -1)
    (two_ne : (2 : F) ≠ 0) : burnsideA315y_Model F (MulAut PSL(3, F)) :=
  burnsideA315y_Model.ofData ⊤ (burnsideA315y_l3c F) burnsideA315y_l3_ker ⟨negDiag3 F, trivial⟩ rfl
    x y 1 (by rw [one_pow, one_mul, hxy])
    ⟨burnsideA315y_blkGL (burnsideA315y_qa F) burnsideA315y_det_qa, trivial⟩
    ⟨burnsideA315y_blkGL ((1 : F) • burnsideA315y_qb x y) (burnsideA315y_l3_det_qb hxy), trivial⟩
    rfl rfl two_ne

variable [Finite F] {x y : F} {hxy : x ^ 2 + y ^ 2 = -1} {two_ne : (2 : F) ≠ 0}

theorem burnsideA315y_l3Model_c (g : ↥(burnsideA315y_l3Model x y hxy two_ne).Γ) :
    (burnsideA315y_l3Model x y hxy two_ne).c g = psl3DiagAut (g : GL (Fin 3) F) :=
  rfl

end L3

end CFSG.ASVolI
