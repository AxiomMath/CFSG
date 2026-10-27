module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofD4
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRankOne
public import CFSG.RankThree.SteinbergR3EEvenQuadraticSL2Fixed
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Zs

open Matrix
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem sl2_central_eq_one {F : Type} [Field F] {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (hB3 : B ^ 3 = 1) (hB : ∀ A : Matrix.SpecialLinearGroup (Fin 2) F, A * B = B * A) :
    B = 1 := by
  have hu' : (B : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (B : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F)) (hB (CFSG.LieType.Chevalley.uSL 1))
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    have e : ((CFSG.LieType.Chevalley.uSL 1 : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = !![1, 1; 0, 1] := rfl
    rw [e] at h
    exact h.symm
  have hl' : (B : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (B : Matrix (Fin 2) (Fin 2) F) := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F)) (hB (CFSG.LieType.Chevalley.vSL 1))
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    have e : ((CFSG.LieType.Chevalley.vSL 1 : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := rfl
    rw [e] at h
    exact h.symm
  have hsc := CFSG.RankThree.QuadraticSL2.eq_scalar_of_commute _ hu' hl'
  set c := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with hc
  have hdet : c ^ 2 = 1 := by
    have h := B.2
    rw [Matrix.det_fin_two, hsc] at h
    simpa [Matrix.scalar_apply, Matrix.diagonal, sq] using h
  have h3 : c ^ 3 = 1 := by
    have h := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 0) hB3
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_apply_eq] at h
    rw [hsc, ← map_pow] at h
    simpa [Matrix.scalar_apply] using h
  have hc1 : c = 1 := by
    have h := h3
    rw [show c ^ 3 = c * c ^ 2 by ring, hdet, mul_one] at h
    exact h
  apply Subtype.ext
  rw [hsc, hc1, Matrix.SpecialLinearGroup.coe_one, map_one]

theorem central_eq_one_of_injective {F : Type} [Field F] {G : Type} [Group G]
    (ι : Matrix.SpecialLinearGroup (Fin 2) F →* G) (hι : Function.Injective ι) {s : G}
    (hs : ∃ B, ι B = s) (hcomm : ∀ A, ι A * s = s * ι A) (hs3 : s ^ 3 = 1) : s = 1 := by
  obtain ⟨B, rfl⟩ := hs
  have hB : ∀ A, A * B = B * A := fun A => hι (by rw [map_mul, map_mul]; exact hcomm A)
  have hB3 : B ^ 3 = 1 := hι (by rw [map_pow, map_one]; exact hs3)
  rw [sl2_central_eq_one hB3 hB, map_one]

section SCentre


theorem d4ShortSL2_central_eq_one {K : Type} [Field K] {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : s ∈ KS11Lie4Proof.d4ShortSL2 K σ.toRingHom)
    (hsC : s ∈ Subgroup.centralizer ((KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :
        Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    (hs3 : s ^ 3 = 1) : s = 1 := by
  set ι := orbitRankOneHom TwistTag.D4 K σ.toRingHom KS11Lie4Proof.d4Outer with hι
  have hinj : Function.Injective ι :=
    CFSG.LieType.Chevalley.orbitRankOneHom_injective_D4 hσ3 KS11Lie4Proof.d4Outer
  have hex : ∃ B, ι B = s.1 := by
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.1 (Subgroup.mem_comap.1 hs)
    exact ⟨B, hB⟩
  have hcomm : ∀ A, ι A * s.1 = s.1 * ι A := fun A => by
    have hmem : ι A ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      CFSG.RankThree.Chevalley.orbitRankOneHom_mem_graphFixedRootGroup (t := TwistTag.D4)
        (K := K) (σ := σ.toRingHom) KS11Lie4Proof.d4Outer A
    have hmemS : (⟨ι A, hmem⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
        KS11Lie4Proof.d4ShortSL2 K σ.toRingHom :=
      Subgroup.mem_comap.2 (MonoidHom.mem_range.2 ⟨A, rfl⟩)
    have h := Subgroup.mem_centralizer_iff.1 hsC _ hmemS
    exact congrArg Subtype.val h
  have hs3' : s.1 ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hs3, Subgroup.coe_one]
  have h1 : s.1 = 1 := central_eq_one_of_injective ι hinj hex hcomm hs3'
  exact Subtype.ext h1

end SCentre

end CFSG.RankThree.PartTwo.Sec11.Item1118Res3ProofU3Zs

end
