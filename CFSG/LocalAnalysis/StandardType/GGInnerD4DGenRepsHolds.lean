module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4DGenContracts
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeOrthTLift
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalMatrixModelTransport
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessBridge

public section

namespace CFSG.StandardType.GGInnerD4DGenParts

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrdg2_nontrivial {K : Type} [Field K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V}
    (hT : ∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) :
    Nontrivial V := by
  obtain ⟨U, hU, -⟩ := hT
  exact Module.nontrivial_of_finrank_pos (R := K)
    (lt_of_lt_of_le (by omega) (Submodule.finrank_le U))

theorem orthogonalInnerRepresentatives_holds :
    S2MathAs51600Contracts.OrthogonalInnerRepresentatives := by
  intro K _ _ _ V _ _ _ Q hQ hT X _ hX θ A hA hAI
  classical
  haveI : Nontrivial V := ltrdg2_nontrivial hT
  let Ω := CFSG.RankThree.Classical2.orthDerived Q
  let R := CFSG.RankThree.Classical2.ProjOrthDerived Q
  set ρ : Ω →* R := QuotientGroup.mk' _ with hρ
  have hρinj : Function.Injective ρ := by
    have hscal : (CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
        (CFSG.RankThree.Classical2.orthDerived Q) = ⊥ :=
      CFSG.StandardType.OrthRestOdd.scalars_subgroupOf_orthDerived_eq_bot Q hQ
    intro a b hab
    have hmem : a * b⁻¹ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    rw [hρ, QuotientGroup.ker_mk', hscal, Subgroup.mem_bot] at hmem
    calc a = a * b⁻¹ * b := by group
      _ = 1 * b := by rw [hmem]
      _ = b := one_mul b
  have hZ : Subgroup.center R = ⊥ :=
    CFSG.RankThree.PartOne.KCOrthogonalModel.center_projOrthDerived_eq_bot hQ hT
  have hconjinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    CFSG.RankThree.PartOne.KCOrthogonalD4.conj_injective_of_trivial_center hZ
  set c : Ω →* MulAut R := (MulAut.conj : R →* MulAut R).comp ρ with hc
  have hcinj : Function.Injective c := hconjinj.comp hρinj
  set φ : A →* MulAut R := (ggInducedAut θ).comp A.subtype with hφ
  have hφmem : ∀ a : A, ∃ x : Ω, c x = φ a := by
    intro a
    obtain ⟨r, hr⟩ := hAI (a : MulAut X) a.2
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
      ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
        (CFSG.RankThree.Classical2.orthDerived Q)) r
    refine ⟨x, ?_⟩
    show (MulAut.conj : R →* MulAut R) (ρ x) = ggInducedAut θ (a : MulAut X)
    rw [hρ, hx, hr]
  let t0 : A → Ω := fun a => Classical.choose (hφmem a)
  have ht0 : ∀ a : A, c (t0 a) = φ a := fun a => Classical.choose_spec (hφmem a)
  have ht0_one : t0 1 = 1 := by
    apply hcinj
    calc c (t0 1) = φ 1 := ht0 1
      _ = 1 := map_one φ
      _ = c 1 := (map_one c).symm
  have ht0_mul : ∀ a b : A, t0 (a * b) = t0 a * t0 b := by
    intro a b
    apply hcinj
    calc c (t0 (a * b)) = φ (a * b) := ht0 (a * b)
      _ = φ a * φ b := map_mul φ a b
      _ = c (t0 a) * c (t0 b) := by rw [ht0 a, ht0 b]
      _ = c (t0 a * t0 b) := (map_mul c (t0 a) (t0 b)).symm
  let t : A →* Ω :=
    { toFun := t0
      map_one' := ht0_one
      map_mul' := ht0_mul }
  refine ⟨t, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro a b hab
    have hφeq : φ a = φ b := by
      rw [← ht0 a, ← ht0 b]
      change c (t a) = c (t b)
      rw [hab]
    have h1 : (a : MulAut X) = (b : MulAut X) :=
      (ggInducedAut_injective_of_perfect hX θ) (by simpa [hφ] using hφeq)
    exact Subtype.ext h1
  ·
    intro a
    change c (t a) = φ a
    exact ht0 a
  ·
    intro a
    apply hcinj
    change c ((t0 a) ^ 3) = c 1
    calc c ((t0 a) ^ 3) = (c (t0 a)) ^ 3 := map_pow c (t0 a) 3
      _ = (φ a) ^ 3 := by rw [ht0 a]
      _ = φ (a ^ 3) := (map_pow φ a 3).symm
      _ = φ 1 := by rw [show a ^ 3 = 1 from Subtype.ext (hA.2 (a : MulAut X) a.2)]
      _ = 1 := map_one φ
      _ = c 1 := (map_one c).symm
  ·
    intro a b
    rw [commute_iff_eq]
    apply hcinj
    change c (t0 a * t0 b) = c (t0 b * t0 a)
    calc c (t0 a * t0 b) = c (t0 a) * c (t0 b) := map_mul c (t0 a) (t0 b)
      _ = φ a * φ b := by rw [ht0 a, ht0 b]
      _ = φ (a * b) := (map_mul φ a b).symm
      _ = φ (b * a) := by rw [hA.1.is_comm.comm a b]
      _ = φ b * φ a := map_mul φ b a
      _ = c (t0 b) * c (t0 a) := by rw [ht0 b, ht0 a]
      _ = c (t0 b * t0 a) := (map_mul c (t0 b) (t0 a)).symm
  ·
    intro a u hu
    apply hcinj
    rw [show c (t a) = φ a from ht0 a]
    exact hu

end CFSG.StandardType.GGInnerD4DGenParts

end
