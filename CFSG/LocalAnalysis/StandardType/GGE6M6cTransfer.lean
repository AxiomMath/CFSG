module

public import CFSG.LocalAnalysis.StandardType.GGLieM6cFinal
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.RankThree.Classical2.TwistedE6RationalOrder

public noncomputable section

namespace CFSG.StandardType.E6M6cTransfer

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
  CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore

theorem isToralSubgroup_map_baseChangeGL
    {τ : Tag} {L M : Type} [Field L] [Field M] (j : L →+* M)
    {A : Subgroup (ModGL τ L)} (hA : ExcFramesHalf.IsToralSubgroup τ L A) :
    ExcFramesHalf.IsToralSubgroup τ M (A.map (baseChangeGL j)) := by
  obtain ⟨g, hg, hgt⟩ := hA
  refine ⟨baseChangeGL j g, baseChangeGL_mem_adjointGroup j hg, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  exact CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup j (hgt x hx)

section Main


theorem isToral_of_card_eq_three_pow_four {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK3 : 3 ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) :
    ExcFramesHalf.IsToralSubgroup .E6 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup .E6 K).subtype)) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hKf]
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hfodd : Odd (f : ℕ) := by
    rcases Nat.even_or_odd (f : ℕ) with ⟨k, hk⟩ | hn
    · exfalso
      have hdiv : 3 ∣ 2 ^ (f : ℕ) + 1 := by rwa [← hK]
      have hmod : 2 ^ (f : ℕ) % 3 = 1 := by
        rw [hk, ← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      omega
    · exact hn
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Algebra (ZMod 2) K := ZMod.algebra K 2
  haveI : Module.Finite (ZMod 2) K := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod 2) K := Algebra.IsAlgebraic.of_finite (ZMod 2) K
  let ι : K →+* GGL := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := GGL)).toRingHom
  let A : Subgroup (ModGL Tag.E6 GGL) :=
    E.map ((baseChangeGL ι).comp (adjointGroup Tag.E6 K).subtype)
  have hpow : ∀ c : K, c ^ 2 ^ (f : ℕ) = c := by
    intro c
    have h := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hFr : (ggFrobT (f : ℕ)).comp ι = ι := by
    ext c
    rw [RingHom.comp_apply, ggFrobT_apply, ← map_pow, hpow]
  let Φ : ModGL Tag.E6 GGL →* ModGL Tag.E6 GGL := ggPhi StatedLieTag.E6 (f : ℕ)
  have hΦ : Φ = Units.map (entrywiseHom (ggFrobT (f : ℕ))) := rfl
  have hA : A ≤ ratPoints Φ := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨baseChangeGL_mem_adjointGroup ι x.2, ?_⟩
    show Φ (baseChangeGL ι (x : ModGL Tag.E6 K)) =
      baseChangeGL ι (x : ModGL Tag.E6 K)
    rw [hΦ, units_map_entrywiseHom_eq_baseChangeGL]
    rw [show baseChangeGL (ggFrobT (f : ℕ)) (baseChangeGL ι (x : ModGL Tag.E6 K)) =
        baseChangeGL ((ggFrobT (f : ℕ)).comp ι) (x : ModGL Tag.E6 K) from
      baseChangeGL_baseChangeGL (f := ι) (ggFrobT (f : ℕ)) (x : ModGL Tag.E6 K), hFr]
  have hAab : IsElemAbelian 3 A := by
    haveI : IsMulCommutative E := hE.1
    haveI : IsMulCommutative A :=
      Subgroup.map_isMulCommutative (H := E)
        (f := (baseChangeGL ι).comp (adjointGroup Tag.E6 K).subtype)
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨a, ha, hxa⟩ := Subgroup.mem_map.1 hx
    rw [← hxa, ← map_pow]
    have hpa : a ^ 3 = 1 := hE.2 a ha
    rw [hpa, map_one]
  have hinj : Function.Injective
      ((baseChangeGL ι).comp (adjointGroup Tag.E6 K).subtype) := by
    intro x y hxy
    exact (Subgroup.subtype_injective (adjointGroup Tag.E6 K))
      (baseChangeGL_injective ι hxy)
  have hAcard : Nat.card A = 3 ^ 4 := by
    change Nat.card (E.map ((baseChangeGL ι).comp
      (adjointGroup Tag.E6 K).subtype)) = 3 ^ 4
    rw [Subgroup.card_map_of_injective hinj, hcard]
  have hA' : A ≤ (ratPoints (ggPhi StatedLieTag.E6 (f : ℕ)) :
      Subgroup (ModGL Tag.E6 GGL)) := by
    change A ≤ ratPoints Φ
    exact hA
  have htoral : ExcFramesHalf.IsToralSubgroup Tag.E6 GGL A :=
    CFSG.StandardType.LieCore.M6c.ggLieNonToralRankFour_holds (f : ℕ) hf StatedLieTag.E6
      (Or.inl ⟨rfl, hfodd⟩) A hA' hAab hAcard
  letI : Algebra K GGL := ι.toAlgebra
  haveI : IsScalarTower (ZMod 2) K GGL := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact Subsingleton.elim (algebraMap (ZMod 2) GGL)
      ((algebraMap K GGL).comp (algebraMap (ZMod 2) K))
  haveI : Algebra.IsAlgebraic K GGL :=
    Algebra.IsAlgebraic.tower_top (K := ZMod 2) (L := K) (A := GGL)
  let jalg : GGL →ₐ[K] AlgebraicClosure K :=
    IsAlgClosed.lift (R := K) (S := GGL) (M := AlgebraicClosure K)
  let j : GGL →+* AlgebraicClosure K := jalg.toRingHom
  have hjcomp : j.comp ι = algebraMap K (AlgebraicClosure K) := by
    show (jalg : GGL →+* AlgebraicClosure K).comp (algebraMap K GGL) =
      algebraMap K (AlgebraicClosure K)
    exact AlgHom.comp_algebraMap jalg
  have htransfer := isToralSubgroup_map_baseChangeGL (τ := Tag.E6) j htoral
  have hmap : A.map (baseChangeGL j) =
      E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E6 K).subtype) := by
    rw [Subgroup.map_map]
    have hcomp : (baseChangeGL j).comp ((baseChangeGL ι).comp
          (adjointGroup Tag.E6 K).subtype) =
        (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (adjointGroup Tag.E6 K).subtype := by
      rw [← MonoidHom.comp_assoc]
      have hbc : (baseChangeGL (τ := Tag.E6) j).comp (baseChangeGL (τ := Tag.E6) ι) =
          baseChangeGL (τ := Tag.E6) (j.comp ι) := by
        refine MonoidHom.ext fun g => ?_
        exact baseChangeGL_baseChangeGL (τ := Tag.E6) (f := ι) j g
      rw [hbc, hjcomp]
    rw [hcomp]
  rw [hmap] at htransfer
  exact htransfer

end Main

end CFSG.StandardType.E6M6cTransfer
