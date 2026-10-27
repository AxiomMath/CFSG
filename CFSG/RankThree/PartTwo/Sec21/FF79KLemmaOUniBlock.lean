module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110h
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.UnitaryInnerExport

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110h

theorem sl_two_false_of_center_bot {E : Type*} [Field E] (h2 : (2 : E) ≠ 0) {T : Type*}
    [Group T] (g : Matrix.SpecialLinearGroup (Fin 2) E →* T) (hg : Function.Surjective g)
    (hZ : Subgroup.center T = ⊥) (hk : ∀ u, g u = 1 → u ^ 3 = 1) : False := by
  obtain ⟨m, hmv⟩ : ∃ m : Matrix.SpecialLinearGroup (Fin 2) E,
      (m : Matrix (Fin 2) (Fin 2) E) = -1 :=
    ⟨⟨-1, by rw [Matrix.det_neg]; simp⟩, rfl⟩
  have hc : ∀ w : Matrix.SpecialLinearGroup (Fin 2) E, w * m = m * w := by
    intro w
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmv]
    simp
  have hm : g m ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨w, rfl⟩ := hg t
    rw [← map_mul, ← map_mul, hc]
  rw [hZ, Subgroup.mem_bot] at hm
  have h3 := hk m hm
  have h4 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) E =>
    (x : Matrix (Fin 2) (Fin 2) E) 0 0) h3
  simp only [Matrix.SpecialLinearGroup.coe_pow, hmv, Matrix.SpecialLinearGroup.coe_one] at h4
  simp [pow_succ] at h4
  apply h2
  linear_combination -h4

theorem two_ne_zero_of_card {E : Type*} [Field E] [Finite E] {ℓ m : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hm : 1 ≤ m) (hc : Nat.card E = ℓ ^ m) : (2 : E) ≠ 0 := by
  intro h
  haveI : CharP E 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h)
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hn⟩ := FiniteField.card E 2
  rw [Nat.card_eq_fintype_card, hn] at hc
  have h1 : ℓ ∣ 2 ^ (n : ℕ) := hc ▸ dvd_pow_self ℓ (by omega)
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h1))

section Factor

open Polynomial CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

variable {ℓ f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData ℓ f K}
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {B : V →ₛₗ[hK.bar] V →ₗ[K] K} {x : LinearMap.GeneralLinearGroup K V}

theorem good_block_a5_false (H : UnitaryPrimaryData hK.bar B x)
    (a : primaryFactors (x : Module.End K V)) (ha : IsGoodBlock hK x a) (hℓ2 : ℓ ≠ 2)
    {T : Type} [Group T] (g : ↥(specialBlock B x (a : K[X])) →* T) (hg : Function.Surjective g)
    (hker : g.ker ≤ Subgroup.center _) (hker3 : ∀ u ∈ g.ker, u ^ 3 = 1)
    (hZ : Subgroup.center T = ⊥)
    (hL : Nonempty ((T ⧸ Subgroup.center T) ≃* alternatingGroup (Fin 5))) : False := by
  haveI := hK.finite
  haveI : CharP K ℓ := hK.charP
  have hd : 1 ≤ (a : K[X]).natDegree :=
    Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors a.2)
  have hℓ1 : 1 ≤ ℓ := hK.prime.one_lt.le
  have hℓ3 : 3 ≤ ℓ := by have := hK.prime.two_le; omega
  have hfd : 1 ≤ f * (a : K[X]).natDegree := Nat.mul_pos hK.one_le hd
  haveI : Finite (AdjoinRoot (a : K[X])) := Module.finite_of_finite K
  have hm2 : 2 ≤ primaryMultiplicity (x : Module.End K V) (a : K[X]) := ha.1
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · obtain ⟨hE, Hf, hHf, hHfl, ⟨e⟩⟩ :=
      nonempty_specialBlock_mulEquiv_sesqSU hself (selfDualPrimaryBlock H a hself)
    rcases Nat.lt_or_ge (primaryMultiplicity (x : Module.End K V) (a : K[X])) 3 with hm | hm
    · have hV : Module.finrank (AdjoinRoot (a : K[X]))
          (primaryComponent (x : Module.End K V) (a : K[X])) = 2 := by
        have : primaryMultiplicity (x : Module.End K V) (a : K[X]) = 2 := by omega
        exact this
      obtain ⟨e2⟩ :=
        CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hE hHf hHfl hV
      haveI : Finite hE.fixedField := inferInstance
      have hcardF : Nat.card hE.fixedField = ℓ ^ (f * (a : K[X]).natDegree) :=
        hE.card_fixedField
      refine sl_two_false_of_center_bot (two_ne_zero_of_card hK.prime hℓ2 hfd hcardF)
        (g.comp (e.trans e2).symm.toMonoidHom) (hg.comp (e.trans e2).symm.surjective) hZ
        (fun u hu => ?_)
      have h1 := congrArg (e.trans e2) (hker3 _ hu)
      simpa [map_pow] using h1
    · obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis hHf hHfl
      obtain ⟨e3⟩ :=
        CFSG.RankThree.CentralLift.nonempty_sesqSpecialUnitaryGroup_mulEquiv_gramSU hE b
          (G := (1 : Matrix (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X]))))
            (Fin (Module.finrank (AdjoinRoot (a : K[X]))
            (primaryComponent (x : Module.End K V) (a : K[X])))) (AdjoinRoot (a : K[X]))))
          (fun i j => by rw [hb i j, Matrix.one_apply])
      let e4 := (e.trans e3).trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU hE _).symm)
      have hφ := InputsL33.ker_comp_mulEquiv_le_center e4.symm g hker
      exact (su_a5_false (m := primaryMultiplicity (x : Module.End K V) (a : K[X])) hE hm
        (g.comp e4.symm.toMonoidHom) (hg.comp e4.symm.surjective) hφ hL)
  · obtain ⟨e⟩ := nonempty_specialBlock_mulEquiv_SL (pairedPrimaryBlock H a (Ne.symm hself))
    have hcard : Nat.card (AdjoinRoot (a : K[X])) = ℓ ^ (2 * (f * (a : K[X]).natDegree)) :=
      natCard_adjoinRoot hK
    have hφ := InputsL33.ker_comp_mulEquiv_le_center e.symm g hker
    obtain ⟨-, h45⟩ := sl_a5 hm2 (g.comp e.symm.toMonoidHom) (hg.comp e.symm.surjective) hφ hL
    have h3 : 3 ≤ ℓ ^ (f * (a : K[X]).natDegree) :=
      le_trans hℓ3 (Nat.le_self_pow (by omega) ℓ)
    rw [hcard, mul_comm 2, pow_mul] at h45
    rcases h45 with h | h <;> nlinarith

end Factor

end CFSG.RankThree.PartTwo.Sec21.FF79
