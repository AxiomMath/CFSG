module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUHypA
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUProj
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParMulEquiv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {K : Type} [Field K] {r ε : ℕ}

private theorem spUCited_pointwise_conj {G : Type} [Group G] (S : Subgroup G) (g : G) :
    MulAut.conj g • S = S.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

theorem uCited_exists_rootParabolic_hypPSU {f : ℕ} (h : UnitaryFieldData 2 f K) (hr : 2 ≤ r)
    (hε : ε ≤ 1) {x : HypIndex r ε → K} (hx0 : x ≠ 0) (hx : hypForm h r ε x x = 0)
    {Sy : Subgroup (hypPSU h r ε)}
    (hSy : ∃ P : Sylow 2 (hypPSU h r ε), (P : Subgroup (hypPSU h r ε)) = Sy)
    (hRSy : (uCitedRoot h r ε x).map (hypProj h r ε) ≤ Sy)
    (hSyR : Sy ≤ Subgroup.normalizer (((uCitedRoot h r ε x).map (hypProj h r ε) :
      Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε))) :
    ∃ X₂ Pα : Subgroup (hypPSU h r ε),
      RootParabolic ((uCitedRoot h r ε x).map (hypProj h r ε)) Sy X₂ Pα 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (hypSU h r ε) := finite_hypSU h
  haveI : Finite (hypPSU h r ε) :=
    Finite.of_surjective (hypProj h r ε) (hypProj_surjective h r ε)
  haveI : Finite (Sylow 2 (hypPSU h r ε)) :=
    Finite.of_injective
      (fun P : Sylow 2 (hypPSU h r ε) => (P : Subgroup (hypPSU h r ε)))
      (fun P Q h => Sylow.ext h)
  obtain ⟨Tbar, hTbar⟩ :=
    (unitary_order_and_Sylow (r := r) (ε := ε) h (by omega) hε).2.2.2.2.1
  have hTbarU : (Tbar : Subgroup (hypPSU h r ε)) =
      (hypUnitriangular h r ε).map (hypProj h r ε) := by
    simpa only [hypProjUnitriangular] using hTbar
  obtain ⟨T0, hT0⟩ := hSy
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (hypPSU h r ε) T0 Tbar
  obtain ⟨s, rfl⟩ := hypProj_surjective h r ε g
  let φ : hypPSU h r ε ≃* hypPSU h r ε := MulAut.conj (hypProj h r ε s)
  have hφSy : Sy.map φ.toMonoidHom = (hypUnitriangular h r ε).map (hypProj h r ε) := by
    have h1 : (↑((hypProj h r ε s) • T0) : Subgroup (hypPSU h r ε)) =
        Sy.map φ.toMonoidHom := by
      rw [Sylow.coe_subgroup_smul, spUCited_pointwise_conj, hT0]
    have h2 : (↑((hypProj h r ε s) • T0) : Subgroup (hypPSU h r ε)) =
        (hypUnitriangular h r ε).map (hypProj h r ε) := by
      rw [hg, hTbarU]
    rw [h1] at h2
    exact h2
  set y : HypIndex r ε → K :=
    (((s : GL (HypIndex r ε) K)) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x with hydef
  have hφRy : ((uCitedRoot h r ε x).map (hypProj h r ε)).map φ.toMonoidHom =
      (uCitedRoot h r ε y).map (hypProj h r ε) := by
    rw [Subgroup.map_map]
    have hcomp : φ.toMonoidHom.comp (hypProj h r ε) =
        (hypProj h r ε).comp (MulAut.conj s).toMonoidHom := by
      ext z
      change MulAut.conj (hypProj h r ε s) (hypProj h r ε z) =
        hypProj h r ε (MulAut.conj s z)
      simp only [MulAut.conj_apply, map_mul, map_inv]
    rw [hcomp, ← Subgroup.map_map, map_conj_uCitedRoot h s hx, hydef]
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hydef] at hy
    refine hx0 (Matrix.mulVec_injective_of_isUnit (Units.isUnit (s : GL (HypIndex r ε) K)) ?_)
    rw [hy, Matrix.mulVec_zero]
  have hy : hypForm h r ε y y = 0 := by
    rw [hydef]
    have h1 : hypForm h r ε (s • x) (s • x) = 0 := by
      rw [hypForm_smul_smul h s x x, hx]
    simpa only [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec] using h1
  have hUR'N : (hypUnitriangular h r ε).map (hypProj h r ε) ≤
      Subgroup.normalizer (((uCitedRoot h r ε y).map (hypProj h r ε) :
        Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε)) := by
    have h1 : Sy.map φ.toMonoidHom ≤
        Subgroup.normalizer (((uCitedRoot h r ε y).map (hypProj h r ε) :
          Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε)) := by
      calc Sy.map φ.toMonoidHom
          ≤ (Subgroup.normalizer (((uCitedRoot h r ε x).map (hypProj h r ε) :
              Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε))).map φ.toMonoidHom :=
            Subgroup.map_mono hSyR
        _ = Subgroup.normalizer ((((uCitedRoot h r ε x).map (hypProj h r ε)).map
              φ.toMonoidHom : Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε)) :=
            Subgroup.map_equiv_normalizer_eq _ φ
        _ = Subgroup.normalizer (((uCitedRoot h r ε y).map (hypProj h r ε) :
              Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε)) := by rw [hφRy]
    rw [← hφSy]
    exact h1
  have hprojroot : (uCitedRoot h r ε y).map (hypProj h r ε) =
      (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))).map
        (hypProj h r ε) :=
    uCited_proj_root_eq_of_normalized h hr hε hy0 hy hUR'N
  have hφR : ((uCitedRoot h r ε x).map (hypProj h r ε)).map φ.toMonoidHom =
      (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))).map
        (hypProj h r ε) :=
    hφRy.trans hprojroot
  refine rootParabolic_exists_of_mulEquiv φ ?_
  exact ⟨(uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K))).map
          (hypProj h r ε),
        (uCitedPar h r ε).map (hypProj h r ε),
        by rw [hφR, hφSy]; exact uCited_rootParabolic_proj h hr hε⟩

end CFSG.LocalAnalysis.WeakClosure81

end
