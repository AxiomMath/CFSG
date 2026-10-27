module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimRep
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimOrth
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Extension
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesDecomp
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

public section

namespace CFSG.StandardType

namespace NSJoin

open CFSG CFSG.Assembly
open CFSG.OddStandard.SmallF3.Omega
open TauCeti
open QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem nsPerp_radical_restrict_polar {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {W : Submodule (ZMod 3) V} {x : W}
    (hx : x ∈ (Q.restrict W).radical) (y : W) : polar Q (x : V) (y : V) = 0 := by
  have hx1 : Q (x : V) = 0 := (QuadraticMap.mem_radical_iff'.mp hx).1
  have hkey : Q ((x : V) + (y : V)) = Q (y : V) :=
    (QuadraticMap.mem_radical_iff'.mp hx).2 y
  rw [QuadraticMap.map_add Q (x : V) (y : V), hx1, zero_add] at hkey
  have h : Q (y : V) + polar Q (x : V) (y : V) = Q (y : V) + 0 := by rw [hkey, add_zero]
  exact add_left_cancel h

private theorem nsPerp_restrict_nondegenerate_isotropic_pair {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {x u : V} (hqx : Q x = 0)
    (hpol : polar Q x u ≠ 0) :
    (Q.restrict (Submodule.span (ZMod 3) ({x, u} : Set V))).Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp z.2
  have hzx : polar Q x (z : V) = 0 := by
    rw [polar_comm]
    exact nsPerp_radical_restrict_polar hz ⟨x, Submodule.subset_span (by simp)⟩
  have hb : b = 0 := by
    have h : polar Q x (z : V) = 0 := hzx
    rw [← hab, polar_add_right, polar_smul_right, polar_smul_right, polar_self, hqx] at h
    simp only [smul_zero, mul_zero, zero_add, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hpol
  have hzu : polar Q (z : V) u = 0 :=
    nsPerp_radical_restrict_polar hz ⟨u, Submodule.subset_span (by simp)⟩
  have ha : a = 0 := by
    rw [← hab, hb, zero_smul, add_zero, polar_smul_left, smul_eq_mul] at hzu
    exact (mul_eq_zero.mp hzu).resolve_right hpol
  apply Subtype.ext
  simp [← hab, ha, hb]

private theorem nsPerp_linearIndependent_isotropic_pair {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {x u : V} (hx : x ≠ 0)
    (hqx : Q x = 0) (hpol : polar Q x u ≠ 0) :
    LinearIndependent (ZMod 3) ![x, u] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have ht : t = 0 := by
    have h := congrArg (fun z => polar Q z x) hst
    simp only [polar_add_left, polar_smul_left, polar_smul_right, polar_self, hqx,
      polar_zero_left, smul_zero, zero_add] at h
    rw [polar_comm Q u x, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_right hpol
  have hs : s = 0 := by
    have h := hst
    rw [ht, zero_smul, add_zero] at h
    exact (smul_eq_zero.mp h).resolve_right hx
  exact ⟨hs, ht⟩

private theorem nsPerp_finrank_span_isotropic_pair {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {x u : V} (hx : x ≠ 0)
    (hqx : Q x = 0) (hpol : polar Q x u ≠ 0) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({x, u} : Set V)) = 2 := by
  have hli := nsPerp_linearIndependent_isotropic_pair hx hqx hpol
  have hrange : Set.range ![x, u] = ({x, u} : Set V) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h := finrank_span_eq_card hli
  rw [hrange] at h
  simpa using h

private theorem nsPerp_exists_ne_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) (x : V)
    (hx : x ≠ 0) {c : ZMod 3} (hc : c ≠ 0) :
    ∃ w : V, QuadraticMap.polar Q w x = 0 ∧ Q w = c := by
  have hQnd : Q.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mp hQ
  have hex : ∃ u, polar Q x u ≠ 0 := by
    by_contra h
    have hx0 : x = 0 := hQ.1 x (by
      intro y
      by_contra hy
      exact h ⟨y, by simpa only [QuadraticMap.polarBilin_apply_apply] using hy⟩)
    exact hx hx0
  rcases hdim with h4 | h5
  · by_cases hqx : Q x = 0
    · obtain ⟨u, hpol⟩ := hex
      let H0 : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({x, u} : Set V)
      let H : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin H0
      have hH0nd : (Q.restrict H0).Nondegenerate := by
        dsimp [H0]
        exact nsPerp_restrict_nondegenerate_isotropic_pair hqx hpol
      have hHnd : (Q.restrict H).Nondegenerate :=
        QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal hQnd hH0nd
      have hfr0 : Module.finrank (ZMod 3) H0 = 2 := by
        dsimp [H0]
        exact nsPerp_finrank_span_isotropic_pair hx hqx hpol
      have hdimH : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V - 2 := by
        dsimp [H]
        rw [LinearMap.BilinForm.finrank_orthogonal hQ, hfr0]
      have h2 : 2 ≤ Module.finrank (ZMod 3) H := by rw [hdimH]; omega
      obtain ⟨w, hwQ⟩ := ff_exists_eq_of_nondegenerate (R := Q.restrict H) hHnd h2 hc
      refine ⟨(w : V), ?_, ?_⟩
      · have hmem := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) x
          (Submodule.subset_span (by simp))
        rw [QuadraticMap.polarBilin_apply_apply] at hmem
        rw [polar_comm]
        exact hmem
      · simpa only [QuadraticMap.restrict_apply] using hwQ
    · let H0 : Submodule (ZMod 3) V := Submodule.span (ZMod 3) {x}
      let H : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin H0
      have hH0nd : (Q.restrict H0).Nondegenerate := by
        dsimp [H0]
        exact ff_restrict_nondegenerate_single hqx
      have hHnd : (Q.restrict H).Nondegenerate :=
        QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal hQnd hH0nd
      have hdimH : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V - 1 := by
        dsimp [H]
        rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hx]
      have h2 : 2 ≤ Module.finrank (ZMod 3) H := by rw [hdimH]; omega
      obtain ⟨w, hwQ⟩ := ff_exists_eq_of_nondegenerate (R := Q.restrict H) hHnd h2 hc
      refine ⟨(w : V), ?_, ?_⟩
      · have hmem := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) x
          (Submodule.mem_span_singleton_self x)
        rw [QuadraticMap.polarBilin_apply_apply] at hmem
        rw [polar_comm]
        exact hmem
      · simpa only [QuadraticMap.restrict_apply] using hwQ
  · by_cases hqx : Q x = 0
    · obtain ⟨u, hpol⟩ := hex
      let H0 : Submodule (ZMod 3) V := Submodule.span (ZMod 3) ({x, u} : Set V)
      let H : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin H0
      have hH0nd : (Q.restrict H0).Nondegenerate := by
        dsimp [H0]
        exact nsPerp_restrict_nondegenerate_isotropic_pair hqx hpol
      have hHnd : (Q.restrict H).Nondegenerate :=
        QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal hQnd hH0nd
      have hfr0 : Module.finrank (ZMod 3) H0 = 2 := by
        dsimp [H0]
        exact nsPerp_finrank_span_isotropic_pair hx hqx hpol
      have hdimH : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V - 2 := by
        dsimp [H]
        rw [LinearMap.BilinForm.finrank_orthogonal hQ, hfr0]
      have h2 : 2 ≤ Module.finrank (ZMod 3) H := by rw [hdimH]; omega
      obtain ⟨w, hwQ⟩ := ff_exists_eq_of_nondegenerate (R := Q.restrict H) hHnd h2 hc
      refine ⟨(w : V), ?_, ?_⟩
      · have hmem := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) x
          (Submodule.subset_span (by simp))
        rw [QuadraticMap.polarBilin_apply_apply] at hmem
        rw [polar_comm]
        exact hmem
      · simpa only [QuadraticMap.restrict_apply] using hwQ
    · let H0 : Submodule (ZMod 3) V := Submodule.span (ZMod 3) {x}
      let H : Submodule (ZMod 3) V := LinearMap.BilinForm.orthogonal Q.polarBilin H0
      have hH0nd : (Q.restrict H0).Nondegenerate := by
        dsimp [H0]
        exact ff_restrict_nondegenerate_single hqx
      have hHnd : (Q.restrict H).Nondegenerate :=
        QuadraticMap.Nondegenerate.nondegenerate_restrict_orthogonal hQnd hH0nd
      have hdimH : Module.finrank (ZMod 3) H = Module.finrank (ZMod 3) V - 1 := by
        dsimp [H]
        rw [LinearMap.BilinForm.finrank_orthogonal hQ, finrank_span_singleton hx]
      have h2 : 2 ≤ Module.finrank (ZMod 3) H := by rw [hdimH]; omega
      obtain ⟨w, hwQ⟩ := ff_exists_eq_of_nondegenerate (R := Q.restrict H) hHnd h2 hc
      refine ⟨(w : V), ?_, ?_⟩
      · have hmem := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.2) x
          (Submodule.mem_span_singleton_self x)
        rw [QuadraticMap.polarBilin_apply_apply] at hmem
        rw [polar_comm]
        exact hmem
      · simpa only [QuadraticMap.restrict_apply] using hwQ

theorem nsOrth_perp_aniso {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 4 ∨ Module.finrank (ZMod 3) V = 5) (x : V)
    {c : ZMod 3} (hc : c ≠ 0) :
    ∃ w : V, QuadraticMap.polar Q w x = 0 ∧ Q w = c := by
  have hQnd : Q.Nondegenerate := (QuadraticMap.nondegenerate_polar_iff).mp hQ
  rcases hdim with h4 | h5
  ·
    have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
    by_cases hx : x = 0
    · subst hx
      obtain ⟨w, hw⟩ := ff_exists_eq_of_nondegenerate hQnd h2 hc
      exact ⟨w, by simp [QuadraticMap.polar], hw⟩
    · exact nsPerp_exists_ne_zero hQ (Or.inl h4) x hx hc
  ·
    have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
    by_cases hx : x = 0
    · subst hx
      obtain ⟨w, hw⟩ := ff_exists_eq_of_nondegenerate hQnd h2 hc
      exact ⟨w, by simp [QuadraticMap.polar], hw⟩
    · exact nsPerp_exists_ne_zero hQ (Or.inr h5) x hx hc

end NSJoin

end CFSG.StandardType

end
