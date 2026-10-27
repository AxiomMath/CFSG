module

public import CFSG.ClassicalGroups.Orthogonal.Eichler
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.StandardType

open QuadraticMap

private lemma ggOrthE_three_var_zero :
    ∀ q₁ q₂ q₃ r₁₂ r₁₃ r₂₃ : ZMod 3,
      ∃ a b c : ZMod 3, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧
        a * a * q₁ + b * b * q₂ + c * c * q₃ +
          a * b * r₁₂ + a * c * r₁₃ + b * c * r₂₃ = 0 := by
  decide

private lemma ggOrthE_expand {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (e : Fin 3 → V) (a b c : ZMod 3) :
    Q (a • e 0 + b • e 1 + c • e 2) =
      a * a * Q (e 0) + b * b * Q (e 1) + c * c * Q (e 2) +
        a * b * polar Q (e 0) (e 1) + a * c * polar Q (e 0) (e 2) +
        b * c * polar Q (e 1) (e 2) := by
  rw [QuadraticMap.map_add Q, QuadraticMap.map_add Q, QuadraticMap.map_smul,
    QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_add_left,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right]
  ring

private lemma ggOrthE_exists_singular_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (T : Submodule (ZMod 3) V) (hT : 3 ≤ Module.finrank (ZMod 3) T) :
    ∃ v ∈ T, v ≠ 0 ∧ Q v = 0 := by
  let B := Module.finBasis (ZMod 3) T
  let e : Fin 3 → V := fun i => (B (Fin.castLE hT i) : V)
  have he : LinearIndependent (ZMod 3) e := by
    have h1 : LinearIndependent (ZMod 3) (fun i : Fin 3 => B (Fin.castLE hT i)) :=
      B.linearIndependent.comp (Fin.castLE hT) (Fin.castLE_injective hT)
    have h2 : LinearIndependent (ZMod 3) (fun i : Fin 3 => (B (Fin.castLE hT i) : V)) :=
      h1.map' (Submodule.subtype T)
        (LinearMap.ker_eq_bot'.mpr fun m hm => Subtype.val_injective hm)
    simpa [e] using h2
  obtain ⟨a, b, c, hne, hzero⟩ := ggOrthE_three_var_zero (Q (e 0)) (Q (e 1)) (Q (e 2))
    (polar Q (e 0) (e 1)) (polar Q (e 0) (e 2)) (polar Q (e 1) (e 2))
  refine ⟨a • e 0 + b • e 1 + c • e 2, ?_, ?_, ?_⟩
  · have h0 : e 0 ∈ T := (B (Fin.castLE hT 0)).2
    have h1 : e 1 ∈ T := (B (Fin.castLE hT 1)).2
    have h2 : e 2 ∈ T := (B (Fin.castLE hT 2)).2
    exact Submodule.add_mem T (Submodule.add_mem T (Submodule.smul_mem T a h0)
      (Submodule.smul_mem T b h1)) (Submodule.smul_mem T c h2)
  · intro hv
    have hsum : (∑ i : Fin 3, (![a, b, c] : Fin 3 → ZMod 3) i • e i) = 0 := by
      rw [Fin.sum_univ_three]
      simpa using hv
    have hg := (Fintype.linearIndependent_iff.mp he) ![a, b, c] hsum
    have ha : a = 0 := by simpa using hg 0
    have hb : b = 0 := by simpa using hg 1
    have hc : c = 0 := by simpa using hg 2
    rcases hne with h | h | h
    · exact h ha
    · exact h hb
    · exact h hc
  · rw [ggOrthE_expand Q e a b c, hzero]

theorem ggOrth_totallySingularPlane {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Module.Finite (ZMod 3) V] (hdim : 6 ≤ Module.finrank (ZMod 3) V)
    (Q : QuadraticForm (ZMod 3) V) (x : V) :
    ∃ u w : V, LinearIndependent (ZMod 3) ![u, w] ∧ Q u = 0 ∧ Q w = 0 ∧
      polar Q u w = 0 ∧ polar Q x u = 0 ∧ polar Q x w = 0 := by
  let Bx : V →ₗ[ZMod 3] ZMod 3 := QuadraticMap.polarBilin Q x
  let P : Submodule (ZMod 3) V := LinearMap.ker Bx
  have hPfin : 5 ≤ Module.finrank (ZMod 3) P := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Bx
    have hrange : Module.finrank (ZMod 3) (LinearMap.range Bx) ≤ 1 := by
      calc Module.finrank (ZMod 3) (LinearMap.range Bx)
          ≤ Module.finrank (ZMod 3) (ZMod 3) := Submodule.finrank_le (LinearMap.range Bx)
        _ = 1 := Module.finrank_self (ZMod 3)
    dsimp only [P]
    omega
  obtain ⟨u, huP, hu_ne, hQu⟩ := ggOrthE_exists_singular_three Q P (by omega)
  have hxu : polar Q x u = 0 := by
    have h : QuadraticMap.polarBilin Q x u = 0 := LinearMap.mem_ker.mp huP
    simpa [QuadraticMap.polarBilin_apply_apply] using h
  let Bu : V →ₗ[ZMod 3] ZMod 3 := QuadraticMap.polarBilin Q u
  let P' : Submodule (ZMod 3) V := P ⊓ LinearMap.ker Bu
  have hP'fin : 4 ≤ Module.finrank (ZMod 3) P' := by
    let f : V →ₗ[ZMod 3] ZMod 3 × ZMod 3 := Bx.prod Bu
    have hker : LinearMap.ker f = P' := by
      rw [LinearMap.ker_prod]
    have hrn := LinearMap.finrank_range_add_finrank_ker f
    have hrange : Module.finrank (ZMod 3) (LinearMap.range f) ≤ 2 := by
      calc Module.finrank (ZMod 3) (LinearMap.range f)
          ≤ Module.finrank (ZMod 3) (ZMod 3 × ZMod 3) := Submodule.finrank_le (LinearMap.range f)
        _ = 2 := by simp [Module.finrank_prod, Module.finrank_self]
    rw [hker] at hrn
    omega
  have huu : polar Q u u = 0 := by rw [QuadraticMap.polar_self, hQu, smul_zero]
  have huP' : u ∈ P' :=
    ⟨huP, LinearMap.mem_ker.mpr (by rw [QuadraticMap.polarBilin_apply_apply]; exact huu)⟩
  let S' : Submodule (ZMod 3) P' := Submodule.span (ZMod 3) {⟨u, huP'⟩}
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl S'
  have hS'fin : Module.finrank (ZMod 3) S' = 1 := by
    have hne : (⟨u, huP'⟩ : P') ≠ 0 := fun h => hu_ne (Subtype.ext_iff.mp h)
    simpa [S'] using finrank_span_singleton hne
  have hC'fin : Module.finrank (ZMod 3) C' = Module.finrank (ZMod 3) P' - 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq S' C'
    rw [hC'.sup_eq_top, hC'.inf_eq_bot, finrank_top, finrank_bot, hS'fin] at h
    omega
  let C : Submodule (ZMod 3) V := Submodule.map P'.subtype C'
  have hCfin : Module.finrank (ZMod 3) C = Module.finrank (ZMod 3) C' := by
    have hf : Function.Injective (P'.subtype.comp C'.subtype) := by
      intro a b h
      exact Subtype.ext (Subtype.ext h)
    have hrange : LinearMap.range (P'.subtype.comp C'.subtype) = C := by
      ext y
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨(c : P'), c.2, rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨⟨c, hc⟩, rfl⟩
    have h2 := LinearMap.finrank_range_of_inj hf
    rw [hrange] at h2
    exact h2
  obtain ⟨w, hwC, hw_ne, hQw⟩ := ggOrthE_exists_singular_three Q C (by omega)
  have hwP' : w ∈ P' := Submodule.map_subtype_le P' C' hwC
  have huw : polar Q u w = 0 := by
    have h : Bu w = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwP').2
    simpa [Bu, QuadraticMap.polarBilin_apply_apply] using h
  have hxw : polar Q x w = 0 := by
    have h : Bx w = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hwP').1
    simpa [Bx, QuadraticMap.polarBilin_apply_apply] using h
  have hw_not : w ∉ Submodule.span (ZMod 3) {u} := by
    intro hwspan
    have hwS' : (⟨w, hwP'⟩ : P') ∈ S' := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton).mp hwspan
      exact (Submodule.mem_span_singleton).mpr ⟨c, Subtype.ext hc⟩
    have hwC' : (⟨w, hwP'⟩ : P') ∈ C' := by
      obtain ⟨c, hc, hcw⟩ := Submodule.mem_map.mp hwC
      have hEq : (⟨w, hwP'⟩ : P') = c := Subtype.ext hcw.symm
      rwa [hEq]
    have hbot : (⟨w, hwP'⟩ : P') ∈ S' ⊓ C' := ⟨hwS', hwC'⟩
    rw [hC'.inf_eq_bot, Submodule.mem_bot] at hbot
    exact hw_ne (Subtype.ext_iff.mp hbot)
  refine ⟨u, w, ?_, hQu, hQw, huw, hxu, hxw⟩
  rw [LinearIndependent.pair_iff' hu_ne]
  intro a ha
  exact hw_not ((Submodule.mem_span_singleton).mpr ⟨a, ha⟩)

end CFSG.StandardType

end
