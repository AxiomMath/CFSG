module

public import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import Mathlib.LinearAlgebra.Basis.Fin

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.ZS

theorem exists_b5_six_basis_of_coroots
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {u : Fin 5 → V} {α : Fin 5 → Module.Dual (ZMod p) V} {x : V}
    (hφ : ∀ i, α i (u i) = 2)
    (hK : ∀ i j, α i (u j) = (CartanMatrix.B 5 i j : ZMod p))
    (hx0 : x ≠ 0) (hαx : ∀ i, α i x = 0)
    (hfin : Module.finrank (ZMod p) V = 6) :
    ∃ b : Module.Basis (Fin 6) (ZMod p) V,
      b 0 = x ∧
      (∀ i : Fin 5, ∀ k : Fin 6, ∃ j : Fin 6, ∃ c : ZMod p,
        Module.reflection (hφ i) (b k) = c • b j) := by
  classical
  let H : Submodule (ZMod p) V := Submodule.span (ZMod p) (Set.range u)
  have huH : ∀ i, u i ∈ H := fun i => Submodule.subset_span (Set.mem_range_self i)
  have hdet : (Matrix.of fun i j : Fin 5 => α i (u j)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : Fin 5 => α i (u j)) =
        (CartanMatrix.B 5).map (fun z : ℤ => (z : ZMod p)) := by
      ext i j
      simp [hK]
    rw [hmat, ← Int.cast_det, CartanMatrix.B_det (by norm_num : 0 < 5)]
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      rw [← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff, Nat.dvd_prime Nat.prime_two] at h
      rcases h with h | h
      · exact (Fact.out : p.Prime).ne_one h
      · exact hp2 h
    simpa using h2
  have hxH : x ∉ H := by
    intro hxmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p)).mp hxmem
    have hv : (Matrix.of fun i j : Fin 5 => α i (u j)).mulVec c = 0 := by
      ext i
      have hi := hαx i
      rw [← hc] at hi
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hi
      simpa [Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using hi
    have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
    have hxzero : x = 0 := by simpa [hc0] using hc.symm
    exact hx0 hxzero
  let uH : Fin 5 → H := fun i => ⟨u i, huH i⟩
  let αH : Fin 5 → Module.Dual (ZMod p) H := fun i => (α i).comp H.subtype
  have hφH : ∀ i, αH i (uH i) = 2 := fun i => hφ i
  have hKH : ∀ i j, αH i (uH j) = (CartanMatrix.B 5 i j : ZMod p) := fun i j => hK i j
  have hspanH : Submodule.span (ZMod p) (Set.range uH) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff H huH).mpr rfl
  obtain ⟨bH, hbH⟩ := ZS.exists_monomial_basis_of_cartan_B (p := p) hp2
    (u := uH) (φ := αH) hφH hKH hspanH
  have hbHV : LinearIndependent (ZMod p) (fun i : Fin 5 => (bH i : V)) :=
    bH.linearIndependent.map' H.subtype (by simp [Submodule.ker_subtype])
  have hspanHV : Submodule.span (ZMod p) (Set.range fun i : Fin 5 => (bH i : V)) = H :=
    (Submodule.span_range_subtype_eq_top_iff H (fun i => (bH i).2)).mp bH.span_eq
  have hxspan : x ∉ Submodule.span (ZMod p) (Set.range fun i : Fin 5 => (bH i : V)) := by
    rw [hspanHV]
    exact hxH
  let v : Fin 6 → V := Fin.cons x (fun i : Fin 5 => (bH i : V))
  have hvli : LinearIndependent (ZMod p) v := by
    simpa [v] using hbHV.finCons hxspan
  have hcard : Fintype.card (Fin 6) = Module.finrank (ZMod p) V := by
    simp [hfin]
  let b : Module.Basis (Fin 6) (ZMod p) V :=
    basisOfLinearIndependentOfCardEqFinrank (K := ZMod p) (b := v) hvli hcard
  refine ⟨b, ?_, ?_⟩
  · simp [b, v]
  · intro i k
    by_cases hk : k = 0
    · subst hk
      refine ⟨0, 1, ?_⟩
      have hb0 : b 0 = x := by simp [b, v]
      rw [hb0, Module.reflection_apply, hαx i, zero_smul, sub_zero, one_smul]
    · obtain ⟨k', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk
      obtain ⟨j', c, hc⟩ := hbH i k'
      refine ⟨j'.succ, c, ?_⟩
      have hreflH : ∀ w : H,
          ((Module.reflection (hφH i) w : H) : V) =
            Module.reflection (hφ i) (w : V) := by
        intro w
        simp [Module.reflection_apply, αH, uH]
      calc Module.reflection (hφ i) (b k'.succ)
          = Module.reflection (hφ i) ((bH k' : H) : V) := by simp [b, v]
        _ = ((Module.reflection (hφH i) (bH k') : H) : V) := (hreflH (bH k')).symm
        _ = c • ((bH j' : H) : V) := congrArg H.subtype hc
        _ = c • b j'.succ := by simp [b, v]

end CFSG.StandardType

end
