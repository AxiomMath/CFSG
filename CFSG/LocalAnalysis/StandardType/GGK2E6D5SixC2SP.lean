module

public import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
public import CFSG.LocalAnalysis.StandardType.GGK2E6C2SPFromMonomial

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.ZS CFSG.StandardType.HdRo7C

theorem exists_d5_six_c2sp_basis_of_cartan
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {u : Fin 5 → V} {α : Fin 5 → Module.Dual (ZMod 3) V} {x : V}
    (hφ : ∀ i, α i (u i) = 2)
    (hK : ∀ i j, α i (u j) = (CartanMatrix.D 5 i j : ZMod 3))
    (hx0 : x ≠ 0) (hαx : ∀ i, α i x = 0)
    (hfin : Module.finrank (ZMod 3) V = 6) :
    ∃ b : Module.Basis (Fin 6) (ZMod 3) V,
      b 0 = x ∧
      ∀ i : Fin 5, C2SP 3 b (Module.reflection (hφ i)) := by
  classical
  let H : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range u)
  have huH : ∀ i, u i ∈ H := fun i => Submodule.subset_span (Set.mem_range_self i)
  have hdet : (Matrix.of fun i j : Fin 5 => α i (u j)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : Fin 5 => α i (u j)) =
        (CartanMatrix.D 5).map (fun z : ℤ => (z : ZMod 3)) := by
      ext i j
      simp [hK]
    rw [hmat, ← Int.cast_det, CartanMatrix.D_det (by norm_num : 2 ≤ 5)]
    decide
  have hxH : x ∉ H := by
    intro hxmem
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 3)).mp hxmem
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
  let αH : Fin 5 → Module.Dual (ZMod 3) H := fun i => (α i).comp H.subtype
  have hφH : ∀ i, αH i (uH i) = 2 := fun i => hφ i
  have hKH : ∀ i j, αH i (uH j) = (CartanMatrix.D 5 i j : ZMod 3) := fun i j => hK i j
  have hspanH : Submodule.span (ZMod 3) (Set.range uH) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff H huH).mpr rfl
  obtain ⟨bH, hbH⟩ := ZS.exists_monomial_basis_of_cartan_D (p := 3) (by norm_num)
    (ℓ := 5) (by norm_num) (u := uH) (φ := αH) hφH hKH hspanH
  have hbHV : LinearIndependent (ZMod 3) (fun i : Fin 5 => (bH i : V)) :=
    bH.linearIndependent.map' H.subtype (by simp [Submodule.ker_subtype])
  have hspanHV : Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => (bH i : V)) = H :=
    (Submodule.span_range_subtype_eq_top_iff H (fun i => (bH i).2)).mp bH.span_eq
  have hxspan : x ∉ Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => (bH i : V)) := by
    rw [hspanHV]
    exact hxH
  let v : Fin 6 → V := Fin.cons x (fun i : Fin 5 => (bH i : V))
  have hvli : LinearIndependent (ZMod 3) v := by
    simpa [v] using hbHV.finCons hxspan
  have hcard : Fintype.card (Fin 6) = Module.finrank (ZMod 3) V := by
    simp [hfin]
  let b : Module.Basis (Fin 6) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank (K := ZMod 3) (b := v) hvli hcard
  have hb0 : b 0 = x := by simp [b, v]
  have hmono : ∀ i : Fin 5, ∀ k : Fin 6,
      ∃ j : Fin 6, ∃ c : ZMod 3, c ≠ 0 ∧
        Module.reflection (hφ i) (b k) = c • b j := by
    intro i k
    by_cases hk : k = 0
    · subst hk
      refine ⟨0, 1, by norm_num, ?_⟩
      rw [hb0, Module.reflection_apply, hαx i, zero_smul, sub_zero, one_smul]
    · obtain ⟨k', rfl⟩ := Fin.exists_succ_eq_of_ne_zero hk
      obtain ⟨j', c, hc⟩ := hbH i k'
      have hreflH : ∀ w : H,
          ((Module.reflection (hφH i) w : H) : V) =
            Module.reflection (hφ i) (w : V) := by
        intro w
        simp [Module.reflection_apply, αH, uH]
      have hspec : Module.reflection (hφ i) (b k'.succ) = c • b j'.succ := by
        calc Module.reflection (hφ i) (b k'.succ)
            = Module.reflection (hφ i) ((bH k' : H) : V) := by simp [b, v]
          _ = ((Module.reflection (hφH i) (bH k') : H) : V) := (hreflH (bH k')).symm
          _ = c • ((bH j' : H) : V) := congrArg H.subtype hc
          _ = c • b j'.succ := by simp [b, v]
      have hcne : c ≠ 0 := by
        intro hc0
        have hz : Module.reflection (hφ i) (b k'.succ) = 0 := by
          rw [hspec, hc0, zero_smul]
        have hbz : b k'.succ = 0 := by
          have := congrArg (Module.reflection (hφ i)).symm hz
          simpa using this
        exact (b.ne_zero k'.succ) hbz
      exact ⟨j'.succ, c, hcne, hspec⟩
  refine ⟨b, hb0, ?_⟩
  intro i
  exact c2sp_of_monomial_three b (Module.reflection (hφ i))
    (by rw [hb0, Module.reflection_apply, hαx i, zero_smul, sub_zero])
    (fun k => hmono i k)

end CFSG.StandardType

end
