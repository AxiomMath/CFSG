module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosExclFalse
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosExclTrue

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma pxe_model (p N : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7) (hN : N = p)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hF : CFSG.StandardType.GGIndepAFrame p N h α x) (hha : αa ha = 2)
    (hx : αa x ≠ 0) (hsp : ha ∈ Submodule.span (ZMod p) (Set.range h)) (s : ℕ) (hs : s ≤ 2)
    (o : ℕ × ℕ × ℕ) (ho : o ∈ posOpts p N)
    (hH : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p))
    (hA : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p)) :
    ModelledIn (exclCell false p N ++ exclCell true p N) s p h α x ha αa := by
  subst N
  let φ : V →ₗ[ZMod p] (Fin (p - 1) → ZMod p) :=
    { toFun := fun v i => α i v
      map_add' := by intro u v; funext i; simp
      map_smul' := by intro c u; funext i; simp }
  have hker : φ.ker = Submodule.span (ZMod p) {x} := by
    apply le_antisymm
    · intro v hv
      exact hF.fix v (fun i => congrFun hv i)
    · intro v hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
      rw [← hc]
      show φ (c • x) = 0
      funext i
      simp [φ, hF.x_ker i]
  have hrange_fin : Module.Finite (ZMod p) (LinearMap.range φ) := inferInstance
  have hqfin : Module.Finite (ZMod p) (V ⧸ φ.ker) :=
    Module.Finite.of_surjective (LinearMap.quotKerEquivRange φ).symm.toLinearMap
      (LinearMap.quotKerEquivRange φ).symm.surjective
  haveI : Module.Finite (ZMod p) (Submodule.span (ZMod p) {x}) :=
    Module.Finite.span_of_finite (ZMod p) (Set.finite_singleton x)
  rw [hker] at hqfin
  have hVfin : Module.Finite (ZMod p) V :=
    Module.Finite.of_submodule_quotient (Submodule.span (ZMod p) {x})
  haveI := hVfin
  have hHd : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) = p - 1 := by
    rw [finrank_span_eq_card hF.indep, Fintype.card_fin]
  have hx1 : Module.finrank (ZMod p) (Submodule.span (ZMod p) {x}) = 1 :=
    finrank_span_singleton hF.x_ne
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hVd : Module.finrank (ZMod p) V = Module.finrank (ZMod p) (LinearMap.range φ) + 1 := by
    rw [← hrn, hker, hx1]
  have hrange_le : Module.finrank (ZMod p) (LinearMap.range φ) ≤ p - 1 := by
    calc Module.finrank (ZMod p) (LinearMap.range φ)
        ≤ Module.finrank (ZMod p) (Fin (p - 1) → ZMod p) := Submodule.finrank_le _
      _ = p - 1 := by rw [Module.finrank_pi, Fintype.card_fin]
  have hHle : Module.finrank (ZMod p) (Submodule.span (ZMod p) (Set.range h)) ≤
      Module.finrank (ZMod p) V := Submodule.finrank_le _
  have hcases : Module.finrank (ZMod p) V = p - 1 ∨ Module.finrank (ZMod p) V = p := by
    omega
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p) (v := h)).mp hsp
  obtain ⟨aa, haa⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod p) (v := h)).mp hF.x_mem
  have hAa : (pxe_A p (p - 1)).mulVec aa = 0 := by
    funext j
    have hxj := hF.x_ker j
    rw [← haa] at hxj
    simp only [map_sum, map_smul, hF.pair, smul_eq_mul] at hxj
    simpa [pxe_A, Matrix.mulVec, dotProduct, mul_comm] using hxj
  obtain ⟨m0, hm0eq⟩ := pxe_ker_cartan p (p - 1) hp rfl aa hAa
  have hm0 : m0 ≠ 0 := by
    intro hm
    apply hF.x_ne
    rw [← haa, hm0eq]
    simp [hm]
  have hcx : m0⁻¹ ≠ 0 := inv_ne_zero hm0
  rcases hcases with hdim | hdim
  · exact pxe_model_false p hp h α x ha αa hF s hs o ho hH hA hdim cc hcc aa haa m0 hm0eq hm0 hcx
  · exact pxe_model_true p hp h α x ha αa hF hx s hs o ho hH hA hdim cc hcc aa haa m0 hm0eq hm0 hcx φ (fun v i => rfl) hVd
theorem excl_model (p N : ℕ) [Fact p.Prime] (hc : (p = 5 ∧ N = 5) ∨ (p = 7 ∧ N = 7)) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] (hV : Module.finrank (ZMod p) V ≤ N)
    (h : Fin (N - 1) → V) (α : Fin (N - 1) → Module.Dual (ZMod p) V) (x : V) (ha : V)
    (αa : Module.Dual (ZMod p) V) (hF : CFSG.StandardType.GGIndepAFrame p N h α x) (hha : αa ha = 2)
    (hx : αa x ≠ 0) (hsp : ha ∈ Submodule.span (ZMod p) (Set.range h)) (s : ℕ) (hs : s ≤ 2)
    (o : ℕ × ℕ × ℕ) (ho : o ∈ posOpts p N)
    (hH : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      α j ha = (((if (j : ℕ) - s = o.1 then o.2.1 else 0 : ℕ)) : ZMod p))
    (hA : ∀ j : Fin (N - 1), s ≤ (j : ℕ) → (j : ℕ) < s + (N - 3) →
      αa (h j) = (((if (j : ℕ) - s = o.1 then o.2.2 else 0 : ℕ)) : ZMod p)) :
    ModelledIn (exclCell false p N ++ exclCell true p N) s p h α x ha αa := by
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact pxe_model 5 5 (Or.inl rfl) rfl h α x ha αa hF hha hx hsp s hs o ho hH hA
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact pxe_model 7 7 (Or.inr rfl) rfl h α x ha αa hF hha hx hsp s hs o ho hH hA

end CFSG.TwoNodeSmall
