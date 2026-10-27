module

public import CFSG.LinearAlgebra.FixedAxisCoordinates
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoCartan
public import TauCeti.LinearAlgebra.Pi

public section

namespace CFSG.StandardType.E6QTwo

open scoped Matrix
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_smul_radical_coroots_of_common_kernel
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x : V)
    (hh : LinearIndependent (ZMod 3) h)
    (hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    ∃ t : ZMod 3, t ≠ 0 ∧
      x = t • Fintype.linearCombination (ZMod 3) h cartanE6KernelVec := by
  classical
  let w := Fintype.linearCombination (ZMod 3) h cartanE6KernelVec
  have hwfix : ∀ i, α i w = 0 := by
    intro i
    rw [show w = Fintype.linearCombination (ZMod 3) h cartanE6KernelVec from rfl,
      apply_linearCombination_eq_cartanE6ModThree hpair i cartanE6KernelVec,
      cartanE6ModThree_mulVec_cartanE6KernelVec]
    rfl
  have hw0 : w ≠ 0 := by
    intro hzero
    have hz : ∀ i, cartanE6KernelVec i = 0 :=
      Fintype.linearIndependent_iff.mp hh cartanE6KernelVec (by
        simpa only [w, Fintype.linearCombination_apply] using hzero)
    exact cartanE6KernelVec_ne_zero (funext hz)
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp ((hfix w).mp hwfix)
  have ht0 : t ≠ 0 := by
    intro h0
    apply hw0
    simpa [h0] using ht.symm
  refine ⟨t⁻¹, inv_ne_zero ht0, ?_⟩
  change x = t⁻¹ • w
  rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]

theorem exists_e6_dependent_fixed_axis_coordinates
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x : V)
    (hdep : ¬ LinearIndependent (ZMod 3) h) (hx : x ≠ 0)
    (hdim : Module.finrank (ZMod 3) V = 7)
    (hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    ∃ e : V ≃ₗ[ZMod 3] ((Fin 6 → ZMod 3) × ZMod 3),
      e x = (0, 1) ∧
      (∀ i, e (h i) = ((fun j => (CartanMatrix.E 6 j i : ZMod 3)), 0)) ∧
      (∀ v, (e v).1 = fun i => α i v) ∧
      (∀ i v, e (v - α i v • h i) =
        ((e v).1 - (e v).1 i • (fun j => (CartanMatrix.E 6 j i : ZMod 3)), (e v).2)) := by
  have hxfix : ∀ i, α i x = 0 :=
    (hfix x).mpr (Submodule.subset_span (Set.mem_singleton x))
  have hxspan : x ∉ Submodule.span (ZMod 3) (Set.range h) := by
    intro hxs
    exact hx (eq_zero_of_mem_coroot_span_of_dependent h α hpair hdep hxs hxfix)
  obtain ⟨e, hex, heh, heα, heact⟩ :=
    CFSG.LinearAlgebra.exists_cartan_fixed_axis_coordinates_of_finrank h α x hxspan
      (by simpa using hdim) hfix
  refine ⟨e, hex, ?_, heα, ?_⟩
  · intro i
    simpa only [hpair] using heh i
  · intro i v
    simpa only [hpair] using heact i v

theorem finrank_six_or_seven_of_common_kernel
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x : V)
    (hx : x ≠ 0)
    (hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    Module.finrank (ZMod 3) V = 6 ∨ Module.finrank (ZMod 3) V = 7 := by
  let F : V →ₗ[ZMod 3] (Fin 6 → ZMod 3) := LinearMap.pi α
  let h' : Fin 6 → F.range := fun i => ⟨F (h i), ⟨h i, rfl⟩⟩
  let α' : Fin 6 → Module.Dual (ZMod 3) F.range :=
    fun i => (LinearMap.proj i).comp F.range.subtype
  have hpair' : ∀ i j, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := hpair
  have hlo : 5 ≤ Module.finrank (ZMod 3) F.range :=
    (five_le_finrank_span hpair').trans (Submodule.finrank_le _)
  have hhi : Module.finrank (ZMod 3) F.range ≤ 6 := by
    simpa using Submodule.finrank_le F.range
  have hker : F.ker = Submodule.span (ZMod 3) {x} := by
    ext v
    change (fun i => α i v) = 0 ↔ _
    simpa only [funext_iff, Pi.zero_apply] using hfix v
  have hrank := F.finrank_range_add_finrank_ker
  rw [hker, finrank_span_singleton hx] at hrank
  omega

theorem exists_e6_independent_six_coordinates
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x : V)
    (hh : LinearIndependent (ZMod 3) h)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    ∃ (s : ZMod 3) (e : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)),
      s ≠ 0 ∧ e x = cartanE6KernelVec ∧
      (∀ i, e (h i) = s • Pi.single i 1) ∧
      ∀ i v, e (v - α i v • h i) = e v -
        (∑ j : Fin 6, (e v) j * (CartanMatrix.E 6 i j : ZMod 3)) • Pi.single i 1 := by
  classical
  let b : Module.Basis (Fin 6) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank hh (by simpa using hdim.symm)
  have hb : ∀ i, b i = h i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hh (by simpa using hdim.symm)) i
  let e₀ : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) := b.equivFun
  have heh : ∀ i, e₀ (h i) = Pi.single i 1 := by
    intro i
    rw [← hb i]
    funext j
    simpa only [e₀, Pi.single_apply, eq_comm] using b.equivFun_self i j
  have heα : ∀ i v, α i v = ∑ j : Fin 6,
      e₀ v j * (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i v
    have hv := (b.sum_equivFun v).symm
    calc
      α i v = α i (∑ j, e₀ v j • b j) := congrArg (α i) hv
      _ = _ := by simp only [map_sum, map_smul, smul_eq_mul, hb, hpair]
  obtain ⟨t, ht0, htx⟩ := exists_smul_radical_coroots_of_common_kernel h α x hh hfix hpair
  have hecomb : e₀ (Fintype.linearCombination (ZMod 3) h cartanE6KernelVec) =
      cartanE6KernelVec := by
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [map_smul, heh]
    decide +kernel
  let e : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) := (Units.mk0 t ht0)⁻¹ • e₀
  have he : ∀ v, e v = t⁻¹ • e₀ v := fun v => by
    simp [e, LinearEquiv.smul_apply]
  refine ⟨t⁻¹, e, inv_ne_zero ht0, ?_, ?_, ?_⟩
  · rw [he, htx, map_smul, hecomb, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  · intro i
    rw [he, heh]
  · intro i v
    have hsum : (∑ j : Fin 6, (e v) j * (CartanMatrix.E 6 i j : ZMod 3)) =
        t⁻¹ * α i v := by
      rw [heα, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [he, Pi.smul_apply, smul_eq_mul]
      ring
    rw [map_sub, map_smul, he (h i), heh, smul_smul, hsum]
    congr 2
    exact mul_comm _ _

theorem exists_e6_dependent_six_coordinates
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (h : Fin 6 → V) (α : Fin 6 → Module.Dual (ZMod 3) V) (x : V)
    (hdep : ¬ LinearIndependent (ZMod 3) h) (hx : x ≠ 0)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hfix : ∀ v, (∀ i, α i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3)) :
    ∃ e : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3),
      e x = Pi.single (5 : Fin 6) 1 ∧
      (∀ i, e (h i) = Fin.cases (![0,1,0,2,1,0] : Fin 6 → ZMod 3)
        (fun j : Fin 5 => Pi.single j.castSucc 1) i) ∧
      ∀ i v, e (v - α i v • h i) = e v -
        (∑ j : Fin 5, (e v) j.castSucc * (CartanMatrix.E 6 i j.succ : ZMod 3)) •
          Fin.cases (![0,1,0,2,1,0] : Fin 6 → ZMod 3)
            (fun j : Fin 5 => Pi.single j.castSucc 1) i := by
  classical
  have hxfix : ∀ i, α i x = 0 := (hfix x).mpr (Submodule.subset_span (by simp))
  have hxspan : x ∉ Submodule.span (ZMod 3) (Set.range h) := by
    intro hm
    exact hx (eq_zero_of_mem_coroot_span_of_dependent h α hpair hdep hm hxfix)
  have hdet : (Matrix.of fun i j : Fin 5 => α i.succ (h j.succ)).det ≠ 0 := by
    have hmat : (Matrix.of fun i j : Fin 5 => α i.succ (h j.succ)) =
        Matrix.of fun i j : Fin 5 => (CartanMatrix.E 6 i.succ j.succ : ZMod 3) := by
      ext i j
      exact hpair _ _
    rw [hmat]
    decide +kernel
  have hli : LinearIndependent (ZMod 3) (fun j : Fin 5 => h j.succ) :=
    linearIndependent_of_det_ne_zero _ (fun i : Fin 5 => α i.succ) hdet
  have hxsub : x ∉ Submodule.span (ZMod 3) (Set.range fun j : Fin 5 => h j.succ) := by
    intro hm
    apply hxspan
    exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j.succ, rfl⟩) hm
  let b : Module.Basis (Fin 6) (ZMod 3) V :=
    basisOfLinearIndependentOfCardEqFinrank (hli.finSnoc hxsub) (by simpa using hdim.symm)
  have hb : ∀ i, b i = Fin.snoc (α := fun _ : Fin 6 => V) (fun j : Fin 5 => h j.succ) x i :=
    fun i => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank (hli.finSnoc hxsub)
      (by simpa using hdim.symm)) i
  let e : V ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) := b.equivFun
  have heg : ∀ j : Fin 5, e (h j.succ) = Pi.single j.castSucc 1 := by
    intro j
    have hb' : b j.castSucc = h j.succ := by rw [hb, Fin.snoc_castSucc]
    rw [← hb']
    funext k
    simpa only [e, Pi.single_apply, eq_comm] using b.equivFun_self j.castSucc k
  have hex : e x = Pi.single (5 : Fin 6) 1 := by
    have hlast : Fin.last 5 = (5 : Fin 6) := by decide
    have hb' : b (Fin.last 5) = x := by rw [hb, Fin.snoc_last]
    rw [← hb']
    funext k
    simpa only [e, Pi.single_apply, eq_comm, hlast] using b.equivFun_self (Fin.last 5) k
  have heh : ∀ i, e (h i) = Fin.cases (![0,1,0,2,1,0] : Fin 6 → ZMod 3)
      (fun j : Fin 5 => Pi.single j.castSucc 1) i := by
    intro i
    refine Fin.cases ?_ (fun j => by simpa using heg j) i
    have hrel := linearCombination_radical_eq_zero_of_dependent h α hpair hdep
    rw [Fintype.linearCombination_apply, Fin.sum_univ_succ] at hrel
    have hzero : h 0 = -(∑ j : Fin 5, cartanE6KernelVec j.succ • h j.succ) := by
      have hcoef : cartanE6KernelVec 0 = 1 := rfl
      rw [hcoef, one_smul] at hrel
      exact eq_neg_of_add_eq_zero_left hrel
    simp only [Fin.cases_zero]
    rw [hzero, map_neg, map_sum]
    simp only [map_smul, heg]
    decide +kernel
  have heα : ∀ i v, α i v = ∑ j : Fin 5,
      e v j.castSucc * (CartanMatrix.E 6 i j.succ : ZMod 3) := by
    intro i v
    have hv := (b.sum_equivFun v).symm
    calc
      α i v = α i (∑ j, e v j • b j) := congrArg (α i) hv
      _ = ∑ j : Fin 6, e v j * α i (b j) := by simp only [map_sum, map_smul, smul_eq_mul]
      _ = _ := by
        rw [Fin.sum_univ_castSucc]
        simp only [hb, Fin.snoc_castSucc, Fin.snoc_last, hpair, hxfix,
          mul_zero, add_zero]
  exact ⟨e, hex, heh, fun i v => by rw [map_sub, map_smul, heα, heh]⟩

end CFSG.StandardType.E6QTwo
