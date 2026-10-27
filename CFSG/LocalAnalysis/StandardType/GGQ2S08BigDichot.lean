module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08DatumConn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}

theorem ggQ2s08_big_dichotomy [Finite G] (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel}
    (hlab : GGQ2S08BigLabel lab) (hMW : GGQ2LabelWeyl lab M.coxeter)
    (U : Submodule (ZMod 3) M.V)
    (hU : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), ∀ u ∈ U, w u ∈ U) :
    U ≤ Submodule.span (ZMod 3) {M.xV} ∨ M.coSpan ≤ U := by
  obtain ⟨hconn, h6⟩ := ggQ2s08d_label_connected hlab M.coxeter hMW
  have hs_mem : ∀ i, ggLin (p := 3) M.model (M.simple i) ∈
      (ggAutomizer L Bs).map (ggLin (p := 3) M.model) := by
    intro i
    exact Subgroup.mem_map_of_mem _ (by
      rw [M.automizer_L]
      exact Subgroup.subset_closure (Set.mem_range_self i))
  by_cases hex : ∃ u ∈ U, ∃ i, M.root i u ≠ 0
  ·
    right
    obtain ⟨u, huU, i, hi⟩ := hex
    have hsiU : ggLin (p := 3) M.model (M.simple i) u ∈ U := hU _ (hs_mem i) u huU
    have h1 : ggLin (p := 3) M.model (M.simple i) u - u ∈ U := U.sub_mem hsiU huU
    rw [M.simple_apply i u] at h1
    have h2 : M.root i u • M.coroot i ∈ U := by
      have hneg := U.neg_mem h1
      have heq : -(u - M.root i u • M.coroot i - u) = M.root i u • M.coroot i := by abel
      rwa [heq] at hneg
    have hhi : M.coroot i ∈ U := by
      have hunit : (M.root i u)⁻¹ * (M.root i u) = 1 := inv_mul_cancel₀ hi
      have h3 := U.smul_mem ((M.root i u)⁻¹) h2
      simpa [smul_smul, hunit] using h3
    have hstep : ∀ a b, (a ≠ b ∧ M.coxeter a b ≠ 2) → M.coroot a ∈ U → M.coroot b ∈ U := by
      intro a b hab haU
      have hsaU : ggLin (p := 3) M.model (M.simple b) (M.coroot a) ∈ U :=
        hU _ (hs_mem b) _ haU
      have h1' : ggLin (p := 3) M.model (M.simple b) (M.coroot a) - M.coroot a ∈ U :=
        U.sub_mem hsaU haU
      rw [M.simple_apply b (M.coroot a)] at h1'
      have hroot_ne : M.root b (M.coroot a) ≠ 0 := by
        rw [M.pairing b a]
        intro hzero
        rcases M.isCartan.2 a b hab.1 with
          ⟨hm, -, -⟩ | ⟨-, -, h2b⟩ | ⟨-, hprod, -, -⟩ | ⟨hm, -, -, -⟩
        · exact hab.2 hm
        · rw [h2b] at hzero
          exact absurd hzero (by norm_num)
        · have h2c : ((2 : ℤ) : ZMod 3) = 0 := by
            rw [← hprod, Int.cast_mul, hzero, mul_zero]
          exact absurd h2c (by decide)
        · exact (h6 a b hab.1) hm
      have h2' : M.root b (M.coroot a) • M.coroot b ∈ U := by
        have hneg := U.neg_mem h1'
        have heq : -(M.coroot a - M.root b (M.coroot a) • M.coroot b - M.coroot a)
            = M.root b (M.coroot a) • M.coroot b := by abel
        rwa [heq] at hneg
      have hunit : (M.root b (M.coroot a))⁻¹ * (M.root b (M.coroot a)) = 1 :=
        inv_mul_cancel₀ hroot_ne
      have h3 := U.smul_mem ((M.root b (M.coroot a))⁻¹) h2'
      simpa [smul_smul, hunit] using h3
    have hall : ∀ j, M.coroot j ∈ U := by
      intro j
      induction hconn i j with
      | refl => exact hhi
      | tail _ hbc ih => exact hstep _ _ hbc ih
    rw [GGQ2LDatum.coSpan, Submodule.span_le]
    rintro y ⟨j, rfl⟩
    exact hall j
  ·
    left
    have hzero : ∀ u ∈ U, ∀ i, M.root i u = 0 := by
      intro u hu i
      by_contra hne
      exact hex ⟨u, hu, i, hne⟩
    intro u hu
    have hgen : ∀ i, ggLin (p := 3) M.model (M.simple i) u = u := by
      intro i
      rw [M.simple_apply i u, hzero u hu i, zero_smul, sub_zero]
    have hfixu : ∀ w ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), w u = u := by
      intro w hw
      obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hw
      clear hw
      rw [M.automizer_L] at hφ
      induction hφ using Subgroup.closure_induction with
      | mem ψ hψ =>
          obtain ⟨i, rfl⟩ := hψ
          exact hgen i
      | one => exact map_one (ggLin (p := 3) M.model) ▸ rfl
      | mul a b _ _ iha ihb => rw [map_mul, LinearEquiv.mul_apply, ihb, iha]
      | inv a _ iha =>
          rw [map_inv]
          calc (ggLin (p := 3) M.model a)⁻¹ u
              = (ggLin (p := 3) M.model a)⁻¹ ((ggLin (p := 3) M.model a) u) := by rw [iha]
            _ = u := LinearEquiv.symm_apply_apply _ u
    have hmem : u ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      exact hfixu (ggLin (p := 3) M.model φ) (Subgroup.mem_map_of_mem _ hφ)
    rwa [M.fixed_x] at hmem

end CFSG.StandardType

end

