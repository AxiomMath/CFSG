module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace
import CFSG.Quasithin.Vol2.GoldschmidtH11AutSL
import CFSG.Timmesfeld.RankOne.SL2

public section

namespace CFSG.Quasithin.SimsG4.OrthPlus

variable {K : Type} [Field K]

theorem trace_conj_map (σ : K ≃+* K) (h x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((h * Matrix.SpecialLinearGroup.map σ.toRingHom x * h⁻¹ :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace =
      σ (x : Matrix (Fin 2) (Fin 2) K).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.SpecialLinearGroup.map_apply_coe,
    Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [RingHom.mapMatrix_apply]

variable [Finite K] [CharP K 2]

theorem isSimpleGroup_SL2 (h4 : 4 ≤ Nat.card K) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact (CFSG.Timmesfeld.RankOne.psl2EquivSL2 K).symm.isSimpleGroup

theorem eq_top_or_graph (h4 : 4 ≤ Nat.card K)
    (Hh : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K))
    (hswap : ∀ x y, (x, y) ∈ Hh → (y, x) ∈ Hh) (hfst : ∀ x, ∃ y, (x, y) ∈ Hh) :
    Hh = ⊤ ∨ ∃ (σ : K ≃+* K) (h : Matrix.SpecialLinearGroup (Fin 2) K),
      ∀ x y, (x, y) ∈ Hh → y = h * Matrix.SpecialLinearGroup.map σ.toRingHom x * h⁻¹ := by
  haveI := isSimpleGroup_SL2 h4
  set N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) := Hh.comap (MonoidHom.inl _ _)
    with hNdef
  have hmemN : ∀ x, x ∈ N ↔ (x, 1) ∈ Hh := fun x => Iff.rfl
  haveI hN : N.Normal := ⟨fun x hx g => by
    obtain ⟨y, hy⟩ := hfst g
    rw [hmemN] at hx ⊢
    have h := Hh.mul_mem (Hh.mul_mem hy hx) (Hh.inv_mem hy)
    simpa using h⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := N) with hb | ht
  · right
    have huniq : ∀ x y y', (x, y) ∈ Hh → (x, y') ∈ Hh → y' = y := by
      intro x y y' h h'
      have h1 := Hh.mul_mem (Hh.inv_mem h) h'
      have h2 : y⁻¹ * y' ∈ N := hswap _ _ (by simpa using h1)
      rw [hb, Subgroup.mem_bot] at h2
      exact (inv_mul_eq_one.mp h2).symm
    choose α hα using hfst
    let αh : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K :=
      { toFun := α
        map_one' := huniq 1 1 (α 1) Hh.one_mem (hα 1)
        map_mul' := fun x x' => huniq (x * x') (α x * α x') (α (x * x'))
          (Hh.mul_mem (hα x) (hα x')) (hα (x * x')) }
    have hinj : Function.Injective αh := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx' : α x = 1 := hx
      have h1 : x ∈ N := by
        rw [hmemN, ← hx']
        exact hα x
      rwa [hb, Subgroup.mem_bot] at h1
    let αe : MulAut (Matrix.SpecialLinearGroup (Fin 2) K) :=
      MulEquiv.ofBijective αh ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
    obtain ⟨σ, h, hσ⟩ := CFSG.Quasithin.H11.exists_aut_formula αe
    refine ⟨σ, h, fun x y hxy => ?_⟩
    rw [huniq x (α x) y (hα x) hxy]
    exact hσ x
  · left
    rw [eq_top_iff]
    rintro ⟨x, y⟩ -
    have hx : (x, 1) ∈ Hh := (hmemN x).mp (by rw [ht]; exact Subgroup.mem_top x)
    have hy : (1, y) ∈ Hh := hswap _ _ ((hmemN y).mp (by rw [ht]; exact Subgroup.mem_top y))
    have h := Hh.mul_mem hx hy
    simpa using h

end CFSG.Quasithin.SimsG4.OrthPlus
