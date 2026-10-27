module

public import CFSG.LocalAnalysis.StandardType.GGHeartAPm
public import CFSG.LocalAnalysis.StandardType.GGQTwoTableBI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggQ2_pm_heartA {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {r : ℕ} (e : Fin r ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A r i j) (hr : 4 ≤ r) (hB : M.ShapeB)
    (φ : MulAut ↥Bs) (hN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs))) :
    ∃ w ∈ ggAutomizer L Bs, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : M.V, ggLin (p := 3) M.model (φ * w) v - ε • v ∈
        Submodule.span (ZMod 3) {M.xV} := by
  classical
  obtain ⟨-, -, hxVn, hsupB⟩ := hB
  have hcoSpan : M.coSpan =
      Submodule.span (ZMod 3) (Set.range fun j : Fin r => M.coroot (e j)) := by
    rw [GGQ2LDatum.coSpan]
    congr 1
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, by simp⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e k, rfl⟩
  have hxH : M.xV ∉
      Submodule.span (ZMod 3) (Set.range fun j : Fin r => M.coroot (e j)) := by
    rw [← hcoSpan]
    exact hxVn
  have hsup : Submodule.span (ZMod 3) (Set.range fun j : Fin r => M.coroot (e j)) ⊔
      Submodule.span (ZMod 3) {M.xV} = ⊤ := by
    rw [← hcoSpan]
    exact hsupB
  have hgen : {t : M.V ≃ₗ[ZMod 3] M.V |
      ∃ j : Fin r, ∀ v, t v = v - (fun j : Fin r => M.root (e j)) j v •
        (fun j : Fin r => M.coroot (e j)) j} =
      ggLin (p := 3) M.model '' Set.range M.simple := by
    ext t
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨M.simple (e j), ⟨e j, rfl⟩, ?_⟩
      refine LinearEquiv.ext fun v => ?_
      rw [M.simple_apply]
      exact (hj v).symm
    · rintro ⟨ψ, ⟨k, rfl⟩, rfl⟩
      refine ⟨e.symm k, fun v => ?_⟩
      rw [M.simple_apply]
      simp only [Equiv.apply_symm_apply]
  have hweyl : ggQ2WeylOf (fun j : Fin r => M.coroot (e j))
      (fun j : Fin r => M.root (e j)) =
      (ggAutomizer L Bs).map (ggLin (p := 3) M.model) := by
    change Subgroup.closure {t : M.V ≃ₗ[ZMod 3] M.V |
        ∃ j : Fin r, ∀ v, t v = v - (fun j : Fin r => M.root (e j)) j v •
          (fun j : Fin r => M.coroot (e j)) j} =
      (ggAutomizer L Bs).map (ggLin (p := 3) M.model)
    rw [hgen, M.automizer_L, MonoidHom.map_closure]
  have hxmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hxfix : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model ψ M.xV = M.xV :=
    mem_ggFixedSubmodule_iff.mp hxmem
  have hxk : ∀ j : Fin r, M.root (e j) M.xV = 0 := by
    intro j
    have hmem : M.simple (e j) ∈ ggAutomizer L Bs := by
      rw [M.automizer_L]
      exact Subgroup.subset_closure ⟨e j, rfl⟩
    have h := hxfix (M.simple (e j)) hmem
    rw [M.simple_apply] at h
    have hsm : M.root (e j) M.xV • M.coroot (e j) = 0 := sub_eq_self.mp h
    have hc : M.coroot (e j) ≠ 0 := by
      intro h0
      have h2 : M.root (e j) (M.coroot (e j)) = 2 := by
        rw [M.pairing (e j) (e j), M.isCartan.1 (e j)]
        norm_num
      rw [h0, map_zero] at h2
      exact absurd h2 (by decide)
    exact (smul_eq_zero.mp hsm).resolve_right hc
  have hfix : ∀ v : M.V, (∀ j : Fin r, M.root (e j) v = 0) →
      v ∈ Submodule.span (ZMod 3) {M.xV} := by
    intro v hv
    have hroot : ∀ k : M.Λ, M.root k v = 0 := by
      intro k
      have := hv (e.symm k)
      simpa only [Equiv.apply_symm_apply] using this
    have hfixall : ∀ ψ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model ψ v = v := by
      intro ψ hψ
      rw [M.automizer_L] at hψ
      refine Subgroup.closure_induction (k := Set.range M.simple)
        (p := fun ψ _ => ggLin (p := 3) M.model ψ v = v) ?_ ?_ ?_ ?_ hψ
      · rintro ψ ⟨k, rfl⟩
        rw [M.simple_apply, hroot k, zero_smul, sub_zero]
      · simp
      · intro a c _ _ iha ihc
        rw [map_mul, LinearEquiv.mul_apply, ihc, iha]
      · intro a _ iha
        rw [map_inv]
        change (ggLin (p := 3) M.model a).symm v = v
        apply LinearEquiv.injective (ggLin (p := 3) M.model a)
        rw [LinearEquiv.apply_symm_apply, iha]
    have hmem : v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) :=
      mem_ggFixedSubmodule_iff.mpr hfixall
    rw [M.fixed_x] at hmem
    exact hmem
  have hα : ∀ i j : Fin r, M.root (e i) (M.coroot (e j)) =
      ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by
    intro i j
    calc M.root (e i) (M.coroot (e j))
        = (M.cartan (e i) (e j) : ZMod 3) := M.pairing (e i) (e j)
      _ = ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by rw [hC i j]
  have hT : ggLin (p := 3) M.model φ ∈
      Subgroup.normalizer (ggQ2WeylOf (fun j : Fin r => M.coroot (e j))
        (fun j : Fin r => M.root (e j)) : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [hweyl]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hN, rfl⟩)
  obtain ⟨w, hw, ε, hε, hwε⟩ :=
    ggHA_pm hr (fun j : Fin r => M.coroot (e j)) (fun j : Fin r => M.root (e j))
      hα M.xV hxH hsup hxk hfix (ggLin (p := 3) M.model φ) hT
  rw [hweyl] at hw
  obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
  exact ⟨w', hw', ε, hε, fun v => by
    rw [map_mul, LinearEquiv.mul_apply]
    exact hwε v⟩

end CFSG.StandardType

end
