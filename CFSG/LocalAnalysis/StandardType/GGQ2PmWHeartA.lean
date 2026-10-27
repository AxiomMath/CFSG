module

public import CFSG.LocalAnalysis.StandardType.GGQTwoWDatum
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import CFSG.LocalAnalysis.StandardType.GGHeartAPm
import CFSG.LocalAnalysis.StandardType.GGTBTorCartan
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
import CFSG.LocalAnalysis.StandardType.GGQTwoPmWDatum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGQ2WDatum.pmW_of_heartA (D : GGQ2WDatum 3) {r : ℕ} (hr : 4 ≤ r) (e : Fin r ≃ D.Λ)
    (hC : ∀ i j, D.cartan (e i) (e j) = CartanMatrix.A r i j)
    (hdim : Module.finrank (ZMod 3) D.V = r)
    (hdep : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range D.coroot)) + 1 = r)
    (u : D.V) (hu0 : u ≠ 0)
    (hfix : ∀ v : D.V, (∀ g ∈ D.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u})
    (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.weyl : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      ∀ v : D.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u} := by
  classical
  let h : Fin r → D.V := fun j => D.coroot (e j)
  let α : Fin r → Module.Dual (ZMod 3) D.V := fun j => D.root (e j)
  have hα : ∀ i j, α i (h j) = ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by
    intro i j
    calc α i (h j) = (D.cartan (e i) (e j) : ZMod 3) := D.pairing (e i) (e j)
      _ = ((CartanMatrix.A r i j : ℤ) : ZMod 3) := by rw [hC i j]
  have hxk : ∀ j : Fin r, α j u = 0 := fun j => D.root_eq_zero_of_fix rfl u hfix (e j)
  let H : Submodule (ZMod 3) D.V := Submodule.span (ZMod 3) (Set.range h)
  have hspanH : Submodule.span (ZMod 3) (Set.range h)
      = Submodule.span (ZMod 3) (Set.range D.coroot) := by
    congr 1
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨e.symm k, by simp [h]⟩
  have hH_eq : Module.finrank (ZMod 3) H = r - 1 := by
    change Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range h)) = r - 1
    rw [hspanH]
    omega
  have hVfin : Module.Finite (ZMod 3) D.V :=
    Module.finite_of_finrank_pos (by rw [hdim]; omega)
  let f : (Fin r → ZMod 3) →ₗ[ZMod 3] D.V := Fintype.linearCombination (ZMod 3) h
  have hrange : LinearMap.range f = H := by
    simp [f, H]
  have hrow : ∀ b : Fin r → ZMod 3, (∀ j, α j (f b) = 0) →
      ∀ j, ∑ k, (CartanMatrix.A r j k : ZMod 3) * b k = 0 := by
    intro b hb j
    have hh : α j (∑ k, b k • h k) = 0 := hb j
    simp only [map_sum, map_smul, hα, smul_eq_mul] at hh
    calc ∑ k, (CartanMatrix.A r j k : ZMod 3) * b k
        = ∑ k, b k * (CartanMatrix.A r j k : ZMod 3) :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
      _ = 0 := hh
  have hrow0 : ∀ b : Fin r → ZMod 3, f b = 0 →
      ∀ j, ∑ k, (CartanMatrix.A r j k : ZMod 3) * b k = 0 :=
    fun b hb => hrow b fun j => by rw [hb, map_zero]
  have hrn : Module.finrank (ZMod 3) H + Module.finrank (ZMod 3) (LinearMap.ker f) = r := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange] at h
    simpa using h
  have hker : Module.finrank (ZMod 3) (LinearMap.ker f) = 1 := by omega
  have hker_ne_bot : LinearMap.ker f ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker
    omega
  obtain ⟨d, hdmem, hdne⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hker_ne_bot
  have hdA : ∀ j, ∑ k, (CartanMatrix.A r j k : ZMod 3) * d k = 0 :=
    hrow0 d (LinearMap.mem_ker.mp hdmem)
  have hxH : u ∉ H := by
    intro huH
    rw [← hrange] at huH
    obtain ⟨c, hc⟩ := huH
    have hcA : ∀ j, ∑ k, (CartanMatrix.A r j k : ZMod 3) * c k = 0 :=
      hrow c fun j => by rw [hc, hxk j]
    obtain ⟨l, hl⟩ := ggCartanA_ker_le_one (p := 3) (N := r) d c hdA hcA hdne
    apply hu0
    rw [← hc, hl, map_smul, LinearMap.mem_ker.mp hdmem, smul_zero]
  have hsup : H ⊔ Submodule.span (ZMod 3) {u} = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hxH, hH_eq, hdim]
    omega
  have hfixroots : ∀ v : D.V, (∀ j : Fin r, α j v = 0) →
      v ∈ Submodule.span (ZMod 3) {u} := by
    intro v hv
    refine D.ker_pi_root_le u hfix ?_
    rw [LinearMap.mem_ker]
    funext k
    simpa [α] using hv (e.symm k)
  have hweyl : ggQ2WeylOf h α = D.weyl := by
    change Subgroup.closure {t : D.V ≃ₗ[ZMod 3] D.V |
        ∃ j : Fin r, ∀ v, t v = v - α j v • h j} =
      Subgroup.closure (Set.range D.simpleRefl)
    congr 1
    ext t
    constructor
    · rintro ⟨j, hj⟩
      exact ⟨e j, LinearEquiv.ext fun v =>
        (D.simpleRefl_apply (e j) v).trans (hj v).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨j, rfl⟩ := e.surjective k
      exact ⟨j, fun v => D.simpleRefl_apply (e j) v⟩
  have hT' : T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
    rw [hweyl]
    exact hT
  obtain ⟨w, hw, ε, hε, hwε⟩ :=
    ggHA_pm hr h α hα u hxH hsup hxk hfixroots T hT'
  exact ⟨w, hweyl ▸ hw, ε, hε, hwε⟩

end CFSG.StandardType

end
