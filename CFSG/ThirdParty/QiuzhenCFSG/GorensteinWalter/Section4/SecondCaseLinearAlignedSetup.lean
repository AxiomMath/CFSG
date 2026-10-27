module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Aligning the ambient Sylow with the selected maximal subgroup

The fixed `CentralizerSetup` need not have its Sylow subgroup already aligned
with the chosen Sylow subgroup of the second-case maximal subgroup.  Since the
fixed Sylow lies in `H = C_G(t)`, conjugacy of Sylow subgroups inside `H`
allows us to conjugate the setup by an element of `H`.  This preserves `H`,
`U`, and the component data while placing the selected Sylow subgroup inside
the new ambient Sylow.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Conjugate the centralizer setup so that a given Sylow subgroup of `M`
(which lies in `C_M(t)`) is contained in the ambient Sylow. -/
public theorem secondCase_linear_aligned_setup
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G)) :
    ∃ c' : CentralizerSetup G, ∃ w' : SecondCaseWitness c',
      ∃ d' : SecondCaseComponentData w',
        w'.M = w.M ∧ d'.E = d.E ∧
          ((SM : Subgroup w.M).map w.M.subtype) ≤ (c'.S : Subgroup G) := by
  classical
  have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
  let A : Subgroup G := (SM : Subgroup w.M).map w.M.subtype
  have hAleH : A ≤ c.H := by
    rw [c.H_eq_centralizer]
    exact hSMcent
  have hAp : IsPGroup 2 A := SM.isPGroup'.map w.M.subtype
  let AH : Subgroup c.H := A.subgroupOf c.H
  have hAHp : IsPGroup 2 AH := hAp.comap_subtype
  let SH : Sylow 2 c.H := c.S.subtype hSleH
  obtain ⟨PH, hAPH⟩ := hAHp.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq c.H SH PH
  let S' : Sylow 2 G := h • c.S
  let S0' : Subgroup G :=
    Subgroup.map (MulAut.conj (h : G)).toMonoidHom c.S0
  have hS0leS' : S0' ≤ (S' : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    change (h : G) * a * (h : G)⁻¹ ∈ (h : G) • (c.S : Sylow 2 G)
    exact Set.mem_smul_set.mpr ⟨a, c.S0_le_S ha, rfl⟩
  have hS0cyc : IsCyclic S0' := by
    let e0 : c.S0 ≃* Subgroup.map (MulAut.conj (h : G)).toMonoidHom c.S0 :=
      Subgroup.equivMapOfInjective c.S0 (MulAut.conj (h : G)).toMonoidHom
        (MulAut.conj (h : G)).injective
    exact (MulEquiv.isCyclic e0).mp c.S0_cyclic
  have hSindex : Nat.card (S' : Subgroup G) = 2 * Nat.card S0' := by
    have hS : Nat.card (S' : Subgroup G) = Nat.card (c.S : Subgroup G) :=
      Nat.card_congr (c.S.equivSMul (h : G)).toEquiv.symm
    have hS0 : Nat.card S0' = Nat.card c.S0 := by
      exact Nat.card_congr (Subgroup.equivMapOfInjective c.S0
        (MulAut.conj (h : G)).toMonoidHom (MulAut.conj (h : G)).injective).toEquiv.symm
    rw [hS, hS0]
    exact c.S_index_two
  have htS0' : c.t ∈ S0' := by
    change c.t ∈ Subgroup.map (MulAut.conj (h : G)).toMonoidHom c.S0
    apply Subgroup.mem_map.mpr
    refine ⟨c.t, c.t_mem_S0, ?_⟩
    have hcomm : Commute (h : G) c.t := by
      have hhcent : (h : G) ∈ Subgroup.centralizer ({c.t} : Set G) := by
        rw [← c.H_eq_centralizer]
        exact h.2
      exact Subgroup.mem_centralizer_singleton_iff.mp hhcent
    simp [MulAut.conj_apply, hcomm.eq]
  have hAinS' : A ≤ (S' : Subgroup G) := by
    intro x hx
    let xH : c.H := ⟨x, hAleH hx⟩
    have hxAH : xH ∈ AH := by
      exact Subgroup.mem_subgroupOf.mpr hx
    have hxPH : xH ∈ PH := hAPH hxAH
    have hxSH : xH ∈ h • SH := by rw [hh]; exact hxPH
    have hsub : h • SH = (S' : Sylow 2 G).subtype (by
      exact Sylow.smul_le hSleH h) := by
      simpa [S', SH] using (Sylow.smul_subtype hSleH h)
    have hxSsub : xH ∈ (S' : Sylow 2 G).subtype (by
      exact Sylow.smul_le hSleH h) := by
      rw [← hsub]
      exact hxSH
    exact Subgroup.mem_subgroupOf.mp hxSsub
  let c' : CentralizerSetup G :=
    { S := S'
      m := c.m
      one_le_m := c.one_le_m
      dihedralEquiv := ⟨(c.S.equivSMul (h : G)).symm.trans
        c.dihedralEquiv.some⟩
      S0 := S0'
      S0_le_S := hS0leS'
      S0_cyclic := hS0cyc
      S_index_two := hSindex
      t := c.t
      t_mem_S0 := htS0'
      t_involution := c.t_involution
      H := c.H
      H_eq_centralizer := c.H_eq_centralizer
      Hhat := c.Hhat
      H_le_Hhat := c.H_le_Hhat
      Hhat_maximal := c.Hhat_maximal }
  let w' : SecondCaseWitness c' :=
    { M := w.M
      M_maximal := w.M_maximal
      M_not_le_Hhat := w.M_not_le_Hhat
      t_mem_componentLayer := w.t_mem_componentLayer
      X := w.X
      X_ne_bot := w.X_ne_bot
      X_le_FU := by
        dsimp [c', CentralizerSetup.FU, CentralizerSetup.U]
        exact w.X_le_FU
      normalizer_X_le_M := w.normalizer_X_le_M }
  let d' : SecondCaseComponentData w' :=
    { E := d.E
      E_component := d.E_component
      t_mem_E := d.t_mem_E
      model := d.model
      E_normal := d.E_normal
      center_odd := d.center_odd }
  refine ⟨c', w', d', rfl, rfl, ?_⟩
  simpa [c', A, S'] using hAinS'

end CFSG.GorensteinWalter
