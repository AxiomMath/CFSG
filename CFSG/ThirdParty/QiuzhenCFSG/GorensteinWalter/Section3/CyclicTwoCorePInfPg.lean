module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePPg
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FUFittingContainment
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

/-- Conjugating a subgroup first by `g⁻¹` and then by `g` is the identity. -/
public theorem conj_inv_then_conj_eq
    {G : Type u} [Group G] (A : Subgroup G) (g : G) :
    conjugateSubgroup (conjugateSubgroup A g⁻¹) g = A := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
    have heq : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom a) = a := by
      simp
      group
    rw [heq]
    exact ha
  · intro hx
    apply Subgroup.mem_map.mpr
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · apply Subgroup.mem_map.mpr
      exact ⟨x, hx, by simp⟩
    · simp
      group

/-- In the cyclic first case, `P ∩ P^g = ⊥` for every `P ≤ F(U)` and
`g ∉ H = C_G(t)`.

The proof transports the normalizer control of `hfirst.2` from
`Y = (P ∩ P^g)^{g⁻¹}` back to `X = P ∩ P^g`, so `X` witnesses
`NormalizerControlledBy Ĥ Ĥ^g`; Lemma 2.5 then forces `g ∈ N_G(Ĥ)`, and
self-normalization of the coatom `Ĥ = H` contradicts `g ∉ H`.  This repairs
the paper's `P ∩ P^g = ⊥` step without the invalid `P^g = P` cardinality
argument. -/
public theorem firstCase_P_inf_Pg_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hHhat : c.Hhat = c.H)
    (P : Subgroup G) (hPfu : P ≤ c.FU)
    (g : G) (hg : g ∉ c.H) :
    P ⊓ conjugateSubgroup P g = ⊥ := by
  let X : Subgroup G := P ⊓ conjugateSubgroup P g
  by_contra hXbot
  have hXne : X ≠ ⊥ := by simpa [X] using hXbot
  let Y : Subgroup G := conjugateSubgroup X g⁻¹
  have hYmap : conjugateSubgroup Y g = X := by
    simpa [Y] using conj_inv_then_conj_eq X g
  have hYleP : Y ≤ P := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hxPg : x ∈ conjugateSubgroup P g := (inf_le_right :
        X ≤ conjugateSubgroup P g) hx
    rcases Subgroup.mem_map.mp hxPg with ⟨p, hp, hxp⟩
    have hxp' : x = g * p * g⁻¹ := by
      simpa [conjugateSubgroup, MulAut.conj_apply] using hxp.symm
    have heq : (MulAut.conj g⁻¹).toMonoidHom x = p := by
      rw [hxp']
      simp
      group
    rw [heq]
    exact hp
  have hYfu : Y ≤ c.FU := hYleP.trans hPfu
  have hYne : Y ≠ ⊥ := by
    intro hYbot
    apply hXne
    rw [← hYmap]
    simp [conjugateSubgroup, hYbot]
  have hNY : Subgroup.normalizer (Y : Set G) ≤ c.Hhat :=
    hfirst.2 Y hYne hYfu
  have hNX : Subgroup.normalizer (X : Set G) ≤
      conjugateSubgroup c.Hhat g := by
    have hmapN : conjugateSubgroup (Subgroup.normalizer (Y : Set G)) g =
        Subgroup.normalizer (X : Set G) := by
      have hYmap' : Y.map (MulAut.conj g).toMonoidHom = X := by
        simpa [conjugateSubgroup] using hYmap
      change (Subgroup.normalizer (Y : Set G)).map
          (MulAut.conj g).toMonoidHom = _
      rw [Subgroup.map_normalizer_eq_of_bijective Y (MulAut.conj g).bijective]
      rw [hYmap']
    rw [← hmapN]
    simpa [conjugateSubgroup] using
      (Subgroup.map_mono hNY (f := (MulAut.conj g).toMonoidHom))
  have hXfu : X ≤ c.FU := inf_le_left.trans hPfu
  have hXfhat : X ≤ fittingSubgroupOf c.Hhat :=
    hXfu.trans (FU_le_fittingSubgroupOf_Hhat_of_centralizerStructure c
      (theorem_2_6 hmin c))
  have hcontrol : NormalizerControlledBy c.Hhat
      (conjugateSubgroup c.Hhat g) :=
    ⟨X, hXne, hXfhat, hNX⟩
  have hodd : oddCoreOf c.Hhat ≠ ⊥ := by
    rw [← (theorem_2_6 hmin c).1]
    exact (lemma_2_2 hmin c).2
  have hEq : c.Hhat = conjugateSubgroup c.Hhat g :=
    lemma_2_5 hmin c g hcontrol hodd
  have hgNorm : g ∈ Subgroup.normalizer (c.Hhat : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEq.symm
  have hHhatne : c.Hhat ≠ ⊥ := by
    intro hbot
    have htH : c.t ∈ c.H := by
      rw [c.H_eq_centralizer]
      exact (Subgroup.mem_centralizer_singleton_iff).mpr rfl
    have htHhat : c.t ∈ c.Hhat := c.H_le_Hhat htH
    rw [hbot] at htHhat
    exact c.t_involution.1 (Subgroup.mem_bot.mp htHhat)
  have hN : Subgroup.normalizer (c.Hhat : Set G) = c.Hhat :=
    normalizer_eq_of_nontrivial_normal_in_coatom
      (minimalCounterexample_isSimple hmin) c.Hhat_maximal le_rfl hHhatne
      (Subgroup.normal_subgroupOf_of_le_normalizer
        (H := c.Hhat) (N := c.Hhat) Subgroup.le_normalizer)
  have hgHhat : g ∈ c.Hhat := by
    rw [← hN]
    exact hgNorm
  rw [hHhat] at hgHhat
  exact hg hgHhat

end CFSG.GorensteinWalter
