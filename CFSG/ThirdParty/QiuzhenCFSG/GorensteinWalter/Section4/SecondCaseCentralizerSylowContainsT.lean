module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The distinguished involution lies in the selected centralizing Sylow

The Sylow subgroup supplied by `secondCase_centralizer_contains_sylow` lies in
`C_M(t)`.  Since `t` is itself an involution in `M`, adjoining its cyclic
subgroup still gives a `2`-subgroup.  Sylow maximality therefore forces `t`
into the selected Sylow subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The distinguished involution belongs to every selected Sylow subgroup of
`M` that centralizes it. -/
public theorem secondCase_centralizer_sylow_contains_t
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) (SM : Sylow 2 (↥w.M))
    (hSMcent : (SM : Subgroup w.M).map w.M.subtype ≤
      Subgroup.centralizer ({c.t} : Set G)) :
    (⟨c.t, d.E_component.1 d.t_mem_E⟩ : w.M) ∈
      (SM : Subgroup w.M) := by
  let tM : w.M := ⟨c.t, d.E_component.1 d.t_mem_E⟩
  have htI : IsInvolution tM := by
    constructor
    · intro h
      exact c.t_involution.1 (congrArg Subtype.val h)
    · apply Subtype.ext
      simpa [pow_two] using c.t_involution.2
  have hcent : ∀ x : w.M, x ∈ (SM : Subgroup w.M) → Commute tM x := by
    intro x hx
    have hxG : (x : G) ∈ (SM : Subgroup w.M).map w.M.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hSMcent hxG)
    change tM * x = x * tM
    apply Subtype.ext
    simpa [tM] using h.symm
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have htP : IsPGroup 2 (Subgroup.zpowers tM) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime htI.2 htI.1
  have hSMP : IsPGroup 2 (SM : Subgroup w.M) := SM.isPGroup'
  have hnorm : Subgroup.zpowers tM ≤
      Subgroup.normalizer ((SM : Subgroup w.M) : Set w.M) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    have hyc : Commute tM y := hcent y hy
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    have hpow : Commute (tM ^ n) y := hyc.zpow_left n
    have heq : tM ^ n * y * (tM ^ n)⁻¹ = y := by
      rw [hpow.eq]
      simp
    rw [heq]
    exact hy
  have hsup : IsPGroup 2
      ((SM : Subgroup w.M) ⊔ Subgroup.zpowers tM : Subgroup w.M) :=
    IsPGroup.to_sup_of_normal_left'
      (H := (SM : Subgroup w.M)) (K := Subgroup.zpowers tM) hSMP htP hnorm
  have hSMle : (SM : Subgroup w.M) ≤
      ((SM : Subgroup w.M) ⊔ Subgroup.zpowers tM : Subgroup w.M) := le_sup_left
  have heq : ((SM : Subgroup w.M) ⊔ Subgroup.zpowers tM : Subgroup w.M) =
      (SM : Subgroup w.M) := Sylow.is_maximal' SM hsup hSMle
  have htSup : tM ∈
      ((SM : Subgroup w.M) ⊔ Subgroup.zpowers tM : Subgroup w.M) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers tM)
  rw [heq] at htSup
  exact htSup

end CFSG.GorensteinWalter
