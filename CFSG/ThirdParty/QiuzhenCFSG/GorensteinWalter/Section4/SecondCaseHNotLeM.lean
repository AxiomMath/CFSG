module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # H is not contained in M  (source: refs/bender-dihedral-sylow.tex L648–649) -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- From `H ≤ M`, Theorem 2.6 applied with `Ĥ := M` places `t` in
`O₂(M)`: `t ∈ S`, `U ≤ H = C_G(t)` gives `t ∈ C_S(U)`, and the second
conjunct of `CentralizerStructure` identifies `C_S(U)` with `O₂(M)`. -/
private theorem t_mem_twoCoreOf_of_H_le_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (w : SecondCaseWitness c) (hHM : c.H ≤ w.M) :
    c.t ∈ twoCoreOf w.M := by
  let c' : CentralizerSetup G :=
    { c with
      Hhat := w.M
      H_le_Hhat := hHM
      Hhat_maximal := w.M_maximal }
  have h26 : CentralizerStructure c' := theorem_2_6 hmin c'
  simpa [c'] using centralizerStructure_t_mem_twoCore c' h26

/-- `O₂(A) ≤ F(A)`: the two-core is a normal nilpotent subgroup of `A`. -/
private theorem twoCoreOf_le_fittingSubgroupOf {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) : twoCoreOf A ≤ fittingSubgroupOf A := by
  have hq2 : twoCoreOf A = qCoreOf A 2 := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton A 2 Nat.prime_two]
  rw [hq2]
  exact qCoreOf_le_fittingSubgroupOf A 2 Nat.prime_two

/-- Bender's bare "By Theorem 2.6, `H ⊄ M`" (L648–649): if `H ≤ M`,
then `t ∈ O₂(M) ≤ F(M)`; the second-case component `E` containing `t`
centralizes `F(M)`, so `t ∈ Z(E)`, contradicting the odd order of `Z(E)`. -/
public theorem secondCase_H_not_le_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (c : CentralizerSetup G)
    (w : SecondCaseWitness c) :
    ¬ c.H ≤ w.M := by
  intro hHM
  have ht2 : c.t ∈ twoCoreOf w.M := t_mem_twoCoreOf_of_H_le_M hmin c w hHM
  have htF : c.t ∈ fittingSubgroupOf w.M := (twoCoreOf_le_fittingSubgroupOf w.M) ht2
  obtain ⟨d⟩ := secondCase_componentData hmin c w
  have hEcF : d.E ≤ Subgroup.centralizer ((fittingSubgroupOf w.M : Subgroup G) : Set G) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := d.E)
      (H₂ := fittingSubgroupOf w.M)).mp (component_centralizes_fittingSubgroupOf d.E_component)
  have htZ : (⟨c.t, d.t_mem_E⟩ : d.E) ∈ Subgroup.center d.E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hcomm : c.t * (y : G) = (y : G) * c.t :=
      (Subgroup.mem_centralizer_iff (g := (y : G))
        (s := ((fittingSubgroupOf w.M : Subgroup G) : Set G))).1 (hEcF y.2) c.t htF
    exact hcomm.symm
  let tZ : Subgroup.center d.E := ⟨⟨c.t, d.t_mem_E⟩, htZ⟩
  have htZne : tZ ≠ 1 := by
    intro h1
    exact c.t_involution.1 (congrArg Subtype.val (congrArg Subtype.val h1))
  have htZsq : tZ * tZ = 1 := by
    ext
    simpa [pow_two] using c.t_involution.2
  have hord2 : orderOf tZ = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using htZsq) htZne
  have hdvd : 2 ∣ Nat.card (Subgroup.center d.E) := by
    have hd := orderOf_dvd_natCard tZ
    simpa [hord2] using hd
  exact d.center_odd.not_two_dvd_nat hdvd

end CFSG.GorensteinWalter
