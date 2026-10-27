module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1BC
public import CFSG.LocalAnalysis.StandardType.GGTPNI1BCSupp
public import CFSG.LocalAnalysis.StandardType.GGTPNI1BCComm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympInner

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  Polynomial
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

private theorem tpbcc_pow_orderOf {G : Type} [Group G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {x : G} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    x ^ p = 1 ∧ orderOf x = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxp : x ^ p = 1 := hE.2 x hxE
  exact ⟨hxp, orderOf_eq_prime hxp hx1⟩

private theorem tpbcc_core_of_support
    {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 3 ≤ m)
    (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hchar : CharP K 2)
    (hK : Nat.card K = 2 ^ n) {x : StatedSp (m + 1) K} {J E : Subgroup (StatedSp (m + 1) K)}
    (H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x))
    (hprojinj : Function.Injective (proj (m + 1) K)) (hxp : x ^ p = 1) (hxord : orderOf x = p)
    (hxE : x ∈ E) (hE : IsElemAbelian p E)
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer {x}))
    (hJO : ∃ O : reciprocalOrbits (spEnd x),
      J = ⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆)
    (hlab : GGHasLabel ⟨.C, m, n⟩ (↥J ⧸ Subgroup.center ↥J))
    (hcomm : ∀ e ∈ E, ∀ j ∈ J, e * j = j * e) : E ≤ Subgroup.zpowers x := by
  obtain ⟨O, hJO⟩ := hJO
  have hO : (O : Set K[X]) = {X - 1} :=
    tpbcc_support_eq_fixed hp hp2 hm hn hchar hK H hprojinj hxp hJ O hJO hlab
  have hJfix : J ≤ spSupported x {X - 1} := by
    rw [← hO, hJO]
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    simp only [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂) (Subgroup.inv_mem _ h₁))
      (Subgroup.inv_mem _ h₂)
  exact tpbcc_le_zpowers_of_fixed hp hp2 hm hn hchar hK H hprojinj hxp hxord hxE hE hJ hJfix hlab
    hcomm

theorem tpbcCore_holds
    : TpbcCore := by
  intro p m n hp hp2 hm hn K _ _ hK x J E hx1 hxE hE hJ hlab hcomm
  have hchar : CharP K 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hK
  haveI : CharP K 2 := hchar
  haveI : NeZero (m + 1) := ⟨by omega⟩
  obtain ⟨hxp, hxord⟩ := tpbcc_pow_orderOf hp hE hxE hx1
  have hprojinj : Function.Injective (proj (m + 1) K) :=
    (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo (r := m + 1)).1
  have hprojx_ord : orderOf (proj (m + 1) K x) = p := by
    rw [← hxord]
    exact orderOf_injective _ hprojinj x
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks
    (ℓ := 2) (f := n) (p := p) (K := K) Nat.prime_two hn hK hp hp2 (by omega) (by omega)
    (proj (m + 1) K x) hprojx_ord
  have H : SpPrimaryBlocks 2 n p x (proj (m + 1) K x) :=
    hblocks x rfl hxord
  exact tpbcc_core_of_support hp hp2 hm hn hchar hK H hprojinj hxp hxord hxE hE hJ
    (tpbcc_component_eq_derived hp hp2 hn hchar hK H hprojinj hxp hJ) hlab hcomm

end CFSG.StandardType

end
