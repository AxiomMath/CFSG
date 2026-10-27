module

public import CFSG.LocalAnalysis.StandardType.GGE6DepBlockDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNbrBalancePumpup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem l5_centralizer_pair (v w : G) :
    Subgroup.centralizer ({v, w} : Set G) =
      Subgroup.centralizer ({v} : Set G) ⊓ Subgroup.centralizer ({w} : Set G) := by
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

theorem ggNbr_of_blocks (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hinn : GGInnerDiagOn Bs L) {v : G} (hD : D = Subgroup.closure {x, v})
    (hblk : GGE6DepBlockCfg p Bs x J v) :
    GGNbr p B x D J v (ggLayerClosure p (Subgroup.centralizer ({v} : Set G)) J) := by
  classical
  obtain ⟨hI, hBsB, hDJ⟩ := hcfg
  have hsimple : IsSimpleGroup G := hI.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hI.2.1
  have hKP : KProper InCatalog G := hI.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBsB.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hxBs : x ∈ Bs := hBsB.1 hS.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  have hJJ : ⁅J, J⁆ = J :=
    commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hinn
  have hBsJ : Bs ≤ normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBsB.1 hDJ.1 hBsL
  obtain ⟨hvB, -, hv1, -⟩ := facts_of_closure_pair hI hDJ hD
  have hKGroup : CFSG.Open.lBalanceIsKGroup ↥(centralizer ({v} : Set G)) :=
    lBalanceIsKGroup_of_kProper hKP (centralizer_singleton_ne_top_of_isSimpleGroup hnab hv1)
  obtain ⟨hKpc, hJK, -, hN | hV⟩ :=
    pumpup_of_stdSub (ggPumpupInput_of_lBalance hL) hI hDJ hpJ hD
  · exact hN
  · exfalso
    obtain ⟨w, Dw, N, n, hwBs, hwp, hvw, hDw, hpDw, hNDw, hNJ, hNN, hpN, hnDw, hnBs,
      hnx⟩ := hblk
    have hBsv : Bs ≤ centralizer ({v} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr (hcomm b hb v (hBsB.1 hvB))
    have hBsK : Bs ≤ normalizer (ggLayerClosure p (centralizer ({v} : Set G)) J : Set G) :=
      GGDichotomy.le_normalizer_of_pComponent hBsv hKpc hJK hJJ hpJ hBsJ
    have hDwY : IsComponentOf Dw
        (Subgroup.centralizer ({v} : Set G) ⊓
          Subgroup.centralizer (({w} : Finset G) : Set G)) := by
      rw [Finset.coe_singleton, ← l5_centralizer_pair v w]
      exact hDw
    have hDwP : CFSG.Open.lBalanceIsPComponent p
        (Subgroup.centralizer ({v} : Set G) ⊓
          Subgroup.centralizer (({w} : Finset G) : Set G)) Dw :=
      lBalanceIsPComponent_of_isComponentOf hDwY (not_le_lBalancePrimeCore_of_dvd hpDw)
    have hSY : ∀ e ∈ ({w} : Finset G), e ∈ centralizer ({v} : Set G) := by
      intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact mem_centralizer_singleton_iff.mpr hvw.symm
    have hSp : ∀ e ∈ ({w} : Finset G), e ^ p = 1 := by
      intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact hwp
    have hSX : ∀ e ∈ ({w} : Finset G),
        e ∈ normalizer (ggLayerClosure p (centralizer ({v} : Set G)) J : Set G) := by
      intro e he
      rw [Finset.mem_singleton] at he
      subst he
      exact hBsK hwBs
    have hSc : ∀ e ∈ ({w} : Finset G), ∀ f ∈ ({w} : Finset G), e * f = f * e := by
      intro e he f hf
      rw [Finset.mem_singleton] at he hf
      subst he
      subst hf
      rfl
    rcases GGDichotomy.pComponent_le_or_commutator_le hL hp hKGroup
        ((largeEvenPComponent_iff_lBalance p (centralizer ({v} : Set G))
          (ggLayerClosure p (centralizer ({v} : Set G)) J)).1 hKpc).2
        ({w} : Finset G) hSY hSp hSX hSc Dw hDwP with hle | hcom
    · have hnK : n ∈ ggLayerClosure p (centralizer ({v} : Set G)) J := hle hnDw
      have hsub : IsSubnormal (ggLayerClosure p (centralizer ({v} : Set G)) J)
          (centralizer ({v} : Set G)) :=
        (AssemblyBPredicates.isSubnormal_iff_open _ _).2
          ((largeEvenPComponent_iff_lBalance p _ _).1 hKpc).2.1
      have hO : n * x * n⁻¹ * x⁻¹ ∈
          CFSG.Open.lBalancePrimeCore p (centralizer ({v} : Set G)) :=
        largeEvenPPrimeCoreOf_le_of_isSubnormal hsub
          (hV (Subgroup.commutator_mem_commutator hnK (Subgroup.mem_zpowers x)))
      have hBs' : n * x * n⁻¹ * x⁻¹ ∈ Bs := by
        have h1 : n * x * n⁻¹ ∈ Bs := (mem_normalizer_iff.mp hnBs x).mp hxBs
        exact Bs.mul_mem h1 (Bs.inv_mem hxBs)
      have hnc : n * x * n⁻¹ * x⁻¹ = 1 :=
        GGDichotomy.eq_one_of_mem_of_coprime
          (LBalance.primeCore_coprime p (Subgroup.centralizer ({v} : Set G)))
          hO (hexp _ hBs')
      exact hnx (mul_inv_eq_one.mp hnc)
    · have hNle : N ≤ CFSG.Open.lBalancePrimeCore p (centralizer ({v} : Set G)) := by
        calc N = ⁅N, N⁆ := hNN.symm
          _ ≤ ⁅Dw, ggLayerClosure p (centralizer ({v} : Set G)) J⁆ :=
              Subgroup.commutator_mono hNDw (hNJ.trans hJK)
          _ ≤ CFSG.Open.lBalancePrimeCore p (centralizer ({v} : Set G)) := hcom
      exact (not_le_lBalancePrimeCore_of_dvd (Y := Subgroup.centralizer ({v} : Set G)) hpN) hNle

end CFSG.StandardType

end
