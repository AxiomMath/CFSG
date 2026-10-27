module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Internal

variable {G : Type} [Group G] [Finite G]

theorem ggDichotomy_refined (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hInn : GGInnerDiagAll p B Bs x L D J) {t : MulAut ↥Bs} {Jt : Subgroup G}
    (hr : GGIsReflection p t) (hind : t ∈ ggInduced Jt Bs)
    (hJC : Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G))
    (hpc : IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G)))) :
    Jt ≤ L ∨ (∃ (d : G) (K : Subgroup G), GGNbr p B x D J d K ∧ J ≤ K ∧ Jt ≤ K) ∨
      ∀ a ∈ ggInduced J Bs, t * a = a * t := by
  obtain ⟨hI, hBsB, hDJ⟩ := hcfg
  have hsimple : IsSimpleGroup G := hI.1
  have hnab : ∃ a b : G, a * b ≠ b * a := hI.2.1
  have hKP : KProper InCatalog G := hI.2.2.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hS.2.2.1
  have hBsabel : IsElemAbelian p Bs := hBsB.2.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hexp : ∀ b ∈ Bs, b ^ p = 1 := hBsabel.2
  have hxBs : x ∈ Bs := hBsB.1 hS.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  have hJJ : ⁅J, J⁆ = J :=
    commutator_self_eq_of_isQuasisimple hDJ.1.2.2.2.2.2.1.2.2
  have hBsL : Bs ≤ normalizer (L : Set G) := GGDichotomy.le_normalizer_of_innerDiagOn hInn.1
  have hBsJ : Bs ≤ normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBsB.1 hDJ.1 hBsL
  have hEBs : ggFixG Bs t ≤ Bs := Subgroup.map_subtype_le _
  have hT : CFSG.Open.lBalanceIsPComponent p (centralizer (ggFixG Bs t : Set G)) Jt :=
    (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p _ Jt hJC).mp hpc
  have hKGroup : ∀ d : G, d ≠ 1 →
      CFSG.Open.lBalanceIsKGroup ↥(centralizer ({d} : Set G)) := fun d hd =>
    lBalanceIsKGroup_of_kProper hKP (centralizer_singleton_ne_top_of_isSimpleGroup hnab hd)
  have step : ∀ (d : G) (X : Subgroup G), d ≠ 1 → d ∈ ggFixG Bs t →
      LargeEvenPComponent p (centralizer ({d} : Set G)) X → J ≤ X →
      Jt ≤ X ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t := by
    intro d X hd1 hdE hX hJX
    have hBsd : Bs ≤ centralizer ({d} : Set G) := fun b hb =>
      mem_centralizer_singleton_iff.mpr (hcomm b hb d (hEBs hdE))
    have hBsX := GGDichotomy.le_normalizer_of_pComponent hBsd hX hJX hJJ hpJ hBsJ
    rcases GGDichotomy.dichotomy_core hL hp hcomm hexp hEBs hdE (hKGroup d hd1) hBsX
        ((largeEvenPComponent_iff_lBalance p _ X).1 hX).2 hT with h | h
    · exact Or.inl h
    · exact Or.inr (GGDichotomy.aut_commute_of_commutator_le hBsd hexp hind hJX h)
  by_cases hxE : x ∈ ggFixG Bs t
  ·
    obtain ⟨hJL, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
    rcases step x L hx1 hxE hLpc hJL with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  ·
    obtain ⟨d, hdD, hdE, hdx⟩ := GGDichotomy.exists_mem_not_mem_zpowers hp
      ((hDJ.1.1).trans hBsB.1) hDJ.1.2.2.1 (hexp x hxBs) (GGDichotomy.relIndex_ggFixG hr) hxE
    have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
    have hD : D = Subgroup.closure {x, d} := eq_closure_pair_of_mem hI hDJ hdD hdx
    obtain ⟨hKpc, hJK, -, hN | hV⟩ :=
      pumpup_of_stdSub (ggPumpupInput_of_lBalance hL) hI hDJ hpJ hD
    · rcases step d _ hd1 hdE hKpc hJK with h | h
      · exact Or.inr (Or.inl ⟨d, _, hN, hJK, h⟩)
      · exact Or.inr (Or.inr h)
    · rcases step d _ hd1 hdE hKpc hJK with h | h
      ·
        exfalso
        obtain ⟨n, hnJt, hnN, hn⟩ := hind
        have hsub : IsSubnormal (ggLayerClosure p (centralizer ({d} : Set G)) J)
            (centralizer ({d} : Set G)) :=
          (AssemblyBPredicates.isSubnormal_iff_open _ _).2
            ((largeEvenPComponent_iff_lBalance p _ _).1 hKpc).2.1
        have hO : n * x * n⁻¹ * x⁻¹ ∈
            CFSG.Open.lBalancePrimeCore p (centralizer ({d} : Set G)) :=
          largeEvenPPrimeCoreOf_le_of_isSubnormal hsub
            (hV (Subgroup.commutator_mem_commutator (h hnJt) (Subgroup.mem_zpowers x)))
        have hBs' : n * x * n⁻¹ * x⁻¹ ∈ Bs := by
          have h1 : n * x * n⁻¹ ∈ Bs := (mem_normalizer_iff.mp hnN x).mp hxBs
          exact Bs.mul_mem h1 (Bs.inv_mem hxBs)
        have hnx : n * x * n⁻¹ * x⁻¹ = 1 :=
          GGDichotomy.eq_one_of_mem_of_coprime (LBalance.primeCore_coprime p _) hO
            (hexp _ hBs')
        exact hxE (GGDichotomy.mem_ggFixG_of_induced hxBs hn (mul_inv_eq_one.mp hnx))
      · exact Or.inr (Or.inr h)

end Internal

end CFSG.StandardType
