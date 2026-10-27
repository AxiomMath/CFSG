module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow subgroups above the selected PSL₂ component are noncyclic
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Every Sylow `2`-subgroup of an ambient subgroup containing the selected
PSL₂ component is noncyclic. -/
public theorem secondCase_psl2_sylow_not_cyclic_of_component_le
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (N : Subgroup G) (hEN : d.E ≤ N) :
    ∀ P : Sylow 2 N, ¬ IsCyclic P := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨SM, _hSMcent, SE, hSEamb⟩ :=
    secondCase_centralizer_contains_sylow c w d
  let Q : Type u := d.E ⧸ Subgroup.center d.E
  let q : d.E →* Q := QuotientGroup.mk' (Subgroup.center d.E)
  let PE : Sylow 2 Q :=
    SE.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center d.E))
  let PP : Sylow 2 (PSL2 K) :=
    PE.mapSurjective (f := e.some.toMonoidHom) e.some.surjective
  have hPPnc : ¬ IsCyclic PP := by
    intro hcyc
    obtain ⟨m, hm, ⟨em⟩⟩ :=
      (psl2_odd_hasDihedralSylowTwo_model K hK) PP
    have hcycD : IsCyclic (DihedralGroup (2 ^ m)) :=
      (MulEquiv.isCyclic em).mp hcyc
    apply DihedralGroup.not_isCyclic
      (by
        have hm0 : m ≠ 0 := by omega
        exact (Nat.one_lt_pow hm0 (by norm_num : 1 < (2 : ℕ))).ne.symm)
      hcycD
  have hSEnc : ¬ IsCyclic SE := by
    intro hcyc
    have hPEcyc : IsCyclic PE :=
      isCyclic_of_surjective
        (q.subgroupMap (SE : Subgroup d.E))
        (q.subgroupMap_surjective (SE : Subgroup d.E))
    have hPPcyc : IsCyclic PP :=
      isCyclic_of_surjective
        (e.some.toMonoidHom.subgroupMap (PE : Subgroup Q))
        (e.some.toMonoidHom.subgroupMap_surjective (PE : Subgroup Q))
    exact hPPnc hPPcyc
  let A : Subgroup G := (SE : Subgroup d.E).map d.E.subtype
  have hAp : IsPGroup 2 A := SE.isPGroup'.map d.E.subtype
  have hAleE : A ≤ d.E := by
    intro x hx
    have hx' : x ∈ ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E := by
      rw [← hSEamb]
      exact hx
    exact hx'.2
  have hAleN : A ≤ N := hAleE.trans hEN
  have hAnc : ¬ IsCyclic A := by
    intro hAcyc
    let eSE : (SE : Subgroup d.E) ≃* A :=
      Subgroup.equivMapOfInjective (SE : Subgroup d.E)
        d.E.subtype d.E.subtype_injective
    exact hSEnc ((MulEquiv.isCyclic eSE).mpr hAcyc)
  intro P hPcyc
  let AN : Subgroup N := A.subgroupOf N
  have hANp : IsPGroup 2 AN := hAp.comap_subtype
  obtain ⟨PN, hANPN⟩ := hANp.exists_le_sylow
  have hPNcyc : IsCyclic PN :=
    (MulEquiv.isCyclic (Sylow.equiv PN P)).mpr hPcyc
  have hANcyc : IsCyclic AN := by
    let : IsCyclic PN := hPNcyc
    exact Subgroup.isCyclic_of_le hANPN
  let eAN : AN ≃* A := Subgroup.subgroupOfEquivOfLe hAleN
  have hAcyc : IsCyclic A := isCyclic_of_surjective eAN eAN.surjective
  exact hAnc hAcyc

end CFSG.GorensteinWalter
