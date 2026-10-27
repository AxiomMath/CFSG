module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitFiveComp
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosurePComp

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem qtwoDU5_ggNbr {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hc : GGConfig 3 B Bs x L D J) {d : G} (hD : D = Subgroup.closure {x, d})
    {J₂ P : Subgroup G} {x₂ : G}
    (hxH : x ∈ Subgroup.centralizer ({d} : Set G))
    (hx₂H : x₂ ∈ Subgroup.centralizer ({d} : Set G)) (hx₂3 : x₂ ^ 3 = 1)
    (hc₁ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)))
    (hc₂ : CFSG.Assembly.IsComponentOf J₂
      (Subgroup.centralizer ({d} : Set G) ⊓ Subgroup.centralizer ({x₂} : Set G)))
    (hl₁ : J ≤ CFSG.Assembly.LargeEvenPLayer 3 (Subgroup.centralizer ({d} : Set G)))
    (hl₂ : J₂ ≤ CFSG.Assembly.LargeEvenPLayer 3 (Subgroup.centralizer ({d} : Set G)))
    (h3₁ : 3 ∣ Nat.card (↥(J.subgroupOf (Subgroup.centralizer ({d} : Set G))) ⧸
      Subgroup.center ↥(J.subgroupOf (Subgroup.centralizer ({d} : Set G)))))
    (h3₂ : 3 ∣ Nat.card (↥(J₂.subgroupOf (Subgroup.centralizer ({d} : Set G))) ⧸
      Subgroup.center ↥(J₂.subgroupOf (Subgroup.centralizer ({d} : Set G)))))
    (hyN₁ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set G)))
        (⟨x, hxH⟩ : ↥(Subgroup.centralizer ({d} : Set G))) ∈
      CFSG.pLayer (↥(Subgroup.centralizer ({d} : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set G))) 3 ⊔
        Subgroup.center (↥(Subgroup.centralizer ({d} : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set G))))
    (hyN₂ : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set G)))
        (⟨x₂, hx₂H⟩ : ↥(Subgroup.centralizer ({d} : Set G))) ∈
      CFSG.pLayer (↥(Subgroup.centralizer ({d} : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set G))) 3 ⊔
        Subgroup.center (↥(Subgroup.centralizer ({d} : Set G)) ⧸
          CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({d} : Set G))))
    (hP₁ : P ≤ J) (hP₂ : P ≤ J₂) (hPJ : ∃ a ∈ P, ∃ b ∈ J, a * b ≠ b * a)
    (hpJ : 3 ∣ Nat.card J) (hpJ₂ : 3 ∣ Nat.card J₂)
    (hxJ₂ : x ∈ Subgroup.normalizer (J₂ : Set G)) (hxc : ∃ j ∈ J₂, x * j ≠ j * x) :
    ∃ N : Subgroup G, GGNbr 3 B x D J d N ∧ J ≤ N ∧ J₂ ≤ N ∧
      LargeEvenPComponent 3 (Subgroup.centralizer ({d} : Set G)) N := by
  have hS : LargeEvenSStar 3 B x L := hc.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hxB
  have hx3' : (⟨x, hxH⟩ : ↥(Subgroup.centralizer ({d} : Set G))) ^ 3 = 1 :=
    Subtype.ext (by simpa using hx3)
  have hx₂3' : (⟨x₂, hx₂H⟩ : ↥(Subgroup.centralizer ({d} : Set G))) ^ 3 = 1 :=
    Subtype.ext (by simpa using hx₂3)
  obtain ⟨N, hN, hJN, hJ₂N⟩ := qtwoDU5_one_component (H := Subgroup.centralizer ({d} : Set G))
    (y₁ := ⟨x, hxH⟩) (y₂ := ⟨x₂, hx₂H⟩) hx3' hx₂3' hc₁ hc₂ hl₁ hl₂ h3₁ h3₂ hyN₁ hyN₂ hP₁ hP₂ hPJ
  have hJperf : ⁅J, J⁆ = J := commutator_self_eq_of_largeEvenStdSub hc.2.2
  refine ⟨N, ggNbr_of_pComponent hc.1 hc.2.2 hpJ hD hN hJN
    (le_iSup_conj_pLayer_of_pComponent hN hJN hJperf hpJ) fun hxO => ?_, hJN, hJ₂N, hN⟩
  obtain ⟨j, hj, hjx⟩ := hxc
  have hcop : Nat.Coprime 3 (Nat.card (LargeEvenPPrimeCoreOf 3 N)) := by
    rw [LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective N.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hcen := mem_centralizer_of_commutator_le_coprime Nat.prime_three hc₂.2.2 hpJ₂ hcop
    (fun j hj => mem_normalizer_largeEvenPPrimeCoreOf (Subgroup.le_normalizer (hJ₂N hj))) hxJ₂
    ((Subgroup.commutator_mono hJ₂N le_rfl).trans hxO)
  exact hjx (Subgroup.mem_centralizer_iff.mp hcen j hj).symm

end CFSG.StandardType.QTwo

end
