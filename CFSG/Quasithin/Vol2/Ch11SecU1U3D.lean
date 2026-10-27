module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Main
public import CFSG.Quasithin.Vol2.Ch11SecE3L0
public import CFSG.Quasithin.Vol2.Ch11SecU1U3A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.U3

open CFSG.Quasithin.E2P.Asc80 CFSG.Quasithin CFSG.Open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin.A312U3 (uniData)

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_psu3_model (hp2 : p ≠ 2) (hU : IsPSU 3 p 1 ↥(CFSG.generalizedFitting G))
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Nat.card F = p ^ 2)
      (_ : PSU3F p F ≃* ↥(CFSG.generalizedFitting G)),
      SecE3.AlmostSimple (CFSG.generalizedFitting G) ∧
        2 ∣ Nat.card ↥(CFSG.generalizedFitting G) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_equiv_psu3 hU
  refine ⟨F, inferInstance, inferInstance, hF, e.symm, ?_, ?_⟩
  · obtain ⟨a, b, hab⟩ := exists_noncomm_psu3 hp2 hF
    exact SecE3.almostSimple_generalizedFitting hs ⟨e.symm a, e.symm b, fun h => hab
      (e.symm.injective (by rw [map_mul, map_mul, h]))⟩ hT.1 hFT
  · rw [Nat.card_congr e.toEquiv, ← orderOf_zcU hp2 hF]
    exact orderOf_dvd_natCard _

omit [Finite G] in
theorem exists_hyp_equiv {L : Subgroup G} {F : Type} [Field F] (hF : Nat.card F = p ^ 2)
    (ψ : PSU3F p F ≃* ↥L) : Nonempty (↥L ≃* hypPSU (uniData hF) 1 1) := by
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) (uniData hF)
  exact ⟨ψ.symm.trans (hypPSUEquivStatedProj (uniData hF) hR (by norm_num)).symm⟩

end CFSG.Quasithin.Vol2.Ch11.SecU1.U3
