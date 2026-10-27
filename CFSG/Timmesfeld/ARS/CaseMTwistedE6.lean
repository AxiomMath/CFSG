module

public import CFSG.Timmesfeld.ARS.CaseMF4Levi

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
open CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Timmesfeld CFSG.LieType.CurtisTits Matrix
open CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem twistedE6Frame_of_aligned {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {f : ℕ} (hf : 1 ≤ f) (hcard : Nat.card A = 2 ^ f)
    (Φ : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →* G)
    (hker : Φ.ker ≤ Subgroup.center _) (hrange : Φ.range = levi R A A₀)
    (hP : ∀ i, ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
      (CaseM.longC3 i)).map Φ = P i)
    (hQ : ∀ i, ((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup
      (-CaseM.longC3 i)).map Φ = Q i)
    (hdr : ∀ a b : Fin 3, a ≠ b → ∀ γ : Fin 3 → ℤ,
      Symplectic.toStd 3 γ = Pi.single a 1 - Pi.single b 1 →
        Commuting (((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup γ).map
          Φ) E ∧
        Commuting (((Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup γ).map
          Φ) ⁅A₀, C⁆)
    (hIb : CaseM.TwistedE6C3LeviInput) (hIc : CaseM.TwistedE6EdgeLeviInput) :
    TwistedE6Frame G f ∧ NSLFrame G R := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  obtain ⟨hF, hEF, -⟩ := IsSubframe.isConfig hS hfr
  obtain ⟨ι, hιker, hιX⟩ := hIb f hf
  obtain ⟨l, hl, hl1, hl2, hl3, hl4, hl5, hl6, hm⟩ := hIc f hf
  choose! m hm' using hm
  obtain ⟨wU, HU, hctU⟩ := Unitary.exists_isCTGroupDatum (CaseM.card_galoisField_two_mul hf) 6
    (by norm_num)
  have hdivU : (Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).divisible = ∅ := by
    change Unitary.divisible 6 = ∅
    simp only [Unitary.divisible, show Even 6 from ⟨3, rfl⟩, ↓reduceIte]
  have hgenL := CaseM.iSup_rankOne_eq_top
    (D := Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6) hctU hdivU
  obtain ⟨-, -, -, hFlevi⟩ := CaseD4.commutator_props hS.hyp hA hS.opp hfr.memC
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hS.config (hfr.memP 2).1 (hfr.memQ 2).1 (hfr.opposite 2)
    hfr.memE (hfr.memQ 2).2.1.2.2.symm hF
    (hFlevi _ (hfr.memP 2).1 (hfr.memP 2).2.1.2.2.symm) hEF
  have htop : Φ.range ⊔ E ⊔ ⁅A₀, C⁆ = ⊤ := by
    rw [hrange]
    exact hS.levi_sup_eq_top hfr.memE hF
  obtain ⟨ψ, hψ, hgen, hnt, hrE, hrF⟩ := CaseM.exists_f4Frame_of_levis
    (Exceptional.twistedE6Datum 2 f).rootGroup
    (Unitary.rootDatum (CaseM.card_galoisField_two_mul hf) 6).rootGroup hR hiso hgenL ι hιX hl
    hl1 hl2 hl3 hl4 hl5 hl6 m hm' Φ hker
    (fun z hz => hS.map_center_eq_one Φ hrange (hιker hz)) hfr.memE.1.1.1 hF.1.1.1
    (hfr.memP 2).1.1.1 (hfr.memQ 2).1.1.1 (hfr.opposite 2) hEF d1 d2 d3 d4 d5 d6
    ((hR.card_eq (hfr.memP 2).1.1.1 hA).trans hcard) (hP 2) (hQ 2) hdr htop
  have hframe : IsCTFrame (Exceptional.twistedE6Datum 2 f) G ψ := by
    refine CaseM.isCTFrame_of_cover (D := Exceptional.twistedE6Datum 2 f)
      (fun t : Fin 4 => ![CaseM.c3PairRoots, CaseM.edge01Roots, CaseM.edge0Roots 2,
        CaseM.edge0Roots 3] t) hψ (fun i j => ?_) hgen hnt
    rcases CaseM.f4_pairRoots_subset i j with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  exact ⟨⟨ψ, hframe⟩, IsCTFrame.nslFrame_twistedE6 hf hframe (0 : Fin 4) Nat.zero_lt_two
    hfr.memE.1.1.1 hrE hrF hEF⟩

end Sec12

end CFSG.Timmesfeld.ARS
