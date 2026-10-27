module

public import CFSG.Timmesfeld.ARS.CaseMF4Levi
public import CFSG.Timmesfeld.ARS.CaseMSpLevi

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
open CFSG.LieType.RootSystem CFSG.Blueprint CFSG.Timmesfeld CFSG.LieType.CurtisTits Matrix
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem f4Frame_of_sp {f : ℕ} (hf : 1 ≤ f) (hcard : Nat.card A = 2 ^ f)
    (Φ : StatedSp 3 (GaloisField 2 f) →* G) (hΦ : Function.Injective Φ)
    (hrange : Φ.range = levi R A A₀)
    (hΔ : ∀ X : Subgroup G, X ∈ leviSet R A A₀ ↔
      ∃ g, X = (conjSub (Symplectic.rootGroup 3 (GaloisField 2 f) (Pi.single 2 1)) g).map Φ)
    (hIa : CaseM.F4C3LeviInput) (hIc : CaseM.F4EdgeLeviInput) :
    F4Frame G f ∧ NSLFrame G R := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  obtain ⟨E, C, P, Q, hfr⟩ := hS.exists_isSubframe
  obtain ⟨hF, hEF, -⟩ := IsSubframe.isConfig hS hfr
  obtain ⟨Φ', hΦ', hrange', hΔ', hP, hQ⟩ := hS.exists_aligned_sp_dict hfr Φ hΦ hrange hΔ
  obtain ⟨ι, hι, hιX⟩ := hIa f hf
  obtain ⟨l, hl, hl1, hl2, hl3, hl4, hl5, hl6, hm⟩ := hIc f hf
  choose! m hm' using hm
  have hgenL := CaseM.iSup_rankOne_eq_top (D := Symplectic.rootDatum 3 (GaloisField 2 f))
    (Symplectic.isCTGroupDatum 3 (GaloisField 2 f)) rfl
  obtain ⟨-, -, -, hFlevi⟩ := CaseD4.commutator_props hS.hyp hA hS.opp hfr.memC
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hS.config (hfr.memP 2).1 (hfr.memQ 2).1 (hfr.opposite 2)
    hfr.memE (hfr.memQ 2).2.1.2.2.symm hF
    (hFlevi _ (hfr.memP 2).1 (hfr.memP 2).2.1.2.2.symm) hEF
  have htop : Φ'.range ⊔ E ⊔ ⁅A₀, C⁆ = ⊤ := by
    rw [hrange']
    exact hS.levi_sup_eq_top hfr.memE hF
  obtain ⟨ψ, hψ, hgen, hnt, hrE, hrF⟩ := CaseM.exists_f4Frame_of_levis
    (Adjoint.f4Datum (GaloisField 2 f)).rootGroup
    (Symplectic.rootDatum 3 (GaloisField 2 f)).rootGroup hR hiso hgenL ι hιX hl
    hl1 hl2 hl3 hl4 hl5 hl6 m hm' Φ'
    (by rw [(MonoidHom.ker_eq_bot_iff Φ').2 hΦ']; exact bot_le)
    (by rw [(MonoidHom.ker_eq_bot_iff ι).2 hι]; exact bot_le) hfr.memE.1.1.1 hF.1.1.1
    (hfr.memP 2).1.1.1 (hfr.memQ 2).1.1.1 (hfr.opposite 2) hEF d1 d2 d3 d4 d5 d6
    ((hR.card_eq (hfr.memP 2).1.1.1 hA).trans hcard) (hP 2) (hQ 2)
    (fun a b hab γ hγ => hS.commuting_diffRoot_sp hfr Φ' hΦ' hrange' hΔ' hP hQ hab hγ) htop
  have hframe : IsCTFrame (Adjoint.f4Datum (GaloisField 2 f)) G ψ := by
    refine CaseM.isCTFrame_of_cover (D := Adjoint.f4Datum (GaloisField 2 f))
      (fun t : Fin 4 => ![CaseM.c3PairRoots, CaseM.edge01Roots, CaseM.edge0Roots 2,
        CaseM.edge0Roots 3] t) hψ (fun i j => ?_) hgen hnt
    rcases CaseM.f4_pairRoots_subset i j with h | h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
  exact ⟨⟨ψ, hframe⟩, IsCTFrame.nslFrame_f4 hf hframe (0 : Fin 4) Nat.zero_lt_two
    hfr.memE.1.1.1 hrE hrF hEF⟩

end Sec12

end CFSG.Timmesfeld.ARS
