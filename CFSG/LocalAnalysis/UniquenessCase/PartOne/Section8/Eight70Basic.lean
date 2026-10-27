module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAltTenDef
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight69Setup
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem eight70_perfect {D : Data G} {L X H : Subgroup G} (hc : MinCex869 D L X H) :
    ⁅X, X⁆ = X := by
  obtain ⟨hcase, hXL, hXsup, hthin⟩ := hc.hyp
  have hLperf : ⁅L, L⁆ = L := by
    rcases hcase with hLC | ⟨-, -, hprod⟩
    · exact hLC.2.1
    · exact CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.perfect_of_isProdOfCalC hprod
  refine commutator_eq_self_of_minimal_supplement L X hLperf hXsup ?_
  intro X₀ hX₀ hX₀sup
  have hHyp : Hyp869 D L X₀ := ⟨hcase, hX₀.le.trans hXL, hX₀sup, hthin⟩
  have hcard : Nat.card X₀ < Nat.card X := Subgroup.card_lt_of_lt hX₀
  have hcal : UC22.calNOf X₀ = {D.M} := hc.minimal L X₀ hHyp hcard
  have hHmem : H ∈ UC22.calNOf X₀ := ⟨hc.mem.1, hX₀.le.trans hc.mem.2⟩
  rw [hcal] at hHmem
  exact hc.ne (by simpa using hHmem)

theorem eight70_config {D : Data G} {L X H : Subgroup G} (hc : MinCex869 D L X H) :
    H ≠ ⊤ ∧ ¬ H ≤ D.M ∧ X ≤ H ⊓ D.M := by
  obtain ⟨hcase, hXL, -, -⟩ := hc.hyp
  have hHtop : H ≠ ⊤ := hc.mem.1.ne_top
  have hHM : ¬ H ≤ D.M := by
    intro hle
    rcases (hc.mem.1.le_iff).mp hle with htop | heq
    · exact CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p20a_M_ne_top D htop
    · exact hc.ne heq.symm
  have hXD : X ≤ D.M := by
    rcases hcase with hLC | ⟨hLM, -, -⟩
    · exact hXL.trans (CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22a_le_of_isSubnormal hLC.1)
    · exact hXL.trans hLM
  exact ⟨hHtop, hHM, le_inf hc.mem.2 hXD⟩

theorem eight70_kconfig (k : Section7.Sec7Core4 G) {D : Data G} {L X H : Subgroup G}
    (hc : MinCex869 D L X H) (hkM : k.M = D.M) (h2 : 1 < CFSG.Open.pRank k.p X) :
    k.Config H := by
  have hconf := eight70_config hc
  refine ⟨hconf.1, ?_, ?_⟩
  · rw [hkM]
    exact hconf.2.1
  · have hXle : X ≤ H ⊓ k.M := by
      simpa [hkM] using hconf.2.2
    have hmono := CFSG.SectionRank.pRank_mono k.prime.one_lt hXle
    omega

omit [Finite G] in
theorem eight70_map_le_and_perfect {p : ℕ} {M H X : Subgroup G} (hXHM : X ≤ H ⊓ M)
    (hX : ⁅X, X⁆ = X) :
    (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ≤
        ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ∧
      ⁅(X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)),
        (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))⁆ =
        (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := by
  constructor
  · exact Subgroup.map_mono (Subgroup.comap_mono hXHM)
  · have hperf : ⁅X.subgroupOf H, X.subgroupOf H⁆ = X.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (hXHM.trans inf_le_left),
        hX]
    have hmap := Subgroup.map_commutator (H₁ := X.subgroupOf H) (H₂ := X.subgroupOf H)
      (f := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    rw [hperf] at hmap
    exact hmap.symm

theorem eight70_not_isSolvable {p : ℕ} (hp : p.Prime) {M H X : Subgroup G} (hXHM : X ≤ H ⊓ M)
    (hX : ⁅X, X⁆ = X) (h1 : 1 ≤ CFSG.Open.pRank p X) :
    ¬ IsSolvable ↥(((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := by
  intro hsol
  have hfact : Fact p.Prime := ⟨hp⟩
  let K : Subgroup ↥H := CFSG.pPrimeCore p ↥H
  let π : ↥H →* (↥H ⧸ K) := QuotientGroup.mk' K
  have hperf := eight70_map_le_and_perfect (p := p) hXHM hX
  let Xbar : Subgroup (↥H ⧸ K) := (X.subgroupOf H).map π
  let Nbar : Subgroup (↥H ⧸ K) := ((H ⊓ M).subgroupOf H).map π
  have hXbar_le : Xbar ≤ Nbar := hperf.1
  have hXbar_perf : ⁅Xbar, Xbar⁆ = Xbar := hperf.2
  have hsolN : Group.IsSolvable ↥Nbar := hsol
  have hsX : Group.IsSolvable ↥Xbar :=
    @Group.isSolvable_of_isSolvable_injective ↥Xbar ↥Nbar _ _
      (Subgroup.inclusion hXbar_le) (Subgroup.inclusion_injective hXbar_le) hsolN
  have hbot : Xbar = ⊥ := by
    have hcore := CFSG.Quasithin.perfectCore_eq_self_of_perfect hXbar_perf
    have hsol0 := (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot Xbar).1 hsX
    rw [hcore] at hsol0
    exact hsol0
  have hXsub_le_K : X.subgroupOf H ≤ K := by
    have hmapbot : (X.subgroupOf H).map π = ⊥ := hbot
    have hle := (Subgroup.map_eq_bot_iff (f := π) (X.subgroupOf H)).1 hmapbot
    rwa [QuotientGroup.ker_mk'] at hle
  have hcardX : Nat.card (X.subgroupOf H) = Nat.card X := by
    rw [← Subgroup.card_map_of_injective (K := X.subgroupOf H) H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le (hXHM.trans inf_le_left)]
  have hdvd : Nat.card X ∣ Nat.card K := by
    rw [← hcardX]
    exact Subgroup.card_dvd_of_le hXsub_le_K
  have hcop : Nat.Coprime p (Nat.card K) :=
    @CFSG.pPrimeCore_coprime_card p ↥H _ _ hfact
  have hcopX : Nat.Coprime p (Nat.card X) := hcop.coprime_dvd_right hdvd
  obtain ⟨E, hEX, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt X
  have hpE : p ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self p (by omega)
  have hpX : p ∣ Nat.card X := hpE.trans (Subgroup.card_dvd_of_le hEX)
  exact (hp.coprime_iff_not_dvd).1 hcopX hpX

theorem eight70_three (hK3 : Section7.StronglyEmbeddedThree) {D : Data G}
    (hcore : Sec7CoreOdd D) {L X H : Subgroup G} (hc : MinCex869 D L X H)
    (h3 : 1 < CFSG.Open.pRank 3 X) : ¬ IsStronglyPEmbedded 3 D.M := by
  intro hsp
  obtain ⟨k, hkM, hkp, -⟩ := hcore 3 Nat.prime_three (by norm_num) hsp
  have h2 : 1 < CFSG.Open.pRank k.p X := by
    rw [hkp]
    exact h3
  have hH : k.Config H := eight70_kconfig k hc hkM h2
  have hsol : IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) :=
    (k.kInputThree hkp hK3 hH).2.2.2
  have hXHM : X ≤ H ⊓ k.M := by
    simpa [hkM] using (eight70_config hc).2.2
  refine eight70_not_isSolvable k.prime hXHM (eight70_perfect hc) ?_ hsol
  rw [hkp]
  omega

theorem eight70_solvable_or_altTen (k : Section7.Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : k.KIDExcluded) {H : Subgroup G} (hH : k.Config H) (h75 : k.Step75)
    (hS : Section7.StronglyEmbeddedSolvableAltTen) :
    IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∨
      (k.p = 5 ∧
        Nonempty (↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≃*
          alternatingGroup (Fin 10)) ∧
        ∀ Y : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H),
          Y ≤ ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) →
          ⁅Y, Y⁆ = Y → Y ≤ CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ∧
            ∃ f : ↥Y →* alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
              Function.Injective f) := by
  have hp : k.p.Prime := k.prime
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  exact hS k.p hp h5 _
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore k.p ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot hp) (k.two_le_pRank_quotient_pPrimeCore hH) _
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) (hno H hH h75)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
