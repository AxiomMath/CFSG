module

public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrLangRegStepZero
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTorARank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcOutdiag
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem card_J_dvd_of_ggResHyp
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    {labJ : LargeEvenLabel} (hlabJ : LargeEvenInLambda2 labJ)
    (hHas : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (htag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpN : p ∣ labJ.rank + 3) :
    p ∣ Nat.card J := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hpd : ¬ p ∣ labJ.rank + 1 := by
    intro hd
    have hdiff : p ∣ (labJ.rank + 3) - (labJ.rank + 1) :=
      Nat.dvd_sub hpN hd
    have hsub : (labJ.rank + 3) - (labJ.rank + 1) = 2 := by omega
    have h2 : p ∣ 2 := by rwa [hsub] at hdiff
    have hp_eq_two : p = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
      · exact absurd h1 hp.ne_one
      · exact h2'
    exact hp2 hp_eq_two
  have houtAll : LargeEvenLabelAll labJ (fun R _ I _ => GGOutdiagPrime p R I) := by
    rcases htag with hA | htw
    · exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_outdiagPrime_linear
        hp hlabJ hA hpd
    · exact CFSG.LocalAnalysis.GLTheoremA.K155X.l154_outdiagPrime_twA
        hp hlabJ htw (fun h => hpd h.1)
  have hpcAll : LargeEvenLabelAll labJ (GGRawPCyclic p) :=
    ggRawPCyclicOn_typeA p hp hp2 labJ hlabJ htag
  have hpcOutAll : LargeEvenLabelAll labJ
      (fun R _ I F => GGRawPCyclic p R I F ∧ GGOutdiagPrime p R I) :=
    largeEvenLabelAll_and hpcAll houtAll
  have hpre : LargeEvenStdSubPre p B x L D J := hH.1.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hpre.2.2.2.2.2.1
  have hJperf : commutator ↥J = ⊤ := hJcomp.2.2.1
  have hJZsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := hJcomp.2.2.2
  have hJZnab : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a :=
    exists_mul_ne_mul_centerQuot_of_perfect hJperf hJZsimple.toNontrivial
  have hraw0 : LargeEvenRawDatum labJ
      (fun R _ _ _ => Nonempty (J ⧸ Subgroup.center J ≃* R)) := hHas
  have hraw1 := hpcOutAll _ hraw0
  obtain ⟨R, hRgrp, I, F, hθ, hPC, hOut⟩ := largeEvenRawDatum_exists hraw1
  let : Group R := hRgrp
  obtain ⟨θ⟩ := hθ
  have hsimpleR : IsSimpleGroup R := (MulEquiv.isSimpleGroup_congr θ).mp hJZsimple
  have hnaR : ∃ a b : R, a * b ≠ b * a := nonabelian_of_mulEquiv θ hJZnab
  let ρ : ↥Bs →* MulAut R := (ggInducedAut θ).comp (ggGamma J hN)
  have hInj : Function.Injective (ggInducedAut θ) :=
    ggInducedAut_injective_of_perfect hJperf θ
  have hρrange_card : Nat.card ρ.range = Nat.card (ggGamma J hN).range := by
    dsimp only [ρ]
    rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hInj]
  have hρrange_ge : p ^ 2 ≤ Nat.card ρ.range := by
    have h := GGResHyp.sq_le_card_gamma_J hH
    rwa [hρrange_card]
  by_contra hpJ
  have hpRnot : ¬ p ∣ Nat.card R := by
    intro hpR
    apply hpJ
    have hpQ : p ∣ Nat.card (J ⧸ Subgroup.center J) := by
      rwa [Nat.card_congr θ.toEquiv]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center J)]
    exact dvd_mul_of_dvd_left hpQ _
  have hBp : ∀ b : ↥Bs, b ^ p = 1 := fun b =>
    Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hρpow : ∀ b : ↥Bs, ρ b ^ p = 1 := fun b => by
    rw [← map_pow, hBp b, map_one]
  have hρI_one : ∀ b : ↥Bs, ρ b ∈ I → ρ b = 1 := by
    intro b hbI
    obtain ⟨r, hr⟩ := hOut (ρ b) hbI (hρpow b)
    have hrp : r ^ p = 1 := by
      have h1 : MulAut.conj (r ^ p) = 1 := by
        rw [map_pow, hr, hρpow b]
      have hcent : r ^ p ∈ Subgroup.center R := by
        rw [Subgroup.mem_center_iff]
        intro x
        have hx := congrArg (fun φ : MulAut R => φ x) h1
        rw [MulAut.conj_apply, MulAut.one_apply] at hx
        calc x * r ^ p = (r ^ p * x * (r ^ p)⁻¹) * r ^ p := by rw [hx]
          _ = r ^ p * x := by group
      have hZR : Subgroup.center R = ⊥ :=
        CFSG.LocalAnalysis.ComponentInitial.center_eq_bot_of_isSimpleGroup hnaR
      rwa [hZR, Subgroup.mem_bot] at hcent
    have hord : orderOf r ∣ p := orderOf_dvd_of_pow_eq_one hrp
    rcases (Nat.dvd_prime hp).mp hord with h1 | hp_eq
    · have hr1 : r = 1 := orderOf_eq_one_iff.mp h1
      rw [hr1, map_one] at hr
      exact hr.symm
    · exact absurd (hp_eq ▸ orderOf_dvd_natCard r) hpRnot
  have hρrange_gt_one : 1 < Nat.card ρ.range := by
    have hp2gt : 1 < p ^ 2 := by nlinarith [hp.two_le]
    exact lt_of_lt_of_le hp2gt hρrange_ge
  have hρrange_ne_bot : ρ.range ≠ ⊥ := by
    intro hbot
    rw [hbot] at hρrange_gt_one
    simp at hρrange_gt_one
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hρrange_ne_bot
  obtain ⟨b₀, hb₀x⟩ := MonoidHom.mem_range.mp x.2
  have hb₀I : ρ b₀ ∉ I := by
    intro hbI
    apply hx1
    apply Subtype.ext
    show (x : MulAut R) = 1
    rw [← hb₀x]
    exact hρI_one b₀ hbI
  let b₀G : G := (b₀ : Bs).1
  have hb₀G : b₀G ∈ Bs := (b₀ : Bs).2
  have hb₀GI : ρ ⟨b₀G, hb₀G⟩ ∉ I := by simpa [b₀G] using hb₀I
  obtain ⟨B₀, hB₀, hB₀card, -, hmem⟩ :=
    exists_index_prime_of_raw_pcyclic hp hBs hsimpleR hnaR hPC ρ hb₀G hb₀GI
  let B₀' : Subgroup ↥Bs := B₀.subgroupOf Bs
  have hB₀'card : Nat.card B₀' = Nat.card B₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀).toEquiv
  have hB₀'ker : B₀' ≤ ρ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    have hbG : (b : G) ∈ B₀ := (Subgroup.mem_subgroupOf).mp hb
    have hbI : ρ ⟨b, hB₀ hbG⟩ ∈ I := (hmem b (hB₀ hbG)).1 hbG
    exact hρI_one ⟨b, hB₀ hbG⟩ hbI
  have hrange_le_p : Nat.card ρ.range ≤ p := by
    have hcard_ker := Subgroup.card_ker_mul_card_range ρ
    have hcard_B₀_le : Nat.card B₀' ≤ Nat.card ρ.ker := Subgroup.card_le_of_le hB₀'ker
    have h1 : Nat.card B₀' * Nat.card ρ.range ≤ Nat.card B₀' * p := by
      calc
        Nat.card B₀' * Nat.card ρ.range ≤ Nat.card ρ.ker * Nat.card ρ.range :=
          Nat.mul_le_mul_right _ hcard_B₀_le
        _ = Nat.card Bs := hcard_ker
        _ = Nat.card B₀ * p := hB₀card.symm
        _ = Nat.card B₀' * p := by rw [hB₀'card]
    exact Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  have : p ^ 2 ≤ p := le_trans hρrange_ge hrange_le_p
  nlinarith [hp.two_le]

end CFSG.StandardType

end
