module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreThree
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Cover
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.LocalAnalysis.SectionRank.CyclicCenter
public import CFSG.LocalAnalysis.SectionRank.SQTKTransport
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd
public import CFSG.RankThree.PartTwo.Census.Carrier.TitsCert
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTits
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Sporadic.Schreier.J1QT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UCK

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_eq_two_of_lieModel_PSL_three_of_mod_one {p f : ℕ}
    (h : LieModel X .PSL 3 p f) (hmod : p ^ f % 3 = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  letI := hKfield
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow f p hadm.1.pos
  have h3q : 3 ∣ p ^ f - 1 := by
    refine ⟨p ^ f / 3, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have h3K : 3 ∣ Nat.card K - 1 := by
    rwa [hK]
  have h3F : 3 ∣ Fintype.card K - 1 := by
    rwa [Nat.card_eq_fintype_card] at h3K
  haveI : ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  have hmain : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 3 K))) = 2 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pRank_statedSL_three (F := K) h3F
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) le_rfl
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact hmain

theorem pRank_three_eq_two_of_threeCover_PSL_three {p f : ℕ} {L : Type} [Group L] [Finite L]
    (h : ThreeCover (fun Y _ => LieModel Y .PSL 3 p f) L) (hmod : p ^ f % 3 = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 := by
  obtain ⟨hQ, hZcard, hmodel⟩ := h
  haveI : Group.IsPerfect L := ⟨hQ.1⟩
  have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hE, hcard⟩ :=
      CFSG.SectionRank.exists_elemAbelian_sq_of_dvd_card_center (L := L) (p := 3)
        (by norm_num) (by simpa [hZcard])
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE
      (by simpa [hcard])
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  letI := hKfield
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow f p hadm.1.pos
  have h3q : 3 ∣ p ^ f - 1 := by
    refine ⟨p ^ f / 3, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have h3K : 3 ∣ Nat.card K - 1 := by
    rwa [hK]
  have h3F : 3 ∣ Fintype.card K - 1 := by
    rwa [Nat.card_eq_fintype_card] at h3K
  have h4le : 4 ≤ Nat.card K := by
    rw [hK]
    have hq2 : 2 ≤ p ^ f := by
      calc 2 ≤ p := hadm.1.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hadm.1.pos hadm.2.1
    have hsubpos : 0 < p ^ f - 1 := by omega
    have h3le : 3 ≤ p ^ f - 1 := Nat.le_of_dvd hsubpos h3q
    omega
  haveI : ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  by_cases h5 : 5 ≤ Nat.card K
  ·
    let Q := StatedProj (StatedSL 3 K)
    let πL : L →* Q := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hπL : Function.Surjective πL :=
      e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))
    have hπLc : πL.ker ≤ Subgroup.center L := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      exact (QuotientGroup.eq_one_iff x).1
        ((map_eq_one_iff e e.injective).1 (by simpa [πL] using hx))
    let ρ : StatedSL 3 K →* Q :=
      QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K))
    have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
    have hρc : ρ.ker ≤ Subgroup.center (StatedSL 3 K) := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
    have hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSL 3 K),
        Function.Surjective π → π.ker ≤ Subgroup.center E →
          ∃ σ : StatedSL 3 K →* E, ∀ g, π (σ g) = g := by
      intro E _ _ π hπ hc
      have hπ' : Function.Surjective
          ((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K).toMonoidHom.comp π) :=
        (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K).surjective.comp hπ
      have hc' : ((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K).toMonoidHom.comp π).ker ≤
          Subgroup.center E := by
        intro x hx
        apply hc
        rw [MonoidHom.mem_ker] at hx ⊢
        exact (map_eq_one_iff _ (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K).injective).1 hx
      obtain ⟨σ, hσ⟩ :=
        CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central
          (m := 2) (by norm_num) h5 hπ' hc'
      refine ⟨σ.comp (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K).toMonoidHom, fun g => ?_⟩
      exact (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K).injective
        (by simpa using hσ ((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 K) g))
    obtain ⟨α, hα, -, -⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin
        (S := StatedSL 3 K) (X := L) (Q := Q) hsec hQ.1 πL hπL hπLc ρ hρ hρc
    have hD : Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) = 3 :=
      CFSG.LocalAnalysis.RankThreeUC.S15.ACore.card_scalars_statedSL_three_of_dvd h3K
    have hcardL : Nat.card L = 3 * Nat.card Q := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L), hZcard,
        Nat.card_congr e.toEquiv]
      ring
    have hcardS : Nat.card (StatedSL 3 K) = 3 * Nat.card Q := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
        ((StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)), hD]
      ring
    have hbij : Function.Bijective α :=
      hα.bijective_of_nat_card_le (by rw [hcardS, hcardL])
    let eL : StatedSL 3 K ≃* L := MulEquiv.ofBijective α hbij
    have hm3SL : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSL 3 K)) = 2 := by
      have hmain := CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pRank_statedSL_three
        (F := K) h3F (⊥ : Subgroup (StatedSL 3 K)) bot_le
      have qe : (StatedSL 3 K) ⧸ (⊥ : Subgroup (StatedSL 3 K)) ≃* StatedSL 3 K :=
        QuotientGroup.quotientBot
      rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) qe]
      exact hmain
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eL.symm]
    exact hm3SL
  ·
    have hK4 : Nat.card K = 4 := by omega
    have hPSLcard : Nat.card (StatedProj (StatedSL 3 K)) = 20160 := by
      have hc := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul
        (F := K)
      rw [hK4] at hc
      norm_num at hc
      omega
    let π : L →* StatedProj (StatedSL 3 K) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hπ : Function.Surjective π :=
      e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))
    have hker : π.ker = Subgroup.center L := by
      ext x
      constructor
      · intro hx
        have hx' : e ((QuotientGroup.mk' (Subgroup.center L)) x) = 1 := by
          simpa [π] using hx
        exact (QuotientGroup.eq_one_iff x).1 ((map_eq_one_iff e e.injective).1 hx')
      · intro hx
        have h1 : (QuotientGroup.mk' (Subgroup.center L)) x = 1 :=
          (QuotientGroup.eq_one_iff x).2 hx
        simpa [π, h1] using hx
    have hodd : Odd (Nat.card π.ker) := by
      rw [hker, hZcard]
      decide
    have h3S : ¬ 3 ^ 3 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
      rw [hPSLcard]
      norm_num
    have hrS : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 →
        ¬ r ^ 2 ∣ Nat.card (StatedProj (StatedSL 3 K)) := by
      intro r hr hr2 hr3 hdvd
      rw [hPSLcard] at hdvd
      have hle : r ^ 2 ≤ 20160 := Nat.le_of_dvd (by norm_num) hdvd
      have hrlt : r < 143 := by nlinarith [hr.two_le]
      exact (by decide +kernel :
        ∀ r < 143, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 2 ∣ 20160) r hrlt hr hr2 hr3 hdvd
    have hbound := CFSG.SectionRank.odd_cover_one_square_order_bound
      (E := L) (S := StatedProj (StatedSL 3 K)) Nat.prime_three (by norm_num)
      π hπ (by rw [hker]) hodd h3S hrS
    have hsq : CFSG.IsStronglyQuasithin (L ⧸ (⊥ : Subgroup L)) := hbound.2 ⊥ bot_le
    have hsqL : CFSG.IsStronglyQuasithin L :=
      CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv QuotientGroup.quotientBot.symm hsq
    exact le_antisymm
      ((CFSG.SectionRank.isStronglyQuasithin_iff.1 hsqL) 3 Nat.prime_three (by norm_num)) hlow

theorem pRank_three_eq_two_of_threeCover_PSU_three
    {p f : ℕ} {L : Type} [Group L] [Finite L]
    (h : ThreeCover (fun Y _ => LieModel Y .PSU 3 p f) L) (hmod : p ^ f % 3 = 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 := by
  obtain ⟨hQ, hZcard, hmodel⟩ := h
  obtain ⟨hadm, K, hKfield, hKfin, hK, ⟨e⟩⟩ := hmodel.statedClassicalModel (by decide)
  letI := hKfield
  letI := hKfin
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hadm.1⟩
  have hq2 : p ^ f ≠ 2 := by
    intro hq
    exact hadm.2.2.2 (by rw [hq])
  have hq3 : 3 ≤ p ^ f := by
    have h2 : 2 ≤ p ^ f := by
      calc 2 ≤ p := hadm.1.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ f := Nat.pow_le_pow_right hadm.1.pos hadm.2.1
    omega
  have h3q : 3 ∣ p ^ f + 1 := by
    refine ⟨p ^ f / 3 + 1, ?_⟩
    have hdm := Nat.div_add_mod (p ^ f) 3
    omega
  have hK' : Fintype.card K = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hchar : CharP K p := by
    have hcard : Fintype.card K = p ^ (2 * f) := by
      rw [hK', ← pow_mul, Nat.mul_comm]
    exact charP_of_card_eq_prime_pow hcard
  letI := hchar
  haveI : ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  have hD : Nat.card
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)) = 3 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel (p := p) (f := f) (K := K) hadm.1 hK
      (n := 3) (by norm_num)).2.2]
    exact Nat.gcd_eq_left h3q
  let Q := StatedProj (StatedSU 3 (p ^ f) K)
  let πL : L →* Q := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπL : Function.Surjective πL :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center L))
  have hπLc : πL.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff x).1
      ((map_eq_one_iff e e.injective).1 (by simpa [πL] using hx))
  let ρ : StatedSU 3 (p ^ f) K →* Q :=
    QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K))
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hρc : ρ.ker ≤ Subgroup.center (StatedSU 3 (p ^ f) K) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _
  have hsec : ∀ (E : Type) [Group E] [Finite E] (π : E →* StatedSU 3 (p ^ f) K),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : StatedSU 3 (p ^ f) K →* E, ∀ g, π (σ g) = g := by
    intro E _ _ π hπ hc
    exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central
      (p := p) (f := f) (F := K) (n := 3) hK hadm.2.1 (by norm_num) (by decide)
      hadm.2.2.2 hπ hc
  obtain ⟨α, hα, -, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22pwlie_exists_cover_of_closed_fin
      (S := StatedSU 3 (p ^ f) K) (X := L) (Q := Q) hsec hQ.1 πL hπL hπLc ρ hρ hρc
  have hcardL : Nat.card L = 3 * Nat.card Q := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L), hZcard,
      Nat.card_congr e.toEquiv]
    ring
  have hcardS : Nat.card (StatedSU 3 (p ^ f) K) = 3 * Nat.card Q := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (p ^ f) K)), hD]
    ring
  have hbij : Function.Bijective α :=
    hα.bijective_of_nat_card_le (by rw [hcardS, hcardL])
  let eL : StatedSU 3 (p ^ f) K ≃* L := MulEquiv.ofBijective α hbij
  have hm3SU : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 (p ^ f) K)) = 2 := by
    have hmain := CFSG.LocalAnalysis.RankThreeUC.S15.ACore.pRank_statedSU_three
      (F := K) (q := p ^ f) hK' hq3 h3q (⊥ : Subgroup (StatedSU 3 (p ^ f) K)) bot_le
    have qe : (StatedSU 3 (p ^ f) K) ⧸ (⊥ : Subgroup (StatedSU 3 (p ^ f) K)) ≃*
        StatedSU 3 (p ^ f) K := QuotientGroup.quotientBot
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) qe]
    exact hmain
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eL.symm]
  exact hm3SU

theorem pRank_three_eq_two_of_lieModel_Tits
    (h : LieModel X .Tits 0 2 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  have hTits : ReeTitsModel X .Tits 2 1 := (h.reeTitsModel (by decide)).2
  have hlow : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_of_titsModel hTits
  have hupper : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 := by
    obtain ⟨K, hKfield, hKfin, hKchar, hK2, ⟨e⟩⟩ :=
      CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hTits
    letI := hKfield
    letI := hKfin
    letI := hKchar
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    have hΓ : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.LieType.Ree.reeFixed
        CFSG.LieType.Ree.ReeTag.F4 K 0)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3
          (⊤ : Subgroup (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)),
        CFSG.SectionRank.pRank_coe_eq_assemblyPRank 3
          (⊤ : Subgroup (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0))]
      exact CFSG.RankThree.PartTwo.Census.Carrier.Tits.pRank_three_reeFixed hK2
    exact (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
      (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)).subtype
      (commutator (CFSG.LieType.Ree.reeFixed CFSG.LieType.Ree.ReeTag.F4 K 0)).subtype_injective).trans
      hΓ
  exact le_antisymm hupper hlow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
