module

public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Final
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPSL
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeOrthBlockModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.ClassicalGroups.UnitaryFlag

private theorem ggSudRow_div_add_two_le_max_sub_three {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : 3 ≤ d) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    d / p + 2 ≤ max (d - 3) 3 := by
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  obtain ⟨k, rfl⟩ := hpd
  rw [Nat.mul_div_cancel_left k hp.pos]
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k <;> simp_all
  · rcases Nat.lt_or_ge p 4 with hp4 | hp4
    · have : p = 3 := by omega
      subst this
      have : k ≠ 2 := fun h => hnd ⟨by omega, rfl⟩
      omega
    · have : 4 * k ≤ p * k := Nat.mul_le_mul_right k hp4
      omega

theorem ggSudRow_labelAll
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hq : GGLabQFour p lab) (h : GGTBRowR5Ud p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (d n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
        (e : R ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))),
        GGTorusLift p (d - 3) R ∧ 5 ≤ d ∧ 2 ≤ n ∧ p ∣ d ∧ p ∣ 2 ^ n + 1 ∧
          Nat.card K = (2 ^ n) ^ 2 ∧
          MulAut.congr e '' I ⊆ LargeEvenMatConjImage
            (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
            (LargeEvenGUSet (Fin d) K (2 ^ n)) := by
  obtain ⟨t, r, f⟩ := lab
  intro Q hQ
  obtain ⟨htag, hr3, hpd, hpq⟩ := h
  unfold GGLabQFour at hq
  dsimp only at hq htag hr3 hpd hpq
  subst htag
  obtain ⟨K, hF, hFin, hK, hQ'⟩ := hQ
  letI := hF
  haveI := hFin
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 hpq
  have hd5 : 5 ≤ r + 1 := by
    by_contra hlt
    have h4 : r + 1 = 4 := by omega
    have hp4 : p ∣ 4 := h4 ▸ hpd
    have hp2' : p ∣ 2 := hp.dvd_of_dvd_pow (m := 2) (n := 2) (by simpa using hp4)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp2')
  have hdq : (r + 1, 2 ^ f) ≠ (3, 2) := by
    intro h32
    have h1 : r + 1 = 3 := congrArg Prod.fst h32
    omega
  have hlift : GGTorusLift p (ggUnitaryTorusRank p (r + 1))
      (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ f))) :=
    ggTorusLift_unitary hK (by omega) (by omega) hdq hp hpq
  have hrank : ggUnitaryTorusRank p (r + 1) = r + 1 - 3 := by
    rw [ggUnitaryTorusRank, if_pos hpd]
  refine ⟨K, hF, hFin, hK, hQ', ?_⟩
  refine ⟨r + 1, f, K, hF, hFin, MulEquiv.refl _, ?_, hd5, hq, hpd, hpq, hK, ?_⟩
  · rw [← hrank]
    exact hlift
  · rintro _ ⟨φ, hφ, rfl⟩
    have hc : MulAut.congr (MulEquiv.refl
        (LargeEvenProj (LargeEvenSUGroup (Fin (r + 1)) K (2 ^ f)))) φ = φ := by
      ext x
      rfl
    rwa [hc]

theorem ggSudRow_tbGroup
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hHyp : GGCorFiveTwentyHyp p B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab) p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (d n : ℕ) (K : Type) (_ : Field K) (_ : Finite K)
      (ψ : ↥L →* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (I : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))),
      5 ≤ d ∧ 2 ≤ n ∧ p ∣ d ∧ p ∣ 2 ^ n + 1 ∧ Nat.card K = (2 ^ n) ^ 2 ∧
        I ⊆ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
          (LargeEvenGUSet (Fin d) K (2 ^ n)) ∧
        GGTorusTBGroup p (d - 3) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) I ↥L ψ
          (ggGamma L hN).range ∧
        p ^ (d / p + 2) ≤ Nat.card (ggGamma L hN).range := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => GGLabQFour p lab ∧ GGTBRowR5Ud p lab)
    (fun lab hlab hs => nbrC_labelAll_guard (ggSudRow_labelAll hp hlab hs.1 hs.2))
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, d, n, K, hKF, hKfin, e, hlift, hd, hn, hpd, hpq,
    hK, hI⟩ := largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3
  have hTB' := GGTorusTBGroup.mulEquiv (I' := MulAut.congr e '' I) e
    (fun φ hφ => ⟨φ, hφ, rfl⟩) hTB
  have hcard : p ^ (d / p + 2) ≤ Nat.card (ggGamma L hN).range := by
    by_cases h63 : d = 6 ∧ p = 3
    · obtain ⟨rfl, rfl⟩ := h63
      have hBI : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (unitarySU 2 n K 6)) (LargeEvenGUSet (Fin 6) K (2 ^ n)),
          LargeEvenInduces (θ.trans e) (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
        intro b hb
        obtain ⟨φ, hφ, hφi⟩ := h3I b hb
        exact ⟨MulAut.congr e φ, hI ⟨φ, hφ, rfl⟩,
          CFSG.LocalAnalysis.GLTheoremA.T171Sh.largeEvenInduces_trans e hφi⟩
      have h3Bs : 3 ^ 5 ≤ Nat.card Bs :=
        Line63.H5.three_pow_five_le_card_of_marking hcfg hK hn hpq hXc (θ.trans e) hBsN hBI
      have hBs_eq : Nat.card (ggGamma L hBsN).range *
          Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = Nat.card Bs :=
        NbrU63.card_range_ggGamma_mul_card_inf hBsN
      have hinf : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 3 :=
        hcfg.card_bstar_inf_centralizer_L
      have h1 : 3 ^ 5 ≤ Nat.card (ggGamma L hN).range * 3 := by
        calc 3 ^ 5 ≤ Nat.card Bs := h3Bs
          _ = Nat.card (ggGamma L hBsN).range *
                Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hBs_eq.symm
          _ = Nat.card (ggGamma L hN).range * 3 := by rw [hinf]
      have h1' : 3 ^ 5 = 3 ^ 4 * 3 := by norm_num
      rw [h1'] at h1
      have hAcard : 3 ^ 4 ≤ Nat.card (ggGamma L hN).range :=
        Nat.le_of_mul_le_mul_right h1 (by norm_num)
      simpa using hAcard
    · have hdp : d / p + 2 ≤ max (d - 3) 3 :=
        ggSudRow_div_add_two_le_max_sub_three hp hp2 (by omega) hpd h63
      rcases le_max_iff.mp hdp with h | h
      · exact (Nat.pow_le_pow_right hp.pos h).trans hr
      · exact (Nat.pow_le_pow_right hp.pos h).trans h3
  exact ⟨d, n, K, hKF, hKfin, e.toMonoidHom.comp (ggQuotHom θ), MulAut.congr e '' I, hd, hn,
    hpd, hpq, hK, hI, hTB', hcard⟩

end CFSG.StandardType

end
