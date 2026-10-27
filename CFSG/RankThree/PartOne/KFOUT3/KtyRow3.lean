module

public import CFSG.RankThree.PartOne.KFOUT3.KtyDih
public import CFSG.RankThree.PartOne.KFOUT3.KtyRoot
public import CFSG.RankThree.PartOne.KFOUT3.KtyRows
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyDihCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import CFSG.RankThree.PartOne.KFOUT3.KtyG2Act
public import CFSG.RankThree.PartOne.KFOUT3.KtyD4Ctx
public import CFSG.RankThree.PartOne.KLAY.Frames
public import CFSG.RankThree.PartOne.KF.R3Final
public import CFSG.RankThree.PartOne.KF.R11Final

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N1322 CFSG.RankThree.PartOne.KLAY CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem kf1322KtyRow3_of_layers
    (hlayers : ∀ (p f : ℕ) (K : Type) [Field K] (σ : K →+* K) (hP : D4Param p f K σ),
      (∀ v : G2V p K, v ≠ 1 → g2s0 p K v = v →
        RootLayer ↥(graphFixedRootGroup TwistTag.D4 K σ) p (tp3M hP v)
          (2 ^ f * ((2 ^ f) ^ 2 - 1))) ∧
      (∀ v : G2V p K, v ≠ 1 → g2s1 p K v = v →
        RootLayer ↥(graphFixedRootGroup TwistTag.D4 K σ) p (tp3M hP v)
          ((2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1)))) :
    KF1322KtyRow 3 := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hmodel t ht s hs hts g hg
  rcases hF12.two with hG | hS
  · have hp := h12.prime
    have h5 := Sec12Three.five_le h12
    obtain ⟨hFexp, hFcomm, hmax⟩ := F_facts h12 hG
    have hcore := table_core_of h12 hG
    obtain ⟨f, K, hKf, hKfin, σ, hP, hζ, ε, hε, hFT₁, hFT₂⟩ := exists_r3frame hcore hmodel
    obtain ⟨SM, hSM⟩ := exists_wctx_d4' hP (d4tau p K) (fun a b => tp3Hom_d4tau a b)
    have hVexp : ∀ d : G2V p K, d ^ p = 1 := fun d =>
      funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
    obtain ⟨S₁, hrel₁⟩ := wctx_ofCentralQuot' hVexp SM (d4Q hP) (isCentralPQuot_d4Q hP) ε hε
      (inf_le_right : E ⊓ L ≤ L) hFexp hFT₁ hFT₂
    have hmem : ∀ γ : DihedralGroup 6, g2Act (K := K) hp h5 γ ∈
        Subgroup.closure (Set.range (d4tau p K)) := by
      intro γ
      rw [range_d4tau]
      exact pairAct_mem_closure g2s0_mul_self g2s1_mul_self (g2_braid hp h5) γ
    let f₁ : DihedralGroup 6 →* ↥(Subgroup.closure (Set.range (d4tau p K))) :=
      (g2Act (K := K) hp h5).codRestrict _ hmem
    have hf₁ : Function.Surjective f₁ := by
      rintro ⟨x, hx⟩
      rw [range_d4tau] at hx
      obtain ⟨γ, hγ⟩ := exists_pairAct_of_mem_closure (by decide) g2s0_mul_self g2s1_mul_self
        (g2_braid hp h5) hx
      exact ⟨γ, Subtype.ext hγ⟩
    let S := wctxPull (act := g2Act (K := K) hp h5) f₁ hf₁ (fun γ => rfl) S₁
    let Temb : G2V p K →* DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ) :=
      (d4Q hP).comp (tp3M hP)
    have hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = Temb d := by
      intro d
      show ε (Subgroup.inclusion inf_le_right (S₁.tor d)) = Temb d
      rw [hrel₁ d, hSM d]
      rfl
    have Hconj : ∀ γ : DihedralGroup 6,
        ∃ m : DerivedCentralQuotient (twistedFixedGroup TwistTag.D4 K σ),
          ∀ v, m * Temb v * m⁻¹ = Temb (g2Act (K := K) hp h5 γ v) := by
      intro γ
      obtain ⟨m, hm⟩ := conj_of_wctx SM (tp3M hP) hSM (d4Q hP) (f₁ γ)
      exact ⟨m, fun v => hm v⟩
    obtain ⟨hl0, hl1⟩ := hlayers p f K σ hP
    have hu : ∀ v : G2V p K, (tp3M hP v) ^ p = 1 := fun v => by
      rw [← map_pow, hVexp, map_one]
    have hq := isCentralPQuot_d4Q hP
    have hq2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hP.one_le
    have hnd := row3_not_dvd hq2
    have Hsmall : ∀ v : G2V p K, v ≠ 1 → g2Act (K := K) hp h5 (DihedralGroup.sr 0) v = v →
        SmallAt (Temb v) (· = (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1)) := by
      intro v hv1 hfix
      rw [g2Act_sr_zero] at hfix
      exact smallAt_of_rootLayer hq (hu v) (hl0 v hv1 hfix) hnd
    have Hbig : ∀ v : G2V p K, v ≠ 1 → g2Act (K := K) hp h5 (DihedralGroup.sr 1) v = v →
        BigAt p (Temb v) (· = (2 ^ f) ^ 3 * (((2 ^ f) ^ 3) ^ 2 - 1)) := by
      intro v hv1 hfix
      rw [g2Act_sr_one] at hfix
      exact bigAt_of_rootLayer hp hq (hu v) (hl1 v hv1 hfix)
    exact kty_of_dih (n := 6) (by norm_num) h12 hG hEA hF13 (g2Act_injective hp h5 hζ)
      (g2Act_refl hp h5 hζ) hε Temb S hrel Hconj Hsmall Hbig t ht s hs hts g hg
  ·
    exfalso
    have hrow := kf123Row11 G p L A E (Sec12Three.table123SU5 h12 hS)
    have hcard : Nat.card E = p ^ 4 := hrow.2.1
    rw [hEA, h12.A_card] at hcard
    have h5 := Sec12Three.five_le h12
    have h1 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

end CFSG.RankThree.PartOne.KFOUT3
