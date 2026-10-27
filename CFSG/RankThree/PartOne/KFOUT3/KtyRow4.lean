module

public import CFSG.RankThree.PartOne.KFOUT3.KtyDih
public import CFSG.RankThree.PartOne.KFOUT3.KtyRoot
public import CFSG.RankThree.PartOne.KFOUT3.KtyRows
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyDihCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore
public import CFSG.RankThree.PartOne.KFOUT3.KtyF4Act
public import CFSG.RankThree.PartOne.KFOUT3.KtyF4Ctx
public import CFSG.RankThree.PartOne.KLAY.Frames
public import CFSG.RankThree.PartOne.KF.R4Final
public import CFSG.RankThree.PartOne.KF.R11Final

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne.N1322 CFSG.RankThree.PartOne.KLAY CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem kf1322KtyRow4_of_layers
    (hlayers : ∀ (p a : ℕ) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
      (hP : F4Param p a K),
      (∀ v : G2V p K, v ≠ 1 → f4s1 p K v = v →
        RootLayer ↥(F4.reeGamma K a) p (tp4M hP v)
          (2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1))) ∧
      (∀ v : G2V p K, v ≠ 1 → f4s2 p K (2 ^ a) v = v →
        RootLayer ↥(F4.reeGamma K a) p (tp4M hP v)
          ((2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)))) :
    KF1322KtyRow 4 := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hmodel t ht s hs hts g hg
  rcases hF12.two with hG | hS
  · have hp := h12.prime
    have h5 := Sec12Three.five_le h12
    obtain ⟨hFexp, hFcomm, hmax⟩ := F_facts h12 hG
    have hcore := table_core_of h12 hG
    obtain ⟨a, K, hKf, hKfin, hchar, hP, hζ, ε, hε, hFT₁, hFT₂⟩ := exists_r4frame hcore hmodel
    have hθ := hP.theta_dvd
    obtain ⟨SM, hSM⟩ := exists_wctx_f4' hP (f4tau p K (2 ^ a))
      (fun i b => tp4Hom_f4tau hP.card i b)
    have hVexp : ∀ d : G2V p K, d ^ p = 1 := fun d =>
      funext fun i => Subtype.ext (by simpa using (mem_rootsOfUnity p _).mp (d i).2)
    obtain ⟨S₁, hrel₁⟩ := wctx_ofCentralQuot' hVexp SM (MonoidHom.id _) (isCentralPQuot_id p _) ε
      hε (inf_le_right : E ⊓ L ≤ L) hFexp hFT₁ hFT₂
    have hmem : ∀ γ : DihedralGroup 8, f4Act (K := K) hθ γ ∈
        Subgroup.closure (Set.range (f4tau p K (2 ^ a))) := by
      intro γ
      rw [range_f4tau]
      exact pairAct_mem_closure f4s1_mul_self f4s2_mul_self (f4_braid hθ) γ
    let f₁ : DihedralGroup 8 →* ↥(Subgroup.closure (Set.range (f4tau p K (2 ^ a)))) :=
      (f4Act (K := K) hθ).codRestrict _ hmem
    have hf₁ : Function.Surjective f₁ := by
      rintro ⟨x, hx⟩
      rw [range_f4tau] at hx
      obtain ⟨γ, hγ⟩ := exists_pairAct_of_mem_closure (by decide) f4s1_mul_self f4s2_mul_self
        (f4_braid hθ) hx
      exact ⟨γ, Subtype.ext hγ⟩
    let S := wctxPull (act := f4Act (K := K) hθ) f₁ hf₁ (fun γ => rfl) S₁
    let Temb : G2V p K →* ↥(F4.reeGamma K a) := tp4M hP
    have hrel : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = Temb d := by
      intro d
      show ε (Subgroup.inclusion inf_le_right (S₁.tor d)) = Temb d
      rw [hrel₁ d, hSM d]
      rfl
    have Hconj : ∀ γ : DihedralGroup 8, ∃ m : ↥(F4.reeGamma K a),
        ∀ v, m * Temb v * m⁻¹ = Temb (f4Act (K := K) hθ γ v) := by
      intro γ
      obtain ⟨m, hm⟩ := conj_of_wctx SM (tp4M hP) hSM (MonoidHom.id _) (f₁ γ)
      exact ⟨m, fun v => hm v⟩
    obtain ⟨hl0, hl1⟩ := hlayers p a K hP
    have hu : ∀ v : G2V p K, (tp4M hP v) ^ p = 1 := fun v => by
      rw [← map_pow, hVexp, map_one]
    have hq := isCentralPQuot_id p ↥(F4.reeGamma K a)
    have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hnd := row4_not_dvd hq2
    have Hsmall : ∀ v : G2V p K, v ≠ 1 → f4Act (K := K) hθ (DihedralGroup.sr 0) v = v →
        SmallAt (Temb v)
          (· = (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) := by
      intro v hv1 hfix
      rw [f4Act_sr_zero] at hfix
      exact smallAt_of_rootLayer hq (hu v) (hl0 v hv1 hfix) hnd
    have Hbig : ∀ v : G2V p K, v ≠ 1 → f4Act (K := K) hθ (DihedralGroup.sr 1) v = v →
        BigAt p (Temb v)
          (· = (2 ^ (2 * a + 1)) ^ 2 * ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)) := by
      intro v hv1 hfix
      rw [f4Act_sr_one] at hfix
      exact bigAt_of_rootLayer hp hq (hu v) (hl1 v hv1 hfix)
    exact kty_of_dih (n := 8) (by norm_num) h12 hG hEA hF13 (f4Act_injective hp h5 hζ hθ)
      (f4Act_refl hp h5 hζ hθ) hε Temb S hrel Hconj Hsmall Hbig t ht s hs hts g hg
  ·
    exfalso
    have hrow := kf123Row11 G p L A E (Sec12Three.table123SU5 h12 hS)
    have hcard : Nat.card E = p ^ 4 := hrow.2.1
    rw [hEA, h12.A_card] at hcard
    have h5 := Sec12Three.five_le h12
    have h1 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

end CFSG.RankThree.PartOne.KFOUT3
