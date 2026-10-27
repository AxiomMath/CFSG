module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixBstarUniqueToralA
public import CFSG.LocalAnalysis.StandardType.GGTypeAFarConfig
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

theorem succ_div_add_three_le_of_not_dvd {n p r : ℕ} (hn : 3 ≤ n) (hp : 3 ≤ p) (hpn : ¬ p ∣ n + 1)
    (h4 : 4 ≤ r) (hr : n - 1 ≤ r) : (n + 1) / p + 3 ≤ r := by
  rcases Nat.lt_or_ge p 4 with h | h
  · obtain rfl : p = 3 := by omega
    omega
  · have h1 : (n + 1) / p ≤ (n + 1) / 4 := Nat.div_le_div_left h (by norm_num)
    omega

theorem succ_div_add_three_le_succ {n p : ℕ} (hn : 3 ≤ n) (hp : 3 ≤ p) :
    (n + 1) / p + 3 ≤ n + 1 := by
  have h1 : (n + 1) / p ≤ (n + 1) / 3 := Nat.div_le_div_left hp (by norm_num)
  omega

theorem not_dvd_add_two_of_dvd_succ {n p : ℕ} (hp : 2 ≤ p) (h : p ∣ n + 1) : ¬ p ∣ n + 2 := by
  intro h'
  have h1 : p ∣ 1 := (Nat.dvd_add_right h).1 h'
  have := Nat.le_of_dvd one_pos h1
  omega

section Cfg

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}

theorem GGTypeANbrCfg.card_bstar_ge (hN : GGTypeANbrCfg p B Bs x L D J n f y K) :
    p ^ ((n + 1) / p + 3) ≤ Nat.card Bs ∧ (p ∣ n + 1 → p ^ (n + 1) ≤ Nat.card Bs) := by
  have hNbr : GGTypeANbr p B Bs x L D J n f y K := hN.2.2.2.2
  obtain ⟨hcfg, hOp, hInn, hNoTr, hmod, hpq, hn, hsc, hnbr, hmodK, hW, hAll⟩ := hN
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; omega
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  obtain ⟨hf1, φ₁, hφL, hker⟩ := GGTypeANbr.exists_lift hcfg hNbr
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hr : n - 1 ≤ LargeEvenTwoLocalRank p G :=
    RootPlaneA.sub_one_le_twoLocalRank (F := GaloisField 2 f) hp hpK (by omega) hker
  by_cases hdvd : p ∣ n + 1
  · have hL : ggAutomizer L Bs ≤ ggAutomizer ⊤ Bs :=
      Subgroup.closure_mono fun φ hφ => by
        obtain ⟨g, hg, hgN, hg'⟩ := hφ
        exact ⟨g, trivial, hgN, hg'⟩
    have hK : ggAutomizer K Bs ≤ ggAutomizer ⊤ Bs :=
      Subgroup.closure_mono fun φ hφ => by
        obtain ⟨g, hg, hgN, hg'⟩ := hφ
        exact ⟨g, trivial, hgN, hg'⟩
    have hA : ∀ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, φ ∈ ggInduced ⊤ Bs :=
      fun φ hφ => mem_ggInduced_top_of_mem_ggAutomizer ((sup_le hL hK) hφ)
    have hbig : p ^ (n + 1) ≤ Nat.card Bs :=
      pow_le_card_of_weylOfType_A hp hp2 hcfg.2.1.2.1 hNoTr hA hW
        (not_dvd_add_two_of_dvd_succ hp.two_le hdvd)
    exact ⟨(Nat.pow_le_pow_right hp.pos (succ_div_add_three_le_succ hn hp3)).trans hbig,
      fun _ => hbig⟩
  · have hrle : (n + 1) / p + 3 ≤ LargeEvenTwoLocalRank p G :=
      succ_div_add_three_le_of_not_dvd hn hp3 hdvd hr4 hr
    exact ⟨(Nat.pow_le_pow_right hp.pos hrle).trans (hBcard.symm.trans_le hBBs),
      fun hd => absurd hd hdvd⟩

end Cfg

end CFSG.StandardType

end
