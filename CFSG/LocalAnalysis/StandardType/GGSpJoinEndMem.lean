module

public import CFSG.LocalAnalysis.StandardType.GGSpFrameRank
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGSpJoinEndFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin

theorem ggSpEnd_mem (hMp : GGInnerDiagMpInput) (hlift : GGSpLiftInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ} {y : G}
    {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) : y ∈ L ∧ x ∈ K := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hm3 : 3 ≤ m := by
    have := hN.2.1
    omega
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  obtain ⟨hrank, hLc, hKc⟩ := ggSpConfig_rank_orders hlift hMp hcfg hInn hN
  obtain ⟨φ₀, hφ₀inj, hφ₀range⟩ := hlift G L (m + 1) f hN.2.1 hInn.1.1 hN.1
  have hmarkK : GGInnerDiagOn Bs K := hInn.2 y K hN.2.2.2.1
  obtain ⟨φK, hφKinj, hφKrange⟩ := hlift G K (m + 1) f hN.2.1 hmarkK.1 hN.2.2.2.2.1
  have hinnerL : ∀ b ∈ Bs, ∃ g ∈ L, ∀ k ∈ L, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by omega) hN.1.1 hInn.1 φ₀ hφ₀inj hφ₀range
  have hnormL : Bs ≤ Subgroup.normalizer (L : Set G) := hInn.1.le_normalizer
  have hcentL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ p :=
    hcfg.card_bstar_centralizer_le
  have hinnerK : ∀ b ∈ Bs, ∃ g ∈ K, ∀ k ∈ K, b * k * b⁻¹ = g * k * g⁻¹ :=
    ggSpInnerAction_of_mp hMp (by omega) hN.1.1 hmarkK φK hφKinj hφKrange
  have hnormK : Bs ≤ Subgroup.normalizer (K : Set G) := hmarkK.le_normalizer
  have hZL : Subgroup.center L = ⊥ := by
    have := center_range_statedSp_eq_bot φ₀ hφ₀inj
    rwa [hφ₀range] at this
  have hZK : Subgroup.center K = ⊥ := by
    have := center_range_statedSp_eq_bot φK hφKinj
    rwa [hφKrange] at this
  have hA : GGWeylOfType p (CoxeterMatrix.B (m + 1 + 1)) (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
    hN.2.2.2.2.2
  have hrankLB : p ^ (m + 1 + 1) ≤ Nat.card Bs := hrank.ge
  have hcentK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    card_bstar_centralizer_le_of_lifts hp hp2 (Nat.succ_pos m) hBs φ₀ hφ₀inj hφ₀range hZL hnormL
      hinnerL φK hφKinj hφKrange hZK hnormK hinnerK hcentL hrankLB
  have hnbr : GGNbr p B x D J y K := hN.2.2.2.1
  have hyBs : y ∈ Bs := hBs.1 hnbr.1.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  have hyL : y ∉ Subgroup.centralizer (L : Set G) := ggNbr_y_not_mem_centralizer_left hcfg hnbr
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxBs : x ∈ Bs := hBs.1 hS.2.1
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := ggNbr_x_not_mem_centralizer hnbr
  have hy1 : y ≠ 1 := hnbr.1.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
    have hxord : orderOf x = p := orderOf_eq_prime (hBs.2.1.2 x hxBs) hx1
    have hcardzx : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
    have hle : Subgroup.zpowers x ≤ Bs ⊓ Subgroup.centralizer (L : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hxBs, hxL⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardzx]; exact hcentL)).symm
  have hBsK : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
    have hyord : orderOf y = p := orderOf_eq_prime (hBs.2.1.2 y hyBs) hy1
    have hcardzy : Nat.card (Subgroup.zpowers y) = p := by rw [Nat.card_zpowers, hyord]
    have hle : Subgroup.zpowers y ≤ Bs ⊓ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr ⟨hyBs, hyK⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardzy]; exact hcentK)).symm
  have hy_not_zx : y ∉ Subgroup.zpowers x := by
    intro hy
    exact hyL (Subgroup.zpowers_le.mpr hxL hy)
  have hx_not_zy : x ∉ Subgroup.zpowers y := by
    intro hx
    exact hxK (Subgroup.zpowers_le.mpr hyK hx)
  have hyL_mem : y ∈ L :=
    spEnd_mem_of_counting_frame hp hp2 hm3 h2 hBs φ₀ hφ₀inj hφ₀range hnormL hinnerL hcentL hrank
      hA le_sup_left le_sup_right hLc hKc hyBs hyK hyL hxBs hxL hx1 hBsL hy_not_zx
  have hxK_mem : x ∈ K :=
    spEnd_mem_of_counting_frame hp hp2 hm3 h2 hBs φK hφKinj hφKrange hnormK hinnerK hcentK hrank
      hA le_sup_right le_sup_left hKc hLc hxBs hxL hxK hyBs hyK hy1 hBsK hx_not_zy
  exact ⟨hyL_mem, hxK_mem⟩

end CFSG.StandardType
