module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviCount
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSpProofJoin

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.LieType.Universal.Symplectic CFSG.StandardType.SpJoin

section Rank

variable {G : Type} [Group G] [Finite G]

theorem ggSpConfig_rank_orders (hlift : GGSpLiftInput) (hMp : GGInnerDiagMpInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {m f : ℕ} {y : G} {K : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hInn : GGInnerDiagAll p B Bs x L D J)
    (hN : GGTypeCNbr p B Bs x L D J (m + 1) f y K) :
    Nat.card Bs = p ^ (m + 1 + 1) ∧
      2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer L Bs) ∧
      2 ^ (m + 1) * (m + 1).factorial ≤ Nat.card (ggAutomizer K Bs) := by
  classical
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hm3 : 3 ≤ m := by
    have := hN.2.1
    omega
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
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
  have hrankLB : p ^ (m + 1 + 1) ≤ Nat.card Bs :=
    pow_le_card_of_weylOfType_B hp hp2 hBs.2.1 (by omega) hA
  have hcentK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≤ p :=
    card_bstar_centralizer_le_of_lifts hp hp2 (Nat.succ_pos m) hBs φ₀ hφ₀inj hφ₀range hZL hnormL
      hinnerL φK hφKinj hφKrange hZK hnormK hinnerK hcentL hrankLB
  refine ⟨?_, ?_, ?_⟩
  ·
    have hsplit := card_ggBstar_split (X := L) hBs hZL hnormL hinnerL
    have hcardBsL : Nat.card ↥(Bs ⊓ L) ≤ p ^ (m + 1) := by
      let E' : Subgroup (StatedSp (m + 1) (GaloisField 2 f)) := (Bs ⊓ L).comap φ₀
      have hE'map : E'.map φ₀ = Bs ⊓ L := by
        show ((Bs ⊓ L).comap φ₀).map φ₀ = Bs ⊓ L
        exact Subgroup.map_comap_eq_self (by rw [← hφ₀range]; exact inf_le_right)
      have hcardE' : Nat.card E' = Nat.card ↥(Bs ⊓ L) := by
        rw [← hE'map]
        exact (Subgroup.card_map_of_injective (K := E') hφ₀inj).symm
      have hE'ab : IsElemAbelian p E' := IsElemAbelian.comap (hBs.2.1.mono inf_le_left) hφ₀inj
      have hpF : (p : GaloisField 2 f) ≠ 0 := natCast_ne_zero_of_two_eq_zero h2 hp2 hp
      have hleE' := card_le_pow_of_isElemAbelian (F := GaloisField 2 f) hp hp2 hpF E' hE'ab
      rwa [hcardE'] at hleE'
    refine le_antisymm ?_ hrankLB
    calc Nat.card Bs
        = Nat.card ↥(Bs ⊓ L) *
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) := hsplit
      _ ≤ p ^ (m + 1) * p := Nat.mul_le_mul hcardBsL hcentL
      _ = p ^ (m + 1 + 1) := (pow_succ p (m + 1)).symm
  · exact two_pow_mul_factorial_le_card_ggAutomizer_of_lift hp hp2 h2 φ₀ hφ₀inj hBs hφ₀range
      hnormL hinnerL hcentL hrankLB
  · exact two_pow_mul_factorial_le_card_ggAutomizer_of_lift hp hp2 h2 φK hφKinj hBs hφKrange
      hnormK hinnerK hcentK hrankLB

end Rank

end CFSG.StandardType
