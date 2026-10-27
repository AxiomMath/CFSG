module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKindCard
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_div_ker {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∀ b : ↥Bs, ggGamma L hN b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := fun b => by
  have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  rw [ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs.2.1
    (hBs.1 hS.2.1) hS.2.2.1 hS.2.2.2.1.1 hS.2.2.2.2]
  exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩

theorem qTwoLMSkel_div_kind {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (_h3 : 3 ∣ m)
    (_hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m) :
    ∃ k : QTwoDivKind, QTwoDivKind.facts k m Bs L := by
  revert hFm
  obtain ⟨F0, hF, m', -, L0, c, hc_surj, hc_ker, hc_two, πSU, hπ_surj, hπ_ker, ρ, hdiag, -,
    hρ⟩ := hFrameL
  intro hFm
  change m' = m at hFm
  subst m'
  have hS : CFSG.Assembly.LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  have hxB : x ∈ Bs := hBs.1 hS.2.1
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hBs.2.1.2 x hxB) hS.2.2.1
  have hup := qTwoLMDivKind_card_le hN (qTwoLMFrameC_perfect hG)
    (qTwoLMSkel_div_ker hG hBs hN) hxB hx3 hF (by omega) c hc_ker πSU hπ_surj ρ hdiag hρ
  have hlow := qTwoLMDivKind_le_card hBs hN hxB hS.2.2.1 (qTwoLMFrameC_le_centralizer hG) hF
    (by omega) c hc_surj hc_ker hc_two πSU hπ_surj hπ_ker ρ hdiag hρ
  have hp : IsPGroup 3 Bs := fun g => ⟨1, Subtype.ext (by simpa using hBs.2.1.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hup hlow
  have hk' : k = m - 1 ∨ k = m := by
    have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hup
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hlow
    omega
  by_cases hz : 3 ∣ Nat.card (Subgroup.center ↥L)
  · rcases hk' with rfl | rfl
    · exact ⟨.suInner, by simp only [QTwoDivKind.facts]; exact ⟨hz, hk⟩⟩
    · exact ⟨.suFull, by simp only [QTwoDivKind.facts]; exact ⟨hz, hk⟩⟩
  · rcases hk' with rfl | rfl
    · exact ⟨.psuInner, by simp only [QTwoDivKind.facts]; exact ⟨hz, hk⟩⟩
    · exact ⟨.psuFull, by simp only [QTwoDivKind.facts]; exact ⟨hz, hk⟩⟩

end CFSG.StandardType.QTwo

end
