module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivAsm
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeAsm
public import CFSG.LocalAnalysis.StandardType.GGQTwoRowDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwo_localRowOut
    {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 5 ≤ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : ¬ 3 ∣ m → PSUTrivialMultiplier m)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m) :
    ∃ (k : QTwoRowKind) (d c : ℕ), QTwoRowData k m d c Bs L x ∧
      ((k = .prime ∨ k = .suFull) → QTwoLocalModel m Bs L x) := by
  by_cases h3 : 3 ∣ m
  · rcases qTwoLMSkel_divRow hG hBs hN (by omega) h3 hL hrt hFrameL hFm with ⟨hr, hlm⟩ | hr | hr | hr
    · exact ⟨.suFull, m, m - 1, hr, fun _ => hlm⟩
    · exact ⟨.suInner, m - 1, m - 1, hr, fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩
    · exact ⟨.psuInner, m - 1, m - 2, hr, fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩
    · exact ⟨.psuFull, m, m - 2, hr, fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩
  · have hlm := qTwo_localModel_prime hG hBs hN hm h3 hL (hMul h3) hrt
    exact ⟨.prime, m, m - 1, qTwo_rowData_prime hlm h3, fun _ => hlm⟩

end CFSG.StandardType.QTwo

end
