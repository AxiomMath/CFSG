module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMHelp
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivKind
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivLinkLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFull
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameB
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModAug
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModHm
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModQm
public import CFSG.LocalAnalysis.StandardType.GGQTwoRowDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_divFrame_suInner
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .suInner m Bs L) :
    ∃ F : QTwoFrame m (QTwoHm m h3) ↥(sumZero m 3) Bs L x,
      IsHmModel m h3 (QTwoHm m h3) F.permV ∧
        IsAugModel m ↥(sumZero m 3) F.permVT := by
  obtain ⟨C, hV, hVT⟩ := qTwoLMSkel_divCoord_suInner hG hBs hN hm h3 hL hFrameL hFm hk
  exact ⟨qTwoLMSkel_divFrameOfCoords C (qTwoLMSkel_x_mem_Bs hG hBs) (qTwoLMSkel_prime_hord hG hBs)
    hBs.2.1 (qTwoLMSkel_div_ker hG hBs hN) (qTwoLMSkel_div_link hBs hN h3 hFrameL hFm),
    hV, hVT⟩

theorem qTwoLMSkel_divFrame_suFull
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .suFull m Bs L) :
    ∃ F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x,
      IsQmModel m (QTwoQm m) F.permV ∧
        IsAugModel m ↥(sumZero m 3) F.permVT := by
  obtain ⟨C, hV, hVT⟩ := qTwoLMSkel_divCoord_suFull hG hBs hN hm h3 hL hFrameL hFm hk
  exact ⟨qTwoLMSkel_divFrameOfCoords C (qTwoLMSkel_x_mem_Bs hG hBs) (qTwoLMSkel_prime_hord hG hBs)
    hBs.2.1 (qTwoLMSkel_div_ker hG hBs hN) (qTwoLMSkel_div_link hBs hN h3 hFrameL hFm),
    hV, hVT⟩

theorem qTwoLMSkel_divFrame_psuInner
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .psuInner m Bs L) :
    ∃ F : QTwoFrame m (QTwoHm m h3) (QTwoHm m h3) Bs L x,
      IsHmModel m h3 (QTwoHm m h3) F.permV ∧
        IsHmModel m h3 (QTwoHm m h3) F.permVT := by
  obtain ⟨C, hV, hVT⟩ := qTwoLMSkel_divCoord_psuInner hG hBs hN hm h3 hL hFrameL hFm hk
  exact ⟨qTwoLMSkel_divFrameOfCoords C (qTwoLMSkel_x_mem_Bs hG hBs) (qTwoLMSkel_prime_hord hG hBs)
    hBs.2.1 (qTwoLMSkel_div_ker hG hBs hN) (qTwoLMSkel_div_link hBs hN h3 hFrameL hFm),
    hV, hVT⟩

theorem qTwoLMSkel_divFrame_psuFull
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G}
    {x : G} {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m)
    (hk : QTwoDivKind.facts .psuFull m Bs L) :
    ∃ F : QTwoFrame m (QTwoQm m) (QTwoHm m h3) Bs L x,
      IsQmModel m (QTwoQm m) F.permV ∧
        IsHmModel m h3 (QTwoHm m h3) F.permVT := by
  obtain ⟨C, hV, hVT⟩ := qTwoLMSkel_divCoord_psuFull hG hBs hN hm h3 hL hFrameL hFm hk
  exact ⟨qTwoLMSkel_divFrameOfCoords C (qTwoLMSkel_x_mem_Bs hG hBs) (qTwoLMSkel_prime_hord hG hBs)
    hBs.2.1 (qTwoLMSkel_div_ker hG hBs hN) (qTwoLMSkel_div_link hBs hN h3 hFrameL hFm),
    hV, hVT⟩

theorem qTwoLMSkel_divFrame
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    {m : ℕ} (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m) :
    (∃ F : QTwoFrame m (QTwoHm m h3) ↥(sumZero m 3) Bs L x,
        IsHmModel m h3 (QTwoHm m h3) F.permV ∧
          IsAugModel m ↥(sumZero m 3) F.permVT) ∨
    (∃ F : QTwoFrame m (QTwoQm m) ↥(sumZero m 3) Bs L x,
        IsQmModel m (QTwoQm m) F.permV ∧
          IsAugModel m ↥(sumZero m 3) F.permVT) ∨
    (∃ F : QTwoFrame m (QTwoHm m h3) (QTwoHm m h3) Bs L x,
        IsHmModel m h3 (QTwoHm m h3) F.permV ∧
          IsHmModel m h3 (QTwoHm m h3) F.permVT) ∨
    (∃ F : QTwoFrame m (QTwoQm m) (QTwoHm m h3) Bs L x,
        IsQmModel m (QTwoQm m) F.permV ∧
          IsHmModel m h3 (QTwoHm m h3) F.permVT) := by
  obtain ⟨k, hk⟩ := qTwoLMSkel_div_kind hG hBs hN hm h3 hL hFrameL hFm
  rcases k with _ | _ | _ | _
  · exact Or.inl (qTwoLMSkel_divFrame_suInner hG hBs hN hm h3 hL hFrameL hFm hk)
  · exact Or.inr (Or.inl (qTwoLMSkel_divFrame_suFull hG hBs hN hm h3 hL hFrameL hFm hk))
  · exact Or.inr (Or.inr (Or.inl
      (qTwoLMSkel_divFrame_psuInner hG hBs hN hm h3 hL hFrameL hFm hk)))
  · exact Or.inr (Or.inr (Or.inr
      (qTwoLMSkel_divFrame_psuFull hG hBs hN hm h3 hL hFrameL hFm hk)))

theorem qTwoLMSkel_divRow
    {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 6 ≤ m) (h3 : 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hFrameL : QTwoFrameL 3 B Bs x L D J) (hFm : hFrameL.m = m) :
    (QTwoRowData .suFull m m (m - 1) Bs L x ∧ QTwoLocalModel m Bs L x) ∨
    QTwoRowData .suInner m (m - 1) (m - 1) Bs L x ∨
    QTwoRowData .psuInner m (m - 1) (m - 2) Bs L x ∨
    QTwoRowData .psuFull m m (m - 2) Bs L x := by
  have hnt := qTwoLMSkel_route_noTransvection hrt
  have hfixL := fun {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x) =>
    qTwoLMSkel_AL_fixes hG F.hx
  rcases qTwoLMSkel_divFrame hG hBs hN hm h3 hL hFrameL hFm with
    ⟨F, hV, hVT⟩ | ⟨F, hV, hVT⟩ | ⟨F, hV, hVT⟩ | ⟨F, hV, hVT⟩
  ·
    exact Or.inr (Or.inl ⟨F.elemAb, F.hx,
      qTwoLMSkel_frame_card F (d := m - 1)
        (by rw [qTwoLMSkel_isHmModel_card h3 hV, show (m - 1) - 1 = m - 2 by omega])
        (by omega),
      qTwoLMSkel_frame_weyl F (by omega) hnt (hfixL F)
        (qTwoLMSkel_isHmModel_faithful h3 hV (by omega))
        (qTwoLMSkel_isHmModel_transposition h3 hV),
      hfixL F, qTwoLMSkel_frame_fixed F (qTwoLMSkel_isHmModel_fixed h3 hV (by omega)),
      qTwoLMSkel_frame_comm F (m - 1) (qTwoLMSkel_isAugModel_card hVT)
        (qTwoLMSkel_isAugModel_comm hVT),
      fun _ => h3, fun h => absurd h (by decide), by simp⟩)
  ·
    have hcard : Nat.card Bs = 3 ^ m :=
      qTwoLMSkel_frame_card F (d := m) (qTwoLMSkel_isQmModel_card hV) (by omega)
    have hweyl := qTwoLMSkel_frame_weyl F (by omega) hnt (hfixL F)
      (qTwoLMSkel_isQmModel_faithful hV (by omega)) (qTwoLMSkel_isQmModel_transposition hV)
    have hfixed := qTwoLMSkel_frame_fixed F (qTwoLMSkel_isQmModel_fixed hV h3 (by omega))
    have hcomm := qTwoLMSkel_frame_comm F (m - 1) (qTwoLMSkel_isAugModel_card hVT)
      (qTwoLMSkel_isAugModel_comm hVT)
    obtain ⟨hstab, hdirect⟩ := qTwoLMSkel_suFull_stabDirectL F hG hBs hL hrt hFrameL hFm hm h3 hV hVT
    exact Or.inl ⟨⟨F.elemAb, F.hx, hcard, hweyl, hfixL F, hfixed, hcomm, fun _ => h3,
        fun h => absurd h (by decide), by simp⟩,
      ⟨F.elemAb, F.hx, hcard, hweyl, hfixL F, hfixed, hcomm, hstab, hdirect⟩⟩
  ·
    exact Or.inr (Or.inr (Or.inl ⟨F.elemAb, F.hx,
      qTwoLMSkel_frame_card F (d := m - 1)
        (by rw [qTwoLMSkel_isHmModel_card h3 hV, show (m - 1) - 1 = m - 2 by omega])
        (by omega),
      qTwoLMSkel_frame_weyl F (by omega) hnt (hfixL F)
        (qTwoLMSkel_isHmModel_faithful h3 hV (by omega))
        (qTwoLMSkel_isHmModel_transposition h3 hV),
      hfixL F, qTwoLMSkel_frame_fixed F (qTwoLMSkel_isHmModel_fixed h3 hV (by omega)),
      qTwoLMSkel_frame_comm F (m - 2) (qTwoLMSkel_isHmModel_card h3 hVT)
        (qTwoLMSkel_isHmModel_comm h3 hVT),
      fun _ => h3, fun h => absurd h (by decide), by simp⟩))
  ·
    exact Or.inr (Or.inr (Or.inr ⟨F.elemAb, F.hx,
      qTwoLMSkel_frame_card F (d := m) (qTwoLMSkel_isQmModel_card hV) (by omega),
      qTwoLMSkel_frame_weyl F (by omega) hnt (hfixL F)
        (qTwoLMSkel_isQmModel_faithful hV (by omega))
        (qTwoLMSkel_isQmModel_transposition hV),
      hfixL F, qTwoLMSkel_frame_fixed F (qTwoLMSkel_isQmModel_fixed hV h3 (by omega)),
      qTwoLMSkel_frame_comm F (m - 2) (qTwoLMSkel_isHmModel_card h3 hVT)
        (qTwoLMSkel_isHmModel_comm h3 hVT),
      fun _ => h3, fun h => absurd h (by decide), by simp⟩))

end CFSG.StandardType.QTwo

end
