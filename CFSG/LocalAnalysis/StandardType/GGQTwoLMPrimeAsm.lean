module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMHelp
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameB
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameC
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeB
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeC
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModAug
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGQTwoRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_primeFrame
    {G : Type} [Group G] [Finite G] {B Bs L D J : Subgroup G} {x : G}
    {m : ℕ} (hcfg : GGConfig 3 B Bs x L D J) (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m) :
    ∃ F : QTwoFrame m ↥(sumZero m 3) ↥(sumZero m 3) Bs L x,
      IsAugModel m ↥(sumZero m 3) F.permV ∧ IsAugModel m ↥(sumZero m 3) F.permVT := by
  obtain ⟨M⟩ := qTwoLMSkel_prime_model hG hBs hN hm h3 hL hMul
  have hr := qTwoLMSkel_prime_rank hcfg hN hm hL
  obtain ⟨Θ, hnorm, hind⟩ := qTwoLMSkel_prime_theta hG hBs hN hm h3 hL hMul M hr.1 hr.2
  obtain ⟨ΘT, hnormT, hindT⟩ := qTwoLMSkel_prime_thetaT hG hBs hN hm h3 hL hMul
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hN, qTwoLMSkel_x_mem_Bs hG hBs, qTwoLMSkel_prime_hord hG hBs, hBs.2.1,
      permAutVHom m 3, permAutVHom m 3, qTwoLMSkel_prime_ker hG hBs hN hL hMul,
      qTwoLMSkel_prime_link hG hBs hN hm h3 hL hMul M hr.1 hr.2, Θ, hnorm, hind, ΘT, hnormT, hindT⟩
  · exact ⟨MulEquiv.refl _, by intro σ v; simp [permAutVHom_apply]⟩
  · exact ⟨MulEquiv.refl _, by intro σ v; simp [permAutVHom_apply]⟩

theorem qTwo_localModel_prime
    {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (hMul : PSUTrivialMultiplier m)
    (hrt : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) :
    QTwoLocalModel m Bs L x := by
  obtain ⟨F, hV, hVT⟩ := qTwoLMSkel_primeFrame hrt.1.1 hG hBs hN hm h3 hL hMul
  exact ⟨hBs.2.1, F.hx, qTwoLMSkel_frame_card F (d := m) (qTwoLMSkel_isAugModel_card hV) (by omega),
    qTwoLMSkel_frame_weyl F (by omega) (qTwoLMSkel_route_noTransvection hrt)
      (qTwoLMSkel_AL_fixes hG F.hx) (qTwoLMSkel_isAugModel_faithful hV (by omega))
      (qTwoLMSkel_isAugModel_transposition hV),
    qTwoLMSkel_AL_fixes hG F.hx, qTwoLMSkel_frame_fixed F (qTwoLMSkel_isAugModel_fixed hV h3 hm),
    qTwoLMSkel_frame_comm F (m - 1) (qTwoLMSkel_isAugModel_card hVT) (qTwoLMSkel_isAugModel_comm hVT),
    qTwoLMSkel_frame_stab F hG hBs hL hMul h3 hV hVT, qTwoLMSkel_frame_direct F hG hBs hL hMul h3 hV hVT⟩

theorem qTwo_rowData_prime {G : Type} [Group G] [Finite G] {m : ℕ} {Bs L : Subgroup G} {x : G}
    (h : QTwoLocalModel m Bs L x) (h3 : ¬ 3 ∣ m) :
    QTwoRowData .prime m m (m - 1) Bs L x :=
  ⟨h.elemAb, h.mem, h.card, h.weyl, h.fixes, h.fixed, h.comm, fun hk => absurd rfl hk,
    fun _ => h3, ⟨fun _ => ⟨rfl, rfl⟩, fun hk => absurd hk (by decide), fun hk => absurd hk (by decide),
      fun hk => absurd hk (by decide), fun hk => absurd hk (by decide)⟩⟩

end CFSG.StandardType.QTwo

end
