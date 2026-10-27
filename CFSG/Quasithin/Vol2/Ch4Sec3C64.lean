module

public import CFSG.Quasithin.Vol2.Ch4Sec3A7
public import CFSG.Quasithin.Vol2.Ch4Sec3C64R
public import CFSG.Quasithin.Background.C64Dihedral

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem lemmaC64Ten_holds : LemmaC64Ten := by
  intro G _ _ L R TH Sig hRN _ _ _ hTH2 hRTH hTHR hTHS _ hC623 hTHL hL α β hα hαk hβ hβk hβe
    a b hab hR1 hR2 hQR hR4 hII hSig2 _ u hu
  have blk : C64.A7Blk L α β := ⟨hL, hα, hαk, hβ, hβk, hβe⟩
  have h : C64.Hyp64 L R TH Sig α β a b :=
    { blk := blk, hab := hab, RN := hRN, TH2 := hTH2, RTH := hRTH, THR := hTHR, THS := hTHS,
      C623 := hC623, THL := hTHL, R1 := hR1, R2 := hR2, QR := hQR, R4 := hR4, II := hII,
      Sig2 := hSig2 }
  refine sup_le (blk.le_centralizer_of_normalizes hab hRN hR1 hR2 hTHL hTHR hu) ?_
  obtain ⟨E, s, t, hE2, hEc, hs2, ht2, hsE, htE, hst, huE, hu1, -, -, hQE, hRE⟩ :=
    h.exists_data hu
  have hN : Sig ⊓ Subgroup.normalizer ((E ⊔ Subgroup.zpowers s : Subgroup G) : Set G) =
      E ⊔ Subgroup.closure {s, t} := by
    rw [← hQE, ← hRE]
    exact hII _ h.Q_ne_bot hQR
      (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ TH))
  have hRS : E ⊔ Subgroup.closure {s, t} ≤ Sig := hRE ▸ h.R_le_Sig
  have key := C64Dihedral.le_centralizer_of_normalizer_eq hSig2 hE2 hEc hs2 ht2 hsE htE
    (hst ▸ huE) (hst ▸ hu1) hRS hN
  rwa [hst] at key

end CFSG.Quasithin.H13.Ch4
