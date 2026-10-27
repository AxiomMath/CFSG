module

public import CFSG.Quasithin.H13.GoldschmidtM22Final
public import CFSG.Quasithin.Background.SzG11G64Old

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Quasithin CFSG.Quasithin.G6

theorem g64Out_of_b56 (h56 : AsB56) : G64Out := by
  intro V _ _ X a h htr hT
  obtain ⟨s, Ks, hd, h4⟩ := SzG11.lemma_G64_all_of_b5 h56 h htr
  obtain ⟨T, hTS, haT, hcent⟩ := hT
  obtain ⟨hs1, hXK, -⟩ := h4 T hTS haT hcent
  subst hs1
  have hdd := hd.decomp
  have hK0 : Ks 0 = X := by
    have := hdd.iSup_eq
    rw [iSup_unique] at this
    rw [hXK]
    exact this
  have hcomm : commV X = ⊤ := hXK ▸ lemma_G62_1 h
  refine ⟨hXK, hcomm, ?_⟩
  obtain ⟨hTX, hTp, hTi⟩ := hTS
  have ha0 : a ∈ Ks 0 := hd.mem_first.choose_spec
  have hTX0 : T ≤ Ks 0 := hK0 ▸ hTX
  have hTi0 : ¬ 2 ∣ (T.subgroupOf (Ks 0)).index := by rw [hK0]; exact hTi
  have hc0 : commV (Ks 0) = ⊤ := by rw [hK0]; exact hcomm
  rcases hdd.type 0 with ⟨n, hn2, hn5, hL⟩ | ⟨n, hn5, hn8, ⟨θ, β, hequiv, hrange, hker⟩⟩ |
      ⟨n, hn, ⟨θ, β, hequiv, hrange, hker⟩⟩
  · obtain ⟨⟨e⟩, hcard, -⟩ := hL
    refine Or.inl ⟨n, hn2, hn5, ?_, ⟨(MulEquiv.subgroupCongr hK0.symm).trans e⟩⟩
    rw [hc0] at hcard
    simpa using hcard
  · have hsw := isSwap_of_card_commV_eq_two (by omega : 5 ≤ n) θ β hequiv (hker ▸ le_rfl) ha0 htr
    have hn5' : n ≠ 5 := fun hn' =>
      not_central_in_sylow_of_isSwap (Or.inl hn') θ ha0 hsw hTX0 hTp hTi0 (fun t ht => hcent t ht)
    have hn8' : n ≠ 8 := fun hn' =>
      not_central_in_sylow_of_isSwap (Or.inr hn') θ ha0 hsw hTX0 hTp hTi0 (fun t ht => hcent t ht)
    exact Or.inr ⟨n, by omega, (MulEquiv.subgroupCongr hK0.symm).trans θ, hsw⟩
  · have hsw := isSwap_of_card_commV_eq_two (by omega : 5 ≤ n) θ β hequiv
      (hker ▸ bot_le) ha0 htr
    have hn8' : n ≠ 8 := fun hn' =>
      not_central_in_sylow_of_isSwap (Or.inr hn') θ ha0 hsw hTX0 hTp hTi0 (fun t ht => hcent t ht)
    exact Or.inr ⟨n, by omega, (MulEquiv.subgroupCongr hK0.symm).trans θ, hsw⟩

theorem stmt6_2_13_of_b56 (hKu : StmtKuM22) (h56 : AsB56) (h612 : Stmt6_1_2) (h616 : Stmt6_1_6)
    (h6110 : Stmt6_1_10) (h621 : Stmt6_2_1) (h622 : Stmt6_2_2) (h625 : Stmt6_2_5)
    (h626 : Stmt6_2_6) (h627 : Stmt6_2_7) (h629 : Stmt6_2_9) (h6210 : Stmt6_2_10)
    (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) : Stmt6_2_13 :=
  stmt6_2_13_of_lemmasG hKu ⟨g64Out_of_b56 h56, h612, h616, h6110, h621, h622, h625, h626, h627,
    h629, h6210, h6211, h6212⟩

end CFSG.Quasithin.H13.GM22
