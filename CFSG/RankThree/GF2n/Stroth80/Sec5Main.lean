module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SL
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec3Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.B_le_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    B ≤ Vt M (LB M Q B) B Z t := by
  have h := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) M.one_mem
    (show t ∈ conjSubgroup (1 : G) (LB M Q B) by rw [conjSubgroup_one]; exact ht)
  rwa [conjSubgroup_one] at h

theorem Ctx.conj_Rt_le_Vt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
  refine sup_le ?_ sec39_Z_le_Vt
  have hn : conjSubgroup r (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr)
  rw [← hn]
  exact Subgroup.map_mono (hc.B_le_Vt ht)

theorem Ctx.Vt_le_Q1 (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    Vt M (LB M Q B) B Z t ≤ Q1 hc t := by
  have htM : t ∈ M := hc.LB_le_M ht
  refine sec39_Vt_le (fun z hz => ?_) (fun m hm htm x hx => ?_)
  · refine (hc.mem_Q1_iff htM).mpr ⟨hc.Z_le_Q hz, ?_⟩
    have := hc.LB_centralizes_Z ht z hz
    rw [commutatorElement_def, this]
    simp
  · have hcm := hc.conj_of_mem hm
    refine (hc.mem_Q1_iff htM).mpr ⟨hcm.le hx, ?_⟩
    have htL : t ∈ LB M Q (conjSubgroup m B) := by rw [hc.LB_conj hm]; exact htm
    exact hcm.comm_B_mem_Z htL hx

theorem stroth_5_2c_of_chi (h : Stroth310ChiStatement) : Stroth52cStatement := by
  intro G _ _ M Q Z B hc n t hs hnat R V W hR hV hW
  subst hR hV hW
  obtain ⟨h1, h2⟩ := h G M Q Z B hc n t hs (Or.inr hnat)
  have := hc.isChiIso_Q1_Ut hs.mem
  rw [h2, h1]
  exact this

theorem stroth_5_3e_of_chi (h : Stroth310ChiStatement) : Stroth53eStatement := by
  intro G _ _ M Q Z B hc n t hs hnat R V W hR hV hW
  subst hR hV hW
  obtain ⟨h1, h2⟩ := h G M Q Z B hc n t hs (Or.inl hnat)
  have := hc.isChiIso_Q1_Ut hs.mem
  rw [h2, h1]
  exact this

theorem stroth310Chi_of_not_le_QB (h34 : Stroth34Statement)
    (h : Stroth310NotQBStatement) : Stroth310ChiStatement := by
  intro G _ _ M Q Z B hc n t hs hnat
  exact hc.Vt_eq_Ut_and_Wt_eq_Q1_of_not_le_QB
    (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1 hs.mem hs.notQ
    (h G M Q Z B hc n t hs hnat)

theorem stroth_5_2c (h34 : Stroth34Statement) (h : Stroth310NotQBStatement) :
    Stroth52cStatement :=
  stroth_5_2c_of_chi (stroth310Chi_of_not_le_QB h34 h)

theorem stroth_5_3e (h34 : Stroth34Statement) (h : Stroth310NotQBStatement) :
    Stroth53eStatement :=
  stroth_5_3e_of_chi (stroth310Chi_of_not_le_QB h34 h)

end CFSG.RankThree.GF2n.Stroth80
