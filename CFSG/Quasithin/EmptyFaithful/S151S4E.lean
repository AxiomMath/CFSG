module

public import CFSG.Quasithin.EmptyFaithful.S151S4D
public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.S151S4

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem star_general_sub (h118 : TheoremC118) (h126 : TheoremC126)
    {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hctx : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂)
    (h17 : Lemma15117Concl T M Z₁) (h18 : Lemma15118Concl T Mc M Z₁)
    {R H : Subgroup G} (hbaum : baum (s1516 T Z₁) ≤ R) (hRS : R ≤ s1516 T Z₁)
    (hHG : H ≤ g1_1516 Z₁) (hRsyl : IsSylowTwoOf R H) (hpc : pCoreOf 2 H ≠ ⊥)
    (hchar : CharTwo H) (hmin : IsMinParabolicOf H H) (hno3 : ¬ C126Third H R) :
    H ≤ M ∨ H ≤ mZ1516 Mc Z₁ := by
  have hq := hctx.qtfe
  have hSet := hctx.setting
  have hMf := hctx.mf
  set S := s1516 T Z₁ with hSdef
  have hSQ : IsSQTKTC H :=
    ⟨kGroup_of_pCoreOf_ne_bot hq.qtke hq.simple hq.nonabelian hpc,
      stronglyQuasithin_of_pCoreOf_ne_bot hq.qtke hpc⟩
  obtain ⟨C₁, C₂, hC⟩ := exists_isGNChoice (G := G) h118
  have hT2 : IsPGroup 2 T := hq.sylow.1
  have hS2 : IsPGroup 2 S := h18.four.2.1
  have hR2 : IsPGroup 2 R := hS2.to_le hRS
  have hZ₁T : Z₁ ≤ T := hSet.z1_le_T hq hMf
  have hT0 : T ≠ ⊥ := ne_bot_of_le_ne_bot hSet.z1_ne hZ₁T
  have hST : S ≤ T := s1516_le T Z₁
  obtain ⟨h1ne, h1Z, -⟩ := hC.pair T hT2 hT0
  have hC1T : C₁ T ≤ centerOf T := h1Z.trans (C1GN.omegaOneCenterOf_le_centerOf T)
  have hC1baum : C₁ T ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  have hcTS : centerOf T ≤ S := fun z hz =>
    ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_iff.mp hz.2 y (hZ₁T hy)⟩
  have hS0 : S ≠ ⊥ := ne_bot_of_le_ne_bot h1ne (hC1T.trans hcTS)
  have hbS : baum S = baum T := h17.baumS
  have hC1R : C₁ T ≤ R := hC1baum.trans (hbS ▸ hbaum)
  have hR0 : R ≠ ⊥ := ne_bot_of_le_ne_bot h1ne hC1R
  have hbR : baum S = baum R := baum_eq_of_le hbaum hRS
  have hc1R : C₁ T ≤ C₁ R := by
    rw [hC.c1_eq R hR2 hR0, ← hbR, hbS]
    refine le_inf ?_ ?_
    · intro z hz
      exact ⟨hC1R hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_iff.mp (hC1T hz).2 y (hST (hRS hy))⟩
    · calc C₁ T = centerOf T ⊓ C₁ (baum T) := hC.c1_eq T hT2 hT0
        _ ≤ C₁ (baum T) := inf_le_right
  have hc2R : C₂ R = C₂ S := by
    rw [hC.c2_eq R hR2 hR0, hC.c2_eq S hS2 hS0, ← hbR]
  rcases h126 G C₁ C₂ hC H R hSQ hRsyl hchar hmin with h1 | h2 | h3
  · right
    have hHc : ∀ y ∈ C₁ R, ∀ h ∈ H, y * h = h * y := fun y hy h hh =>
      (Subgroup.mem_centralizer_iff.mp (h1 hy).2 h hh).symm
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1ne
    have hzZ : (z : G) ∈ quasithinOmegaOneCenter T := h1Z z.2
    have hzC : (z : G) ∈ C₁ R := hc1R z.2
    intro h hh
    have hhC : h ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hHc (z : G) hzC h hh
    exact ⟨hHG hh, ya7_centralizer_le_mc hq hzZ (fun h => hz1 (Subtype.ext h)) hhC⟩
  · left
    obtain ⟨-, -, -, h2ne, h2B, h2char, -⟩ := hC.pair S hS2 hS0
    have hNle : Subgroup.normalizer (C₂ S : Set G) ≤ M := by
      refine le_trans ?_ h17.cgs
      exact le_iSup_of_le (C₂ S) (le_iSup_of_le h2B (le_iSup_of_le h2ne
        (le_iSup_of_le h2char le_rfl)))
    rw [hc2R] at h2
    exact fun h hh => hNle (h2 hh)
  · exact (hno3 h3).elim

theorem l2_isBlock_of_baum (h118 : TheoremC118) (h126 : TheoremC126)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L) (hLM : ¬ L ≤ M)
    (hchar : CharTwo L) {n : ℕ} (hn : 2 ≤ n) (hLn : IsPSL 2 2 n (↥L ⧸ CFSG.pCore 2 ↥L))
    (hbaum : baum (s1516 T Z₁) ≤ Subgroup.normalizer (L : Set G)) :
    IsBlock2 (L ⊔ s1516 T Z₁) L := by
  by_contra hnb
  set S := s1516 T Z₁ with hSdef
  set R := S ⊓ Subgroup.normalizer (L : Set G) with hRdef
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hR2 : IsPGroup 2 ↥R := hS2.to_le inf_le_left
  have hRN : R ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hsylS : IsSylowTwoOf (S ⊓ L) L := lemma_15_1_20_sylow hc.h18.four hc.hL
  have hRL : R ⊓ L = S ⊓ L := by
    ext x
    constructor
    · rintro ⟨⟨hxS, _⟩, hxL⟩
      exact ⟨hxS, hxL⟩
    · rintro ⟨hxS, hxL⟩
      exact ⟨⟨hxS, Subgroup.le_normalizer hxL⟩, hxL⟩
  have hsyl : IsSylowTwoOf (R ⊓ L) L := by
    rw [hRL]
    exact hsylS
  have hLloc : L ∈ cComp (L ⊔ S) := cComp_of_isLocal hc.hL.mem.2
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hLloc
  have hL0 : L ≠ ⊥ := ne_bot_of_mem_cComp hLloc
  have hsub : (L.subgroupOf (L ⊔ S)).IsSubnormal :=
    (isSubnormal_iff_subgroupOf le_sup_left).mp (subnormal_of_mem_cComp hLloc)
  have hno3 : ¬ C126Third (L ⊔ R) R := fun h3 =>
    hnb ⟨isShort2_of_c126Third hRN hR2 hperf hc.hL.quasi h3, le_sup_left, hsub⟩
  have hLG : L ≤ g1_1516 Z₁ := hc.hL.mem.1
  have hHG : L ⊔ R ≤ g1_1516 Z₁ := sup_le hLG (inf_le_left.trans (s1516_le_g1 T Z₁))
  have hOp : pCoreOf 2 L ≠ ⊥ := by
    intro h
    apply hL0
    rw [eq_bot_iff]
    intro x hx
    have h1 : x ∈ pCoreOf 2 L := hchar ⟨hx, by
      rw [h]
      exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Subgroup.mem_bot.mp hy]
        simp⟩
    rw [h] at h1
    exact h1
  have hpc : pCoreOf 2 (L ⊔ R) ≠ ⊥ := by
    have hHN : L ⊔ R ≤ Subgroup.normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
      sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
        (fun s hs => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hRN hs))
    have h2 : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ R) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) hHN
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    exact ne_bot_of_le_ne_bot hOp h2
  have hcharH : CharTwo (L ⊔ R) := zb_charTwo_sup hRN hR2 hchar
  have hmin : IsMinParabolicOf (L ⊔ R) (L ⊔ R) := l2_isMinParabolic hn hLn hR2 hRN hsyl
  have hRsyl : IsSylowTwoOf R (L ⊔ R) := sylow_sup_of_normalizes hRN hR2 hsyl
  rcases star_general_sub h118 h126 hc.ctx hc.h17 hc.h18 (R := R) (H := L ⊔ R)
      (le_inf (C1GN.baum_le S) hbaum) inf_le_left hHG hRsyl hpc hcharH hmin hno3 with h | h
  · exact hLM (le_sup_left.trans h)
  · exact hc.hL.not_le (le_sup_left.trans h)

end CFSG.Quasithin.S151S4
