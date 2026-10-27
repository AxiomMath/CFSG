module

public import CFSG.Quasithin.MS93.S512ZStmt
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S512TStmt
public import CFSG.Quasithin.MS93.S512TThree

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512R

@[expose] def Three56F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le),
        S5B.IsChain512Sel h (2 ^ k) a (S5.Opp56 h (2 ^ k) a) α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        ∀ l : Submodule F (MSP.V4 F),
          S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
          S5.Concl56 h (2 ^ k) a α' l g x →
          (μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
            μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) →
          (μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 →
            ¬ ZM _ (x • α') ≤ Subgroup.normalizer
              (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
                XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal)) →
          (μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 →
            ¬ ZM _ (x⁻¹ • α') ≤ Subgroup.normalizer
              (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
                XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal)) →
          (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k

section Smul

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem zm_le_normalizer_smul (h : PUHyp M T L) {w : (puAmalgam h.le).Universal}
    (hw : w ∈ stab _ (baseA (puAmalgam h.le))) {α' μ γ : Vtx (puAmalgam h.le)}
    (hZ : ZM _ α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ γ) ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) :
        Set (puAmalgam h.le).Universal)) :
    ZM _ (w • α') ≤ Subgroup.normalizer
      (((S5.uSub h.le L (w • μ) ⊓ Qv _ (w • γ)) ⊔ XM _ (baseA (puAmalgam h.le)) :
        Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hX : XM _ (baseA (puAmalgam h.le)) =
      (XM _ (baseA (puAmalgam h.le))).map (MulAut.conj w).toMonoidHom := by
    rw [← xm_smul, (mem_stab _).1 hw]
  have e : ((S5.uSub h.le L (w • μ) ⊓ Qv _ (w • γ)) ⊔ XM _ (baseA (puAmalgam h.le)) :
      Subgroup _) = ((S5.uSub h.le L μ ⊓ Qv _ γ) ⊔ XM _ (baseA (puAmalgam h.le))).map
        (MulAut.conj w).toMonoidHom := by
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj w).injective, ← hX,
      S5B.uSub_smul h.le hLn, qv_smul]
  rw [e, normalizer_map_conj, zm_smul]
  exact Subgroup.map_mono hZ

theorem commutator_zm_smul_le_stabCenter (h : PUHyp M T L) {w : (puAmalgam h.le).Universal}
    (hw : w ∈ stab _ (baseA (puAmalgam h.le))) {u v : Vtx (puAmalgam h.le)}
    (huv : ⁅ZM (puAmalgam h.le) u, ZM (puAmalgam h.le) v⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le))) :
    ⁅ZM (puAmalgam h.le) (w • u), ZM (puAmalgam h.le) (w • v)⁆ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  rw [zm_smul, zm_smul, ← Subgroup.map_commutator]
  rintro _ ⟨z, hz, rfl⟩
  have hc := S510.commute_of_mem_stabCenter (huv hz) hw
  have e : (MulAut.conj w).toMonoidHom z = z := by
    change w * z * w⁻¹ = z
    rw [hc]
    group
  rw [e]
  exact huv hz

end Smul

theorem s512ThreeF_holds (h32 : S32) (h54 : S54) (h58 : S5B.S58) (hone : S512Z.OneCF)
    (hA2 : S512T.ThreeAlt2) (h356 : Three56F) : S5B.S512ThreeF := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS hq1 hq
  have hch := S5B.isChain512Sel_subset hchS
  have hZ := hone G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS μ₁
    (S5B.lamSel_subset hchS.2.2.2.2.1)
  by_cases h56 : ∃ l, S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l
  ·
    obtain ⟨g, x, hg, hx, hconc, hμeq⟩ := hch.2.2.2.2.1
    obtain ⟨l, hl, hc56⟩ : ∃ l, S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l ∧
        S5.Concl56 h (2 ^ k) a α' l g x := by
      rcases hconc with ⟨hno, -⟩ | ⟨l, hl, hc⟩
      · obtain ⟨l, hl⟩ := h56
        exact absurd hl (hno l)
      · exact ⟨l, hl, hc⟩
    by_cases hc1 : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∧
        ZM _ (x • α') ≤ Subgroup.normalizer
          (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
            XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal)
    · exact S512T.three_of_le_normalizer h32 h58 h hmin hb4 hd hch hq
        (S512T.le_normalizer_of_concl56_g_of h54 h hmin hb4 hd hch hZ hq1 hq hl hg hc56
          hc1.1 hc1.2)
    by_cases hc2 : μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∧
        ZM _ (x⁻¹ • α') ≤ Subgroup.normalizer
          (((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
            XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set (puAmalgam h.le).Universal)
    · exact S512T.three_of_le_normalizer h32 h58 h hmin hb4 hd hch hq
        (S512T.le_normalizer_of_concl56_x_of h54 h hmin hb4 hd hch hZ hq1 hq hl hg hx hc56
          hc2.1 hc2.2)
    exact h356 G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hchS hq1 hq l hl g hg x hx hc56 hμeq
      (fun h1 h2 => hc1 ⟨h1, h2⟩) (fun h1 h2 => hc2 ⟨h1, h2⟩)
  push Not at h56
  obtain ⟨g, x, hg, hx, hconc, hμeq⟩ := hch.2.2.2.2.1
  have hc55 : S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x := by
    rcases hconc with ⟨-, h1⟩ | ⟨l, hl, -⟩
    · exact h1
    · exact absurd hl (h56 l)
  rcases h54 G M T L h hmin (by omega) k F _ _ a hd with ⟨-, hline, -⟩ | ⟨-, hJT, -⟩
  · by_cases hL : puTrans h.le L (baseA _) ≤
        S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
          S5.zHat _ (baseA _) α'
    · exact S512T.three_of_le_normalizer h32 h58 h hmin hb4 hd hch hq
        (S512T.le_normalizer_of_le_sup_of h54 h hmin hb4 hd hch hZ hq hL)
    ·
      have halt : ¬ puTrans h.le L (baseA _) ≤
          (S5.jOff h.le L (2 ^ k) (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
              (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA _) α') ⊓
            (S5.rconj x (S5.jOff h.le L (2 ^ k) (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
              (g⁻¹ • baseB (puAmalgam h.le))) ⊔ S5.zHat _ (baseA _) α') :=
        fun h1 => hL (S512T.le_sup_of_alt1 h hb4 hch hg hx hμeq h1)
      by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
      · exfalso
        have hX := S512T.xm_eq_uSub_sup_of_xq h hXU
        obtain ⟨-, -, hc3⟩ := hc55
        tauto
      · by_cases hTY : Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤
            Subgroup.normalizer ((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) :
              Subgroup _) : Set (puAmalgam h.le).Universal)
        · exact S512T.three_of_le_normalizer h32 h58 h hmin hb4 hd hch hq
            ((puTrans_le_stab h.le L _).trans
              (S512T.stab_le_normalizer_of_qv_of h hb4 hd hch hZ hq1 h56 hTY))
        · exact hA2 G M T L h hmin hb4 k F _ _ a hd α' ν μ₁ μ₂ hch hq1 hq h56 hline hXU g hg x
            hx hc55 hμeq hL hTY
  · exact S512T.three_of_le_normalizer h32 h58 h hmin hb4 hd hch hq
      ((puTrans_le_stab h.le L _).trans
        (S512T.stab_le_normalizer_of_point_of h54 h hmin hb4 hd hch hZ hq1 hq h56 hJT))

end S512R

end CFSG.Quasithin.MS93
