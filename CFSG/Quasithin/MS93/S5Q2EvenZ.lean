module

public import CFSG.Quasithin.MS93.S5Q2JOff

public section

namespace CFSG.Quasithin.MS93.S5Q2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

@[expose] def Q2EvenZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L 1 F a → Xq M = Uq M T L ⊔ Zq M L →
      ¬ Zq M L ≤ Subgroup.centralizer (M : Set G) →
      ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
        (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h 2 a δ l →
        S5.vIm h.le a (S5.jOff h.le L 2 (baseA _) (baseB _)) ≤ commutator (MSP.Sp4 F) →
        ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
            (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) : Set (puAmalgam h.le).Universal) ≤
          ZM _ (baseA (puAmalgam h.le))

namespace UC

variable (h : PUHyp M T L)

private theorem stabCenter_inf_xm_le_zm' {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ ≤ ZM _ ρ := by
  refine sup_le (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L ρ).trans
    (stab_le_normalizer_zm _ _))) ?_
  rintro x ⟨hxX, hxZ⟩
  refine zh_le_zm _ hρε (Subgroup.subset_closure ⟨⟨qv_le_qv _ h.hyp20 hρ hρε (xm_le_qv _ ρ hxX),
    Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, (isElemAbelian_xm _ ρ).2 x hxX⟩)
  obtain ⟨w, hw, rfl⟩ := hxZ
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, qv_le_stab_of_adj _ hρε.symm hy⟩))

private theorem xm_le_zm_of_le {ρ ε : Vtx (puAmalgam h.le)} (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hC : Zq M L ≤ Subgroup.centralizer (M : Set G)) (hρ : IsMVtx _ ρ)
    (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) : XM _ ρ ≤ ZM _ ρ := by
  rw [S5Q2.xm_eq_uSub_sup_centralizer h hXU hρ]
  exact (sup_le_sup_left (le_inf inf_le_left (S5Q2.xm_inf_centralizer_le_stabCenter h hC hρ))
    _).trans (stabCenter_inf_xm_le_zm' h hρ hρε)

theorem zm_inf_xm_inf_centralizer_jOff_le_zm (hZ : Q2EvenZ) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {k : ℕ} (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) :
    ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
          Set (puAmalgam h.le).Universal) ≤
      ZM _ (baseA (puAmalgam h.le)) := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  by_cases hC : Zq M L ≤ Subgroup.centralizer (M : Set G)
  · exact (inf_le_left.trans inf_le_right).trans (xm_le_zm_of_le h hXU hC hα hαβ)
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    by_cases hJe : S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
        commutator (MSP.Sp4 F)
    · exact hZ G M T L h hmin hb F _ _ a hd hXU hC δ l hβδ (by simpa using hl) hJe
    · refine (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        ((xm_inf_centralizer_jOff_le_of_odd h hd hXU hJe hα hαβ).trans
          (stabCenter_inf_xm_le_zm' h hα hαβ))
  · exact absurd (S5Q2.zq_le_centralizer_of_two_le h hd hk) hC

theorem zm_inf_xm_inf_centralizer_jOff_le_zm' (hZ : Q2EvenZ) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {k : ℕ} (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ XM _ δ ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) δ (baseB _) : Set (puAmalgam h.le).Universal) ≤ ZM _ δ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  by_cases hC : Zq M L ≤ Subgroup.centralizer (M : Set G)
  · exact (inf_le_left.trans inf_le_right).trans (xm_le_zm_of_le h hXU hC hδM hβδ.symm)
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    by_cases hJe : S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
        commutator (MSP.Sp4 F)
    ·
      obtain ⟨g, hg, hgα⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
      have hgβ : g • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hg
      have hgβ' : g⁻¹ • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 (inv_mem hg)
      have hJg : (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)).map
          (MulAut.conj g).toMonoidHom = S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) := by
        have e := S5B.jOff_smul h.le hLn 2 g (baseA (puAmalgam h.le)) (baseB _)
        rw [hgα, hgβ] at e
        rw [← e]
        simpa using hl.1
      have hJg' : S5.jOff h.le L 2 (g⁻¹ • baseA (puAmalgam h.le)) (baseB _) =
          S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _) := by
        have e := S5B.jOff_smul h.le hLn 2 g⁻¹ (baseA (puAmalgam h.le)) (baseB _)
        rw [hgβ'] at e
        rw [e]
        conv_lhs => rw [← hJg]
        rw [map_conj_inv_map_conj]
      have hβδ' : (puAmalgam h.le).treeGraph.Adj (baseB _) (g⁻¹ • baseA (puAmalgam h.le)) := by
        have := (adj_smul _ g⁻¹ (baseB (puAmalgam h.le)) (baseA _)).mpr
          (adj_baseA_baseB (puAmalgam h.le)).symm
        rwa [hgβ'] at this
      have hl' : S5.Case56 h 2 a (g⁻¹ • baseA (puAmalgam h.le)) l :=
        ⟨hJg', hl.2.1, hl.2.2.1, by simpa using hl.2.2.2⟩
      have key := hZ G M T L h hmin hb F _ _ a hd hXU hC _ l hβδ' hl' hJe
      have h2 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) key
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
        Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← zm_smul, ← xm_smul,
        ← PU.centralizer_map_mulEquiv, hJg, ← zm_smul, smul_inv_smul, hgα] at h2
      have e := S5B.jOff_smul h.le hLn 2 g (baseA (puAmalgam h.le)) (baseB _)
      rw [hgα, hgβ, hJg] at e
      simpa [e] using h2
    · refine (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        ((xm_inf_centralizer_jOff_le_of_odd h hd hXU hJe hδM hβδ.symm).trans
          (stabCenter_inf_xm_le_zm' h hδM hβδ.symm))
  · exact absurd (S5Q2.zq_le_centralizer_of_two_le h hd hk) hC

theorem cX_inf_centralizer_inf_zm_le_stabCenter (hZ : Q2EvenZ) (h32 : S32)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) {k : ℕ}
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) :
    XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
          Set (puAmalgam h.le).Universal) ⊓ ZM _ δ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hcent : Zq M L ≤ Subgroup.centralizer (M : Set G) →
      XM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) :
          Set (puAmalgam h.le).Universal) ⊓ ZM _ δ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := fun hC =>
    (inf_le_left.trans inf_le_left).trans (S5Q2.xm_inf_centralizer_le_stabCenter h hC hα)
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
    · by_cases hC : Zq M L ≤ Subgroup.centralizer (M : Set G)
      · exact hcent hC
      by_cases hJe : S5.vIm h.le a (S5.jOff h.le L 2 (baseA (puAmalgam h.le)) (baseB _)) ≤
          commutator (MSP.Sp4 F)
      · rintro r ⟨⟨⟨hrX, hrL⟩, hrJ⟩, hrZ⟩
        have hrZα := zm_inf_xm_inf_centralizer_jOff_le_zm h hZ hmin hb hd hXU hβδ hl
          ⟨⟨hrZ, hrX⟩, hrJ⟩
        exact zm_inf_centralizer_le_stabCenter h hd hα ⟨hrZα, hrL⟩
      · exact inf_le_left.trans (cX_inf_centralizer_jOff_le_stabCenter h hd hJe hα hαβ)
    · exact hcent (S5Q2.X52.zq_le_centralizer_of_ne h hd (h32 G M T L h).2.1 hXU)
  · exact hcent (S5Q2.zq_le_centralizer_of_two_le h hd hk)

end UC

end CFSG.Quasithin.MS93.S5Q2
