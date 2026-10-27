module

public import CFSG.Quasithin.MS93.S5BStmt
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S5BEqv
public import CFSG.Quasithin.MS93.S5BXZ

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5B

theorem isSumOfNaturalModulesVia_restrict {G : Type} [Group G] {A B V Z : Subgroup G}
    (hAB : A ≤ B) {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥B →* ↥Γ} {dual : Bool} {k : ℕ}
    (hα : IsSumOfNaturalModulesVia B V Z α dual k) :
    IsSumOfNaturalModulesVia A V Z (α.comp (Subgroup.inclusion hAB)) dual k := by
  obtain ⟨hN, hZV, β, hβs, hβk, hβe⟩ := hα
  exact ⟨fun a ha => hN (hAB ha), hZV, β, hβs, hβk,
    fun a u v huv i => hβe (Subgroup.inclusion hAB a) u v huv i⟩

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section ZHat

variable (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}

include h in
theorem commutator_zHat_le_critR (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {t₁ t₂ t₃ : (puAmalgam h.le).Universal}
    (ht : S5.IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃)
    (hn : t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α') :
    ⁅Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) ⊓
        Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _),
      S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤ critR _ (baseA (puAmalgam h.le)) α' := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hd := hc.2.1
  set R := critR (puAmalgam h.le) (baseA _) α' with hR
  set Zh := S5.zHat (puAmalgam h.le) (baseA _) α' with hZh
  have hZhZ : Zh ≤ ZM _ α' := inf_le_left
  have hZht : Zh ≤ Subgroup.centralizer ({t₃} : Set (puAmalgam h.le).Universal) :=
    S5.zHat_le_centralizer ht hn
  have hQZ' : Qv _ α' ≤ Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set _) :=
    (qv_le_centralizer_xm _ α').trans (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hα'))
  have hcr' := ms22_iii _ hyp hb0 hC hc
  have hZαst : ZM (puAmalgam h.le) (baseA _) ≤ stab _ α' := by
    have hlt : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ α' (baseA (puAmalgam h.le)) 1) <
        critDist (puAmalgam h.le) := by
      rw [SimpleGraph.dist_comm, dist_geo_right _ (by rw [SimpleGraph.dist_comm]; omega),
        SimpleGraph.dist_comm, hd]
      omega
    exact (zm_le_qv_of_dist_lt _ hα hlt).trans (qv_le_stab_of_adj _
      (adj_geo_one_of_isCritical _ hb0 hcr').symm)
  have hRZ' : R ≤ ZM _ α' := by
    rw [hR, critR, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hZαst.trans (stab_le_normalizer_zm _ _))
  have hZ'st : ZM (puAmalgam h.le) α' ≤ stab _ (baseA _) := by
    have hlt : (puAmalgam h.le).treeGraph.dist α' (geo _ (baseA (puAmalgam h.le)) α' 1) <
        critDist (puAmalgam h.le) := by
      rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd]
      omega
    exact (zm_le_qv_of_dist_lt _ hα' hlt).trans (qv_le_stab_of_adj _
      (adj_geo_one_of_isCritical _ hb0 hc).symm)
  have hRZ : R ≤ ZM _ (baseA (puAmalgam h.le)) :=
    commutator_le_left_of_le_normalizer (hZ'st.trans (stab_le_normalizer_zm _ _))
  have hZZ : ZM (puAmalgam h.le) (baseA _) ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) (baseA _) : Set _) :=
    (zm_le_qv_self _ hα hb0).trans ((qv_le_centralizer_xm _ _).trans
      (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hα)))
  have hZαR : ZM (puAmalgam h.le) (baseA _) ≤ Subgroup.centralizer (R : Set _) :=
    hZZ.trans (Subgroup.centralizer_le hRZ)
  have hQR : Qv _ α' ≤ Subgroup.centralizer (R : Set (puAmalgam h.le).Universal) :=
    hQZ'.trans (Subgroup.centralizer_le hRZ')
  let S : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {w | w ∈ Subgroup.centralizer (R : Set _) ∧ ∀ z ∈ Zh, w * z * w⁻¹ * z⁻¹ ∈ R}
      one_mem' := ⟨one_mem _, fun z _ => by simp⟩
      mul_mem' := by
        rintro w₁ w₂ ⟨hw₁, h₁⟩ ⟨hw₂, h₂⟩
        refine ⟨mul_mem hw₁ hw₂, fun z hz => ?_⟩
        have e : w₁ * w₂ * z * (w₁ * w₂)⁻¹ * z⁻¹ =
            (w₁ * (w₂ * z * w₂⁻¹ * z⁻¹) * w₁⁻¹) * (w₁ * z * w₁⁻¹ * z⁻¹) := by group
        rw [e]
        have hc₁ : w₁ * (w₂ * z * w₂⁻¹ * z⁻¹) * w₁⁻¹ = w₂ * z * w₂⁻¹ * z⁻¹ := by
          rw [← Subgroup.mem_centralizer_iff.1 hw₁ _ (h₂ z hz), mul_inv_cancel_right]
        rw [hc₁]
        exact mul_mem (h₂ z hz) (h₁ z hz)
      inv_mem' := by
        rintro w ⟨hw, h₁⟩
        refine ⟨inv_mem hw, fun z hz => ?_⟩
        have e : w⁻¹ * z * w⁻¹⁻¹ * z⁻¹ = w⁻¹ * (w * z * w⁻¹ * z⁻¹)⁻¹ * w := by group
        rw [e]
        have hc₁ : w⁻¹ * (w * z * w⁻¹ * z⁻¹)⁻¹ * w = (w * z * w⁻¹ * z⁻¹)⁻¹ := by
          have := Subgroup.mem_centralizer_iff.1 (inv_mem hw) _ (inv_mem (h₁ z hz))
          rw [← this, inv_mul_cancel_right]
        rw [hc₁]
        exact inv_mem (h₁ z hz) }
  have hZS : ZM (puAmalgam h.le) (baseA _) ⊔ Qv _ α' ≤ S := by
    refine sup_le (fun z' hz' => ⟨hZαR hz', fun z hz => ?_⟩) (fun q hq => ⟨hQR hq, fun z hz => ?_⟩)
    · rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hz' (hZhZ hz)
    · have : z * q = q * z := Subgroup.mem_centralizer_iff.1 (hQZ' hq) z (hZhZ hz)
      rw [← this, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  obtain ⟨-, -, -, -, -, -, -, h12, h123⟩ := ht
  have hclos : Subgroup.closure ({t₁, t₂, t₃} : Set (puAmalgam h.le).Universal) ≤ S := by
    rw [Subgroup.closure_le]
    intro t htt
    rcases htt with rfl | rfl | rfl
    · exact hZS (h12 ▸ Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
    · exact hZS (h12 ▸ Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
    · have ht3 : t ∈ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) ⊓
          Subgroup.centralizer (R : Set _) ⊔ Qv _ α' :=
        h123 ▸ Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      refine ⟨(sup_le inf_le_right hQR) ht3, fun z hz => ?_⟩
      have : t * z = z * t := Subgroup.mem_centralizer_iff.1 (hZht hz) t rfl
      rw [this, mul_inv_cancel_right, mul_inv_cancel]
      exact one_mem _
  have hle : Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1) ⊓ Subgroup.centralizer (R : Set _) ≤ S :=
    le_sup_left.trans (h123.le.trans (sup_le hclos (le_sup_right.trans hZS)))
  rw [Subgroup.commutator_le]
  intro w hw z hz
  exact (hle hw).2 z hz

end ZHat

section XZ

theorem zq_le_centralizer (hq2 : Q2Cent) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) :
    Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    exact hq2 G M T L h hmin hb F _ _ a hd
  · rw [Subgroup.le_centralizer_iff]
    refine (eq_sup_pCoreOf h hd hk).le.trans (sup_le ?_ ?_)
    · exact Subgroup.le_centralizer_iff.1 inf_le_right
    · refine Subgroup.le_centralizer_iff.1 (inf_le_left.trans ?_)
      exact (PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M)).trans inf_le_right

theorem zq_le_z0q (h : PUHyp M T L) (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    Zq M L ≤ Z0q M T := by
  refine le_trans ?_ (le_normalClosureIn (PU.omegaOneCenterOf_le T |>.trans h.le))
  rw [h.omegaOneCenterOf_eq]
  exact le_inf inf_le_left (hZc.trans (Subgroup.centralizer_le h.le))

omit [Finite G] in
theorem imM_sup_of_le (hTM : T ≤ M) {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM (K ⊔ K') = imM hTM K ⊔ imM hTM K' := by
  rw [imM, imM, imM, ← Subgroup.map_sup, Subgroup.subgroupOf_sup hK hK']

theorem xm_eq_uSub_sup (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    XM _ (baseA (puAmalgam h.le)) =
      S5.uSub h.le L (baseA _) ⊔ XM _ (baseA (puAmalgam h.le)) ⊓ stabCenter _ (baseA _) := by
  set C := M ⊓ Subgroup.centralizer (M : Set G) with hC
  have hZC : Zq M L ≤ Xq M ⊓ C := le_inf inf_le_left (le_inf (inf_le_left.trans (Xq_le M)) hZc)
  have hM : Xq M = Uq M T L ⊔ Xq M ⊓ C := by
    apply le_antisymm
    · calc Xq M = Uq M T L ⊔ Zq M L := hXU
        _ ≤ Uq M T L ⊔ Xq M ⊓ C := sup_le_sup_left hZC _
    · exact sup_le h.Uq_le_Xq inf_le_left
  have hsup := imM_sup_of_le h.le (Uq_le (T := T) h.L_le)
    (inf_le_left.trans (Xq_le M) : Xq M ⊓ C ≤ M)
  have hinf := imM_inf h.le (Xq M) C
  rw [xm_baseA_eq h, uSub_baseA h, stabCenter_baseA h.le, ← hC, ← hinf, ← hsup, ← hM]

theorem xm_eq_zm (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    XM _ (baseA (puAmalgam h.le)) = ZM _ (baseA (puAmalgam h.le)) := by
  have hM : Xq M = Z0q M T := by
    refine le_antisymm ?_ h.Z0q_le_Xq
    rw [hXU]
    exact sup_le (Uq_le_Z0q h.L_le) (zq_le_z0q h hZc)
  rw [xm_baseA_eq h, puAmalgam.zm_baseA, hM]

end XZ

end S5B

end CFSG.Quasithin.MS93
