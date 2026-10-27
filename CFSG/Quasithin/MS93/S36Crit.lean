module

public import CFSG.Quasithin.MS93.S36Frat

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G]

namespace S36

section TImage

variable {T : Subgroup G}

theorem tImage_mono (ψ : MulAut ↥T) {K K' : Subgroup G} (h : K ≤ K') :
    tImage ψ K ≤ tImage ψ K' :=
  Subgroup.map_mono (Subgroup.map_mono fun _ hx => h hx)

theorem tImage_one {K : Subgroup G} (hK : K ≤ T) : tImage (1 : MulAut ↥T) K = K := by
  rw [tImage]
  have : (K.subgroupOf T).map (1 : MulAut ↥T).toMonoidHom = K.subgroupOf T := by
    ext x
    simp
  rw [this, Subgroup.map_subgroupOf_eq_of_le hK]

theorem tImage_mul (φ ψ : MulAut ↥T) (K : Subgroup G) :
    tImage (φ * ψ) K = tImage φ (tImage ψ K) := by
  rw [tImage, tImage, tImage_subgroupOf]
  congr 1
  rw [Subgroup.map_map]
  rfl

theorem tImage_inv_tImage (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage ψ⁻¹ (tImage ψ K) = K := by
  rw [← tImage_mul, inv_mul_cancel, tImage_one hK]

theorem tImage_tImage_inv (ψ : MulAut ↥T) {K : Subgroup G} (hK : K ≤ T) :
    tImage ψ (tImage ψ⁻¹ K) = K := by
  rw [← tImage_mul, mul_inv_cancel, tImage_one hK]

theorem tImage_commutator (ψ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) (hK' : K' ≤ T) :
    tImage ψ ⁅K, K'⁆ = ⁅tImage ψ K, tImage ψ K'⁆ := by
  rw [tImage, tImage, tImage, commutator_subgroupOf hK hK', Subgroup.map_commutator,
    Subgroup.map_commutator]

theorem le_tImage_inv_iff (ψ : MulAut ↥T) {K K' : Subgroup G} (hK : K ≤ T) (hK' : K' ≤ T) :
    K ≤ tImage ψ⁻¹ K' ↔ tImage ψ K ≤ K' := by
  constructor
  · intro hle
    have := tImage_mono ψ hle
    rwa [tImage_tImage_inv ψ hK'] at this
  · intro hle
    have := tImage_mono ψ⁻¹ hle
    rwa [tImage_inv_tImage ψ hK] at this

end TImage

section Critical

variable [Finite G] {M T L : Subgroup G}

theorem qv_inr (h : PUHyp M T L) (ψ : MulAut ↥T) :
    Qv (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) =
      imM h.le (tImage ψ (pCoreOf 2 M)) := by
  rw [qv_smul, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    imM_map_conj_inr h.le ψ h.pCore_le]

theorem Z0q_le_T (h : PUHyp M T L) : Z0q M T ≤ T := h.Z0q_le_pCoreOf.trans h.pCore_le

theorem isCritical_inr_iff (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    (ψ : MulAut ↥T) :
    IsCritical (puAmalgam h.le) (baseA _)
        ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) ↔
      ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M) := by
  have hiff : ZM (puAmalgam h.le) (baseA _) ≤
        Qv (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) ↔
      Z0q M T ≤ tImage ψ (pCoreOf 2 M) := by
    rw [qv_inr h, puAmalgam.zm_baseA, imM_le_imM_iff h.le (Z0q_le M T)]
  constructor
  · intro hc
    exact hiff.not.mp hc.2.2
  · intro hn
    refine ⟨isMVtx_baseA _, ?_, hiff.not.mpr hn⟩
    rw [hb]
    have hne : baseA (puAmalgam h.le) ≠
        (puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _ := by
      intro heq
      apply hn
      rw [← hiff, ← heq]
      exact zm_le_qv_self _ (isMVtx_baseA _) h.critDist_pos
    exact dist_eq_two_of_adj_adj _ (adj_baseA_baseB _)
      ((puAmalgam.adj_baseB_iff_mulAut h.le _).mpr ⟨ψ, rfl⟩) hne

theorem exists_critical_inr (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2) :
    ∃ ψ : MulAut ↥T, ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M) := by
  obtain ⟨α', hc, hgeo⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos (isMVtx_baseA _)
    (adj_baseA_baseB (puAmalgam h.le))
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 2 := hc.2.1.trans hb
  have hadj : (puAmalgam h.le).treeGraph.Adj (baseB _) α' := by
    have := adj_geo (puAmalgam h.le) (u := baseA _) (w := α') (i := 1) (by omega)
    rwa [hgeo, geo_of_le _ (by omega)] at this
  obtain ⟨ψ, rfl⟩ := (puAmalgam.adj_baseB_iff_mulAut h.le α').mp hadj
  exact ⟨ψ, (isCritical_inr_iff h hb ψ).mp hc⟩

theorem not_le_tImage_iff (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    (ψ : MulAut ↥T) :
    ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M) ↔ ¬ tImage ψ (Z0q M T) ≤ pCoreOf 2 M := by
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hiff : ZM (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) ≤
        Qv (puAmalgam h.le) (baseA _) ↔ tImage ψ (Z0q M T) ≤ pCoreOf 2 M := by
    rw [zm_inr h, hQ, imM_le_imM_iff h.le ((tImage_le ψ _).trans h.le)]
  constructor
  · intro hn
    have hc := (isCritical_inr_iff h hb ψ).mpr hn
    exact hiff.not.mp (ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc).2.2
  · intro hn
    rw [← isCritical_inr_iff h hb ψ]
    refine ms22_iii _ h.hyp20 h.critDist_pos h.centHyp ⟨?_, ?_, hiff.not.mpr hn⟩
    · exact (isMVtx_smul _ _ _).mpr (isMVtx_baseA _)
    · rw [hb]
      have hne : (puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _ ≠
          baseA (puAmalgam h.le) := by
        intro heq
        apply hn
        rw [← hiff, heq]
        exact zm_le_qv_self _ (isMVtx_baseA _) h.critDist_pos
      exact dist_eq_two_of_adj_adj _
        (((puAmalgam.adj_baseB_iff_mulAut h.le _).mpr ⟨ψ, rfl⟩).symm) (adj_baseA_baseB _).symm
        hne

theorem exists_tImage_not_le_Dq (h : PUHyp M T L) {K : Subgroup G} (hKT : K ≤ T)
    (hK : K ≠ ⊥) : ∃ φ : MulAut ↥T, ¬ tImage φ K ≤ Dq M L := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  set C := charClosureIn T K with hC
  have hCD : C ≤ Dq M L := by
    rw [hC, charClosureIn, Subgroup.map_iSup]
    exact iSup_le fun φ => hall φ
  have hCT : C ≤ T := charClosureIn_le T K
  have hCne : C ≠ ⊥ := fun hb => hK (le_bot_iff.mp ((le_charClosureIn hKT).trans hb.le))
  have hchar := charClosureIn_characteristic T K
  have hTn : T ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).1 inferInstance
  have hLn : L ≤ Subgroup.normalizer (C : Set G) := by
    have : L ≤ Subgroup.centralizer (C : Set G) := by
      rw [← Subgroup.le_centralizer_iff]
      exact hCD.trans inf_le_right
    exact this.trans (Subgroup.centralizer_le_normalizer _)
  have hMn : M ≤ Subgroup.normalizer (C : Set G) := by
    rw [h.eq_sup]
    exact sup_le hLn hTn
  exact h.noChar C hCT hCne hchar hMn

theorem Uq_normal (h : PUHyp M T L) : ((Uq M T L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (Uq_le h.L_le)).2 (le_normalizer_Uq h.le_normalizer)

theorem L_normal (h : PUHyp M T L) : (L.subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer

theorem puTrans_Uq_inf_centralizer_inr (h : PUHyp M T L) (ψ : MulAut ↥T) :
    puTrans h.le (Uq M T L) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) ⊓
        Subgroup.centralizer (puTrans h.le L
          ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) :
            Set (puAmalgam h.le).Universal) =
      imM h.le (tImage ψ (Uq M T L ⊓ Subgroup.centralizer (L : Set G))) := by
  rw [puTrans_smul_baseA (Uq_normal h), puTrans_smul_baseA (L_normal h),
    PU.centralizer_map_mulEquiv, ← Subgroup.map_inf _ _ _ (MulAut.conj _).injective,
    ← imM_inf_centralizer h.le _ h.L_le,
    imM_map_conj_inr h.le ψ (inf_le_left.trans ((Uq_le_Z0q h.L_le).trans (Z0q_le_T h)))]

theorem g2U_clauses (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    (hG2 : IsG2U h.le L) {ψ : MulAut ↥T} (hψ : ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M)) :
    tImage ψ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) =
        Uq M T L ⊓ Subgroup.centralizer (L : Set G) ∧
      Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ ⁅Z0q M T, tImage ψ (Z0q M T)⁆ := by
  have hc := (isCritical_inr_iff h hb ψ).mpr hψ
  obtain ⟨h1, h2⟩ := hG2.2.2.2 _ hc
  rw [puTrans_Uq_inf_centralizer_inr h, h.Uq_inf_Zq] at h1
  rw [h.Uq_inf_Zq, zm_inr h, puAmalgam.zm_baseA,
    ← imM_commutator h.le (Z0q_le M T) ((tImage_le ψ _).trans h.le)] at h2
  have hAM : Uq M T L ⊓ Subgroup.centralizer (L : Set G) ≤ M := inf_le_left.trans (Uq_le h.L_le)
  have hψM : tImage ψ (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ M :=
    (tImage_le ψ _).trans h.le
  refine ⟨le_antisymm ((imM_le_imM_iff h.le hψM).mp h1.symm.le)
    ((imM_le_imM_iff h.le hAM).mp h1.le), (imM_le_imM_iff h.le hAM).mp h2⟩

theorem commutator_pCoreOf_le_Dq (h : PUHyp M T L) (hVU : Vq M L = Uq M T L) :
    ⁅pCoreOf 2 M, pCoreOf 2 M⁆ ≤ Dq M L := by
  have hVQ : ⁅Vq M L, pCoreOf 2 M⁆ = ⊥ := by
    rw [hVU, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h.Uq_le_Xq.trans ((PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right)
  have hbot : ∀ H : Subgroup G, H ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) :=
    fun H x _ => Subgroup.mem_normalizer_iff.mpr fun n => by
      simp only [Subgroup.mem_bot]
      constructor
      · rintro rfl
        group
      · intro hn
        have : n = x⁻¹ * (x * n * x⁻¹) * x := by group
        rw [this, hn]
        group
  have h3 : ⁅⁅pCoreOf 2 M, pCoreOf 2 M⁆, L⁆ ≤ ⊥ := by
    refine three_subgroups_le (N := ⊥) (hbot _) (hbot _) (hbot _) ?_ ?_
    · exact hVQ.le
    · rw [Subgroup.commutator_comm L (pCoreOf 2 M)]
      exact hVQ.le
  refine le_inf (commutator_le_of_le le_rfl le_rfl) ?_
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp h3)

theorem uq_inf_dq_eq_bot_of_g2 (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2)
    (hG2 : IsG2U h.le L) (hVU : Vq M L = Uq M T L) : Uq M T L ⊓ Dq M L = ⊥ := by
  rw [h.Uq_inf_Dq]
  by_contra hA
  set A := Uq M T L ⊓ Subgroup.centralizer (L : Set G) with hAdef
  have hAT : A ≤ T := inf_le_left.trans ((Uq_le_Z0q h.L_le).trans (Z0q_le_T h))
  have hAD : A ≤ Dq M L :=
    le_inf (inf_le_left.trans (h.Uq_le_Xq.trans (Xq_le_pCoreOf M))) inf_le_right
  have hQT : pCoreOf 2 M ≤ T := h.pCore_le
  have hDT : Dq M L ≤ T := inf_le_left.trans hQT
  obtain ⟨φ₀, hφ₀⟩ := exists_tImage_not_le_Dq h hAT hA
  set φ := φ₀⁻¹ with hφ
  have hAφ : ¬ A ≤ tImage φ (Dq M L) := by
    rw [hφ, le_tImage_inv_iff φ₀ hAT hDT]
    exact hφ₀
  obtain ⟨ψ, hψ⟩ := exists_critical_inr h hb
  obtain ⟨hψA, hAR⟩ := g2U_clauses h hb hG2 hψ
  have hφZ : Z0q M T ≤ tImage φ (pCoreOf 2 M) := by
    by_contra hn
    obtain ⟨hφA, -⟩ := g2U_clauses h hb hG2 hn
    exact hAφ (hφA.symm.le.trans (tImage_mono φ hAD))
  have hψφZ : tImage ψ (Z0q M T) ≤ tImage φ (pCoreOf 2 M) := by
    have h1 : Z0q M T ≤ tImage (ψ⁻¹ * φ) (pCoreOf 2 M) := by
      by_contra hn
      obtain ⟨hA', -⟩ := g2U_clauses h hb hG2 hn
      apply hAφ
      have h2 : tImage φ A = A := by
        have := congrArg (tImage ψ) hA'
        rwa [← tImage_mul, mul_inv_cancel_left, hψA] at this
      rw [← h2]
      exact tImage_mono φ hAD
    have := tImage_mono ψ h1
    rwa [← tImage_mul, mul_inv_cancel_left] at this
  have hR : ⁅Z0q M T, tImage ψ (Z0q M T)⁆ ≤ tImage φ (Dq M L) := by
    refine (Subgroup.commutator_mono hφZ hψφZ).trans ?_
    rw [← tImage_commutator φ hQT hQT]
    exact tImage_mono φ (commutator_pCoreOf_le_Dq h hVU)
  exact hAφ (hAR.trans hR)

end Critical

end S36

end CFSG.Quasithin.MS93
