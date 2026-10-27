module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Blk
public import CFSG.Quasithin.Vol2.Ch3zStep
public import CFSG.Quasithin.Vol2.Ch3zGood
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Plus

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z

section Setting

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem Setting.kerIn_le_centralizerMod (hB69 : B69Struct) (h : Setting H T M₂ U A)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    kerIn M₂ H ≤ centralizerMod L H N := by
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  obtain ⟨𝓗, hctx⟩ := h.blkCtx hB69 hstep hnc
  have hbot := BlkCtx.kerIn_eq_bot hctx (chiefAut_pCoreOf_eq_bot hstep h.UH hE)
  intro g hg
  have hgH : g ∈ H := h.mp.kerIn_le_H hg
  have hmem : chiefPsi hHL hHN ⟨g, hgH⟩ ∈
      kerIn (chiefImg hHL hHN M₂) (chiefAut H L N) := by
    intro b hb
    obtain ⟨h', hh'⟩ := chiefHom_surjective hHL hHN ⟨b, hb⟩
    have hb' : b = chiefPsi hHL hHN h' := congrArg Subtype.val hh'.symm
    rw [hb']
    have : chiefPsi hHL hHN h' * chiefPsi hHL hHN ⟨g, hgH⟩ * (chiefPsi hHL hHN h')⁻¹ =
        chiefPsi hHL hHN (h' * ⟨g, hgH⟩ * h'⁻¹) := by simp
    rw [this]
    have h1 : (h' : G) * g * (h' : G)⁻¹ ∈ M₂ := (mem_kerIn.mp hg) (h' : G) h'.2
    have h2 : h' * ⟨g, hgH⟩ * h'⁻¹ ∈ M₂.subgroupOf H := h1
    exact Subgroup.mem_map_of_mem (chiefPsi hHL hHN) h2
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (chiefHom_eq_one_iff hHL hHN hNL ⟨g, hgH⟩).mp (Subtype.ext hmem)

end Setting

@[expose] def Lemma319Common : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M M₀ H V : Subgroup G, InM T M → ∀ h : Hyp315Base T M M₀ H V, Hyp315.CaseII M H V →
      qInt M₀ V h.reduced.2.2.1 = 2 → IsUniqueM M₀ M → V ≤ pCoreOf 2 H → ¬ IsDualFFOn M₀ V →
      Concl319 T M V H False →
      MinParabolic H T (H ⊓ M) ∧ IsSQTKSub H ∧ conjClosure V H ≤ T ∧
        (∀ A : Subgroup G, IsMinOffender T H V A →
          Ch3z.Setting H T (H ⊓ M) (conjClosure V H) A) ∧
        (∃ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N ∧ ¬ IsCentralStep H L N ∧
          ∃ z ∈ V, z ∈ N ∧ z ∉ L ∧ ∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ L) ∧
        (∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
          centralizerMod L H N = kerIn (H ⊓ M) H)

theorem lemma319Common_of_inputs (hB69 : B69Struct) : Lemma319Common := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hsq : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hUe := hconcl.elemAbelian
  have hUT : conjClosure V H ≤ T := conjClosure_le_T hD h.le_pCore
  have hRT := h.pCoreOf_le hT
  have hTH : T ≤ H := h.hStar.1.1
  have hset : ∀ A : Subgroup G, IsMinOffender T H V A →
      Ch3z.Setting H T (H ⊓ M) (conjClosure V H) A := fun A hA =>
    ⟨hmp, hsq, hUT, hUe, hA.1, hA.not_le hRT,
      fun L' N' hs' hnc' => hconcl.count_four A hA L' N' hs' hnc'⟩
  refine ⟨hmp, hsq, hUT, hset, ?_, ?_⟩
  · have hTV : T ≤ Subgroup.normalizer (V : Set G) := fun t ht =>
      hII (Subgroup.mem_inf.mpr ⟨hTH ht, h.le_M (h.T_le ht)⟩)
    have hgen : ∀ W : Subgroup G, IsNormalIn H (conjClosure V H) W → V ≤ W →
        conjClosure V H ≤ W :=
      fun W hW hVW => conjClosure_le fun g hg z hz => hW.2 g hg z (hVW hz)
    obtain ⟨L₁, N₁, hstep₁, hnc₁⟩ := exists_noncentral_of_series hconcl.chief (by norm_num)
    exact exists_good_step hmp.isSylow hUT hUe (le_normalizer_conjClosure V H)
      (le_conjClosure V H) hgen hTV ⟨L₁, N₁, hstep₁, hnc₁⟩
  · intro L N hstep hnc
    obtain ⟨A, hA⟩ := hconcl.exists_A
    exact le_antisymm (centralizerMod_le_kerIn hmp hUT hstep hnc)
      (Setting.kerIn_le_centralizerMod hB69 (hset A hA) hstep hnc)

end CFSG.Quasithin.H13.L319
