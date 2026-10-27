module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Seven
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Step
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Glue
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Series
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Two

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z CFSG.Quasithin.H13.L319.S66

theorem six6TwoIndex_of (hB69 : B69Struct) (hB1 : B69One) : Six6TwoIndex := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA L N hstep hnc
    z hzV hzN hzL hzT hset 𝓗 hctx H' hH' hNat y hyM hy3ex hcentU hψH' hψne
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  obtain ⟨-, -, -, -, -, hstep2⟩ :=
    lemma319Common_of_inputs hB69 G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl
  have hTH : T ≤ H := hset.mp.isSylow.1
  have hTM : T ≤ M := h.T_le.trans h.le_M
  have hTS : T ≤ H ⊓ M := le_inf hTH hTM
  have hAC : A ≤ Subgroup.centralizer (V : Set G) := IsMinOffender.le_centralizer hT h hA
  have hAV : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a := fun a ha v hv =>
    ((Subgroup.mem_centralizer_iff.mp (hAC ha)) v hv).symm
  have hTV : ∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V := fun t ht v hv =>
    (Subgroup.mem_normalizer_iff.mp (hII (hTS ht)) v).mp hv
  have hyHM : (y : G) ∈ H ⊓ M := ⟨y.2, hyM⟩
  have hyV : ∀ v ∈ V, (y : G) * v * (y : G)⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp (hII hyHM) v).mp hv
  have hy3 : ∀ v ∈ V, (y : G) ^ 3 * v * ((y : G) ^ 3)⁻¹ = v := fun v hv =>
    hcentU v (le_conjClosure V H hv)
  have hVe : IsElemAbelian 2 V := by
    have hU := hconcl.elemAbelian
    have hVU := le_conjClosure V H
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun w hw => hU.2 w (hVU hw)⟩
    have hc := congrArg Subtype.val (hU.1.is_comm.comm ⟨a, hVU a.2⟩ ⟨b, hVU b.2⟩)
    exact Subtype.ext hc
  have hUe := hconcl.elemAbelian
  have hloc : ∀ L' N' : Subgroup G, IsChiefStep H (conjClosure V H) L' N' →
      (IsCentralStep H L' N' → (Subgroup.centralizer ({(y : G)} : Set G)).relIndex (V ⊓ N') ≤
          (Subgroup.centralizer ({(y : G)} : Set G)).relIndex (V ⊓ L')) ∧
      (¬ IsCentralStep H L' N' → (Subgroup.centralizer ({(y : G)} : Set G)).relIndex (V ⊓ N') ≤
          4 * (Subgroup.centralizer ({(y : G)} : Set G)).relIndex (V ⊓ L')) := by
    intro L' N' hst
    refine ⟨fun hc => relIndex_step_le_one hUe hst hc hVe y.2 hyV hy3, fun hnc' => ?_⟩
    obtain ⟨𝓗', hctx'⟩ := Setting.blkCtx hB69 hset hst hnc'
    have hJ : centralizerMod L' H N' = centralizerMod L H N :=
      (hstep2 L' N' hst hnc').trans (hstep2 L N hstep hnc).symm
    obtain ⟨K₀, hK₀, hK₀nat, hyK⟩ :=
      exists_block_eq_theta hB1 hset hstep hnc hst hnc' hJ hctx hH' hNat hctx' y.2 hψH'
    exact relIndex_step_le_four hB1 hset hst hnc' hVe y.2 hyV hy3 hctx' hK₀ hK₀nat hyK hAV hTV
  have hser := relIndex_le_four_pow_of_chiefSeries hloc hconcl.chief
  have hVU : V ⊓ conjClosure V H = V := inf_eq_left.mpr (le_conjClosure V H)
  rw [hVU] at hser
  simpa using hser

end CFSG.Quasithin.H13.L319

