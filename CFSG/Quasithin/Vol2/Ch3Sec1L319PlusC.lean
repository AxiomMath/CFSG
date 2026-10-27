module

public import CFSG.Quasithin.Vol2.Ch3Sec1L319Plus
public import CFSG.Quasithin.Vol2.Ch3Sec1L319QMinC
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Form
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Nine
public import CFSG.Quasithin.Vol2.Ch3zCmp

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13

theorem lemma319SixPlusD_of_shapeC (hShape : Lemma319SixShapeD) : Lemma319SixPlusD := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6ii h6iii hJ3 hS5
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hUT : conjClosure V H ≤ T := conjClosure_le_T hD h.le_pCore
  have hTH : T ≤ H := h.hStar.1.1
  have hUH : conjClosure V H ≤ H := hUT.trans hTH
  have hUe := hconcl.elemAbelian
  obtain ⟨A, hA⟩ := hconcl.exists_A
  have hrk : 2 ≤ secRank A (A ⊓ pCoreOf 2 H) :=
    h6ii.trans (h.qMin_le_of_concl hT hconcl hA)
  have hAH : A ≤ H := hA.1.1.trans hTH
  have hAe : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := hA.1.2.1.2 a ha
    simpa [pow_two] using this
  have key : ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
      ∃ φ : ↥H →* (Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)), Function.Surjective φ ∧
        φ.ker = (cSecIn H L N).subgroupOf H := by
    intro L N hstep hnc
    obtain ⟨hnorm, hcases⟩ := hShape G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH
      hdual hconcl h6i h6iii L N hstep hnc
    rcases hcases with h1 | h2 | h3 | h4
    · exfalso
      obtain ⟨⟨φ, -, hφk, -⟩, -⟩ := h1
      exact not_quotIso_perm_three hAH hAe hstep.2.1 (hconcl.count_four A hA L N hstep hnc).1 hrk
        φ hφk
    · exact absurd ⟨hnorm, h2⟩ (hS5 L N hstep hnc).1
    · obtain ⟨⟨φ, hφs, hφk, -⟩, -⟩ := h3
      exact ⟨φ, hφs, hφk⟩
    · exact absurd ⟨hnorm, h4⟩ (hS5 L N hstep hnc).2
  obtain ⟨L₀, N₀, hstep₀, hnc₀⟩ := exists_noncentral_of_series hconcl.chief (by norm_num)
  obtain ⟨φ₀, hφ₀s, hφ₀k⟩ := key L₀ N₀ hstep₀ hnc₀
  have hcenJ : ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
      cSecIn H L N ≤ kerIn (H ⊓ M) H := by
    intro L N hstep hnc
    rw [cSecIn_eq_centralizerMod le_rfl hstep.2.1]
    exact centralizerMod_le_kerIn hmp hUT hstep hnc
  have hJ : kerIn (H ⊓ M) H = pCoreOf 2 H := by
    refine kerIn_eq_pCoreOf_of_index hmp (hcenJ L₀ N₀ hstep₀ hnc₀) ?_ hJ3
    intro q hq hqd
    have hidx : (cSecIn H L₀ N₀).relIndex H = 72 := by
      have e1 : (cSecIn H L₀ N₀).relIndex H = φ₀.ker.index := by rw [hφ₀k]; rfl
      rw [e1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ₀s, Subgroup.card_top,
        S3Wr_card]
    exact prime_dvd_seventy_two hq (hidx ▸ hqd)
  have hcen : ∀ L N : Subgroup G, IsChiefStep H (conjClosure V H) L N → ¬ IsCentralStep H L N →
      cSecIn H L N = pCoreOf 2 H := by
    intro L N hstep hnc
    apply le_antisymm
    · exact (hcenJ L N hstep hnc).trans hJ.le
    · rw [cSecIn_eq_centralizerMod le_rfl hstep.2.1]
      exact Ch3z.pCoreOf_le_centralizerMod hUH hstep
        (D15Proof.isElemAbelian_secImg_of_le hUe hstep.1.1)
  refine ⟨hcen, φ₀, hφ₀s, ?_⟩
  rw [hφ₀k, hcen L₀ N₀ hstep₀ hnc₀]

end CFSG.Quasithin.H13.L319
