module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Fin
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKS9Grp
public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKPre

public section

namespace CFSG.Quasithin.H13.L829NK

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
  CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.H13.L829N
open scoped commutatorElement

theorem nk_step9_core (hL : NKLeaves) (hmod : StmtFSUModule) (hD4 : StmtD4L3M22)
    (hS3 : Step828Three) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8)
    {G : Type} [Group G] [Finite G] {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)]
    (hrow : Case8_2 T L I) {H : Subgroup G} {h : G} {k : ℕ}
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k)
    (hrow' : Row711L3Nine T L I 1 ∨ Row711M22Code T L I)
    {K : Subgroup G} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hq : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K))
    (hres : L32Residual H T (H ⊓ fsuM T L) K) (hTM : T ≤ fsuM T L)
    (hP7 : H ⊓ fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hVJ : ¬ fsuV T I ≤ kerIn (H ⊓ fsuM T L) H) : False := by
  obtain ⟨hVT, hTV, hVc, hVsq⟩ := asf_V_basic hmod hyp
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hT : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hTH : T ≤ H := hT.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  obtain ⟨hKG, W₀, W₁, W, hWa, hWm, hWf, SW, hcfg, hKne⟩ :=
    nk_prelude hmod hD4 hS3 h825 h828 hyp h731 h821 hrow hH hh hC hrow' hKc
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hres.1
  obtain ⟨hs, hna, hsolv⟩ := star_facts_case2 hKc hHK hTK hq hres.2.1
  have hKs3 : IsPSL 3 2 1 (E2.star (H ⊓ fsuM T L) H K) := by
    rcases hres.2.2 with ⟨hL', -, -⟩ | ⟨hL', -, -⟩
    · exact hL'
    · exact isPSL_three_two_of_isPSL_two_seven hL'
  have hKG' : K ≤ Subgroup.closure {x : G | ∃ h ∈ H, ∃ v ∈ fsuV T I, x = h * v * h⁻¹} := by
    refine hKG.trans ?_
    unfold conjClosure
    apply Subgroup.closure_mono
    rintro x ⟨h, hh', z, hz, e⟩
    exact ⟨h, hh', z, hz, e.symm⟩
  obtain ⟨v, hv, hvgen, hQ⟩ := nk_s9_group_data hL.l32 hT hTM hHK hKc hq hres hVT hV hVJ hP7 hKG'
  obtain ⟨τ, hτ, hout⟩ := s9_outer_t hKc hHK hres hT
  have hker := proper_normal_le_ker_star hKH hKperf hs hsolv
  have hLuΛ : ch82LU L (ch82U (fsuV T I) h) ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H := le_sup_left
  have hKΛ : K ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H := hKH.trans le_sup_right
  have hVΛ : fsuV T I ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H :=
    (hVT.trans hTH).trans le_sup_right
  have hTΛ : T ≤ ch82LU L (ch82U (fsuV T I) h) ⊔ H := hTH.trans le_sup_right
  exact nk_s9main_final hL.schur hL.sl3 (fun X _ hX => ((hL.l32 X hX).1)) SW hcfg hKne hLuΛ hKΛ
    hVΛ hTΛ hKG hTK hVT hv hvgen hτ hs hna hKs3
    (starHom (H ⊓ fsuM T L) H K hKH) (starHom_surjective (H ⊓ fsuM T L) H K hKH)
    (kerIn (H ⊓ fsuM T L) H) (fun z => mem_ker_starHom (H ⊓ fsuM T L) H K hKH z) hker hout
    (commutator_top_of_perfect hKperf) hQ

end CFSG.Quasithin.H13.L829NK
