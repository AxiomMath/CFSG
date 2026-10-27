module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3Early
public import CFSG.GroupTheory.PCoreQuotientSylow
public import CFSG.GroupTheory.PowMemSupOfPGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_conjClosure_of_le {M K W : Subgroup G} (hKM : K ≤ M) :
    conjClosure M (conjClosure K W) = conjClosure M W := by
  refine le_antisymm ?_ ?_
  · refine uc22p22v_conjClosure_le (uc22p22v_le_normalizer_conjClosure M W) ?_
    exact uc22p22v_conjClosure_le
      (hKM.trans (uc22p22v_le_normalizer_conjClosure M W))
      (uc22p22v_le_conjClosure M W)
  · refine uc22p22v_conjClosure_le
      (uc22p22v_le_normalizer_conjClosure M (conjClosure K W)) ?_
    exact (uc22p22v_le_conjClosure K W).trans
      (uc22p22v_le_conjClosure M (conjClosure K W))

private def pCorePreimage {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch) :
    Subgroup ↥D.M :=
  (CFSG.pCore 2 c.MBarTilde).comap
    (QuotientGroup.mk' ((c.CMETilde.subgroupOf D.M).normalCore))

private theorem pCorePreimage_normal {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) : (pCorePreimage c).Normal :=
  (CFSG.pCore_normal (p := 2) (G := c.MBarTilde)).comap
    (QuotientGroup.mk' ((c.CMETilde.subgroupOf D.M).normalCore))

private theorem s23fifteen_T_le_centralizerMod {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D)
    (hZnorm : D.M ≤ Subgroup.normalizer (D.Z : Set G))
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z) (k : ↥D.M) :
    D.T.map (MulAut.conj (k : G)).toMonoidHom ≤
      centralizerMod D.Z D.M (c.W.map (MulAut.conj (k : G)).toMonoidHom) := by
  have hTk_le_M : D.T.map (MulAut.conj (k : G)).toMonoidHom ≤ D.M := by
    have hkM : D.M.map (MulAut.conj (k : G)).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := D.M) k.2)
    have h := Subgroup.map_mono (f := (MulAut.conj (k : G)).toMonoidHom) D.sylowM.le
    simpa only [hkM] using h
  have hcommk : ⁅c.W.map (MulAut.conj (k : G)).toMonoidHom,
      D.T.map (MulAut.conj (k : G)).toMonoidHom⁆ ≤ D.Z := by
    have h := Subgroup.map_mono (f := (MulAut.conj (k : G)).toMonoidHom) (hWT h1930 c)
    rw [Subgroup.map_commutator] at h
    have hZmap : D.Z.map (MulAut.conj (k : G)).toMonoidHom = D.Z :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hZnorm k.2)
    simpa only [hZmap] using h
  intro x hx
  rw [mem_centralizerMod]
  refine ⟨hTk_le_M hx, hZnorm (hTk_le_M hx), ?_⟩
  intro u hu
  have hmem : ⁅x, u⁆ ∈ ⁅D.T.map (MulAut.conj (k : G)).toMonoidHom,
      c.W.map (MulAut.conj (k : G)).toMonoidHom⁆ :=
    Subgroup.commutator_mem_commutator hx hu
  rw [Subgroup.commutator_comm] at hmem
  simpa [commutatorElement_def] using hcommk hmem

private theorem s23fifteen_CMETilde_le_centralizerMod {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (k : ↥D.M) (hVleE : c.V ≤ c.E) (hWV : c.W ≤ c.V)
    (hEinv : c.E.map (MulAut.conj (k : G)).toMonoidHom = c.E) :
    c.CMETilde ≤ centralizerMod D.Z D.M (c.W.map (MulAut.conj (k : G)).toMonoidHom) := by
  have hWk_le_E : c.W.map (MulAut.conj (k : G)).toMonoidHom ≤ c.E := by
    have h1 : c.W.map (MulAut.conj (k : G)).toMonoidHom ≤
        c.V.map (MulAut.conj (k : G)).toMonoidHom := Subgroup.map_mono hWV
    have h2 : c.V.map (MulAut.conj (k : G)).toMonoidHom ≤ c.E := by
      rw [← hEinv]
      exact Subgroup.map_mono hVleE
    exact h1.trans h2
  exact centralizerMod_anti_right D.M hWk_le_E

private theorem s23fifteen_preimage_le_sup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (k : ↥D.M) :
    (pCorePreimage c).map (D.M).subtype ≤
      D.T.map (MulAut.conj (k : G)).toMonoidHom ⊔ c.CMETilde := by
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  have hsurj : Function.Surjective (MulAut.conj k).toMonoidHom := (MulAut.conj k).surjective
  have hle := CFSG.pCore_comap_le_sup_sylow (p := 2)
    (K := (c.CMETilde.subgroupOf D.M).normalCore)
    (S.mapSurjective (f := (MulAut.conj k).toMonoidHom) hsurj)
  have hYle : pCorePreimage c ≤ (c.CMETilde.subgroupOf D.M).normalCore ⊔
      (S.mapSurjective (f := (MulAut.conj k).toMonoidHom) hsurj : Subgroup ↥D.M) := by
    simpa [pCorePreimage] using hle
  have hSk : (S.mapSurjective (f := (MulAut.conj k).toMonoidHom) hsurj : Subgroup ↥D.M) =
      (D.T.map (MulAut.conj (k : G)).toMonoidHom).subgroupOf D.M := by
    rw [Sylow.coe_mapSurjective, hS]
    exact (uc22br4_subgroupOf_map_conj D.M D.T k).symm
  have hTk_le_M : D.T.map (MulAut.conj (k : G)).toMonoidHom ≤ D.M := by
    have hkM : D.M.map (MulAut.conj (k : G)).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := D.M) k.2)
    have h := Subgroup.map_mono (f := (MulAut.conj (k : G)).toMonoidHom) D.sylowM.le
    simpa only [hkM] using h
  have hmap := Subgroup.map_mono (f := (D.M).subtype) hYle
  rw [Subgroup.map_sup] at hmap
  refine hmap.trans ?_
  refine sup_le ?_ ?_
  · have hK0map : (c.CMETilde.subgroupOf D.M).normalCore.map (D.M).subtype ≤
        c.CMETilde := by
      calc (c.CMETilde.subgroupOf D.M).normalCore.map (D.M).subtype ≤
            (c.CMETilde.subgroupOf D.M).map (D.M).subtype :=
            Subgroup.map_mono (Subgroup.normalCore_le _)
        _ = c.CMETilde :=
            Subgroup.map_subgroupOf_eq_of_le (centralizerMod_le_left D.Z D.M c.E)
    exact hK0map.trans le_sup_right
  · rw [hSk, Subgroup.map_subgroupOf_eq_of_le hTk_le_M]
    exact le_sup_left

private theorem s23fifteen_preimage_le_cent {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z) (k : ↥D.M) :
    (pCorePreimage c).map (D.M).subtype ≤
      centralizerMod D.Z D.M (c.W.map (MulAut.conj (k : G)).toMonoidHom) := by
  have h4c := h4 h1930 c.toCtx23L
  have hZnorm : D.M ≤ Subgroup.normalizer (D.Z : Set G) := h4c.1 ▸ h4c.2.2
  have hVleE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  have hMnormE : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  have hLN : c.L ≤ c.N := by
    have hNmem : c.N ∈ calMOf (c.L ⊔ D.T) := by rw [c.hN]; simp
    exact le_sup_left.trans hNmem.2
  have hWV : c.W ≤ c.V :=
    uc22p22v_conjClosure_mono (c.hX.1.2.1.trans hLN) D.Z
  have hEinv : c.E.map (MulAut.conj (k : G)).toMonoidHom = c.E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnormE k.2)
  exact (s23fifteen_preimage_le_sup c k).trans
    (sup_le (s23fifteen_T_le_centralizerMod c h1930 hZnorm hWT k)
      (s23fifteen_CMETilde_le_centralizerMod c k hVleE hWV hEinv))

private theorem s23fifteen_E_eq_iSup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D)
    (hKW : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    c.E = ⨆ k : ↥D.M, c.W.map (MulAut.conj (k : G)).toMonoidHom := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  rw [Ctx23L.E, ← hKW h1930 c]
  exact (conjClosure_conjClosure_of_le hKM).trans (uc22br4_conjClosure_eq D.M c.W)

private theorem s23fifteen_W_le_normalizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    ∀ k : ↥D.M, c.W.map (MulAut.conj (k : G)).toMonoidHom ≤
      Subgroup.normalizer (D.Z : Set G) := by
  have h4c := h4 h1930 c.toCtx23L
  have hZnorm : D.M ≤ Subgroup.normalizer (D.Z : Set G) := h4c.1 ▸ h4c.2.2
  have hSylN : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N :=
    D.sylowG.of_le (Ctx23L.N_mem_calMOf_T c.toCtx23L).2 le_top
  have hVT : c.V ≤ D.T :=
    (Ctx23L.V_le_pCoreOf_N c.toCtx23L h4 h1930).trans
      (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
        (CFSG.ABGLocalTools.isSylowOf_iff.mp hSylN))
  have hVleE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  have hE_le_M : c.E ≤ D.M :=
    uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) (hVT.trans D.sylowM.le)
  have hMnormE : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  have hLN : c.L ≤ c.N := by
    have hNmem : c.N ∈ calMOf (c.L ⊔ D.T) := by rw [c.hN]; simp
    exact le_sup_left.trans hNmem.2
  have hWV : c.W ≤ c.V :=
    uc22p22v_conjClosure_mono (c.hX.1.2.1.trans hLN) D.Z
  intro k
  have h1 : c.W.map (MulAut.conj (k : G)).toMonoidHom ≤
      c.V.map (MulAut.conj (k : G)).toMonoidHom := Subgroup.map_mono hWV
  have h2 : c.V.map (MulAut.conj (k : G)).toMonoidHom ≤ c.E := by
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq.mp (hMnormE k.2)]
    exact Subgroup.map_mono hVleE
  exact ((h1.trans h2).trans hE_le_M).trans hZnorm

private theorem s23fifteen_preimage_le_CMETilde {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z)
    (hKW : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    (pCorePreimage c).map (D.M).subtype ≤ c.CMETilde := by
  have hstep : ∀ k : ↥D.M, (pCorePreimage c).map (D.M).subtype ≤
      centralizerMod D.Z D.M (c.W.map (MulAut.conj (k : G)).toMonoidHom) :=
    fun k => s23fifteen_preimage_le_cent c h4 h1930 hWT k
  have hjoin : (⨅ k : ↥D.M,
      centralizerMod D.Z D.M (c.W.map (MulAut.conj (k : G)).toMonoidHom)) =
      c.CMETilde := by
    rw [Ctx2311.CMETilde, s23fifteen_E_eq_iSup c h1930 hKW]
    exact (centralizerMod_iSup_right (V₁ := D.Z) (X := D.M)
      (fun k : ↥D.M => c.W.map (MulAut.conj (k : G)).toMonoidHom)
      (s23fifteen_W_le_normalizer c h4 h1930)).symm
  have h1 : (pCorePreimage c).map (D.M).subtype ≤ (⨅ k : ↥D.M,
      centralizerMod D.Z D.M (c.W.map (MulAut.conj (k : G)).toMonoidHom)) :=
    le_iInf hstep
  rwa [hjoin] at h1

private theorem s23fifteen_preimage_le_core {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z)
    (hKW : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    pCorePreimage c ≤ (c.CMETilde.subgroupOf D.M).normalCore := by
  have hle := s23fifteen_preimage_le_CMETilde c h4 h1930 hWT hKW
  have hsub : pCorePreimage c ≤ c.CMETilde.subgroupOf D.M := by
    rw [← Subgroup.comap_subtype]
    exact (Subgroup.map_le_iff_le_comap).mp hle
  haveI : (pCorePreimage c).Normal := pCorePreimage_normal c
  exact (Subgroup.normal_le_normalCore).mpr hsub

theorem s23_15_2_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (hWT : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.W, D.T⁆ ≤ D.Z)
    (hKW : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    S23_15_2 D Ch := by
  intro h1930 c
  have hcore := s23fifteen_preimage_le_core c h4 h1930 hWT hKW
  have hmap : CFSG.pCore 2 c.MBarTilde = (pCorePreimage c).map
      (QuotientGroup.mk' ((c.CMETilde.subgroupOf D.M).normalCore)) :=
    (Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective ((c.CMETilde.subgroupOf D.M).normalCore))
      (CFSG.pCore 2 c.MBarTilde)).symm
  rw [hmap, Subgroup.map_eq_bot_iff]
  simpa [pCorePreimage] using hcore

private theorem isElemAbelian_E_of_le_centralizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hcent : c.E ≤ Subgroup.centralizer (c.V : Set G)) : IsElemAbelian 2 c.E := by
  have hVleE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  have hMnormE : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  have hEeq : c.E = ⨆ k : ↥D.M, c.V.map (MulAut.conj (k : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  have hVk_ea : ∀ k : ↥D.M, IsElemAbelian 2
      (c.V.map (MulAut.conj (k : G)).toMonoidHom) :=
    fun k => (c.isElemAbelian_V h4 h1930).map _
  have hVk_cent : ∀ k : ↥D.M,
      c.V.map (MulAut.conj (k : G)).toMonoidHom ≤
        Subgroup.centralizer (c.E : Set G) := by
    intro k v hv
    obtain ⟨v0, hv0, rfl⟩ := Subgroup.mem_map.mp hv
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    change e * ((k : G) * v0 * (k : G)⁻¹) = ((k : G) * v0 * (k : G)⁻¹) * e
    have hkE : (k : G)⁻¹ * e * (k : G) ∈ c.E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hMnormE (D.M.inv_mem k.2)) e).mp he
    have hv0c : v0 * ((k : G)⁻¹ * e * (k : G)) =
        ((k : G)⁻¹ * e * (k : G)) * v0 :=
      (Subgroup.mem_centralizer_iff.mp (hcent hkE)) v0 hv0
    calc e * ((k : G) * v0 * (k : G)⁻¹)
        = (k : G) * ((k : G)⁻¹ * e * (k : G) * v0) * (k : G)⁻¹ := by group
      _ = (k : G) * (v0 * ((k : G)⁻¹ * e * (k : G))) * (k : G)⁻¹ := by rw [hv0c]
      _ = ((k : G) * v0 * (k : G)⁻¹) * e := by group
  have hpair : ∀ i j : ↥D.M,
      ∀ x ∈ c.V.map (MulAut.conj (i : G)).toMonoidHom,
      ∀ y ∈ c.V.map (MulAut.conj (j : G)).toMonoidHom, x * y = y * x := by
    intro i j x hx y hy
    have hyE : y ∈ c.E := by
      rw [hEeq]
      exact Subgroup.mem_iSup_of_mem j hy
    exact ((Subgroup.mem_centralizer_iff.mp (hVk_cent i hx)) y hyE).symm
  rw [hEeq]
  exact CFSG.Quasithin.CosetGeom.isElemAbelian_iSup _ hVk_ea hpair

private theorem s23sixteen_E_cent {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (h14 : S23_14 D Ch)
    (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) :
    ¬ c.E ≤ Subgroup.centralizer (c.V : Set G) := by
  intro hcent
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥c.E) :=
    ⟨Ctx2311.isPGroup_E c h1930 h4 h12 (hVK h1930 c)⟩
  have hphi : frattini ↥c.E = ⊥ :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥c.E) (p := 2)).mpr
      (isElemAbelian_E_of_le_centralizer c h4 h1930 hcent).isElementaryAbelian
  exact (h14 h1930 c) hphi

private theorem s23sixteen_E_pCoreOf {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (h14 : S23_14 D Ch)
    (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V)
    (hLV : H1930 D → ∀ c : Ctx2311 D Ch,
      c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L) :
    ¬ c.E ≤ CFSG.Open.pCoreOf 2 c.L := by
  intro hle
  refine s23sixteen_E_cent c h4 h12 h14 h1930 hVK (hle.trans ?_)
  calc CFSG.Open.pCoreOf 2 c.L = c.L ⊓ Subgroup.centralizer (c.V : Set G) :=
        (hLV h1930 c).symm
    _ ≤ Subgroup.centralizer (c.V : Set G) := inf_le_right

private theorem s23sixteen_I_sup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (h14 : S23_14 D Ch)
    (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V)
    (hLV : H1930 D → ∀ c : Ctx2311 D Ch,
      c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L)
    (hLJ : H1930 D → ∀ c : Ctx2311 D Ch, ∀ J : Subgroup G, J ≤ c.L → IsPGroup 2 J →
      ¬ J ≤ CFSG.Open.pCoreOf 2 c.L →
      conjClosure c.L J ⊔ CFSG.Open.pCoreOf 2 c.L = c.L) :
    c.I ⊔ CFSG.Open.pCoreOf 2 c.L = c.L := by
  have hVKc : ⁅c.V, c.K⁆ = c.V := hVK h1930 c
  have hEK : c.E ≤ c.K := Ctx2311.E_le_K c h1930 h4 h12 hVKc
  have hEL : c.E ≤ c.L :=
    hEK.trans ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right)
  have hE2 : IsPGroup 2 ↥c.E := Ctx2311.isPGroup_E c h1930 h4 h12 hVKc
  have hEO2 : ¬ c.E ≤ CFSG.Open.pCoreOf 2 c.L :=
    s23sixteen_E_pCoreOf c h4 h12 h14 h1930 hVK hLV
  simpa [Ctx2311.I] using hLJ h1930 c c.E hEL hE2 hEO2

private theorem s23sixteen_I_le_L {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) :
    c.I ≤ c.L := by
  have hVKc : ⁅c.V, c.K⁆ = c.V := hVK h1930 c
  have hEK : c.E ≤ c.K := Ctx2311.E_le_K c h1930 h4 h12 hVKc
  have hEL : c.E ≤ c.L :=
    hEK.trans ((uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right)
  rw [Ctx2311.I]
  exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := c.L)) hEL

private theorem s23sixteen_I_normal {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V) :
    (c.I.subgroupOf c.L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (s23sixteen_I_le_L c h4 h12 h1930 hVK)).mpr
    (uc22p22v_le_normalizer_conjClosure c.L c.E)

private theorem s23sixteen_quotient_isPGroup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (h14 : S23_14 D Ch)
    (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V)
    (hLV : H1930 D → ∀ c : Ctx2311 D Ch,
      c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L)
    (hLJ : H1930 D → ∀ c : Ctx2311 D Ch, ∀ J : Subgroup G, J ≤ c.L → IsPGroup 2 J →
      ¬ J ≤ CFSG.Open.pCoreOf 2 c.L →
      conjClosure c.L J ⊔ CFSG.Open.pCoreOf 2 c.L = c.L)
    [hInorm : (c.I.subgroupOf c.L).Normal] :
    IsPGroup 2 (↥c.L ⧸ c.I.subgroupOf c.L) := by
  have hIL := s23sixteen_I_sup c h4 h12 h14 h1930 hVK hLV hLJ
  have hsup : CFSG.Open.pCoreOf 2 c.L ⊔ c.I = c.L := by
    rw [sup_comm]
    exact hIL
  haveI hInormSup : (c.I.subgroupOf (CFSG.Open.pCoreOf 2 c.L ⊔ c.I)).Normal := by
    rw [hsup]
    exact hInorm
  have hpquot := CFSG.GroupTheory.isPGroup_quotient_sup_left (p := 2)
    (T := CFSG.Open.pCoreOf 2 c.L) (C := c.I) (uc22main1_isPGroup_pCoreOf c.L)
  exact IsPGroup.of_equiv hpquot
    (QuotientGroup.equivQuotientSubgroupOfOfEq (A' := c.I)
      (A := CFSG.Open.pCoreOf 2 c.L ⊔ c.I) (B' := c.I) (B := c.L) rfl hsup)

private theorem s23sixteen_I_eq_L {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch) (h14 : S23_14 D Ch)
    (h1930 : H1930 D)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V)
    (hLV : H1930 D → ∀ c : Ctx2311 D Ch,
      c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L)
    (hLJ : H1930 D → ∀ c : Ctx2311 D Ch, ∀ J : Subgroup G, J ≤ c.L → IsPGroup 2 J →
      ¬ J ≤ CFSG.Open.pCoreOf 2 c.L →
      conjClosure c.L J ⊔ CFSG.Open.pCoreOf 2 c.L = c.L) :
    c.I = c.L := by
  have hI_le_L := s23sixteen_I_le_L c h4 h12 h1930 hVK
  haveI hInorm : (c.I.subgroupOf c.L).Normal :=
    s23sixteen_I_normal c h4 h12 h1930 hVK
  have hLp := s23sixteen_quotient_isPGroup c h4 h12 h14 h1930 hVK hLV hLJ
  haveI hperfL : Group.IsPerfect ↥c.L := Subgroup.isPerfect_iff.mpr c.hL.1.2.1
  have hsub : Subsingleton (↥c.L ⧸ c.I.subgroupOf c.L) := by
    by_contra h
    haveI : Nontrivial (↥c.L ⧸ c.I.subgroupOf c.L) :=
      not_subsingleton_iff_nontrivial.mp h
    exact Group.IsPerfect.not_isNilpotent (G := ↥c.L ⧸ c.I.subgroupOf c.L) hLp.isNilpotent
  have htop : c.I.subgroupOf c.L = ⊤ :=
    QuotientGroup.subgroup_eq_top_of_subsingleton _ hsub
  exact le_antisymm hI_le_L (Subgroup.subgroupOf_eq_top.mp htop)

theorem s23_16_2_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h12 : S23_12 D Ch)
    (h14 : S23_14 D Ch)
    (hVK : H1930 D → ∀ c : Ctx2311 D Ch, ⁅c.V, c.K⁆ = c.V)
    (hLV : H1930 D → ∀ c : Ctx2311 D Ch,
      c.L ⊓ Subgroup.centralizer (c.V : Set G) = CFSG.Open.pCoreOf 2 c.L)
    (hLJ : H1930 D → ∀ c : Ctx2311 D Ch, ∀ J : Subgroup G, J ≤ c.L → IsPGroup 2 J →
      ¬ J ≤ CFSG.Open.pCoreOf 2 c.L →
      conjClosure c.L J ⊔ CFSG.Open.pCoreOf 2 c.L = c.L) :
    S23_16_2 D Ch := by
  intro h1930 c
  refine ⟨Ctx2311.E_le_K c h1930 h4 h12 (hVK h1930 c), ?_⟩
  exact s23sixteen_I_eq_L c h4 h12 h14 h1930 hVK hLV hLJ

end CFSG.LocalAnalysis.UniquenessCase.UC22
