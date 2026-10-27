module

public import CFSG.Quasithin.Background.F7E1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

namespace CosetGeom

variable {G₀ G₁ G₂ T : Subgroup G}

theorem exists_E1_config [Finite G] {V : Subgroup G} (hyp : AmalgamHypV G₀ G₁ G₂ T V) (hV : V ≠ ⊥)
    {γ : CosetGeom G₀ G₁ G₂} (hγ : IsCriticalVertex G₀ G₁ G₂ V γ)
    (ha₃ : 3 ≤ critDist G₀ G₁ G₂ V) (ha₂ : Odd (critDist G₀ G₁ G₂ V))
    (hb : IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)))
    (hc : E1.nParam G₂ = 1) {A : Subgroup G} (hA₁ : A ≤ Vv V (γ₁ G₀ G₁ G₂))
    (hA₂ : ¬ A ≤ ballStab 1 γ) :
    (∃ g : G, stab γ = conjSub g G₂) ∧ IsElemAbelian 2 A ∧ ¬ A ≤ pCoreOf 2 (stab γ) ∧
      ∃ S H W : Subgroup G, IsSylowTwoOf S (stab γ) ∧ A ≤ S ∧ E1.IsE 1 (stab γ) S A H ∧
        A ≤ H ∧ S ≤ Subgroup.normalizer (W : Set G) ∧
        (∃ g ∈ H, ¬ A ≤ Subgroup.normalizer (conjSub g W : Set G)) ∧
        ∀ g ∈ H, ∃ α ∈ nbrs γ, Vv V α = conjSub g W := by
  have hb2 : 2 ≤ critDist G₀ G₁ G₂ V := by omega
  obtain ⟨⟨β, hβnb, hdβ⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic hb2
  have hAel : IsElemAbelian 2 A :=
    isElemAbelian_mono (isElemAbelian_Vv_γ₁ hyp hV (by omega)) hA₁
  have hAp : IsPGroup 2 A := isPGroup_of_isElemAbelian hAel
  have hAstab : A ≤ stab β ⊓ stab γ :=
    hA₁.trans ((Vv_γ₁_le_pCoreOf_stab_inf hyp hV hβnb hdβ).trans (pCoreOf_le 2 _))
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact ha₂)
  have hadj : (graph G₀ G₁ G₂).Adj β γ := hβnb
  obtain ⟨g, hg0, hg1, hAg⟩ := exists_edge_conj_sylow hyp.toAmalgamHyp hadj hvt hAstab hAp
  have hstabγ : stab γ = conjSub (g : G) G₂ := by rw [← hg1, stab_smul, stab_γ₁ hyp.le₂]
  have hVβ : Vv V β = conjSub (g : G) V := by rw [← hg0]; exact Vv_smul_γ₀ hyp.normalizes g
  set N₀ := G₂ ⊓ Subgroup.normalizer (V : Set G) with hN₀
  set M := stab γ ⊓ Subgroup.normalizer (Vv V β : Set G) with hM
  have hMeq : M = conjSub (g : G) N₀ := by
    rw [hM, hstabγ, hVβ, conjSub_inf, conjSub_normalizer]
  obtain ⟨hmax, hTN₀, huniq⟩ := isUniqueMaxOver_iff.mp hb
  have hMlt : M < stab γ := by
    rw [hMeq, hstabγ]
    exact lt_of_le_of_ne (conjSub_mono _ hmax.1.le) fun e => hmax.1.ne ((conjSub_inj _).mp e)
  have hunique : ∀ K : Subgroup G, K ≤ stab γ → K ≠ stab γ → conjSub (g : G) T ≤ K → K ≤ M := by
    intro K hK hKne hTK
    have hK' : conjSub (g : G)⁻¹ K ≤ G₂ := by
      rw [hstabγ] at hK
      exact (le_conjSub_iff _).mp hK
    have hKne' : conjSub (g : G)⁻¹ K ≠ G₂ := by
      intro e
      apply hKne
      rw [hstabγ, ← e, conjSub_inv_conjSub]
    have hTK' : T ≤ conjSub (g : G)⁻¹ K := (conjSub_le_iff _).mp hTK
    obtain ⟨N, hN, hKN⟩ := exists_isMaxSubgroupIn (lt_of_le_of_ne hK' hKne')
    have hNN₀ : N = N₀ := huniq N hN (hTK'.trans hKN)
    rw [hMeq]
    have := conjSub_mono (g : G) (hNN₀ ▸ hKN)
    rwa [conjSub_inv_conjSub] at this
  have hInE : E1.InE 1 (stab γ) := by
    rw [hstabγ]
    exact (E1.inE_conj 1 (g : G) G₂).mpr (inE_one_of_nParam_eq_one hc)
  have hTγ : IsSylowTwoOf (conjSub (g : G) T) (stab γ) := by
    rw [hstabγ]; exact isSylowTwoOf_conj hyp.sylow₂ _
  have hnot : ¬ A ≤ pCoreOf 2 (stab γ) := fun h =>
    hA₂ (h.trans (pCoreOf_stab_le_ballStab_one hyp.toAmalgamHyp γ))
  obtain ⟨y, hy, hAS, H, hH, hHM⟩ :=
    exists_isE_not_le_of_inE_one hInE hTγ hMlt hunique hAg hAel hnot
  set S := conjSub y (conjSub (g : G) T) with hSdef
  have hS : IsSylowTwoOf S (stab γ) := by
    have := isSylowTwoOf_conj hTγ y
    rwa [F7.conjSub_eq_of_mem hy] at this
  have hHγ : H ≤ stab γ := hH.1
  have hAH : A ≤ H := by
    have h1 : A ⊔ pCoreOf 2 (stab γ) ≤ E1.tauOf (stab γ) S A := E1.le_tauOf hS hAS hAel
    exact (le_sup_left.trans h1).trans (hH.2.1.trans inf_le_right)
  set W := conjSub y (Vv V β) with hW
  have hSW : S ≤ Subgroup.normalizer (W : Set G) := by
    rw [hW, hVβ]
    have hT1 : T ≤ Subgroup.normalizer (V : Set G) := hyp.sylow₁.1.trans hyp.normalizes
    exact conjSub_le_normalizer (conjSub_le_normalizer hT1)
  have hex : ∃ h ∈ H, ¬ A ≤ Subgroup.normalizer (conjSub h W : Set G) := by
    by_contra hcon
    push Not at hcon
    have hcl : conjClosure A H ≤ Subgroup.normalizer (W : Set G) := by
      refine conjClosure_le fun h hh a ha => ?_
      have h1 := hcon h⁻¹ (H.inv_mem hh) ha
      rw [conjSub_normalizer, mem_conjSub] at h1
      simpa using h1
    have hSH : IsSylowTwoOf (S ⊓ H) H := hH.2.2.1
    have hres : twoResidual H ≤ conjClosure A H := E1.twoResidual_le_conjClosure ⟨1, hH⟩
    have hHle : H ≤ (S ⊓ H) ⊔ conjClosure A H :=
      calc H = (S ⊓ H) ⊔ twoResidual H := (sup_twoResidual_eq hSH).symm
        _ ≤ (S ⊓ H) ⊔ conjClosure A H := sup_le_sup_left hres _
    have hHN : H ≤ Subgroup.normalizer (W : Set G) :=
      hHle.trans (sup_le (inf_le_left.trans hSW) hcl)
    apply hHM
    have e : conjSub y M = stab γ ⊓ Subgroup.normalizer (W : Set G) := by
      rw [hM, conjSub_inf, F7.conjSub_eq_of_mem hy, hW, conjSub_normalizer]
    rw [e]
    exact le_inf hHγ hHN
  refine ⟨⟨(g : G), hstabγ⟩, hAel, hnot, S, H, W, hS, hAS, hH, hAH, hSW, hex, fun h hhH => ?_⟩
  have hh0 : h ∈ G₀ := stab_le γ (hHγ hhH)
  have hy0 : y ∈ G₀ := stab_le γ hy
  set kk : ↥G₀ := ⟨h, hh0⟩ * ⟨y, hy0⟩ * g with hkk
  have hkkv : (kk : G) = h * y * (g : G) := rfl
  have hkk1 : kk • γ₁ G₀ G₁ G₂ = γ := by
    rw [hkk, mul_smul, mul_smul, hg1, smul_eq_of_mem_stab (g := ⟨y, hy0⟩) hy]
    exact smul_eq_of_mem_stab (g := ⟨h, hh0⟩) (hHγ hhH)
  refine ⟨kk • γ₀ G₀ G₁ G₂, ?_, ?_⟩
  · have := (smul_adj kk).mpr (adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂))
    rw [hkk1] at this
    exact this.symm
  · rw [Vv_smul_γ₀ hyp.normalizes, hkkv, conjSub_mul, conjSub_mul, hW, hVβ]

end CosetGeom

end CFSG.Quasithin
