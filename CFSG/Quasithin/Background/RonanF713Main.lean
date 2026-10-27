module

public import CFSG.Quasithin.Background.RonanF713E1
public import CFSG.Quasithin.Background.RonanF713Claim
public import CFSG.Quasithin.Background.RonanF713Fix
public import CFSG.Quasithin.Background.F7TwoZ

public section

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type*} [Group G] {G₀ G₁ G₂ T V : Subgroup G}

theorem exists_E1_config_loc [Finite ↥G₂] (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    {γ : CosetGeom G₀ G₁ G₂} (hγ : IsCriticalVertex G₀ G₁ G₂ V γ)
    (ha₃ : 3 ≤ critDist G₀ G₁ G₂ V) (ha₂ : Odd (critDist G₀ G₁ G₂ V))
    (hb : IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)))
    (hc : E1.nParam G₂ = 1) {A : Subgroup G} (hA₁ : A ≤ Vv V (γ₁ G₀ G₁ G₂))
    (hA₂ : ¬ A ≤ ballStab 1 γ) (hAel : IsElemAbelian 2 A)
    (hAβ : ∀ β : CosetGeom G₀ G₁ G₂, γ ∈ nbrs β →
      dist (γ₁ G₀ G₁ G₂) β + 2 = critDist G₀ G₁ G₂ V →
        Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab β ⊓ stab γ))
    (hcore : pCoreOf 2 (stab γ) ≤ ballStab 1 γ) :
    (∃ g : G, stab γ = conjSub g G₂) ∧ ¬ A ≤ pCoreOf 2 (stab γ) ∧
      ∃ S H W : Subgroup G, IsSylowTwoOf S (stab γ) ∧ A ≤ S ∧ E1.IsE 1 (stab γ) S A H ∧
        A ≤ H ∧ S ≤ Subgroup.normalizer (W : Set G) ∧
        (∃ g ∈ H, ¬ A ≤ Subgroup.normalizer (conjSub g W : Set G)) ∧
        ∀ g ∈ H, ∃ α ∈ nbrs γ, Vv V α = conjSub g W := by
  have hb2 : 2 ≤ critDist G₀ G₁ G₂ V := by omega
  obtain ⟨⟨β, hβnb, hdβ⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic hb2
  have hAp : IsPGroup 2 A := isPGroup_of_isElemAbelian hAel
  have hAstab : A ≤ stab β ⊓ stab γ := hA₁.trans ((hAβ β hβnb hdβ).trans (pCoreOf_le 2 _))
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact ha₂)
  have hadj : (graph G₀ G₁ G₂).Adj β γ := hβnb
  obtain ⟨g, hg0, hg1, hAg⟩ := exists_edge_conj_sylow_loc hyp.toAmalgamHyp hadj hvt hAstab hAp
  have hstabγ : stab γ = conjSub (g : G) G₂ := by rw [← hg1, stab_smul, stab_γ₁ hyp.le₂]
  haveI : Finite ↥(stab γ) := by rw [hstabγ]; exact finite_conjSub _ _
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
    obtain ⟨N, hN, hKN⟩ := exists_isMaxSubgroupIn_loc (lt_of_le_of_ne hK' hKne')
    have hNN₀ : N = N₀ := huniq N hN (hTK'.trans hKN)
    rw [hMeq]
    have := conjSub_mono (g : G) (hNN₀ ▸ hKN)
    rwa [conjSub_inv_conjSub] at this
  have hInEFor : E1.InEFor 1 (stab γ) (conjSub (g : G) T) := by
    rw [hstabγ]
    exact inEFor_conj_loc (g : G) (inE_one_of_nParam_eq_one_loc hc T hyp.sylow₂)
  have hTγ : IsSylowTwoOf (conjSub (g : G) T) (stab γ) := by
    rw [hstabγ]; exact isSylowTwoOf_conj hyp.sylow₂ _
  have hnot : ¬ A ≤ pCoreOf 2 (stab γ) := fun h => hA₂ (h.trans hcore)
  obtain ⟨y, hy, hAS, H, hH, hHM⟩ :=
    exists_isE_not_le_of_inEFor_one_loc hInEFor hTγ hMlt hunique hAg hAel hnot
  set S := conjSub y (conjSub (g : G) T) with hSdef
  have hS : IsSylowTwoOf S (stab γ) := by
    have := isSylowTwoOf_conj hTγ y
    rwa [F7.conjSub_eq_of_mem hy] at this
  have hHγ : H ≤ stab γ := hH.1
  haveI : Finite ↥H := Finite.of_injective (Subgroup.inclusion hHγ)
    (Subgroup.inclusion_injective hHγ)
  have hAH : A ≤ H := by
    have h1 : A ⊔ pCoreOf 2 (stab γ) ≤ E1.tauOf (stab γ) S A := le_tauOf_loc hS hAS hAel
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
    have hres : twoResidual H ≤ conjClosure A H := twoResidual_le_conjClosure_loc ⟨1, hH⟩
    have hHle : H ≤ (S ⊓ H) ⊔ conjClosure A H :=
      calc H = (S ⊓ H) ⊔ twoResidual H := (sup_twoResidual_eq_loc hSH).symm
        _ ≤ (S ⊓ H) ⊔ conjClosure A H := sup_le_sup_left hres _
    have hHN : H ≤ Subgroup.normalizer (W : Set G) :=
      hHle.trans (sup_le (inf_le_left.trans hSW) hcl)
    apply hHM
    have e : conjSub y M = stab γ ⊓ Subgroup.normalizer (W : Set G) := by
      rw [hM, conjSub_inf, F7.conjSub_eq_of_mem hy, hW, conjSub_normalizer]
    rw [e]
    exact le_inf hHγ hHN
  refine ⟨⟨(g : G), hstabγ⟩, hnot, S, H, W, hS, hAS, hH, hAH, hSW, hex, fun h hhH => ?_⟩
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

end CFSG.Quasithin.RonanF713

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] {G₀ G₁ G₂ T V : Subgroup G}

theorem f713_main [Finite ↥G₂] (hC : F7Two.ClaimCE1) (hyp : AmalgamHypV G₀ G₁ G₂ T V)
    {γ : CosetGeom G₀ G₁ G₂} (hγ : IsCriticalVertex G₀ G₁ G₂ V γ)
    (ha₃ : 3 ≤ critDist G₀ G₁ G₂ V) (ha₂ : Odd (critDist G₀ G₁ G₂ V))
    (hb : IsUniqueMaxOver G₂ T (G₂ ⊓ Subgroup.normalizer (V : Set G)))
    (hc : E1.nParam G₂ = 1) {A : Subgroup G} (hA₁ : A ≤ Vv V (γ₁ G₀ G₁ G₂))
    (hA₂ : ¬ A ≤ ballStab 1 γ) (hAel : IsElemAbelian 2 A)
    (hAβ : ∀ β : CosetGeom G₀ G₁ G₂, γ ∈ nbrs β →
      dist (γ₁ G₀ G₁ G₂) β + 2 = critDist G₀ G₁ G₂ V →
        Vv V (γ₁ G₀ G₁ G₂) ≤ pCoreOf 2 (stab β ⊓ stab γ))
    (hcore : pCoreOf 2 (stab γ) ≤ ballStab 1 γ) :
    (∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2) ∧
      (CFSG.SectionRank.IsSQTKCat ↥G₂ →
        ∃ α ∈ nbrs γ, (A ⊓ Subgroup.normalizer (Vv V α : Set G)).relIndex A = 2 ∧
          ∃ h : G, h ∈ stab γ ∧ conjSub h⁻¹ A ≤ stab α ∧ ¬ IsPGroup 2 ↥(A ⊔ conjSub h⁻¹ A)) := by
  obtain ⟨⟨g, hstab⟩, hnot, S, H, W, hS, hAS, hH, hAH, hSW, hex, hvert⟩ :=
    exists_E1_config_loc hyp hγ ha₃ ha₂ hb hc hA₁ hA₂ hAel hAβ hcore
  haveI hfinγ : Finite ↥(stab γ) := by rw [hstab]; exact finite_conjSub _ _
  have hHγ : H ≤ stab γ := hH.1
  haveI : Finite ↥H := Finite.of_injective (Subgroup.inclusion hHγ)
    (Subgroup.inclusion_injective hHγ)
  have hSH : IsSylowTwoOf (S ⊓ H) H := hH.2.2.1
  obtain ⟨R, hRA, hRH, hRidx⟩ := exists_index_two_of_isE_loc hAel hAH hH
  have hRN : ∀ g' ∈ H, R ≤ Subgroup.normalizer (conjSub g' W : Set G) := by
    intro g' hg'
    have e : conjSub g'⁻¹ (pCoreOf 2 H) = pCoreOf 2 H :=
      F7.conjSub_eq_of_mem_normalizer (inv_mem (le_normalizer_pCoreOf 2 H hg'))
    have hK : pCoreOf 2 H ≤ Subgroup.normalizer (conjSub g' W : Set G) := by
      rw [conjSub_normalizer, le_conjSub_iff, e]
      exact ((isSylowTwoOf_pCoreOf_le_loc hSH).trans inf_le_left).trans hSW
    exact hRH.trans hK
  refine ⟨?_, fun hSQ => ?_⟩
  · obtain ⟨g', hg', hg'not⟩ := hex
    obtain ⟨α, hα, hVα⟩ := hvert g' hg'
    exact ⟨α, hα, by
      rw [hVα]; exact F7Two.relIndex_inf_eq_two (hRN g' hg') hRA hRidx hg'not⟩
  · have hSQγ : CFSG.SectionRank.IsSQTKCat ↥(stab γ) := by
      rw [hstab]
      exact isSQTKCat_conjSub_loc g hSQ
    have hgen := claimCE1_loc hC hSQγ hS hAS hAel hnot hH hAH
    obtain ⟨h, hh, g', hg', hAh, hAg'⟩ := F7Two.exists_nonTwoConj_not_normalizing (A := A)
      (H := H) (P := S ⊓ H) (X := twoResidual H) (W := W) (le_inf hAS hAH) inf_le_right
      (inf_le_left.trans hSW) (inf_le_right.trans (le_normalizer_twoResidual H))
      (by rw [sup_comm]; exact (sup_twoResidual_eq_loc hSH).ge) hgen hex
    obtain ⟨α₀, hα₀, hVα₀⟩ := hvert g' hg'
    have hidx : (A ⊓ Subgroup.normalizer (conjSub g' W : Set G)).relIndex A = 2 :=
      F7Two.relIndex_inf_eq_two (hRN g' hg') hRA hRidx hAg'
    have hhγ : h ∈ stab γ := hHγ hh.1
    have hAγ : A ≤ stab γ := hAS.trans hS.1
    have hXγ : conjSubgroup A h ≤ stab γ := by
      have := conjSub_mono h⁻¹ hAγ
      rwa [F7.conjSub_eq_of_mem (inv_mem hhγ)] at this
    have hXp : IsPGroup 2 ↥(conjSubgroup A h) :=
      (F7Two.isPGroup_conjSubgroup_iff h).mpr (isPGroup_of_isElemAbelian hAel)
    obtain ⟨α, hα, hVα, hXα⟩ := exists_nbr_fixed_of_le_normalizer_loc hyp hα₀ hXp hXγ
      (by rw [hVα₀]; exact hAh)
    exact ⟨α, hα, by rw [hVα, hVα₀]; exact hidx, h, hhγ, hXα, hh.2⟩

end CFSG.Quasithin.RonanF713
