module

public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBEightA
public import CFSG.LocalAnalysis.WeakClosure81.EightTailPShape
public import CFSG.LocalAnalysis.WeakClosure81.W16LSixBBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem w16l_exists_isBarMap_of_eq {Γ : Type} [Group Γ] {K K' N N' : Subgroup Γ} {X : Type}
    [Group X] {φ : ↥K →* X} (hK : K = K') (hN : N = N') (hφ : SevenK.IsBarMap K N φ) :
    ∃ φ' : ↥K' →* X, SevenK.IsBarMap K' N' φ' ∧
      ∀ A : Subgroup Γ, SevenK.barSub K' φ' A = SevenK.barSub K φ A := by
  subst hK
  subst hN
  exact ⟨φ, hφ, fun A => rfl⟩

section Certified


theorem IsMinFam16.kGenIn_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) =
      kSub (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (vHat (D.img H)) := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  let A : Subgroup (VG (D.img H)) := hatV1 D V₀ V
  let E : Subgroup (VG (D.img H)) := vHat (D.img H)
  have h711 : SevenK.Hyp711 A ⊤ E := IsMinFam16.hyp711_img h1 h5 hS h hH hV D
  have hEnorm : E.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : E ≤ ⊤)).mp h711.normal
  have hpcn : (pCoreOf 2 (⊤ : Subgroup (VG (D.img H)))).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤
  obtain ⟨g₀, -, hEA, hApc⟩ := mem_omegaSet.1 h711.mem
  have hkconj : kSub A ⊤ E ≤ CFSG.Quasithin.conjClosure A ⊤ := by
    refine iSup₂_le fun U hU => ?_
    obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.1 hU
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hx' : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ CFSG.Quasithin.conjClosure A ⊤ :=
      mem_conjClosure (Z := A) (H := (⊤ : Subgroup (VG (D.img H))))
        (h := g⁻¹) (z := g * x * g⁻¹) trivial hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at hx'
  change kGenIn A ⊤ = kSub A ⊤ E
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun k hk => ?_
    refine le_iSup₂_of_le (conjSubgroup A k) ?_ le_rfl
    rw [mem_omegaSet]
    refine ⟨k, rfl, ?_, ?_⟩
    · intro hbot
      haveI : E.Normal := hEnorm
      have hconjE : conjSubgroup E k = E := by
        rw [conjSubgroup_eq_iff_mem_normalizer]
        exact Subgroup.le_normalizer_of_normal (H := E) (K := ⊤) trivial
      have h1 : conjSubgroup (E ⊓ A) k = ⊥ := by
        rw [E3.conjSubgroup_inf, hconjE, hbot]
      have h2 : E ⊓ A = ⊥ := by
        have hh := congrArg (fun X : Subgroup (VG (D.img H)) => conjSubgroup X k⁻¹) h1
        rwa [E3.conjSubgroup_conj_inv, E3.conjSubgroup_bot] at hh
      exact hEA h2
    · intro hle
      apply hApc
      haveI : (pCoreOf 2 (⊤ : Subgroup (VG (D.img H)))).Normal := hpcn
      have hconjPc : conjSubgroup (pCoreOf 2 (⊤ : Subgroup (VG (D.img H)))) k⁻¹ =
          pCoreOf 2 (⊤ : Subgroup (VG (D.img H))) := by
        rw [conjSubgroup_eq_iff_mem_normalizer]
        exact Subgroup.le_normalizer_of_normal
          (H := pCoreOf 2 (⊤ : Subgroup (VG (D.img H)))) (K := ⊤) trivial
      calc A = conjSubgroup (conjSubgroup A k) k⁻¹ := (E3.conjSubgroup_conj_inv A k).symm
        _ ≤ conjSubgroup (pCoreOf 2 (⊤ : Subgroup (VG (D.img H)))) k⁻¹ :=
            E3.conjSubgroup_mono_left k⁻¹ hle
        _ = pCoreOf 2 (⊤ : Subgroup (VG (D.img H))) := hconjPc
  · refine iSup₂_le fun U hU => ?_
    obtain ⟨k, hk, hUk⟩ := h711.transitive U hU
    rw [hUk]
    exact le_iSup₂_of_le k (hkconj hk) le_rfl

theorem IsMinFam16.top_eq_kGenIn_sup_hatT1 (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    (⊤ : Subgroup (VG (D.img H))) =
      kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) ⊔ hatT1 D S := by
  have hVH : V ≤ H := h.V_le_S.trans hH.1.1
  let A : Subgroup (VG (D.img H)) := hatV1 D V₀ V
  let E : Subgroup (VG (D.img H)) := vHat (D.img H)
  have hKeq : kGenIn A ⊤ = kSub A ⊤ E := IsMinFam16.kGenIn_hat h1 h5 hS h hH hV D
  have hsup : S ⊔ CFSG.Quasithin.conjClosure V H = H :=
    IsMinFam16.sup_conjClosure_eq h1 hS h hH hV
  have hSH : S ≤ H := hH.1.1
  have hKH : CFSG.Quasithin.conjClosure V H ≤ H :=
    conjClosure_le fun g hg z hz => H.mul_mem (H.mul_mem hg (hVH hz)) (H.inv_mem hg)
  have hass : Assumption131 (D.img H) (hatGamma D V) (hatVA D V₀ V) (mRank (D.img V)) :=
    Cex16.assumption131_iSub16 h1 h5 hS h hH.1 hV D
  have hrank : ∀ B ∈ hatGamma D V, mRank B ≤ mRank (D.img V) :=
    Cex16.mRank_le_iSub16 h hH.1 D
  have htrans : ∀ B ∈ hatGamma D V, ∀ C ∈ hatGamma D V, ∃ k ∈ D.img H, C = cj k B :=
    hatGamma_transitive D V hVH
  have hA₀ : D.img V ∈ hatGamma D V := ⟨1, H.one_mem, by rw [conjSubgroup_one]⟩
  have hmapK : (kSub A ⊤ E).map (projG (D.img H)) = hatK D V :=
    (map_projG_kSub_UAOf_orbit hass hrank htrans hA₀).trans (kHatOf_hatGamma_eq D V hVH)
  have hhKn : D.img H ≤ Subgroup.normalizer (hatK D V : Set (LGL 2 D.W)) :=
    D.img_le_normalizer le_rfl hKH (le_normalizer_conjClosure V H)
  have hS_le : D.img S ≤ Subgroup.normalizer (hatK D V : Set (LGL 2 D.W)) :=
    (D.img_mono hSH).trans hhKn
  have hImgH : D.img H = hatK D V ⊔ D.img S := by
    calc D.img H = D.img (S ⊔ CFSG.Quasithin.conjClosure V H) := congrArg D.img hsup.symm
      _ = D.img S ⊔ D.img (CFSG.Quasithin.conjClosure V H) := D.img_sup hSH hKH
      _ = hatK D V ⊔ D.img S := by rw [sup_comm]
  have hcoe : (↑(D.img H) : Set (LGL 2 D.W)) =
      (hatK D V : Set (LGL 2 D.W)) * (D.img S : Set (LGL 2 D.W)) := by
    rw [hImgH]
    exact Subgroup.coe_mul_of_right_le_normalizer_left (hatK D V) (D.img S) hS_le
  change (⊤ : Subgroup (VG (D.img H))) = kGenIn A ⊤ ⊔ hatT1 D S
  rw [hKeq]
  refine le_antisymm ?_ le_top
  intro x _
  have hx : projG (D.img H) x ∈ (↑(D.img H) : Set (LGL 2 D.W)) := x.2.2
  rw [hcoe, Set.mem_mul] at hx
  obtain ⟨k, hkK, s, hsS, hks⟩ := hx
  have hkK' : k ∈ (kSub A ⊤ E).map (projG (D.img H)) := by
    rw [hmapK]
    exact hkK
  obtain ⟨k', hk'K₁, hk'proj⟩ := Subgroup.mem_map.1 hkK'
  have hmem : k'⁻¹ * x ∈ hatT1 D S := by
    show projG (D.img H) (k'⁻¹ * x) ∈ D.img S
    rw [map_mul, map_inv, hk'proj, ← hks]
    rw [show k⁻¹ * (k * s) = s by group]
    exact hsS
  have hxsup := Subgroup.mul_mem_sup hk'K₁ hmem
  rw [show k' * (k'⁻¹ * x) = x by group] at hxsup
  exact hxsup

theorem IsMinFam16.exists_hatBar_kGenIn (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H)) :
    ∃ φ : ↥(kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))) →* hatX D V,
      SevenK.IsBarMap (kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))))
        (pCoreOf 2 (kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))))) φ ∧
      SevenK.barSub (kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))) φ
        (hatV1 D V₀ V) = hatS D V := by
  let A : Subgroup (VG (D.img H)) := hatV1 D V₀ V
  let E : Subgroup (VG (D.img H)) := vHat (D.img H)
  obtain ⟨φ, hbar, himg⟩ := IsMinFam16.exists_hatBar h1 h5 hS h hH hV D
  have hKeq : kSub A ⊤ E = kGenIn A ⊤ :=
    (IsMinFam16.kGenIn_hat h1 h5 hS h hH hV D).symm
  have hNeq : pCoreOf 2 (kSub A ⊤ E) = pCoreOf 2 (kGenIn A ⊤) :=
    congrArg (pCoreOf 2) hKeq
  obtain ⟨φ', hbar', hsame⟩ := w16l_exists_isBarMap_of_eq hKeq hNeq hbar
  refine ⟨φ', hbar', ?_⟩
  change SevenK.barSub (kGenIn A ⊤) φ' A = hatS D V
  rw [hsame A, himg]

theorem IsMinFam16.shapeData_hat (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (D : ModDataE H (iSub16 V H))
    (hcent : Nat.card (hatS D V) = 2 → CentralInSylow (hatX D V) (hatS D V)) :
    ∃ φ : ↥(kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))) →* hatX D V,
      ShapeData (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H))) (hatT1 D S) φ ∧
      SevenK.barSub (kGenIn (hatV1 D V₀ V) (⊤ : Subgroup (VG (D.img H)))) φ
        (hatV1 D V₀ V) = hatS D V := by
  let A : Subgroup (VG (D.img H)) := hatV1 D V₀ V
  obtain ⟨φ, hbar, himg⟩ := IsMinFam16.exists_hatBar_kGenIn h1 h5 hS h hH hV D
  have hsit : BarSituation (hatX D V) (SevenK.barSub (kGenIn A ⊤) φ A) := by
    rw [himg]
    exact IsMinFam16.barSituation_hat h1 h5 hS h hH hV D
  have hcentral : Nat.card (SevenK.barSub (kGenIn A ⊤) φ A) = 2 →
      CentralInSylow (hatX D V) (SevenK.barSub (kGenIn A ⊤) φ A) := by
    intro hc
    rw [himg] at hc ⊢
    exact hcent hc
  refine ⟨φ, ⟨IsMinFam16.hyp83_hat h1 h5 hS h hH hV D,
    IsMinFam16.top_eq_kGenIn_sup_hatT1 h1 h5 hS h hH hV D, hbar, hsit, hcentral⟩, ?_⟩
  change SevenK.barSub (kGenIn A ⊤) φ A = hatS D V
  exact himg

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
