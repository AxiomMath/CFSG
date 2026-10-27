module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsF
import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.Setup
import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintFam
import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintReduced
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5EF
import CFSG.LocalAnalysis.WeakClosure81.FiveTenSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.E2.E22N CFSG.Open Subgroup
open CFSG.Quasithin.RonanE111 CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.Vol2.Ch11.SecB (E111Reduced)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (CompFactorAutInF)
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf)
open scoped commutatorElement Pointwise

variable {Q : Type} [Group Q] {T F Z : Subgroup Q}

private theorem exists_mem_le_map_eq_layerH [Finite Q] [Z.Normal] (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) {A' : Subgroup Q} (hA' : A' ∈ Ω)
    (hA'T : A'.map (QuotientGroup.mk' Z) ≤ T.map (QuotientGroup.mk' Z)) :
    ∃ A ∈ Ω, A ≤ T ∧ A.map (QuotientGroup.mk' Z) = A'.map (QuotientGroup.mk' Z) := by
  have hA'2 : IsPGroup 2 A' := fun a =>
    ⟨1, Subtype.ext (by simpa using (hΩ.isElemAbelian A' hA').2 a a.2)⟩
  have hA'TZ : A' ≤ T ⊔ Z := by
    have h1 : A' ≤ (T.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) :=
      Subgroup.map_le_iff_le_comap.mp hA'T
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  obtain ⟨m, hm, hconj⟩ :=
    exists_conjSub_le_of_isSylowIn hT le_sup_left hA'2 hA'TZ le_top
  rw [Subgroup.mem_inf] at hm
  obtain ⟨t, htT, z, hzZ, htz⟩ := (Subgroup.mem_sup_of_normal_right (s := T) (t := Z)).mp hm.1
  refine ⟨A1b.conjSub z A', hΩ.conj A' hA' z (Subgroup.mem_top z), ?_, ?_⟩
  · intro a ha
    have hmem : t * a * t⁻¹ ∈ A1b.conjSub t (A1b.conjSub z A') := A1b.mem_conjSub_of_mem ha
    rw [← A1b.conjSub_mul, htz] at hmem
    have hTmem : t * a * t⁻¹ ∈ T := hconj hmem
    have hEq : a = t⁻¹ * (t * a * t⁻¹) * t := by group
    rw [hEq]
    exact T.mul_mem (T.mul_mem (T.inv_mem htT) hTmem) htT
  · have hπz : ∀ x : Q, (QuotientGroup.mk' Z) (z * x * z⁻¹) = (QuotientGroup.mk' Z) x := by
      intro x
      have hz1 : (QuotientGroup.mk' Z) z = 1 := (QuotientGroup.eq_one_iff z).mpr hzZ
      rw [map_mul, map_mul, map_inv, hz1]
      group
    have hAdef : A1b.conjSub z A' = A'.map (MulAut.conj z).toMonoidHom := rfl
    rw [hAdef, Subgroup.map_map]
    exact congrArg (fun f => A'.map f) (MonoidHom.ext hπz)

private theorem le_map_eGenP_layerH [Finite Q] [Z.Normal] (hT : IsSylowIn 2 T ⊤)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (hO2' : pCoreOf 2 (⊤ : Subgroup (Q ⧸ Z)) = ⊥)
    (hZT : Z ⊓ T = ⊥) (hZs : Group.IsSolvable ↥Z) {Ω : Set (Subgroup Q)}
    (hΩ : E1.IsInvColl ⊤ Ω) {j : ℕ} {A : Subgroup Q} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    {I : Subgroup (Q ⧸ Z)}
    (hI : F12.IsEP j ⊤ (T.map (QuotientGroup.mk' Z)) (A.map (QuotientGroup.mk' Z)) I) :
    I ≤ (F12.eGenP j ⊤ T Ω ⊔ T).map (QuotientGroup.mk' Z) := by
  have h := isEP_iff_isEG.mp hI
  rw [layer_tauOf_map hZT hO2 hO2' hAT] at h
  obtain ⟨J, hJ, hres⟩ :=
    isEG_ten_seven hT hAT (hΩ.isElemAbelian A hAΩ) le_rfl hZs h
  have hJle : J ≤ F12.eGenP j ⊤ T Ω := le_eGenP hAΩ hAT (isEP_iff_isEG.mpr hJ)
  refine (E1.le_twoResidual_sup_of_isSylowIn hI.2.2.1).trans (sup_le ?_ ?_)
  · rw [hres]
    exact (Subgroup.map_mono ((twoResidual_le J).trans hJle)).trans (Subgroup.map_mono le_sup_left)
  · exact inf_le_left.trans (Subgroup.map_mono (le_sup_right : T ≤ F12.eGenP j ⊤ T Ω ⊔ T))

private theorem eq_sup_inf_layerH [Z.Normal] (hZF : Z ≤ F) {G₁ : Subgroup Q}
    (h : F.map (QuotientGroup.mk' Z) ≤ G₁.map (QuotientGroup.mk' Z)) : F = Z ⊔ (G₁ ⊓ F) := by
  refine le_antisymm ?_ (sup_le hZF inf_le_right)
  intro x hx
  have hx' : (QuotientGroup.mk' Z) x ∈ G₁.map (QuotientGroup.mk' Z) :=
    h (Subgroup.mem_map_of_mem _ hx)
  obtain ⟨g, hgG, hgx⟩ := Subgroup.mem_map.mp hx'
  have hzg : g⁻¹ * x ∈ Z := by
    rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker, map_mul, map_inv, hgx]
    group
  have hgF : g ∈ F := by
    have hEq : g = x * (g⁻¹ * x)⁻¹ := by group
    rw [hEq]
    exact F.mul_mem hx (F.inv_mem (hZF hzg))
  have hxEq : x = g * (g⁻¹ * x) := by group
  rw [hxEq, sup_comm]
  exact Subgroup.mul_mem_sup ⟨hgG, hgF⟩ hzg

theorem layer_eGenP_le [Finite Q] [Z.Normal] (hT : IsSylowIn 2 T ⊤)
    (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (hO2' : pCoreOf 2 (⊤ : Subgroup (Q ⧸ Z)) = ⊥)
    (hZT : Z ⊓ T = ⊥) (hZs : Group.IsSolvable ↥Z) {Ω : Set (Subgroup Q)}
    (hΩ : E1.IsInvColl ⊤ Ω) {j : ℕ} :
    F12.eGenP j ⊤ (T.map (QuotientGroup.mk' Z)) ((fun A => A.map (QuotientGroup.mk' Z)) '' Ω) ≤
      (F12.eGenP j ⊤ T Ω ⊔ T).map (QuotientGroup.mk' Z) := by
  refine iSup₂_le fun B hB => iSup_le fun hBT => iSup₂_le fun I hI => ?_
  obtain ⟨A', hA'Ω, rfl⟩ := hB
  change F12.IsEP j ⊤ (T.map (QuotientGroup.mk' Z)) (A'.map (QuotientGroup.mk' Z)) I at hI
  obtain ⟨A, hAΩ, hAT, hAA'⟩ := exists_mem_le_map_eq_layerH hT hΩ hA'Ω hBT
  rw [← hAA'] at hI
  exact le_map_eGenP_layerH hT hO2 hO2' hZT hZs hΩ hAΩ hAT hI

theorem layer_map_le_eGenP [Finite Q] [Z.Normal] {j : ℕ} (hj : 1 ≤ j) (hT : IsSylowIn 2 T ⊤)
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) (hne : Ω.Nonempty) (hbot : ∀ A ∈ Ω, A ≠ ⊥)
    (hcf : CompFactorAutInF j ⊤ T) (hO2 : pCoreOf 2 (⊤ : Subgroup Q) = ⊥) (hperf : ⁅F, F⁆ = F)
    (hZ : Z ≤ Subgroup.centralizer (F : Set Q)) (hchief : IsChiefFactorOf ⊤ F Z)
    (hC : Subgroup.centralizer (F : Set Q) ≤ F) (hFT : F ⊔ T = ⊤) :
    F.map (QuotientGroup.mk' Z) ≤
      F12.eGenP j ⊤ (T.map (QuotientGroup.mk' Z)) ((fun A => A.map (QuotientGroup.mk' Z)) '' Ω) ⊔
        T.map (QuotientGroup.mk' Z) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hAΩ, hAT⟩ := exists_mem_le_of_isSylowOf
    (CFSG.ABGLocalTools.isSylowOf_iff.mpr hT) hΩ hne
  have hR := layer_reduced hT hperf hZ hchief hC hFT
  obtain ⟨S, hS, hAS⟩ := E111R.exists_isComp_not_le hR
    (layer_map_ne_bot (layer_inf_eq_bot hT hO2 hZ hchief) hAT (hbot A hAΩ))
  set G₁ : Subgroup (Q ⧸ Z) :=
    F12.eGenP j ⊤ (T.map (QuotientGroup.mk' Z)) ((fun A => A.map (QuotientGroup.mk' Z)) '' Ω) ⊔
      T.map (QuotientGroup.mk' Z) with hG₁
  have hSG : S ≤ G₁ := by
    rw [hG₁]
    exact fourFive_le_of_not_centralizerP hj hR hS
      (layer_local hcf hT hperf hZ hchief hC hFT hS)
      (layer_isInvColl_map (Z := Z) hΩ)
      ⟨_, ⟨A, hAΩ, rfl⟩, Subgroup.map_mono hAT, hAS⟩
  rw [← E111R.iSup_conj_eq hR hS]
  refine iSup₂_le fun t ht => ?_
  intro x hx
  have hxS : t⁻¹ * x * t ∈ S := A1b.mem_conjSub_iff.mp hx
  have htG : t ∈ G₁ := Subgroup.mem_sup_right ht
  have hEq : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
  rw [hEq]
  exact G₁.mul_mem (G₁.mul_mem htG (hSG hxS)) (G₁.inv_mem htG)

theorem w3Lem45_2Chief_holds : UniquenessCase.PartTwo.W3Lem45_2Chief := by
  intro Q _ _ T j Ω F Z hj hT hΩ hne hbot hcf hO2 hperf hZ hchief hC hFT
  have hZn : Z.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hchief.1.2)
  haveI : Z.Normal := hZn
  have hZF : Z ≤ F := le_of_lt hchief.2.2.1
  have hZab : ∀ z ∈ Z, ∀ w ∈ Z, z * w = w * z := by
    intro z hz w hw
    exact (Subgroup.mem_centralizer_iff.mp (hZ hz) w (hZF hw)).symm
  have hZs : Group.IsSolvable ↥Z :=
    Group.isSolvable_of_comm fun z w => Subtype.ext (hZab z z.2 w w.2)
  have hZT : Z ⊓ T = ⊥ := layer_inf_eq_bot hT hO2 hZ hchief
  have hO2' : pCoreOf 2 (⊤ : Subgroup (Q ⧸ Z)) = ⊥ :=
    layer_pCore_eq_bot hT hperf hZ hchief hC hFT
  refine Or.inl ?_
  exact eq_sup_inf_layerH hZF
    ((layer_map_le_eGenP hj hT hΩ hne hbot hcf hO2 hperf hZ hchief hC hFT).trans
      (sup_le (layer_eGenP_le hT hO2 hO2' hZT hZs hΩ) (Subgroup.map_mono le_sup_right)))

end CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer
