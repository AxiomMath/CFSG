module

public import CFSG.RankThree.PartTwo.Sec15.LiebeckY4ProdDefs
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofProd
import CFSG.RankThree.PartTwo.Sec15.Read148PerfProof
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofMem

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Proof15Res8Prod Proof15Res8Diag

section Types

variable {Γ : Type*} [Group Γ] {U V : Subgroup Γ}

theorem prodType_symm (h : ProdTypeA U V ∨ ProdTypeHJ U V) :
    ProdTypeA V U ∨ ProdTypeHJ V U := by
  rcases h with (⟨h3, hU, hV⟩ | ⟨hinf, h | h | h | h⟩) | ⟨hinf, hU, hV⟩
  · exact Or.inl (Or.inl ⟨by rwa [inf_comm], hV, hU⟩)
  · exact Or.inl (Or.inr ⟨by rwa [inf_comm], Or.inr (Or.inl ⟨h.2, h.1⟩)⟩)
  · exact Or.inl (Or.inr ⟨by rwa [inf_comm], Or.inl ⟨h.2, h.1⟩⟩)
  · exact Or.inl (Or.inr ⟨by rwa [inf_comm], Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))⟩)
  · exact Or.inr ⟨by rwa [inf_comm], h.2, h.1⟩
  · exact Or.inl (Or.inr ⟨by rwa [inf_comm], Or.inr (Or.inr (Or.inr ⟨hV, hU⟩))⟩)

end Types

section Factors

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} [(ker148 A M).Normal]

private theorem exists_component_map_eq {X : Subgroup G} (hXM : X ≤ M)
    (hN : ((X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))).Normal)
    {W : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)} (hWX : W ≤ img148 A M X)
    (hXW : img148 A M X ≤ Subgroup.normalizer (W : Set (↥(M ⊔ A) ⧸ ker148 A M)))
    (hWq : IsQuasisimple ↥W) :
    ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), IsComponent J ∧
      J.map (iota148 (A := A) (M := M)) = W := by
  set ι := iota148 (A := A) (M := M)
  have hιi : Function.Injective ι := iota148_injective
  set Xs := (X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))
  have hXι : Xs.map ι = img148 A M X := map_iota148 (A := A) hXM
  set J := W.comap ι
  have hJX : J ≤ Xs := by
    intro q hq
    have h1 : ι q ∈ Xs.map ι := hXι ▸ hWX hq
    obtain ⟨x, hx, hxq⟩ := h1
    exact hιi hxq ▸ hx
  have hXJ : Xs ≤ Subgroup.normalizer (J : Set (↥M ⧸ CFSG.pPrimeCore 3 ↥M)) := by
    intro d hd
    apply mem_normalizer_of_conj_mem
    intro q hq
    show ι (d * q * d⁻¹) ∈ W
    rw [map_mul, map_mul, map_inv]
    have hdW : ι d ∈ Subgroup.normalizer (W : Set (↥(M ⊔ A) ⧸ ker148 A M)) :=
      hXW (hXι ▸ Subgroup.mem_map_of_mem ι hd)
    exact (Subgroup.mem_normalizer_iff.mp hdW (ι q)).mp hq
  have hJW : J.map ι = W := by
    refine Subgroup.map_comap_eq_self ?_
    intro w hw
    obtain ⟨x, -, hxw⟩ := (hXι ▸ hWX hw : w ∈ Xs.map ι)
    exact ⟨x, hxw⟩
  have hJq : IsQuasisimple ↥J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((J.equivMapOfInjective ι hιi).trans (MulEquiv.subgroupCongr hJW)).symm hWq
  exact ⟨J, ⟨hJq, Subgroup.IsSubnormal.step J Xs hJX hN.isSubnormal
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hJX).mpr hXJ)⟩, hJW⟩

private theorem exists_shape {J : Subgroup G} (hJM : J ∈ thetaComponentsIn M)
    (hJD : J ≤ deltaZero A (lB A) M) (hJR : ¬ J.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M)
    (hN : (((deltaZero A (lB A) M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))).Normal)
    (hDp : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)))
    {U V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M)}
    (hsup : U ⊔ V = img148 A M (deltaZero A (lB A) M))
    (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u)
    (hDU : img148 A M (deltaZero A (lB A) M) ≤
      Subgroup.normalizer (U : Set (↥(M ⊔ A) ⧸ ker148 A M)))
    (hDV : img148 A M (deltaZero A (lB A) M) ≤
      Subgroup.normalizer (V : Set (↥(M ⊔ A) ⧸ ker148 A M)))
    (hUq : IsQuasisimple ↥U) (hVq : IsQuasisimple ↥V) (hty : ProdTypeA U V ∨ ProdTypeHJ U V) :
    ∃ U V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M),
      img148 A M (deltaZero A (lB A) M) = U ⊔ V ∧ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧
        Group.IsPerfect ↥(U ⊔ V) ∧ img148 A M J = U ∧ (ProdTypeA U V ∨ ProdTypeHJ U V) := by
  have hJleM : J ≤ M := le_of_mem_thetaComponentsIn hJM
  have hXM : deltaZero A (lB A) M ≤ M := deltaZero_le M
  obtain ⟨JU, hJUc, hJU⟩ := exists_component_map_eq hXM hN (le_sup_left.trans hsup.le) hDU hUq
  obtain ⟨JV, hJVc, hJV⟩ := exists_component_map_eq hXM hN (le_sup_right.trans hsup.le) hDV hVq
  have hJc : IsComponent ((J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))) :=
    Y4Core.isComponent_map_mk' (mem_thetaComponentsIn_iff.mp hJM).2 hJR
  have hJle : (J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M)) ≤ JU ⊔ JV := by
    rw [← Subgroup.map_le_map_iff_of_injective (iota148_injective (A := A) (M := M)),
      Subgroup.map_sup, hJU, hJV, hsup, map_iota148 hJleM]
    exact img148_mono hJD
  have hDp' : Group.IsPerfect ↥(U ⊔ V) := hsup ▸ hDp
  rcases Y4Core.eq_or_eq_of_le_sup hJc (Or.inr hJUc) (Or.inr hJVc) hJle with h | h
  · refine ⟨U, V, hsup.symm, hc, hDp', ?_, hty⟩
    rw [← map_iota148 hJleM, h, hJU]
  · refine ⟨V, U, by rw [sup_comm V U]; exact hsup.symm, fun v hv u hu => (hc u hu v hv).symm,
      by rw [sup_comm V U]; exact hDp', ?_, prodType_symm hty⟩
    rw [← map_iota148 hJleM, h, hJV]

private theorem exists_shape_of_types {J : Subgroup G} (hJM : J ∈ thetaComponentsIn M)
    (hJD : J ≤ deltaZero A (lB A) M) (hJR : ¬ J.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M)
    (hN : (((deltaZero A (lB A) M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))).Normal)
    (hDp : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)))
    (hrank : ∀ F : Subgroup (↥(M ⊔ A) ⧸ ker148 A M), CFSG.Assembly.IsElemAbelian 3 F →
      Nat.card F ≤ 27)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2)
    (hcase : IsCentralProductA6Covers ↥(img148 A M (deltaZero A (lB A) M)) ∨
      IsA6CoverTimesA5 ↥(img148 A M (deltaZero A (lB A) M)) ∨
      Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
        alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2)) :
    ∃ U V : Subgroup (↥(M ⊔ A) ⧸ ker148 A M),
      img148 A M (deltaZero A (lB A) M) = U ⊔ V ∧ (∀ u ∈ U, ∀ v ∈ V, u * v = v * u) ∧
        Group.IsPerfect ↥(U ⊔ V) ∧ img148 A M J = U ∧ (ProdTypeA U V ∨ ProdTypeHJ U V) := by
  set D := img148 A M (deltaZero A (lB A) M)
  have hq5 : ∀ {X : Type} [Group X], (X ≃* alternatingGroup (Fin 5)) → IsQuasisimple X :=
    fun e => CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      Sec15.Y4Core.good3_alternatingGroup_five.1
  rcases hcase with ⟨U₀, V₀, hU₀, hV₀, hsup, hcomm, h3, hTU, hTV⟩ |
    ⟨U₀, V₀, hU₀, hV₀, hinf, hsup, hTU, ⟨eV⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  ·
    have hc₀ : ∀ a ∈ U₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
      Item148PtRes.commute_of_commutator_eq_bot hcomm ha hb
    obtain ⟨hc, hUV, hDU, hDV⟩ := factors_of_normal hU₀ hV₀ hsup hc₀
    have h3' : Nat.card (U₀.map D.subtype ⊓ V₀.map D.subtype :
        Subgroup (↥(M ⊔ A) ⧸ ker148 A M)) = 3 := by
      rw [map_inf_subtype, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h3]
    have hTU' := isTripleCover_congr
      (U₀.equivMapOfInjective _ (Subgroup.subtype_injective _)) hTU
    have hTV' := isTripleCover_congr
      (V₀.equivMapOfInjective _ (Subgroup.subtype_injective _)) hTV
    have hcV : ∀ v ∈ V₀.map D.subtype, ∀ u ∈ U₀.map D.subtype, v * u = u * v :=
      fun v hv u hu => (hc u hu v hv).symm
    have hUp := isPerfect_of_six_six hc h3' hTU' hTV' hrank
    have hVp := isPerfect_of_six_six hcV (by rwa [inf_comm]) hTV' hTU' hrank
    exact exists_shape hJM hJD hJR hN hDp hUV hc hDU hDV (isQuasisimple_tripleCover hUp hTU')
      (isQuasisimple_tripleCover hVp hTV') (Or.inl (Or.inl ⟨h3', ⟨hUp, hTU'⟩, ⟨hVp, hTV'⟩⟩))
  ·
    have hc₀ : ∀ a ∈ U₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
      Item148PtRes.commute_of_commutator_eq_bot
        (le_bot_iff.mp (hinf ▸ Subgroup.commutator_le_inf U₀ V₀)) ha hb
    obtain ⟨hc, hUV, hDU, hDV⟩ := factors_of_normal hU₀ hV₀ hsup hc₀
    have hinf' : U₀.map D.subtype ⊓ V₀.map D.subtype = ⊥ := by
      rw [map_inf_subtype, hinf, Subgroup.map_bot]
    have hTU' := isTripleCover_congr
      (U₀.equivMapOfInjective _ (Subgroup.subtype_injective _)) hTU
    have eV' := (V₀.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eV
    have hDp' : Group.IsPerfect ↥(U₀.map D.subtype ⊔ V₀.map D.subtype) := by
      rw [hUV]
      exact hDp
    have hUp := isPerfect_of_six_five hc hinf' hDp'
    exact exists_shape hJM hJD hJR hN hDp hUV hc hDU hDV (isQuasisimple_tripleCover hUp hTU')
      (hq5 eV') (Or.inl (Or.inr ⟨hinf', Or.inl ⟨⟨hUp, hTU'⟩, ⟨eV'⟩⟩⟩))
  ·
    obtain ⟨U, V, hc, hinf, hUV, hDU, hDV, ⟨eU⟩, ⟨eV⟩⟩ := exists_factors_of_prod φ
    exact exists_shape hJM hJD hJR hN hDp hUV hc hDU hDV (hq5 eU) (hq5 eV)
      (Or.inl (Or.inr ⟨hinf, Or.inr (Or.inr (Or.inl ⟨⟨eU⟩, ⟨eV⟩⟩))⟩))
  ·
    obtain ⟨U, V, hc, hinf, hUV, hDU, hDV, ⟨eU⟩, ⟨eV⟩⟩ := exists_factors_of_prod φ
    have hVp : Group.IsPerfect ↥V :=
      isPerfect_of_six_five (U := V) (V := U) (fun v hv u hu => (hc u hu v hv).symm)
        (by rwa [inf_comm]) (by rw [sup_comm V U, hUV]; exact hDp)
    have : IsSimpleGroup ↥V := haveI := hJ2; eV.isSimpleGroup
    exact exists_shape hJM hJD hJR hN hDp hUV hc hDU hDV (hq5 eU)
      (Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect this hVp)
      (Or.inl (Or.inr ⟨hinf, Or.inr (Or.inr (Or.inr ⟨⟨eU⟩, ⟨eV⟩⟩))⟩))

end Factors

section Main


variable {G : Type} [Group G] [Finite G]

private theorem prodCases_of_item148 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h148 : Item148 A (lB A)) {M : Subgroup G} (hM : M ∈ scriptY2 A)
    (hq : ¬ IsQuasisimple ↥(((deltaZero A (lB A) M).subgroupOf M).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥M))))
    (hne : ¬ deltaZero A (lB A) M ≤ pPrimeCoreOf 3 M) :
    letI := ker148_normal hM.1.2
    IsCentralProductA6Covers ↥(img148 A M (deltaZero A (lB A) M)) ∨
      IsA6CoverTimesA5 ↥(img148 A M (deltaZero A (lB A) M)) ∨
      Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∨
      Nonempty (↥(img148 A M (deltaZero A (lB A) M)) ≃*
        alternatingGroup (Fin 5) × CFSG.Blueprint.NativeSporadic.J2) := by
  let := ker148_normal hM.1.2
  obtain ⟨e₀⟩ := Y4Core.nonempty_img148_equiv_map hM.1.2 (deltaZero_le (LB := lB A) M)
  have hperf : Group.IsPerfect ↥(img148 A M (deltaZero A (lB A) M)) :=
    Read148Perf.isPerfect_img148 h h148 hM.1
  have hnq : ¬ IsQuasisimple ↥(img148 A M (deltaZero A (lB A) M)) := fun hq' =>
    hq (CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀ hq')
  have hsimp : ¬ IsSimpleGroup ↥(img148 A M (deltaZero A (lB A) M)) := fun hs =>
    hnq (Proof15Res6.isQuasisimple_of_isSimpleGroup_of_isPerfect hs hperf)
  obtain ⟨-, hcases⟩ := (item148_iff A (lB A)).mp h148 M hM.1
  rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact absurd h1 hne
  ·
    exfalso
    obtain ⟨_, -, -, L', hL', hcases⟩ := h2
    rcases hcases with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, _, hp, hf, _, -, hε⟩ | ⟨-, h6' | ⟨⟨φ⟩⟩⟩
    · exact hnq (CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hL'.1))
    · have := Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact hsimp φ.isSimpleGroup
    · exact hsimp (Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε)
    · have := Y4Core.isSimpleGroup_alternatingGroup 6 (by norm_num)
      exact hnq (Proof15Res6.isQuasisimple_of_isTripleCover_of_isPerfect hperf h6')
    · have := Y4Core.isSimpleGroup_alternatingGroup 5 le_rfl
      exact hsimp φ.isSimpleGroup
  ·
    have h3' := h3
    obtain ⟨_, _, _, -, -, -, -, -, -, -, hcases⟩ := h3'
    rcases hcases with hON | hCP | hA6A5 | hφ | ⟨⟨φ⟩⟩ | ⟨_, ⟨φ⟩⟩
    · exfalso
      have := CFSG.Sporadic.ON.fam_on_simplicity.2.2
      exact hnq (Proof15Res6.isQuasisimple_of_isTripleCover_of_isPerfect hperf hON)
    · exact Or.inl hCP
    · exact Or.inr (Or.inl hA6A5)
    · exact Or.inr (Or.inr (Or.inl hφ))
    · exfalso
      have := Y4Core.isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact hsimp φ.isSimpleGroup
    · exfalso
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      exact hsimp φ.isSimpleGroup
  ·
    exfalso
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    have := Y4Core.isSimpleGroup_alternatingGroup 10 (by norm_num)
    exact hsimp φ.isSimpleGroup
  ·
    exfalso
    obtain ⟨_, -, _, n, _, -, -, hn, -, hiso, -⟩ := h5
    exact hsimp (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega : 1 ≤ 3 * n)
      hiso).1
  ·
    obtain ⟨hφ, -, -⟩ := h6
    exact Or.inr (Or.inr (Or.inr hφ))
  ·
    exact (Proof15Res6.false_of_case148Seven_two h h148 hM h7).elim

theorem step148ProdShape_of (h148 : Item148R) (h149 : Sec16.Item149S14)
    (hbot : Item145BotS14) : Step148ProdShape := by
  intro G _ _ A c L hR _ M hM _ hq J hJ hAJ
  have h14 := hR.toSec14Std
  have h148' := h148 G A c L hR
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := hM.1.2
  let := ker148_normal hAM
  have hJM : J ∈ thetaComponentsIn M :=
    Y4Core.mem_thetaComponentsIn_of_item149 (h149 G A c L h14) hM.1 hJ
  have hJD : J ≤ deltaZero A (lB A) M :=
    calc J = oPrimeResidualOf 3 J := hJ.2
      _ ≤ oPrimeResidualOf 3 (delta A (lB A) M) :=
        oPrimeResidualOf_mono 3 (Y4Core.le_of_mem_comp3In hJ)
      _ ≤ deltaZero A (lB A) (delta A (lB A) M) :=
        Y4Core.oPrimeResidualOf_le_deltaZero h14.isE27 (hbot G A c L h14)
          (le_normalizer_delta M) (delta_delta M).symm
      _ ≤ deltaZero A (lB A) M := deltaZero_mono (delta_le M)
  have hJcomp : J ∈ comp3In M := ⟨hJM, hJ.2⟩
  have hJR : ¬ J.subgroupOf M ≤ CFSG.pPrimeCore 3 ↥M := fun hle =>
    Y4Core.not_le_pPrimeCoreOf hJcomp (by
      rw [← Subgroup.map_subgroupOf_eq_of_le (mem_thetaComponentsIn_iff.mp hJM).1]
      exact Subgroup.map_mono hle)
  have hne : ¬ deltaZero A (lB A) M ≤ pPrimeCoreOf 3 M := fun h1 =>
    Y4Core.not_le_pPrimeCoreOf hJcomp (hJD.trans h1)
  exact exists_shape_of_types hJM hJD hJR ((item148_iff A (lB A)).mp h148' M hM.1).1
    (Read148Perf.isPerfect_img148 h14 h148' hM.1)
    (fun F hF => card_le_of_isElemAbelian_img148 h14 hAM hM.2 hF)
    CFSG.Sporadic.J2.isSimpleGroup_J2 (prodCases_of_item148 h14 h148' hM hq hne)

end Main

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4
