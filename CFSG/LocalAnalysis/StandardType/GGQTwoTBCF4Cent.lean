module

public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public import CFSG.Blueprint.Chevalley
public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Good
import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap
import CFSG.LocalAnalysis.StandardType.GGF4TwoNTFrame
import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
import CFSG.LocalAnalysis.StandardType.GGTorusGenSpTwoCent
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.StandardType.TBCF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.SeitzReduction.F4Pilot
open CFSG.StandardType.TableBF4TwoInputs CFSG.StandardType.TableBF4TwoTB
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie

section


theorem ggTBC_F4Two_centralizer_le {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {H : Subgroup (adjointGroup .F4 K)} (hH : CFSG.Open.IsElemAbelian 3 H)
    (hcard : Nat.card H = 3 ^ 4) :
    Subgroup.centralizer (H : Set (adjointGroup .F4 K)) ≤ H := by
  classical
  haveI : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  obtain ⟨c, hc⟩ := F4TwoNonToral.exists_conj_frame_of_card_F4 K hK H hH
    (le_of_eq hcard.symm)
  suffices hframe : Subgroup.centralizer ((tE K).range : Set (adjointGroup .F4 K)) ≤
      (tE K).range by
    intro g hg
    have hgT : c⁻¹ * g * c ∈
        Subgroup.centralizer ((tE K).range : Set (adjointGroup .F4 K)) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro t ht
      have htH : c * t * c⁻¹ ∈ H := by
        rw [hc]
        exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      have hcomm : (c * t * c⁻¹) * g = g * (c * t * c⁻¹) := hg (c * t * c⁻¹) htH
      calc t * (c⁻¹ * g * c) = c⁻¹ * ((c * t * c⁻¹) * g) * c := by group
        _ = c⁻¹ * (g * (c * t * c⁻¹)) * c := by rw [hcomm]
        _ = (c⁻¹ * g * c) * t := by group
    have hmem : c⁻¹ * g * c ∈ (tE K).range := hframe hgT
    rw [hc]
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * g * c, hmem, ?_⟩
    show MulAut.conj c (c⁻¹ * g * c) = g
    rw [MulAut.conj_apply]
    group
  set T : Subgroup (adjointGroup .F4 K) := (tE K).range with hTdef
  set T3 : Subgroup (adjointGroup .F4 K) := (TableBF4Two.torus3 K).range
  set D : Subgroup (adjointGroup .F4 K) := C3Levi K with hDdef
  set N : Subgroup (adjointGroup .F4 K) := Subgroup.zpowers (nodeElt K) with hNdef
  have hnT : nodeElt K ∈ T := X1F4.nodeElt_mem_range
  have hT3T : T3 ≤ T := X1F4.range_torus3_le_range_tE
  have hT3D : T3 ≤ D := TableBF4TwoInputs.range_torus3_le_C3Levi
  have hcardT3 : Nat.card T3 = 3 ^ 3 := TableBF4TwoInputs.card_range_torus3
  have hTel : CFSG.Open.IsElemAbelian 3 T := X1F4.isElemAbelian_range_tE
  have hT3el : CFSG.Open.IsElemAbelian 3 T3 := X1F4.isElemAbelian_of_le hTel hT3T
  have hX := centralizer_nonsplit (K := K) TableBF4TwoInputs.zpowers_nodeElt_le
    (Subgroup.isCyclic_zpowers _) (TableBF4TwoInputs.card_zpowers_nodeElt hK)
  have hXc : Subgroup.centralizer (N : Set (adjointGroup .F4 K)) = N ⊔ D := by
    rw [hNdef, hDdef]
    exact hX.1
  have hXdisj : N ⊓ D = ⊥ := by
    rw [hNdef, hDdef]
    exact disjoint_iff.1 hX.2.1
  have hXcomm : N ≤ Subgroup.centralizer (D : Set (adjointGroup .F4 K)) := by
    rw [hNdef, hDdef]
    exact hX.2.2
  intro g hg
  have hgC_T : ∀ t ∈ T, t * g = g * t := fun t ht =>
    Subgroup.mem_centralizer_iff.1 hg t ht
  have hgC_N : g ∈ Subgroup.centralizer (N : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hgC_T y (Subgroup.zpowers_le.2 hnT (hNdef ▸ hy))
  have hgND : g ∈ ((N ⊔ D : Subgroup (adjointGroup .F4 K)) : Set _) := by
    rw [← hXc]
    exact hgC_N
  have hNnorm : N ≤ Subgroup.normalizer (D : Set (adjointGroup .F4 K)) :=
    hXcomm.trans (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right N D hNnorm] at hgND
  obtain ⟨x, hxN, l, hlD, hxl⟩ := hgND
  have hxT : x ∈ T := Subgroup.zpowers_le.2 hnT (hNdef ▸ hxN)
  have hxcentT : x ∈ Subgroup.centralizer (T : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact hTel.comm ht hxT
  have hlcentT : l ∈ Subgroup.centralizer (T : Set (adjointGroup .F4 K)) := by
    have hl_eq : l = x⁻¹ * g := by rw [← hxl]; group
    rw [hl_eq]
    exact mul_mem (inv_mem hxcentT) hg
  have hlcentT3 : l ∈ Subgroup.centralizer (T3 : Set (adjointGroup .F4 K)) := by
    rw [Subgroup.mem_centralizer_iff] at hlcentT ⊢
    intro t ht
    exact hlcentT t (hT3T ht)
  set φ : StatedSp 3 K →* adjointGroup .F4 K :=
    D.subtype.comp (c3LeviEquiv K).toMonoidHom with hφdef
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply (c3LeviEquiv K).injective
    apply Subtype.ext
    simpa [hφdef] using hab
  set E : Subgroup (StatedSp 3 K) := T3.comap φ with hEdef
  have hEel : CFSG.Open.IsElemAbelian 3 E := by
    rw [hEdef]
    exact hT3el.comap (f := φ) hφinj
  have hEsc : ∀ Z : StatedSp 3 K, (∀ Y ∈ E, Z * Y = Y * Z) → Z ^ 3 = 1 → Z ∈ E := by
    intro Z hZ hZ3
    set z' : adjointGroup .F4 K := φ Z with hz'def
    have hz'3 : z' ^ 3 = 1 := by
      rw [hz'def, ← map_pow, hZ3, map_one]
    have hz'D : z' ∈ D := by
      have hmem : ((c3LeviEquiv K Z : C3Levi K) : adjointGroup .F4 K) ∈ C3Levi K :=
        (c3LeviEquiv K Z).2
      simpa [hz'def, hφdef, hDdef] using hmem
    have hDleC : D ≤ Subgroup.centralizer (N : Set (adjointGroup .F4 K)) :=
      Subgroup.le_centralizer_iff.1 hXcomm
    have hz'N : ∀ y ∈ N, y * z' = z' * y := fun y hy =>
      Subgroup.mem_centralizer_iff.1 (hDleC hz'D) y hy
    have hz'T3 : z' ∈ Subgroup.centralizer (T3 : Set (adjointGroup .F4 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨Y, hYφ⟩ : ∃ Y : StatedSp 3 K, φ Y = t := by
        refine ⟨(c3LeviEquiv K).symm ⟨t, hT3D ht⟩, ?_⟩
        simp [hφdef]
      have hYE : Y ∈ E := by
        rw [hEdef, Subgroup.mem_comap, hYφ]
        exact ht
      have hcomm := congrArg φ (hZ Y hYE)
      have h' : z' * t = t * z' := by
        simpa [hz'def, map_mul, hYφ] using hcomm
      exact h'.symm
    have hNle : N ≤ Subgroup.centralizer (T3 : Set (adjointGroup .F4 K)) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact hTel.comm (hT3T ht) (Subgroup.zpowers_le.2 hnT (hNdef ▸ hy))
    have hT3le : T3 ≤ Subgroup.centralizer (N : Set (adjointGroup .F4 K)) :=
      Subgroup.le_centralizer_iff.1 hNle
    have hdisj : T3 ⊓ N = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzT3, hzN⟩ := Subgroup.mem_inf.1 hz
      have hmem : z ∈ N ⊓ D := Subgroup.mem_inf.2 ⟨hzN, hT3D hzT3⟩
      rw [hXdisj, Subgroup.mem_bot] at hmem
      exact hmem
    have hNT3el : CFSG.Open.IsElemAbelian 3 (T3 ⊔ N) := by
      have hzN : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (nodeElt K)) :=
        isElemAbelian_zpowers (p := 3) TableBF4TwoInputs.nodeElt_pow_three
      have hNel : CFSG.Open.IsElemAbelian 3 N := hNdef ▸ hzN
      exact CFSG.Open.IsElemAbelian.sup_of_commute hT3el hNel (by
        intro a ha b hb
        exact hTel.comm (hT3T ha) (Subgroup.zpowers_le.2 hnT (hNdef ▸ hb)))
    have hcardT3N : Nat.card ↥(T3 ⊔ N) = 3 ^ 4 := by
      rw [card_sup_eq_mul_of_le_centralizer hNle hdisj, hcardT3,
        hNdef, TableBF4TwoInputs.card_zpowers_nodeElt hK, hK]
      norm_num
    have hT'Cz : T3 ⊔ N ≤
        Subgroup.centralizer (Subgroup.zpowers z' : Set (adjointGroup .F4 K)) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
        exact hz'T3
      · rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        exact hz'N
    have hAz : CFSG.Open.IsElemAbelian 3 ((T3 ⊔ N) ⊔ Subgroup.zpowers z') := by
      have hz'el : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers z') :=
        isElemAbelian_zpowers (p := 3) hz'3
      exact CFSG.Open.IsElemAbelian.sup_of_commute hNT3el hz'el (by
        intro a ha b hb
        exact (Subgroup.mem_centralizer_iff.1 (hT'Cz ha) b hb).symm)
    have hAzcard : Nat.card ↥((T3 ⊔ N) ⊔ Subgroup.zpowers z') ≤ 3 ^ 4 :=
      TableBF4Two.card_le_adjointF4 hK hAz
    have hAz_eq : (T3 ⊔ N) ⊔ Subgroup.zpowers z' = T3 ⊔ N := by
      refine (Subgroup.eq_of_le_of_card_ge le_sup_left ?_).symm
      rw [hcardT3N]
      exact hAzcard
    have hz'T3N : z' ∈ T3 ⊔ N := by
      have hmem : z' ∈ (T3 ⊔ N) ⊔ Subgroup.zpowers z' :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers z')
      rwa [hAz_eq] at hmem
    have hnorm : T3 ≤ Subgroup.normalizer (N : Set (adjointGroup .F4 K)) :=
      hT3le.trans (Subgroup.centralizer_le_normalizer _)
    have hz'mem : z' ∈ ((T3 ⊔ N : Subgroup (adjointGroup .F4 K)) : Set _) := hz'T3N
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T3 N hnorm] at hz'mem
    obtain ⟨t, ht, y, hy, hty⟩ := hz'mem
    have hyD : y ∈ D := by
      have htD : t ∈ D := hT3D ht
      have hy_eq : y = t⁻¹ * z' := by rw [← hty]; group
      rw [hy_eq]
      exact mul_mem (inv_mem htD) hz'D
    have hy1 : y = 1 := by
      have hmem : y ∈ N ⊓ D := Subgroup.mem_inf.2 ⟨hy, hyD⟩
      rwa [hXdisj, Subgroup.mem_bot] at hmem
    have hz'T3 : z' ∈ T3 := by
      have h1 : z' = t := by simpa [hy1] using hty.symm
      rw [h1]
      exact ht
    rw [hEdef, Subgroup.mem_comap]
    simpa [hz'def] using hz'T3
  have hcent : Subgroup.centralizer (E : Set (StatedSp 3 K)) ≤ E :=
    centralizer_le_of_selfCent_spTwo hK hEel hEsc
  set z : StatedSp 3 K := (c3LeviEquiv K).symm ⟨l, hlD⟩ with hzdef
  have hzC : z ∈ Subgroup.centralizer (E : Set (StatedSp 3 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro Y hY
    have hφY : φ Y ∈ T3 := Subgroup.mem_comap.1 (hEdef ▸ hY)
    have hcomm : ((c3LeviEquiv K Y : C3Levi K) : adjointGroup .F4 K) * l =
        l * ((c3LeviEquiv K Y : C3Levi K) : adjointGroup .F4 K) := by
      have := Subgroup.mem_centralizer_iff.1 hlcentT3 (φ Y) hφY
      simpa [hφdef] using this
    have hcommD : c3LeviEquiv K Y * ⟨l, hlD⟩ = ⟨l, hlD⟩ * c3LeviEquiv K Y := by
      apply Subtype.ext
      exact hcomm
    have hcomm' : c3LeviEquiv K Y * c3LeviEquiv K z =
        c3LeviEquiv K z * c3LeviEquiv K Y := by
      simpa [hzdef] using hcommD
    apply (c3LeviEquiv K).injective
    simpa [map_mul] using hcomm'
  have hzE : z ∈ E := hcent hzC
  have hlT3 : l ∈ T3 := by
    have h := Subgroup.mem_comap.1 (hEdef ▸ hzE)
    simpa [hzdef, hφdef] using h
  have hgT : g ∈ T := by
    rw [← hxl]
    exact mul_mem hxT (hT3T hlT3)
  rwa [hTdef] at hgT

end

end CFSG.StandardType.TBCF4

end
