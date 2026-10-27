module

public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalField
public import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalModel
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9

import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalPairing
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalRoots
import CFSG.Quasithin.Recognition.St84.Gen.VertexIsoSylow
import CFSG.Quasithin.Recognition.St84.Gen.AmalGlueDC
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalDC
import CFSG.Quasithin.Recognition.St84.Gen.L2RankOne
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.ClassicalGroups.PCoreSection
import CFSG.Quasithin.EmptyFaithful.T1521SBlkBasic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146CoverA
import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabD

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Fin257.L3 CFSG.GH74.QTGen4.DSGen4.L34
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

theorem L3qLocalData.linAction_left (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    LinAction (L1 ⊔ bigB L1 L2 S) (pCoreOf 2 L1) (cubeDetGL (GaloisField 2 f)) := by
  have hf : 1 ≤ f := hD.one_le
  have hS1 : IsSylowTwoOf S L1 := by
    have h := hH.h1.sylow
    rwa [inf_eq_left.mpr (hD.le_left hH)] at h
  have hS2 : IsSylowTwoOf S L2 := by
    have h := hH.h2.sylow
    rwa [inf_eq_left.mpr (hD.le_right hH)] at h
  obtain ⟨c₁⟩ := exists_vertexCoord (L := L1) (S := S) (f := f) hf hS1 hD.lin_left
    hD.blockU_left hD.blockZ_left
  obtain ⟨c₂⟩ := exists_vertexCoord (L := L2) (S := S) (f := f) hf hS2 hD.lin_right
    hD.blockU_right hD.blockZ_right
  obtain ⟨ρ, e₁, e₂, h₁, h₂⟩ := hD.exists_ringEquiv_pairing hH c₁ c₂
  exact hD.linAction_left_of_pairing hH c₁ c₂ ρ e₁ e₂ h₁ h₂

theorem L3qLocalData.linAction_right (hH : Hyp111 L1 L2 S) (hD : L3qLocalData L1 L2 S f) :
    LinAction (L2 ⊔ bigB L1 L2 S) (pCoreOf 2 L2) (cubeDetGL (GaloisField 2 f)) := by
  have hf : 1 ≤ f := hD.one_le
  have hS1 : IsSylowTwoOf S L1 := by
    have h := hH.h1.sylow
    rwa [inf_eq_left.mpr (hD.le_left hH)] at h
  have hS2 : IsSylowTwoOf S L2 := by
    have h := hH.h2.sylow
    rwa [inf_eq_left.mpr (hD.le_right hH)] at h
  obtain ⟨c₂⟩ := exists_vertexCoord (L := L2) (S := S) (f := f) hf hS2 hD.lin_right
    hD.blockU_right hD.blockZ_right
  obtain ⟨c₁⟩ := exists_vertexCoord (L := L1) (S := S) (f := f) hf hS1 hD.lin_left
    hD.blockU_left hD.blockZ_left
  obtain ⟨ρ, e₁, e₂, h₁, h₂⟩ := hD.symm.exists_ringEquiv_pairing hH.symm c₂ c₁
  exact hD.linAction_right_of_pairing hH c₂ c₁ ρ e₁ e₂ h₁ h₂

theorem L3qLocalData.map_pCoreOf_left_eq_V2 (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f)
    (ψ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(Pt (GaloisField 2 f)))
    (hQ2 : ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L2 ↔
        ((ψ x : ↥(Pt (GaloisField 2 f))) : projectiveSL 3 (GaloisField 2 f)) ∈
          (V1 : Subgroup (projectiveSL 3 (GaloisField 2 f))))
    (hS : ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ S ↔
        ((ψ x : ↥(Pt (GaloisField 2 f))) : projectiveSL 3 (GaloisField 2 f)) ∈
          projUnitriangular 3 (GaloisField 2 f)) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L1 ↔
        ((ψ x : ↥(Pt (GaloisField 2 f))) : projectiveSL 3 (GaloisField 2 f)) ∈
          (V2 : Subgroup (projectiveSL 3 (GaloisField 2 f))) := by
  classical
  let F := GaloisField 2 f
  let Y := projectiveSL 3 F
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := pCoreOf 2 L1
  let Q2 : Subgroup G := pCoreOf 2 L2
  let φ : ↥P2 →* Y := (Pt F).subtype.comp ψ.toMonoidHom
  have hφinj : Function.Injective φ := (Pt F).subtype_injective.comp ψ.injective
  have hQ1P2 : Q1 ≤ P2 :=
    hH.pCoreOf_le_left.trans ((hD.le_right hH).trans le_sup_left)
  have hQ2P2 : Q2 ≤ P2 := (CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 L2).trans le_sup_left
  let E : Subgroup Y := (Q1.subgroupOf P2).map φ
  let E2 : Subgroup Y := (Q2.subgroupOf P2).map φ
  have hE2 : E2 = (V1 : Subgroup Y) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hQ2 x).mp (Subgroup.mem_subgroupOf.mp hx)
    · intro hy
      have hyPt : y ∈ Pt F := Subgroup.le_normalizer hy
      obtain ⟨x, hx⟩ := ψ.surjective (⟨y, hyPt⟩ : ↥(Pt F))
      refine ⟨x, ?_, ?_⟩
      · exact (hQ2 x).mpr (by rw [hx]; exact hy)
      · exact congrArg Subtype.val hx
  have hEU : E ≤ (projUnitriangular 3 F : Subgroup Y) := by
    rintro y ⟨x, hx, rfl⟩
    exact (hS x).mp (hH.pCoreOf_le_left (Subgroup.mem_subgroupOf.mp hx))
  have hEea : IsElemAbelian 2 E := by
    have h := CFSG.Open.IsElemAbelian.map
      (CFSG.Open.IsElemAbelian.subgroupOf hD.isElemAbelian_left P2) φ
    simpa [E] using h
  have hf0 : f ≠ 0 := by
    have h : 1 ≤ f := hD.one_le
    omega
  have hFcard : Nat.card F = 2 ^ f := GaloisField.card 2 f hf0
  have hEcard : Nat.card E = Nat.card F ^ 2 := by
    have h1 : Nat.card E = Nat.card Q1 := by
      change Nat.card ((Q1.subgroupOf P2).map φ) = Nat.card Q1
      rw [Subgroup.card_map_of_injective hφinj]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1P2).toEquiv
    calc Nat.card E = Nat.card Q1 := h1
      _ = 2 ^ (2 * f) := hD.card_left
      _ = (2 ^ f) ^ 2 := by rw [← pow_mul]; congr 1; omega
      _ = Nat.card F ^ 2 := by rw [hFcard]
  rcases eq_V2_or_eq_V1_of_le_projUnitriangular hEU hEea hEcard with hE | hE
  · intro x
    constructor
    · intro hx
      have hxE : φ x ∈ E := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hx)
      rw [hE] at hxE
      simpa [φ] using hxE
    · intro hx
      have hxE : φ x ∈ E := by rw [hE]; exact hx
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxE
      have hzx' : z = x := hφinj hzx
      subst hzx'
      exact Subgroup.mem_subgroupOf.mp hz
  · exfalso
    have hEE2 : E = E2 := by rw [hE, hE2]
    have hsub : Q1.subgroupOf P2 = Q2.subgroupOf P2 :=
      Subgroup.map_injective hφinj hEE2
    have hQ1eq : Q1 = Q2 := by
      calc Q1 = (Q1.subgroupOf P2).map P2.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hQ1P2).symm
        _ = (Q2.subgroupOf P2).map P2.subtype := by rw [hsub]
        _ = Q2 := Subgroup.map_subgroupOf_eq_of_le hQ2P2
    exact hD.pCoreOf_ne hQ1eq

theorem isAmalgamOfGroup_psl3_of_dcStd (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) (hDC : DCStd (GaloisField 2 f)) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 f) := by
  classical
  let F := GaloisField 2 f
  let Y := projectiveSL 3 F
  let U : Subgroup Y := projUnitriangular 3 F
  let P1 : Subgroup G := L1 ⊔ bigB L1 L2 S
  let P2 : Subgroup G := L2 ⊔ bigB L1 L2 S
  let Q1 : Subgroup G := pCoreOf 2 L1
  have hR : Hyp111R L1 L2 S :=
    hyp111R_of_isL2Quot (by omega) (by omega) hH
      (CFSG.Quasithin.F146Field.isL2Quot_of_isPSL
        (isPSL_of_isLin2Type1521 hf hD.lin_left))
      (CFSG.Quasithin.F146Field.isL2Quot_of_isPSL
        (isPSL_of_isLin2Type1521 hf hD.lin_right))
  have hbigB1 : bigB L1 L2 S = P1 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := bigB_eq_parabolic_inf hR
    rwa [inf_eq_left.mpr (hD.le_left hH)] at h
  have hbigB2 : bigB L1 L2 S = P2 ⊓ Subgroup.normalizer (S : Set G) := by
    have h := bigB_eq_parabolic_inf hR.symm
    rw [bigB_comm L1 L2 S, inf_eq_left.mpr (hD.le_right hH)] at h
    exact h
  have hN : Subgroup.normalizer (U : Set Y) = Ln F ⊓ Pt F := by
    simpa [U, Ln, Pt] using normalizer_U_eq_inf_V (F := F)
  have hcore1 : pCoreOf 2 (Ln F) = (V2 : Subgroup Y) := by
    simpa [Ln] using CFSG.QuasithinUnique.Fin257.L3.core_V2 (F := F)
  have hU_V2 : IsSylowTwoOf U (Ln F) :=
    CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U_normalizer (F := F) (U_le_normalizer_V2 (F := F))
  have hU_V1 : IsSylowTwoOf U (Pt F) :=
    CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U_normalizer (F := F) (U_le_normalizer_V1 (F := F))
  obtain ⟨ψ₁, hψ₁Q, hψ₁S, hψ₁N⟩ :=
    (hD.isLinSemidirect_left hH (hD.linAction_left hH)).exists_mulEquiv_sylow
      (isLinSemidirect_Ln (F := F)) (hD.isSylowTwoOf_sup_bigB_left hH) hU_V2
  obtain ⟨ψ₂, hψ₂Q, hψ₂S, hψ₂N⟩ :=
    (hD.isLinSemidirect_right hH (hD.linAction_right hH)).exists_mulEquiv_sylow
      (isLinSemidirect_Pt (F := F)) (hD.isSylowTwoOf_sup_bigB_right hH) hU_V1
  have hB1 : ∀ x : ↥P1, (x : G) ∈ P2 ↔ ((ψ₁ x : ↥(Ln F)) : Y) ∈ Pt F := by
    intro x
    constructor
    · intro hxP2
      have hxinf : (x : G) ∈ P1 ⊓ P2 := ⟨x.2, hxP2⟩
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [← parabolic_inf_parabolic hR]
        exact hxinf
      have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
        rw [hbigB1] at hxB
        exact hxB.2
      have hψN : ((ψ₁ x : ↥(Ln F)) : Y) ∈ Subgroup.normalizer (U : Set Y) :=
        (hψ₁N x).mp hxN
      rw [hN] at hψN
      exact hψN.2
    · intro hxM2
      have hxM1 : ((ψ₁ x : ↥(Ln F)) : Y) ∈ Ln F := (ψ₁ x).2
      have hxN : ((ψ₁ x : ↥(Ln F)) : Y) ∈ Subgroup.normalizer (U : Set Y) := by
        rw [hN]
        exact ⟨hxM1, hxM2⟩
      have hxNG : (x : G) ∈ Subgroup.normalizer (S : Set G) := (hψ₁N x).mpr hxN
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [hbigB1]
        exact ⟨x.2, hxNG⟩
      exact (le_sup_right : bigB L1 L2 S ≤ P2) hxB
  have hB2 : ∀ x : ↥P2, (x : G) ∈ P1 ↔ ((ψ₂ x : ↥(Pt F)) : Y) ∈ Ln F := by
    intro x
    constructor
    · intro hxP1
      have hxinf : (x : G) ∈ P1 ⊓ P2 := ⟨hxP1, x.2⟩
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [← parabolic_inf_parabolic hR]
        exact hxinf
      have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := by
        rw [hbigB2] at hxB
        exact hxB.2
      have hψN : ((ψ₂ x : ↥(Pt F)) : Y) ∈ Subgroup.normalizer (U : Set Y) :=
        (hψ₂N x).mp hxN
      rw [hN] at hψN
      exact hψN.1
    · intro hxM1
      have hxM2 : ((ψ₂ x : ↥(Pt F)) : Y) ∈ Pt F := (ψ₂ x).2
      have hxN : ((ψ₂ x : ↥(Pt F)) : Y) ∈ Subgroup.normalizer (U : Set Y) := by
        rw [hN]
        exact ⟨hxM1, hxM2⟩
      have hxNG : (x : G) ∈ Subgroup.normalizer (S : Set G) := (hψ₂N x).mpr hxN
      have hxB : (x : G) ∈ bigB L1 L2 S := by
        rw [hbigB2]
        exact ⟨x.2, hxNG⟩
      exact (le_sup_right : bigB L1 L2 S ≤ P1) hxB
  have hQ1 : ∀ x : ↥P1, (x : G) ∈ Q1 ↔
      ((ψ₁ x : ↥(Ln F)) : Y) ∈ pCoreOf 2 (Ln F) := by
    intro x
    rw [hcore1]
    exact hψ₁Q x
  have hQ1' : ∀ x : ↥P2, (x : G) ∈ Q1 ↔
      ((ψ₂ x : ↥(Pt F)) : Y) ∈ pCoreOf 2 (Ln F) := by
    intro x
    rw [hcore1]
    exact hD.map_pCoreOf_left_eq_V2 hH ψ₂ hψ₂Q hψ₂S x
  have hiso : Nonempty ((RankTwoAmalgam.ofSubgroups P1 P2).Iso
      (RankTwoAmalgam.ofSubgroups (Ln F) (Pt F))) :=
    amalgam_iso_of_dcProp hDC ψ₁ ψ₂ hB1 hB2 hQ1 hQ1'
  refine ⟨Y, inferInstance, isLieOverTwo_psl3 hf, U, ?_⟩
  refine ⟨Ln F, Pt F, isYAmalgamPair_L3 (F := F), ?_⟩
  simpa [f112Amalgam, P1, P2] using hiso

theorem isAmalgamOfGroup_psl3_of_l3qLocalData (hf : 3 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : L3qLocalData L1 L2 S f) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSL 3 f) := by
  refine isAmalgamOfGroup_psl3_of_dcStd (by omega) hH hD (dcStd_of_eight_le ?_)
  rw [GaloisField.card 2 f (by omega)]
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

end CFSG.Quasithin.F112R.St84
