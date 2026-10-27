module

public import CFSG.Sporadic.Co1Patterson.AmalgamEdge
public import CFSG.Sporadic.Co1Patterson.Setting
public import CFSG.LargeExtraspecial.S3bConj
public import CFSG.Sporadic.Co1Patterson.GraphDefs
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section TrivMod

variable {G : Type*} [Group G]

theorem conj_mem_coreOf {K : Subgroup G} {g : G} (hg : ∀ k, k ∈ K ↔ g * k * g⁻¹ ∈ K) {x : G}
    (hx : x ∈ coreOf K) : g * x * g⁻¹ ∈ coreOf K :=
  (isoOn_conj g hg).map_mem_coreOf hx

@[expose] def trivModCore (K : Subgroup G) : Subgroup G where
  carrier := {g | (∀ k, k ∈ K ↔ g * k * g⁻¹ ∈ K) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ coreOf K}
  one_mem' := ⟨fun k => by simp, fun k _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro g₁ g₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
    refine ⟨fun k => by rw [h₂, h₁]; group, fun k hk => ?_⟩
    have e : g₁ * g₂ * k * (g₁ * g₂)⁻¹ * k⁻¹ =
        g₁ * (g₂ * k * g₂⁻¹ * k⁻¹) * g₁⁻¹ * (g₁ * k * g₁⁻¹ * k⁻¹) := by group
    rw [e]
    exact mul_mem (conj_mem_coreOf h₁ (h₂' k hk)) (h₁' k hk)
  inv_mem' := by
    rintro g ⟨h, h'⟩
    have hinv : ∀ k, k ∈ K ↔ g⁻¹ * k * g⁻¹⁻¹ ∈ K := fun k => by
      rw [h (g⁻¹ * k * g⁻¹⁻¹)]
      group
    refine ⟨hinv, fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g ∈ K := by simpa using (hinv k).1 hk
    have := inv_mem (h' _ hk')
    rw [show (g * (g⁻¹ * k * g) * g⁻¹ * (g⁻¹ * k * g)⁻¹)⁻¹ = g⁻¹ * k * g⁻¹⁻¹ * k⁻¹ by group]
      at this
    exact this

theorem mem_trivModCore {K : Subgroup G} {g : G} :
    g ∈ trivModCore K ↔
      (∀ k, k ∈ K ↔ g * k * g⁻¹ ∈ K) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ coreOf K := Iff.rfl

theorem mem_coreOf_of_isPGroup {K P : Subgroup G} (hP : IsPGroup 2 P)
    (hnorm : ∀ k ∈ K, ∀ x ∈ P, k * x * k⁻¹ ∈ P) {x : G} (hxK : x ∈ K) (hxP : x ∈ P) :
    x ∈ coreOf K := by
  have hle : P.subgroupOf K ≤ CFSG.pCore 2 K := by
    refine le_sSup ⟨⟨fun n hn k => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hn ⊢
      simpa using hnorm k.1 k.2 n.1 hn
    · exact hP.comap_of_injective K.subtype K.subtype_injective
  exact ⟨⟨x, hxK⟩, hle (by rw [mem_subgroupOf]; exact hxP), rfl⟩

end TrivMod

section SettingQ

variable {G : Type*} [Group G] (S : Setting G)

theorem comm_QG_eq {x y : G} (hx : x ∈ S.QG) (hy : y ∈ S.QG) :
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = S.z := by
  have h1 : x * y ∈ S.QG := mul_mem hx hy
  have h2 : x * y * x⁻¹ ∈ S.QG := mul_mem h1 (inv_mem hx)
  rw [← S.cl_eq_zero_iff (mul_mem h2 (inv_mem hy)), S.cl_mul h2 (inv_mem hy), S.cl_mul h1
    (inv_mem hx), S.cl_mul hx hy, S.cl_inv hx, S.cl_inv hy,
    show S.cl x + S.cl y + S.cl x + S.cl y = (S.cl x + S.cl x) + (S.cl y + S.cl y) by abel,
    ZModModule.add_self, ZModModule.add_self, add_zero]

theorem QG_le_trivModCore {v : G} (hv : v ∈ S.QG) :
    S.QG ≤ trivModCore (C[S.z] ⊓ C[v]) := by
  intro x hx
  have hxM : x ∈ S.M := S.QG_le_M hx
  have hvz : S.z * v = v * S.z := (S.z_comm_QG hv).symm
  have hxz : x * S.z * x⁻¹ = S.z := by
    rw [S.z_comm hxM]; group
  have hK : ∀ k, k ∈ C[S.z] ⊓ C[v] ↔ x * k * x⁻¹ ∈ C[S.z] ⊓ C[v] := by
    rcases comm_QG_eq S hx hv with h | h
    · have hxv : x * v * x⁻¹ = v := by
        calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
          _ = v := by rw [h, one_mul]
      exact conj_mem_inf_iff_of hxz hxv (fun _ => Iff.rfl)
    · have hxv : x * v * x⁻¹ = S.z * v := by
        calc x * v * x⁻¹ = x * v * x⁻¹ * v⁻¹ * v := by group
          _ = S.z * v := by rw [h]
      exact conj_mem_inf_iff_of hxz hxv (mem_inf_mul_right_iff hvz)
  refine ⟨hK, fun k hk => ?_⟩
  have hkM : k ∈ S.M := (mem_inf.1 hk).1
  refine mem_coreOf_of_isPGroup S.isPGroup_QG (fun c hc y hy => S.conj_mem_QG
    (mem_inf.1 hc).1 hy) ?_ ?_
  · exact mul_mem ((hK k).1 hk) (inv_mem hk)
  · have := mul_mem hx (S.conj_mem_QG hkM (inv_mem hx))
    simpa [mul_assoc] using this

end SettingQ

theorem IsoOn.mem_qOf {G Y : Type} [Group G] [Group Y] {A : G → Y} {a : G} {t : Y}
    (hA : IsoOn A C[a] C[t]) {x : G} (hx : x ∈ qOf a) : A x ∈ qOf t := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hF := CFSG.LargeExtraspecial.Bridge.timmesfeldFStar_map hA.toMulEquiv
  have : hA.toMulEquiv y ∈ CFSG.Open.timmesfeldFStar C[t] := hF ▸ ⟨y, hy, rfl⟩
  exact ⟨hA.toMulEquiv y, this, rfl⟩

theorem qOf_le_centralizer {Y : Type} [Group Y] (w : Y) : qOf w ≤ C[w] := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

section Patterson

variable {X : Type} [Group X] [Finite X] {t : X}

theorem setting_Qa_eq (h : PattersonCo1Hyp X t) (c : X) :
    (setting h).Qa c = qOf (c * t * c⁻¹) := by
  ext y
  rw [Setting.Qa_eq_map, mem_qOf_conj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rfl

theorem mem_qOf_symm (h : PattersonCo1Hyp X t) {u : X} (hu : IsConj t u) (hne : u ≠ t)
    (htu : t ∈ qOf u) : u ∈ qOf t := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hu
  have h1 := (setting h).mem_Qa_symm (g₁ := 1) (g₂ := c) (by simpa using hne.symm)
    (by rw [setting_Qa_eq h]; simpa using htu)
  rw [Setting.Qa_one] at h1
  exact h1

theorem mem_qOf_symm₂ (h : PattersonCo1Hyp X t) {u v : X} (hu : IsConj t u) (hv : IsConj t v)
    (hne : u ≠ v) (huv : u ∈ qOf v) : v ∈ qOf u := by
  obtain ⟨g₁, rfl⟩ := isConj_iff.1 hu
  obtain ⟨g₂, rfl⟩ := isConj_iff.1 hv
  have h1 := (setting h).mem_Qa_symm (g₁ := g₁) (g₂ := g₂) hne
    (by rw [setting_Qa_eq h]; exact huv)
  rwa [setting_Qa_eq h] at h1

theorem exists_swap_trivModCore (h : PattersonCo1Hyp X t) {u : X} (hu : u ∈ qOf t)
    (hconj : IsConj t u) (hut : u ≠ t) :
    (∃ g ∈ qOf t ⊔ qOf u, g * t * g⁻¹ = u ∧ g * u * g⁻¹ = t) ∧ t ∈ qOf u ∧
      qOf t ⊔ qOf u ≤ trivModCore (C[t] ⊓ C[u]) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hQa : (setting h).Qa c = qOf u := by rw [setting_Qa_eq h, hc]
  obtain ⟨g, hg, hg1, hg2⟩ := (setting h).exists_swap hc hu hut
  have htu : t ∈ qOf u := hQa ▸ (setting h).z_mem_Qa_of_mem_QG hc hu hut
  refine ⟨⟨g, by rwa [hQa] at hg, hg1, hg2⟩, htu, sup_le ?_ ?_⟩
  · exact QG_le_trivModCore (setting h) hu
  · have hT := QG_le_trivModCore ((setting h).conjBy c) (v := t) (by
      change t ∈ (setting h).Qa c
      rw [hQa]; exact htu)
    have hz : ((setting h).conjBy c).z = u := hc
    rw [hz, inf_comm] at hT
    change (setting h).Qa c ≤ _ at hT
    rwa [hQa] at hT

end Patterson

end CFSG.Sporadic.Co1Patterson
