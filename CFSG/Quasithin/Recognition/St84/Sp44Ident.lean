module

public import CFSG.Quasithin.Recognition.St84.Sp44Data
public import CFSG.Quasithin.Recognition.St84.Sp44Vertex
public import CFSG.Quasithin.Recognition.St84.Sp44DC
public import CFSG.Quasithin.Recognition.CertF6Bridge
public import CFSG.GH74.QTGen4.DSGen4.L34Generic
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModel
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4
public import CFSG.Quasithin.Background.F1AmalgamRestrict
public import Certificates.Certificate113
public import Certificates.Certificate320030
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenLie
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassical
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCat
public import CFSG.LocalAnalysis.SteinbergCCSymplecticFourCenterFusion
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.EmptyFaithful.R3c11Core
public import CFSG.Quasithin.EmptyFaithful.R3c12Cl
public import CFSG.Quasithin.EmptyFaithful.R3c15Cl
public import CFSG.Quasithin.EmptyFaithful.SzN27Cfg
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpTrans
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4
open CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique.Fin257.Sp4
open scoped commutatorElement

variable {G : Type} [Group G]

local notation "F₄" => GaloisField 2 2

noncomputable abbrev sp44M1 : Subgroup (antiSp F₄) :=
  Subgroup.normalizer (radA1 F₄ : Set (antiSp F₄))

noncomputable abbrev sp44M2 : Subgroup (antiSp F₄) :=
  Subgroup.normalizer (radA2 F₄ : Set (antiSp F₄))

theorem sp44_centerOf_centralizer_rootU (j : Fin 2) :
    centerOf (Subgroup.centralizer (rootU F₄ (axisOf j) : Set (antiSp F₄))) = rootU F₄ (axisOf j) :=
  axis_centerOf_centralizer (hS_axis (F := F₄) le_rfl (Sp44.card_galoisField_two_two) j)
    (rootU_le_rootA j) (two_lt_card le_rfl (Sp44.card_galoisField_two_two))

theorem sp44_centerOf_centralizer_rootU₁ :
    centerOf (Subgroup.centralizer (rootU₁ F₄ : Set (antiSp F₄))) = rootU₁ F₄ :=
  sp44_centerOf_centralizer_rootU 0

theorem sp44_centerOf_centralizer_rootU₂ :
    centerOf (Subgroup.centralizer (rootU₂ F₄ : Set (antiSp F₄))) = rootU₂ F₄ :=
  sp44_centerOf_centralizer_rootU 1

theorem sp44_borel_left [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (hD : Sp44LocalData L1 L2 S)
    {ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(sp44M1)}
    (hN1 : ∀ z : ↥(L1 ⊔ bigB L1 L2 S),
      (z : G) ∈ Subgroup.normalizer (S : Set G) ↔
        (ψ₁ z : antiSp F₄) ∈ Subgroup.normalizer (antiUnipotent F₄ : Set (antiSp F₄))) :
    ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ (ψ₁ x : antiSp F₄) ∈ Sp44.B0 F₄ := by
  intro x
  have hBN : bigB L1 L2 S = (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) :=
    hD.bigB_eq_parabolic_inf hF
  have hiff : (x : G) ∈ bigB L1 L2 S ↔
      (x : G) ∈ (L1 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) :=
    ⟨fun h => le_of_eq hBN h, fun h => ge_of_eq hBN h⟩
  exact hiff.trans ⟨fun h => (hN1 x).mp h.2,
    fun h => Subgroup.mem_inf.mpr ⟨x.2, (hN1 x).mpr h⟩⟩

theorem sp44_borel_right [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (hD : Sp44LocalData L1 L2 S)
    {ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(sp44M2)}
    (hN2 : ∀ z : ↥(L2 ⊔ bigB L1 L2 S),
      (z : G) ∈ Subgroup.normalizer (S : Set G) ↔
        (ψ₂ z : antiSp F₄) ∈ Subgroup.normalizer (antiUnipotent F₄ : Set (antiSp F₄))) :
    ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ (ψ₂ x : antiSp F₄) ∈ Sp44.B0 F₄ := by
  intro x
  have hBN : bigB L1 L2 S = (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) := by
    have h := hD.symm.bigB_eq_parabolic_inf hF.symm
    rwa [bigB_comm L1 L2 S] at h
  have hiff : (x : G) ∈ bigB L1 L2 S ↔
      (x : G) ∈ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) :=
    ⟨fun h => le_of_eq hBN h, fun h => ge_of_eq hBN h⟩
  exact hiff.trans ⟨fun h => (hN2 x).mp h.2,
    fun h => Subgroup.mem_inf.mpr ⟨x.2, (hN2 x).mpr h⟩⟩

theorem sp44_mem_pCoreOf_left_iff_radA1 [Finite G]
    {L1 L2 S : Subgroup G} (hSL2 : S ≤ L2) (hQ1S : pCoreOf 2 L1 ≤ S)
    (hQ1e : IsElemAbelian 2 (pCoreOf 2 L1))
    (hQ1card : Nat.card (pCoreOf 2 L1) = 2 ^ 6)
    (hne : pCoreOf 2 L1 ≠ pCoreOf 2 L2)
    {ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(sp44M2)}
    (hS2 : ∀ z : ↥(L2 ⊔ bigB L1 L2 S),
      (z : G) ∈ S ↔ (ψ₂ z : antiSp F₄) ∈ antiUnipotent F₄)
    (hQ2 : ∀ z : ↥(L2 ⊔ bigB L1 L2 S),
      (z : G) ∈ pCoreOf 2 L2 ↔ (ψ₂ z : antiSp F₄) ∈ radA2 F₄) :
    ∀ y : ↥(L2 ⊔ bigB L1 L2 S),
      (y : G) ∈ pCoreOf 2 L1 ↔ (ψ₂ y : antiSp F₄) ∈ radA1 F₄ := by
  classical
  have hQ1P2 : pCoreOf 2 L1 ≤ L2 ⊔ bigB L1 L2 S :=
    hQ1S.trans (hSL2.trans le_sup_left)
  let ι₂ : ↥(L2 ⊔ bigB L1 L2 S) →* antiSp F₄ := (sp44M2).subtype.comp ψ₂.toMonoidHom
  have hι₂ : Function.Injective ι₂ := by
    intro x y h
    exact ψ₂.injective (Subtype.ext h)
  set E : Subgroup (antiSp F₄) := ((pCoreOf 2 L1).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ι₂ with hE
  have hEmem : ∀ y : ↥(L2 ⊔ bigB L1 L2 S), (y : G) ∈ pCoreOf 2 L1 ↔ ι₂ y ∈ E := by
    intro y
    rw [hE, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rw [hι₂ hzy] at hz
      exact Subgroup.mem_subgroupOf.mp hz
  have hEU : E ≤ antiUnipotent F₄ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact (hS2 y).1 (hQ1S (Subgroup.mem_subgroupOf.mp hy))
  have hEab : ∀ z ∈ E, z * z = 1 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    have hy2 : y ^ 2 = 1 :=
      Subtype.ext (by simpa using hQ1e.2 (y : G) (Subgroup.mem_subgroupOf.mp hy))
    have h2 : ι₂ y ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
    simpa [pow_two] using h2
  have hEcard : Nat.card E = 2 ^ 6 := by
    rw [hE, Subgroup.card_map_of_injective hι₂,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1P2).toEquiv]
    exact hQ1card
  have hradA1 : Nat.card (radA1 F₄) = 2 ^ 6 := by
    rw [(card_radicals (K := F₄)).2.1, Sp44.card_galoisField_two_two]
    norm_num
  have hradA2 : Nat.card (radA2 F₄) = 2 ^ 6 := by
    rw [(card_radicals (K := F₄)).2.2.1, Sp44.card_galoisField_two_two]
    norm_num
  rcases elementary_le_radA1_or_radA2 (K := F₄) hEU hEab with h1 | h2
  · have h1eq : E = radA1 F₄ :=
      Subgroup.eq_of_le_of_card_ge h1 (by rw [hEcard, hradA1])
    intro y
    have h := hEmem y
    rw [h1eq] at h
    exact h
  · exfalso
    apply hne
    have h2eq : E = radA2 F₄ :=
      Subgroup.eq_of_le_of_card_ge h2 (by rw [hEcard, hradA2])
    ext g
    constructor
    · intro hg
      have hgP2 : g ∈ L2 ⊔ bigB L1 L2 S := hQ1P2 hg
      have hm : ι₂ ⟨g, hgP2⟩ ∈ E := (hEmem ⟨g, hgP2⟩).1 hg
      rw [h2eq] at hm
      exact (hQ2 ⟨g, hgP2⟩).2 hm
    · intro hg
      have hgP2 : g ∈ L2 ⊔ bigB L1 L2 S :=
        Subgroup.mem_sup_left ((CFSG.LieType.BorelTits.pCoreOf_le 2 L2) hg)
      have hm : ι₂ ⟨g, hgP2⟩ ∈ E := by
        rw [h2eq]
        exact (hQ2 ⟨g, hgP2⟩).1 hg
      exact (hEmem ⟨g, hgP2⟩).2 hm

theorem sp44_gluing_mem_radA1_iff [Finite G] {L1 L2 S : Subgroup G}
    {ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(sp44M1)}
    {ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(sp44M2)}
    {β₁ β₂ : ↥(bigB L1 L2 S) ≃* ↥(Sp44.B0 F₄)}
    (hβ₁ : ∀ z : ↥(bigB L1 L2 S),
      ((β₁ z : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₁ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M1)) : antiSp F₄))
    (hβ₂ : ∀ z : ↥(bigB L1 L2 S),
      ((β₂ z : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₂ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M2)) : antiSp F₄))
    (hQ1 : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ pCoreOf 2 L1 ↔ (ψ₁ x : antiSp F₄) ∈ radA1 F₄)
    (hKEY : ∀ y : ↥(L2 ⊔ bigB L1 L2 S),
      (y : G) ∈ pCoreOf 2 L1 ↔ (ψ₂ y : antiSp F₄) ∈ radA1 F₄) :
    ∀ b : ↥(Sp44.B0 F₄), (b : antiSp F₄) ∈ radA1 F₄ ↔
      (((β₁.symm.trans β₂) b : ↥(Sp44.B0 F₄)) : antiSp F₄) ∈ radA1 F₄ := by
  intro b
  obtain ⟨z, rfl⟩ := β₁.surjective b
  have hγ : (((β₁.symm.trans β₂) (β₁ z) : ↥(Sp44.B0 F₄)) : antiSp F₄)
      = ((β₂ z : ↥(Sp44.B0 F₄)) : antiSp F₄) := by
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hγ]
  calc (β₁ z : antiSp F₄) ∈ radA1 F₄
      ↔ ((ψ₁ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M1)) : antiSp F₄) ∈ radA1 F₄ := by rw [hβ₁ z]
    _ ↔ (z : G) ∈ pCoreOf 2 L1 :=
        (hQ1 ⟨z, Subgroup.mem_sup_right z.2⟩).symm
    _ ↔ ((ψ₂ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M2)) : antiSp F₄) ∈ radA1 F₄ :=
        hKEY ⟨z, Subgroup.mem_sup_right z.2⟩
    _ ↔ (β₂ z : antiSp F₄) ∈ radA1 F₄ := by rw [hβ₂ z]

theorem sp44_exists_rootU₁_gluing_not_mem_rootU₂ [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (hD : Sp44LocalData L1 L2 S)
    {ψ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(sp44M1)}
    {ψ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(sp44M2)}
    {β₁ β₂ : ↥(bigB L1 L2 S) ≃* ↥(Sp44.B0 F₄)}
    (hβ₁ : ∀ z : ↥(bigB L1 L2 S),
      ((β₁ z : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₁ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M1)) : antiSp F₄))
    (hβ₂ : ∀ z : ↥(bigB L1 L2 S),
      ((β₂ z : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₂ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M2)) : antiSp F₄))
    (hL1 : ∀ z : ↥(L1 ⊔ bigB L1 L2 S), (z : G) ∈ L1 ↔
      (ψ₁ z : antiSp F₄) ∈ Subgroup.centralizer (rootU₁ F₄ : Set (antiSp F₄)))
    (hL2 : ∀ z : ↥(L2 ⊔ bigB L1 L2 S), (z : G) ∈ L2 ↔
      (ψ₂ z : antiSp F₄) ∈ Subgroup.centralizer (rootU₂ F₄ : Set (antiSp F₄))) :
    ∃ b : ↥(Sp44.B0 F₄), (b : antiSp F₄) ∈ rootU₁ F₄ ∧
      (((β₁.symm.trans β₂) b : ↥(Sp44.B0 F₄)) : antiSp F₄) ∉ rootU₂ F₄ := by
  classical
  have hQ1S : pCoreOf 2 L1 ≤ S := by
    have h := hF.1.h1.sylow
    rw [inf_eq_left.mpr hD.le_left] at h
    exact F7.isSylowTwoOf_pCoreOf_le h
  have hcQ : centerOf L1 ≤ pCoreOf 2 L1 := (hD.side_left hF h1).center_le
  have hZ1 : centerOf (Subgroup.centralizer (rootU₁ F₄ : Set (antiSp F₄))) = rootU₁ F₄ :=
    sp44_centerOf_centralizer_rootU₁
  have hZ2 : centerOf (Subgroup.centralizer (rootU₂ F₄ : Set (antiSp F₄))) = rootU₂ F₄ :=
    sp44_centerOf_centralizer_rootU₂
  have hZc1 : ∀ (z : G) (hz : z ∈ centerOf L1),
      ((ψ₁ ⟨z, Subgroup.mem_sup_left (Subgroup.mem_inf.mp hz).1⟩ : ↥(sp44M1)) :
        antiSp F₄) ∈ rootU₁ F₄ := by
    intro z hz
    have hzL : z ∈ L1 := (Subgroup.mem_inf.mp hz).1
    have hzc : z ∈ Subgroup.centralizer (L1 : Set G) := (Subgroup.mem_inf.mp hz).2
    rw [← hZ1]
    refine Subgroup.mem_inf.mpr ⟨(hL1 ⟨z, Subgroup.mem_sup_left hzL⟩).mp hzL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hcM : c ∈ sp44M1 := by
      have hpc := axis_perfectCore_normalizer
        (hS_axis (F := F₄) le_rfl (Sp44.card_galoisField_two_two) 0)
      have hc' : c ∈ perfectCore
          (Subgroup.normalizer (rootA F₄ (axisOf 0) : Set (antiSp F₄))) := by
        rw [hpc]
        exact hc
      exact perfectCore_le _ hc'
    let y : ↥(L1 ⊔ bigB L1 L2 S) := ψ₁.symm ⟨c, hcM⟩
    have hyL : (y : G) ∈ L1 := by
      rw [hL1]
      simpa [y] using hc
    have hcomm : (y : G) * z = z * (y : G) := Subgroup.mem_centralizer_iff.mp hzc _ hyL
    have hzyP : z ∈ (L1 ⊔ bigB L1 L2 S) := Subgroup.mem_sup_left hzL
    have h3 : ψ₁ ⟨z, hzyP⟩ * ψ₁ y = ψ₁ y * ψ₁ ⟨z, hzyP⟩ := by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ₁ (Subtype.ext hcomm.symm)
    have h4 : ((ψ₁ ⟨z, hzyP⟩ : ↥(sp44M1)) : antiSp F₄) * c
        = c * ((ψ₁ ⟨z, hzyP⟩ : ↥(sp44M1)) : antiSp F₄) := by
      have h5 := congrArg (fun t : ↥(sp44M1) => (t : antiSp F₄)) h3
      simpa [y] using h5
    exact h4.symm
  have hZc2 : ∀ (z : G) (hzB : z ∈ bigB L1 L2 S),
      ((ψ₂ ⟨z, Subgroup.mem_sup_right hzB⟩ : ↥(sp44M2)) : antiSp F₄) ∈ rootU₂ F₄ →
        z ∈ centerOf L2 := by
    intro z hzB hzU
    have hzP : z ∈ L2 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right hzB
    have hzZ : ((ψ₂ ⟨z, hzP⟩ : ↥(sp44M2)) : antiSp F₄) ∈
        centerOf (Subgroup.centralizer (rootU₂ F₄ : Set (antiSp F₄))) := by
      rw [hZ2]; exact hzU
    have hz' := Subgroup.mem_inf.mp hzZ
    refine Subgroup.mem_inf.mpr ⟨(hL2 ⟨z, hzP⟩).mpr hz'.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwP : w ∈ L2 ⊔ bigB L1 L2 S := Subgroup.mem_sup_left hw
    have hwc : ((ψ₂ ⟨w, hwP⟩ : ↥(sp44M2)) : antiSp F₄) ∈
        Subgroup.centralizer (rootU₂ F₄ : Set (antiSp F₄)) := (hL2 ⟨w, hwP⟩).mp hw
    have hcomm : ((ψ₂ ⟨w, hwP⟩ : ↥(sp44M2)) : antiSp F₄) *
          ((ψ₂ ⟨z, hzP⟩ : ↥(sp44M2)) : antiSp F₄)
        = ((ψ₂ ⟨z, hzP⟩ : ↥(sp44M2)) : antiSp F₄) *
          ((ψ₂ ⟨w, hwP⟩ : ↥(sp44M2)) : antiSp F₄) :=
      Subgroup.mem_centralizer_iff.mp hz'.2 _ hwc
    have hmul : ψ₂ (⟨w, hwP⟩ * ⟨z, hzP⟩) = ψ₂ (⟨z, hzP⟩ * ⟨w, hwP⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext hcomm
    exact congrArg Subtype.val (ψ₂.injective hmul)
  by_contra hcon
  have hcon' : ∀ b : ↥(Sp44.B0 F₄), (b : antiSp F₄) ∈ rootU₁ F₄ →
      (((β₁.symm.trans β₂) b : ↥(Sp44.B0 F₄)) : antiSp F₄) ∈ rootU₂ F₄ := by
    intro b hb
    by_contra hb2
    exact hcon ⟨b, hb, hb2⟩
  have hZle : centerOf L1 ≤ centerOf L2 := by
    intro z hz
    have hzL : z ∈ L1 := (Subgroup.mem_inf.mp hz).1
    have hzS : z ∈ S := hQ1S (hcQ hz)
    have hzB : z ∈ bigB L1 L2 S := Subgroup.mem_sup_right hzS
    have hv1 : ((ψ₁ ⟨z, Subgroup.mem_sup_left hzL⟩ : ↥(sp44M1)) : antiSp F₄) ∈ rootU₁ F₄ :=
      hZc1 z hz
    have hbU : ((β₁ ⟨z, hzB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄) ∈ rootU₁ F₄ := by
      rw [hβ₁ ⟨z, hzB⟩]
      have hsub : (⟨z, Subgroup.mem_sup_right hzB⟩ : ↥(L1 ⊔ bigB L1 L2 S))
          = ⟨z, Subgroup.mem_sup_left hzL⟩ := Subtype.ext rfl
      rw [hsub]
      exact hv1
    have hγb : (((β₁.symm.trans β₂) (β₁ ⟨z, hzB⟩) : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₂ ⟨z, Subgroup.mem_sup_right hzB⟩ : ↥(sp44M2)) : antiSp F₄) := by
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact hβ₂ ⟨z, hzB⟩
    have h2v : ((ψ₂ ⟨z, Subgroup.mem_sup_right hzB⟩ : ↥(sp44M2)) : antiSp F₄) ∈ rootU₂ F₄ := by
      rw [← hγb]
      exact hcon' (β₁ ⟨z, hzB⟩) hbU
    exact hZc2 z hzB h2v
  have hcore : coreIn (bigB L1 L2 S) (L1 ⊔ L2 ⊔ S) = ⊥ :=
    (prop_F19_of_listed rankOneListedFacts hF.1).2.2.1
  have hL1N : L1 ≤ Subgroup.normalizer (centerOf L1 : Set G) :=
    (show L1 ≤ Subgroup.centralizer (centerOf L1 : Set G) from by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 g hg).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hL2N : L2 ≤ Subgroup.normalizer (centerOf L1 : Set G) :=
    (show L2 ≤ Subgroup.centralizer (centerOf L1 : Set G) from by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy2 : y ∈ centerOf L2 := hZle hy
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy2).2 g hg).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hZcore : centerOf L1 ≤ coreIn (bigB L1 L2 S) (L1 ⊔ L2 ⊔ S) := by
    refine le_coreIn ?_ ?_ ?_
    · intro x hx
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hx).1)
    · exact sup_le (sup_le hL1N hL2N) (hD.le_left.trans hL1N)
    · exact hcQ.trans (hQ1S.trans le_sup_right)
  have hbot : centerOf L1 = ⊥ := by
    have h := hZcore
    rw [hcore] at h
    exact le_bot_iff.mp h
  have hcard : Nat.card ↥(centerOf L1) = 1 := by rw [hbot]; simp
  rw [hD.center_left] at hcard
  norm_num at hcard

noncomputable def sp44CorrAut (g : antiSp F₄) (k : ℕ) : MulAut (antiSp F₄) :=
  MulAut.conj g * frobAut F₄ ^ k

theorem sp44CorrAut_apply (g : antiSp F₄) (k : ℕ) (x : antiSp F₄) :
    sp44CorrAut g k x = g * (frobAut F₄ ^ k) x * g⁻¹ := by
  simp [sp44CorrAut, MulAut.mul_apply, MulAut.conj_apply]

theorem sp44CorrAut_mem_radA1 {g : antiSp F₄} (hg : g ∈ Sp44.B0 F₄) (k : ℕ) (x : antiSp F₄) :
    x ∈ radA1 F₄ ↔ sp44CorrAut g k x ∈ radA1 F₄ := by
  have hgN : g ∈ Subgroup.normalizer (radA1 F₄ : Set (antiSp F₄)) :=
    normalizer_U_le_normalizer_radA1 (K := F₄) hg
  have hconj : ∀ y : antiSp F₄, y ∈ radA1 F₄ ↔ g * y * g⁻¹ ∈ radA1 F₄ := by
    intro y
    rw [Subgroup.mem_normalizer_iff] at hgN
    exact hgN y
  have hFr : ∀ (j : ℕ) (y : antiSp F₄),
      (frobAut F₄ ^ j) y ∈ radA1 F₄ ↔ y ∈ radA1 F₄ := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ j ih =>
        intro y
        rw [pow_succ, MulAut.mul_apply, ih, frobAut_mem_radA1_iff]
  rw [sp44CorrAut_apply, ← hconj ((frobAut F₄ ^ k) x)]
  exact (hFr k x).symm

theorem sp44CorrAut_mem_normalizer {g : antiSp F₄} (hg : g ∈ Sp44.B0 F₄) (k : ℕ)
    (x : antiSp F₄) : x ∈ sp44M1 ↔ sp44CorrAut g k x ∈ sp44M1 := by
  have ha1 : ∀ y : antiSp F₄, y ∈ radA1 F₄ ↔ sp44CorrAut g k y ∈ radA1 F₄ :=
    sp44CorrAut_mem_radA1 hg k
  have hmap : (radA1 F₄).map (sp44CorrAut g k).toMonoidHom = radA1 F₄ := by
    ext y
    rw [Subgroup.mem_map_equiv]
    exact (ha1 ((sp44CorrAut g k).symm y)).trans (by simp)
  have hN : sp44M1.map (sp44CorrAut g k).toMonoidHom = sp44M1 := by
    have h := Subgroup.map_equiv_normalizer_eq (H := radA1 F₄) (f := sp44CorrAut g k)
    rw [hmap] at h
    exact h
  constructor
  · intro hx
    have h : sp44CorrAut g k x ∈ sp44M1.map (sp44CorrAut g k).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rwa [hN] at h
  · intro hx
    have hiff : sp44CorrAut g k x ∈ sp44M1.map (sp44CorrAut g k).toMonoidHom ↔ x ∈ sp44M1 := by
      rw [Subgroup.mem_map_equiv]
      simp
    rw [hN] at hiff
    exact hiff.mp hx


theorem sp44_isAmalgamIso [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : Sp44LocalData L1 L2 S) :
    F6.IsAmalgamIso (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S) sp44M1 sp44M2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : Nat.card F₄ = 2 ^ 2 := Sp44.card_galoisField_two_two
  obtain ⟨ψ₁, hS1, hQ1, hL1, hN1⟩ := (hD.side_left hF h1).exists_vertexIso_one
  obtain ⟨ψ₂, hS2, hQ2, hL2, hN2⟩ := (hD.side_right hF h1 h2).exists_vertexIso
  have hB1 : ∀ x : ↥(L1 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ (ψ₁ x : antiSp F₄) ∈ Sp44.B0 F₄ :=
    sp44_borel_left hF hD hN1
  have hB2 : ∀ x : ↥(L2 ⊔ bigB L1 L2 S),
      (x : G) ∈ bigB L1 L2 S ↔ (ψ₂ x : antiSp F₄) ∈ Sp44.B0 F₄ :=
    sp44_borel_right hF hD hN2
  have hBN2 : bigB L1 L2 S = (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) := by
    have h := hD.symm.bigB_eq_parabolic_inf hF.symm
    rwa [bigB_comm L1 L2 S] at h
  have hB0M1 : Sp44.B0 F₄ ≤ sp44M1 := normalizer_U_le_normalizer_radA1 (K := F₄)
  have hB0M2 : Sp44.B0 F₄ ≤ sp44M2 := normalizer_U_le_normalizer_radA2 (K := F₄)
  let β₁ : ↥(bigB L1 L2 S) ≃* ↥(Sp44.B0 F₄) :=
    F1.restrictEquiv ψ₁ (le_sup_right : bigB L1 L2 S ≤ L1 ⊔ bigB L1 L2 S) hB0M1 hB1
  let β₂ : ↥(bigB L1 L2 S) ≃* ↥(Sp44.B0 F₄) :=
    F1.restrictEquiv ψ₂ (le_sup_right : bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S) hB0M2 hB2
  have hβ₁ : ∀ z : ↥(bigB L1 L2 S), ((β₁ z : ↥(Sp44.B0 F₄)) : antiSp F₄)
      = ((ψ₁ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M1)) : antiSp F₄) := fun _ => rfl
  have hβ₂ : ∀ z : ↥(bigB L1 L2 S), ((β₂ z : ↥(Sp44.B0 F₄)) : antiSp F₄)
      = ((ψ₂ ⟨z, Subgroup.mem_sup_right z.2⟩ : ↥(sp44M2)) : antiSp F₄) := fun _ => rfl
  have hQ1S : pCoreOf 2 L1 ≤ S := by
    have h := hF.1.h1.sylow
    rw [inf_eq_left.mpr hD.le_left] at h
    exact F7.isSylowTwoOf_pCoreOf_le h
  have hne : pCoreOf 2 L1 ≠ pCoreOf 2 L2 := by
    intro heq
    have hcard := hD.card_inf
    rw [heq, inf_idem, hD.card_right] at hcard
    norm_num at hcard
  have hKEY : ∀ y : ↥(L2 ⊔ bigB L1 L2 S),
      (y : G) ∈ pCoreOf 2 L1 ↔ (ψ₂ y : antiSp F₄) ∈ radA1 F₄ :=
    sp44_mem_pCoreOf_left_iff_radA1 hD.le_right hQ1S hD.elem_left hD.card_left hne hS2 hQ2
  have hA : ∀ b : ↥(Sp44.B0 F₄), (b : antiSp F₄) ∈ radA1 F₄ ↔
      (((β₁.symm.trans β₂) b : ↥(Sp44.B0 F₄)) : antiSp F₄) ∈ radA1 F₄ :=
    sp44_gluing_mem_radA1_iff hβ₁ hβ₂ hQ1 hKEY
  have hU : ∃ b : ↥(Sp44.B0 F₄), (b : antiSp F₄) ∈ rootU₁ F₄ ∧
      (((β₁.symm.trans β₂) b : ↥(Sp44.B0 F₄)) : antiSp F₄) ∉ rootU₂ F₄ :=
    sp44_exists_rootU₁_gluing_not_mem_rootU₂ hF h1 hD hβ₁ hβ₂ hL1 hL2
  obtain ⟨g, hg, k, hgk⟩ := Sp44.sp44_dc hF4 (β₁.symm.trans β₂) hA hU
  have hM1 : ∀ x : antiSp F₄, x ∈ sp44M1 ↔ sp44CorrAut g k x ∈ sp44M1 :=
    sp44CorrAut_mem_normalizer hg k
  let φ₁ : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(sp44M1) :=
    ψ₁.trans (subgroupEquiv (sp44CorrAut g k) hM1)
  let φ₂ : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(sp44M2) := ψ₂
  have hclause1 : ∀ (x : G) (hx1 : x ∈ L1 ⊔ bigB L1 L2 S) (hx2 : x ∈ L2 ⊔ bigB L1 L2 S),
      ((φ₁ ⟨x, hx1⟩ : ↥(sp44M1)) : antiSp F₄)
        = ((φ₂ ⟨x, hx2⟩ : ↥(sp44M2)) : antiSp F₄) := by
    intro x hx1 hx2
    have hL1B : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
      hD.parabolic_inf hF
    have hxB : x ∈ bigB L1 L2 S := by
      rw [← hL1B]
      exact Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    have hsub1 : (⟨x, Subgroup.mem_sup_right hxB⟩ : ↥(L1 ⊔ bigB L1 L2 S)) = ⟨x, hx1⟩ :=
      Subtype.ext rfl
    have hsub2 : (⟨x, Subgroup.mem_sup_right hxB⟩ : ↥(L2 ⊔ bigB L1 L2 S)) = ⟨x, hx2⟩ :=
      Subtype.ext rfl
    have hb1 : ((β₁ ⟨x, hxB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₁ ⟨x, hx1⟩ : ↥(sp44M1)) : antiSp F₄) := by
      rw [hβ₁ ⟨x, hxB⟩, hsub1]
    have hb2 : ((β₂ ⟨x, hxB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄)
        = ((ψ₂ ⟨x, hx2⟩ : ↥(sp44M2)) : antiSp F₄) := by
      rw [hβ₂ ⟨x, hxB⟩, hsub2]
    have hstep : sp44CorrAut g k ((ψ₁ ⟨x, hx1⟩ : ↥(sp44M1)) : antiSp F₄)
        = ((β₂ ⟨x, hxB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄) := by
      calc sp44CorrAut g k ((ψ₁ ⟨x, hx1⟩ : ↥(sp44M1)) : antiSp F₄)
          = sp44CorrAut g k ((β₁ ⟨x, hxB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄) := by rw [hb1]
        _ = g * (frobAut F₄ ^ k) ((β₁ ⟨x, hxB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄) * g⁻¹ :=
            sp44CorrAut_apply g k _
        _ = (((β₁.symm.trans β₂) (β₁ ⟨x, hxB⟩) : ↥(Sp44.B0 F₄)) : antiSp F₄) :=
            (hgk (β₁ ⟨x, hxB⟩)).symm
        _ = ((β₂ ⟨x, hxB⟩ : ↥(Sp44.B0 F₄)) : antiSp F₄) := by
            rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    show ((ψ₁.trans (subgroupEquiv (sp44CorrAut g k) hM1)) ⟨x, hx1⟩ : antiSp F₄)
        = ((ψ₂ ⟨x, hx2⟩ : ↥(sp44M2)) : antiSp F₄)
    rw [MulEquiv.trans_apply]
    show sp44CorrAut g k ((ψ₁ ⟨x, hx1⟩ : ↥(sp44M1)) : antiSp F₄) = _
    rw [hstep, hb2]
  have hclause2 : ∀ (y : antiSp F₄) (hy1 : y ∈ sp44M1) (hy2 : y ∈ sp44M2),
      ((φ₁.symm ⟨y, hy1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : G)
        = ((φ₂.symm ⟨y, hy2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : G) := by
    intro y hy1 hy2
    have hBor : Borel252.BorelData (antiSp F₄) (antiUnipotent F₄) (radA1 F₄) (radA2 F₄) :=
      borel_antiSp (F := F₄) le_rfl hF4
    have hyB : y ∈ Sp44.B0 F₄ := by
      show y ∈ Subgroup.normalizer (antiUnipotent F₄ : Set (antiSp F₄))
      rw [← hBor.inf_norm]
      exact Subgroup.mem_inf.mpr ⟨hy1, hy2⟩
    let x₂ : ↥(L2 ⊔ bigB L1 L2 S) := φ₂.symm ⟨y, hy2⟩
    have hx₂ : ((ψ₂ x₂ : ↥(sp44M2)) : antiSp F₄) = y := by
      have h : ((φ₂ x₂ : ↥(sp44M2)) : antiSp F₄) = y := by
        rw [show φ₂ x₂ = ⟨y, hy2⟩ from MulEquiv.apply_symm_apply φ₂ ⟨y, hy2⟩]
      exact h
    have hx₂N : (x₂ : G) ∈ Subgroup.normalizer (S : Set G) :=
      (hN2 x₂).mpr (by rw [hx₂]; exact hyB)
    have hx₂B : (x₂ : G) ∈ bigB L1 L2 S := by
      have hiff : (x₂ : G) ∈ bigB L1 L2 S ↔
          (x₂ : G) ∈ (L2 ⊔ bigB L1 L2 S) ⊓ Subgroup.normalizer (S : Set G) :=
        ⟨fun h => le_of_eq hBN2 h, fun h => ge_of_eq hBN2 h⟩
      exact hiff.mpr (Subgroup.mem_inf.mpr ⟨x₂.2, hx₂N⟩)
    have hx₂P₁ : (x₂ : G) ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_right hx₂B
    have h1 : ((φ₁ ⟨x₂, hx₂P₁⟩ : ↥(sp44M1)) : antiSp F₄) = y := by
      have h := hclause1 (x₂ : G) hx₂P₁ x₂.2
      exact h.trans hx₂
    have h2 : φ₁ ⟨x₂, hx₂P₁⟩ = ⟨y, hy1⟩ := Subtype.ext h1
    have h3 : φ₁.symm ⟨y, hy1⟩ = ⟨x₂, hx₂P₁⟩ := by
      rw [← h2, MulEquiv.symm_apply_apply]
    calc ((φ₁.symm ⟨y, hy1⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : G)
        = ((⟨x₂, hx₂P₁⟩ : ↥(L1 ⊔ bigB L1 L2 S)) : G) := congrArg Subtype.val h3
      _ = (x₂ : G) := rfl
      _ = ((φ₂.symm ⟨y, hy2⟩ : ↥(L2 ⊔ bigB L1 L2 S)) : G) := rfl
  exact ⟨φ₁, φ₂, hclause1, hclause2⟩

theorem isAmalgamOfGroup_sp4_of_sp44LocalData [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    (hD : Sp44LocalData L1 L2 S) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsSp4Over 2) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : Nat.card F₄ = 2 ^ 2 := Sp44.card_galoisField_two_two
  obtain ⟨iso⟩ := nonempty_iso_ofSubgroups_of_isAmalgamIso (sp44_isAmalgamIso hF h1 h2 hD)
  refine ⟨antiSp F₄, inferInstance, Or.inr ⟨le_rfl, lieModel_Sp (K := F₄) le_rfl hF4⟩,
    antiUnipotent F₄, sp44M1, sp44M2, ?_, ⟨iso⟩⟩
  exact L34.isYAmalgamPair_of_borelData (borel_antiSp (F := F₄) le_rfl hF4)
    (O2_antiSp (F := F₄) le_rfl hF4)


end CFSG.Quasithin.F112R.St84
