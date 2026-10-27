module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsCore
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsPerm
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndFactsSixWC
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndDichotomy
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Fischer.Classification.Unitary.Coords
public import CFSG.LargeExtraspecial.AS35QThModel
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Pairs
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem exists_eq_zpowers_of_card_eq_three (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) :
    ∃ b : G, b ∈ B ∧ b ≠ 1 ∧ B = Subgroup.zpowers b := by
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB3
    omega
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbB : (b : G) ∈ B := b.2
  have hb1' : (b : G) ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbA : (b : G) ∈ F.A := hBA hbB
  have hcard : Nat.card (Subgroup.zpowers (b : G)) = 3 :=
    F.card_zpowers_of_mem_A hbA hb1'
  exact ⟨(b : G), hbB, hb1',
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB)
      (by rw [hcard, hB3])).symm⟩

private theorem exists_lift_phiA (F : A10Frame c) {w : Equiv.Perm (Fin 10)}
    (hw : w ∈ A10Perm.atilde) (hw0 : w.support.card ≠ 0) :
    ∃ w₁ : G, ∃ hw₁A : w₁ ∈ F.A, F.phiA ⟨w₁, F.A_le_M hw₁A⟩ = w ∧
      w₁ ≠ 1 ∧ F.deg (Subgroup.zpowers w₁) = w.support.card := by
  have hw' : w ∈ Subgroup.map F.phiA (F.A.subgroupOf D.M) := by
    rwa [F.map_A_phiA]
  obtain ⟨a, ha, hφa⟩ := Subgroup.mem_map.mp hw'
  have haA : (a : G) ∈ F.A := Subgroup.mem_subgroupOf.mp ha
  have ha1 : (a : G) ≠ 1 := by
    intro h
    have ha_eq : a = 1 := Subtype.ext h
    have hw1 : w = 1 := by rw [← hφa, ha_eq, map_one]
    rw [hw1, Equiv.Perm.support_one, Finset.card_empty] at hw0
    exact hw0 rfl
  refine ⟨(a : G), haA, hφa, ha1, ?_⟩
  rw [F.deg_zpowers_eq (F.P_le_L (F.A_le haA)), hφa]

private structure SixBasis (F : A10Frame c) (B : Subgroup G) where
  b : G
  hbB : b ∈ B
  hbM : b ∈ D.M
  hb1 : b ≠ 1
  hB : B = Subgroup.zpowers b
  y₁ : G
  hy₁A : y₁ ∈ F.A
  hy₁M : y₁ ∈ D.M
  hy₁1 : y₁ ≠ 1
  z₁ : G
  hz₁A : z₁ ∈ F.A
  hz₁M : z₁ ∈ D.M
  hz₁1 : z₁ ≠ 1
  y : Equiv.Perm (Fin 10)
  z : Equiv.Perm (Fin 10)
  hφy : F.phiA ⟨y₁, hy₁M⟩ = y
  hφz : F.phiA ⟨z₁, hz₁M⟩ = z
  hy3 : y.support.card = 3
  hydeg : F.deg (Subgroup.zpowers y₁) = 3
  hzdeg : F.deg (Subgroup.zpowers z₁) = 6
  hdisj : Disjoint y.support (F.phiA ⟨b, hbM⟩).support
  hz_supp : z.support = (F.phiA ⟨b, hbM⟩).support
  hz_not : z ∉ Subgroup.zpowers (F.phiA ⟨b, hbM⟩)
  hxz3 : (F.phiA ⟨b, hbM⟩ * z).support.card = 3
  hbz_deg : F.deg (Subgroup.zpowers (b * z₁)) = 3
  hgen : A10Perm.atilde ≤ Subgroup.zpowers (F.phiA ⟨b, hbM⟩) ⊔
    Subgroup.zpowers y ⊔ Subgroup.zpowers z

private theorem deg_zpowers_mul_of_lift (F : A10Frame c) {b z₁ : G}
    {z : Equiv.Perm (Fin 10)} (hbA : b ∈ F.A) (hz₁A : z₁ ∈ F.A) (hbM : b ∈ D.M)
    (hφz : F.phiA ⟨z₁, F.A_le_M hz₁A⟩ = z)
    (hxz3 : (F.phiA ⟨b, hbM⟩ * z).support.card = 3) :
    F.deg (Subgroup.zpowers (b * z₁)) = 3 := by
  have hbzA : b * z₁ ∈ F.A := F.A.mul_mem hbA hz₁A
  have hbzL : b * z₁ ∈ c.L := F.P_le_L (F.A_le hbzA)
  rw [F.deg_zpowers_eq hbzL]
  have hmul : F.phiA ⟨b * z₁, F.A_le_M hbzA⟩ =
      F.phiA ⟨b, hbM⟩ * F.phiA ⟨z₁, F.A_le_M hz₁A⟩ := by
    rw [show (⟨b * z₁, F.A_le_M hbzA⟩ : ↥D.M) =
      ⟨b, hbM⟩ * ⟨z₁, F.A_le_M hz₁A⟩ from rfl, map_mul]
  rw [hmul, hφz, hxz3]

private theorem exists_six_basis (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) :
    Nonempty (SixBasis F B) := by
  obtain ⟨b, hbB, hb1, hB_eq⟩ := F.exists_eq_zpowers_of_card_eq_three hBA hB3
  have hbA : b ∈ F.A := hBA hbB
  have hbM : b ∈ D.M := F.A_le_M hbA
  have hbL : b ∈ c.L := F.P_le_L (F.A_le hbA)
  have hx_mem : F.phiA ⟨b, hbM⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr hbA)
  have hx_supp : (F.phiA ⟨b, hbM⟩).support.card = 6 := by
    rw [← F.deg_zpowers_eq hbL, ← hB_eq, hB6]
  obtain ⟨y, hy_mem, z, hz_mem, hy3, hdisj, -, hz_supp, hz_not, hxz3, -,
    hgen⟩ := A10Perm.exists_basis_of_card_support_eq_six hx_mem hx_supp
  obtain ⟨y₁, hy₁A, hφy, hy₁1, hydeg'⟩ :=
    F.exists_lift_phiA hy_mem (by rw [hy3]; norm_num)
  obtain ⟨z₁, hz₁A, hφz, hz₁1, hzdeg'⟩ :=
    F.exists_lift_phiA hz_mem (by rw [hz_supp, hx_supp]; norm_num)
  have hydeg : F.deg (Subgroup.zpowers y₁) = 3 := by rw [hydeg', hy3]
  have hzdeg : F.deg (Subgroup.zpowers z₁) = 6 := by rw [hzdeg', hz_supp, hx_supp]
  exact ⟨{
    b := b
    hbB := hbB
    hbM := hbM
    hb1 := hb1
    hB := hB_eq
    y₁ := y₁
    hy₁A := hy₁A
    hy₁M := F.A_le_M hy₁A
    hy₁1 := hy₁1
    z₁ := z₁
    hz₁A := hz₁A
    hz₁M := F.A_le_M hz₁A
    hz₁1 := hz₁1
    y := y
    z := z
    hφy := hφy
    hφz := hφz
    hy3 := hy3
    hydeg := hydeg
    hzdeg := hzdeg
    hdisj := hdisj
    hz_supp := hz_supp
    hz_not := hz_not
    hxz3 := hxz3
    hbz_deg := F.deg_zpowers_mul_of_lift hbA hz₁A hbM hφz hxz3
    hgen := hgen }⟩

private theorem A_le_sup_zpowers_of_map (F : A10Frame c) {b y₁ z₁ : G}
    {y z : Equiv.Perm (Fin 10)} (hbM : b ∈ D.M) (hy₁M : y₁ ∈ D.M) (hz₁M : z₁ ∈ D.M)
    (hbA : b ∈ F.A) (hy₁A : y₁ ∈ F.A) (hz₁A : z₁ ∈ F.A)
    (hby : F.phiA ⟨y₁, hy₁M⟩ = y) (hbz : F.phiA ⟨z₁, hz₁M⟩ = z)
    (hle : A10Perm.atilde ≤ Subgroup.zpowers (F.phiA ⟨b, hbM⟩) ⊔ Subgroup.zpowers y ⊔
      Subgroup.zpowers z) :
    F.A ≤ Subgroup.zpowers b ⊔ Subgroup.zpowers y₁ ⊔ Subgroup.zpowers z₁ := by
  classical
  let V : Subgroup ↥D.M := Subgroup.zpowers ⟨b, hbM⟩ ⊔ Subgroup.zpowers ⟨y₁, hy₁M⟩ ⊔
    Subgroup.zpowers ⟨z₁, hz₁M⟩
  have hVle : V ≤ F.A.subgroupOf D.M := by
    refine sup_le (sup_le ?_ ?_) ?_
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hbA)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hy₁A)
    · exact Subgroup.zpowers_le.mpr (Subgroup.mem_subgroupOf.mpr hz₁A)
  have hVmap : V.map F.phiA = Subgroup.zpowers (F.phiA ⟨b, hbM⟩) ⊔
      Subgroup.zpowers y ⊔ Subgroup.zpowers z := by
    simp only [V, Subgroup.map_sup, MonoidHom.map_zpowers, hby, hbz]
  have hcardAM : Nat.card (F.A.subgroupOf D.M) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe F.A_le_M).toEquiv, F.card_A]
  have hcardV : Nat.card V = 27 := by
    refine le_antisymm ?_ ?_
    · calc Nat.card V ≤ Nat.card (F.A.subgroupOf D.M) :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hVle)
            (Subgroup.inclusion_injective hVle)
        _ = 27 := hcardAM
    · have hle_atilde : A10Perm.atilde ≤ V.map F.phiA := by
        rw [hVmap]
        exact hle
      calc 27 = Nat.card A10Perm.atilde := A10Perm.card_atilde.symm
        _ ≤ Nat.card (V.map F.phiA) :=
            Nat.card_le_card_of_injective (Subgroup.inclusion hle_atilde)
              (Subgroup.inclusion_injective hle_atilde)
        _ ≤ Nat.card V := Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd V F.phiA)
  have hVeq : V = F.A.subgroupOf D.M :=
    Subgroup.eq_of_le_of_card_ge hVle (by rw [hcardV, hcardAM])
  have hmap := congrArg (Subgroup.map D.M.subtype) hVeq
  rw [Subgroup.map_subgroupOf_eq_of_le F.A_le_M] at hmap
  simpa [V, Subgroup.map_sup, MonoidHom.map_zpowers] using hmap.ge

private theorem A_le_centralizer (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A) :
    F.A ≤ Subgroup.centralizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact congrArg Subtype.val (F.elemAbelian.1.is_comm.comm ⟨b, hBA hb⟩ ⟨a, ha⟩)

private theorem centralizer_zpowers_subgroupOf_le_M (F : A10Frame c)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    {H : Subgroup G} (hAH : F.A ≤ H) {y : G} (hyA : y ∈ F.A)
    (hyde : F.deg (Subgroup.zpowers y) = 3) :
    Subgroup.centralizer ((Subgroup.zpowers y).subgroupOf H : Set ↥H) ≤ D.M.subgroupOf H := by
  classical
  have hyL : y ∈ c.L := F.P_le_L (F.A_le hyA)
  have hy1 : y ≠ 1 := F.ne_one_of_deg_ne_zero hyL (by rw [hyde]; norm_num)
  have hCy : Subgroup.centralizer (Subgroup.zpowers y : Set G) ≤ D.M :=
    le_trans (Subgroup.centralizer_le_normalizer _)
      (hN1 (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyA)
        (F.card_zpowers_of_mem_A hyA hy1) hyde)
  intro w hw
  refine Subgroup.mem_subgroupOf.mpr (hCy ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rcases Subgroup.mem_zpowers_iff.mp hg with ⟨n, rfl⟩
  have hcomm : Commute y (w : G) :=
    congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hw) (⟨y, hAH hyA⟩ : ↥H)
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y)))
  exact hcomm.zpow_left n

private theorem centralizer_zpowers_subgroupOf_le_M_of_mul (F : A10Frame c)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    {H : Subgroup G} (hAH : F.A ≤ H) {b z : G} (hbA : b ∈ F.A) (hzA : z ∈ F.A)
    (hHb : H ≤ Subgroup.centralizer ({b} : Set G))
    (hdeg : F.deg (Subgroup.zpowers (b * z)) = 3) :
    Subgroup.centralizer ((Subgroup.zpowers z).subgroupOf H : Set ↥H) ≤ D.M.subgroupOf H := by
  classical
  have hbzA : b * z ∈ F.A := F.A.mul_mem hbA hzA
  have hbzL : b * z ∈ c.L := F.P_le_L (F.A_le hbzA)
  have hbz1 : b * z ≠ 1 := F.ne_one_of_deg_ne_zero hbzL (by rw [hdeg]; norm_num)
  have hCbz : Subgroup.centralizer (Subgroup.zpowers (b * z) : Set G) ≤ D.M :=
    le_trans (Subgroup.centralizer_le_normalizer _)
      (hN1 (Subgroup.zpowers (b * z)) (Subgroup.zpowers_le.mpr hbzA)
        (F.card_zpowers_of_mem_A hbzA hbz1) hdeg)
  intro w hw
  refine Subgroup.mem_subgroupOf.mpr (hCbz ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rcases Subgroup.mem_zpowers_iff.mp hg with ⟨n, rfl⟩
  have hwb : b * (w : G) = (w : G) * b :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hHb w.2)).symm
  have hwz : z * (w : G) = (w : G) * z :=
    congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hw) (⟨z, hAH hzA⟩ : ↥H)
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z)))
  have hcomm : Commute (b * z) (w : G) := by
    show (b * z) * (w : G) = (w : G) * (b * z)
    calc (b * z) * w = b * (z * w) := by group
      _ = b * (w * z) := by rw [hwz]
      _ = (b * w) * z := by group
      _ = (w * b) * z := by rw [hwb]
      _ = w * (b * z) := by group
  exact hcomm.zpow_left n

private theorem normalizer_subgroupOf_le_M (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {H : Subgroup G} (hAH : F.A ≤ H) :
    Subgroup.normalizer ((F.A.subgroupOf H) : Set ↥H) ≤ D.M.subgroupOf H := by
  intro w hw
  rw [← Subgroup.subgroupOf_normalizer_eq hAH] at hw
  exact Subgroup.mem_subgroupOf.mpr (hNA (Subgroup.mem_subgroupOf.mp hw))

private theorem isSylowOf_subgroupOf_centralizer (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) :
    CFSG.ABGLocalTools.IsSylowOf 3 (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3)
    (K := Subgroup.centralizer (B : Set G))).mp ?_
  simpa [Subgroup.map_subgroupOf_eq_of_le (A_le_centralizer F hBA), Subgroup.map_top,
    Subgroup.range_subtype] using isSylowOf_A_centralizer_of_deg_six F hNA hBA hB3 hB6

private theorem sylow_data_of_six_basis (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) (data : SixBasis F B) :
    CFSG.ABGLocalTools.IsSylowOf 3 (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) ⊤ ∧
      CFSG.Open.IsElemAbelian 3 (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) ∧
      Nat.card (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) = 27 ∧
      (Subgroup.zpowers data.y₁).subgroupOf (Subgroup.centralizer (B : Set G)) ≤
        F.A.subgroupOf (Subgroup.centralizer (B : Set G)) ∧
      (Subgroup.zpowers data.z₁).subgroupOf (Subgroup.centralizer (B : Set G)) ≤
        F.A.subgroupOf (Subgroup.centralizer (B : Set G)) := by
  have hAH : F.A ≤ Subgroup.centralizer (B : Set G) := A_le_centralizer F hBA
  refine ⟨isSylowOf_subgroupOf_centralizer F hNA hBA hB3 hB6,
    F.elemAbelian.subgroupOf _, ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, F.card_A]
  · exact Subgroup.subgroupOf_mono _ (Subgroup.zpowers_le.mpr data.hy₁A)
  · exact Subgroup.subgroupOf_mono _ (Subgroup.zpowers_le.mpr data.hz₁A)

private theorem six_basis_card_data (F : A10Frame c) {H : Subgroup G} (hAH : F.A ≤ H)
    {y₁ z₁ : G} (hy₁A : y₁ ∈ F.A) (hz₁A : z₁ ∈ F.A)
    (hy₁1 : y₁ ≠ 1) (hz₁1 : z₁ ≠ 1)
    (hydeg : F.deg (Subgroup.zpowers y₁) = 3)
    (hzdeg : F.deg (Subgroup.zpowers z₁) = 6) :
    Nat.card ((Subgroup.zpowers y₁).subgroupOf H) = 3 ∧
      Nat.card ((Subgroup.zpowers z₁).subgroupOf H) = 3 ∧
      (Subgroup.zpowers y₁).subgroupOf H ≠ (Subgroup.zpowers z₁).subgroupOf H := by
  have hZ₁ : Nat.card ((Subgroup.zpowers y₁).subgroupOf H) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le.mpr hy₁A).trans hAH)).toEquiv]
    exact F.card_zpowers_of_mem_A hy₁A hy₁1
  have hZ₂ : Nat.card ((Subgroup.zpowers z₁).subgroupOf H) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      ((Subgroup.zpowers_le.mpr hz₁A).trans hAH)).toEquiv]
    exact F.card_zpowers_of_mem_A hz₁A hz₁1
  refine ⟨hZ₁, hZ₂, ?_⟩
  intro heq
  have hyZ : (⟨y₁, hAH hy₁A⟩ : ↥H) ∈ (Subgroup.zpowers y₁).subgroupOf H :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y₁)
  have hyZ₂ : (⟨y₁, hAH hy₁A⟩ : ↥H) ∈ (Subgroup.zpowers z₁).subgroupOf H := heq ▸ hyZ
  have hyz : y₁ ∈ Subgroup.zpowers z₁ := Subgroup.mem_subgroupOf.mp hyZ₂
  have hle : Subgroup.zpowers y₁ ≤ Subgroup.zpowers z₁ := Subgroup.zpowers_le.mpr hyz
  have heq2 : Subgroup.zpowers y₁ = Subgroup.zpowers z₁ :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [F.card_zpowers_of_mem_A hz₁A hz₁1,
        F.card_zpowers_of_mem_A hy₁A hy₁1])
  have hdeg : F.deg (Subgroup.zpowers y₁) = F.deg (Subgroup.zpowers z₁) := by rw [heq2]
  omega

private theorem isWeaklyClosedIn_subgroupOf_of_six_basis (F : A10Frame c)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) (data : SixBasis F B) :
    IsWeaklyClosedIn ((Subgroup.zpowers data.y₁).subgroupOf
      (Subgroup.centralizer (B : Set G)))
      (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) ∧
    IsWeaklyClosedIn ((Subgroup.zpowers data.z₁).subgroupOf
      (Subgroup.centralizer (B : Set G)))
      (F.A.subgroupOf (Subgroup.centralizer (B : Set G))) := by
  constructor
  · exact isWeaklyClosedIn_of_disjoint F hNA hBA hB3 hB6 data.hbB data.hb1 data.hy₁A
      data.hy₁1 (by simpa [data.hφy] using data.hdisj)
  · exact isWeaklyClosedIn_of_support_eq F hNA hBA hB3 hB6 data.hbB data.hb1 data.hz₁A
      (by simpa [data.hφz] using data.hz_supp)
      (by simpa [data.hφz] using data.hz_not)

private theorem subgroupOf_centralizer_le_center (F : A10Frame c) {B : Subgroup G} :
    B.subgroupOf (Subgroup.centralizer (B : Set G)) ≤
      Subgroup.center ↥(Subgroup.centralizer (B : Set G)) := by
  intro w hw
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  have hwB : (w : G) ∈ B := Subgroup.mem_subgroupOf.mp hw
  exact ((Subgroup.mem_centralizer_iff.mp h.2) (w : G) hwB).symm

private theorem gen_subgroupOf_of_six_basis (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (data : SixBasis F B) :
    F.A.subgroupOf (Subgroup.centralizer (B : Set G)) ≤
      (Subgroup.zpowers data.y₁).subgroupOf (Subgroup.centralizer (B : Set G)) ⊔
      (Subgroup.zpowers data.z₁).subgroupOf (Subgroup.centralizer (B : Set G)) ⊔
      B.subgroupOf (Subgroup.centralizer (B : Set G)) := by
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  have hA_le_U : F.A ≤ Subgroup.zpowers data.b ⊔ Subgroup.zpowers data.y₁ ⊔
      Subgroup.zpowers data.z₁ :=
    A_le_sup_zpowers_of_map F data.hbM data.hy₁M data.hz₁M (hBA data.hbB)
      data.hy₁A data.hz₁A data.hφy data.hφz data.hgen
  have h1 : F.A.subgroupOf H ≤ (Subgroup.zpowers data.b ⊔ Subgroup.zpowers data.y₁ ⊔
      Subgroup.zpowers data.z₁).subgroupOf H := Subgroup.subgroupOf_mono H hA_le_U
  have hsup : (Subgroup.zpowers data.b ⊔ Subgroup.zpowers data.y₁ ⊔
      Subgroup.zpowers data.z₁).subgroupOf H =
      B.subgroupOf H ⊔ (Subgroup.zpowers data.y₁).subgroupOf H ⊔
        (Subgroup.zpowers data.z₁).subgroupOf H := by
    rw [Subgroup.subgroupOf_sup (A := Subgroup.zpowers data.b ⊔ Subgroup.zpowers data.y₁)
      (A' := Subgroup.zpowers data.z₁)
      (sup_le (Subgroup.zpowers_le.mpr (hAH (hBA data.hbB)))
        (Subgroup.zpowers_le.mpr (hAH data.hy₁A)))
      (Subgroup.zpowers_le.mpr (hAH data.hz₁A))]
    rw [Subgroup.subgroupOf_sup (A := Subgroup.zpowers data.b)
      (A' := Subgroup.zpowers data.y₁) (Subgroup.zpowers_le.mpr (hAH (hBA data.hbB)))
      (Subgroup.zpowers_le.mpr (hAH data.hy₁A))]
    simp [data.hB, sup_assoc]
  rw [hsup] at h1
  simpa [H, sup_comm, sup_left_comm, sup_assoc] using h1

private theorem top_le_sup_pPrimeCore_centralizer (F : A10Frame c) (hK332 : UCK.K332ThreeAb)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) :
    (⊤ : Subgroup ↥(Subgroup.centralizer (B : Set G))) ≤
      D.M.subgroupOf (Subgroup.centralizer (B : Set G)) ⊔
        CFSG.pPrimeCore 3 ↥(Subgroup.centralizer (B : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨data⟩ := exists_six_basis F hBA hB3 hB6
  let H : Subgroup G := Subgroup.centralizer (B : Set G)
  let S : Subgroup ↥H := F.A.subgroupOf H
  let Z₁ : Subgroup ↥H := (Subgroup.zpowers data.y₁).subgroupOf H
  let Z₂ : Subgroup ↥H := (Subgroup.zpowers data.z₁).subgroupOf H
  let B' : Subgroup ↥H := B.subgroupOf H
  let Y : Subgroup ↥H := D.M.subgroupOf H
  have hAH : F.A ≤ H := A_le_centralizer F hBA
  obtain ⟨hS, hSe, hS27, hZ₁S, hZ₂S⟩ :=
    sylow_data_of_six_basis F hNA hBA hB3 hB6 data
  obtain ⟨hZ₁, hZ₂, hZ₁₂⟩ :=
    six_basis_card_data F hAH data.hy₁A data.hz₁A data.hy₁1 data.hz₁1 data.hydeg
      data.hzdeg
  obtain ⟨hw₁, hw₂⟩ := isWeaklyClosedIn_subgroupOf_of_six_basis F hNA hBA hB3 hB6 data
  have hBne : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB3
    omega
  have hHtop : H ≠ ⊤ :=
    CFSG.SeitzReduction.F4Pilot.centralizer_ne_top_of_ne_bot D.standing.simple
      D.standing.nonab hBne
  have hK : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper D.standing.kProper hHtop
  have hB : B' ≤ Subgroup.center ↥H := subgroupOf_centralizer_le_center F
  have hgen : S ≤ Z₁ ⊔ Z₂ ⊔ B' := gen_subgroupOf_of_six_basis F hBA data
  have hHb : H ≤ Subgroup.centralizer ({data.b} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp hh) data.b data.hbB).symm
  have hC₁ : Subgroup.centralizer (Z₁ : Set ↥H) ≤ Y :=
    centralizer_zpowers_subgroupOf_le_M F hN1 hAH data.hy₁A data.hydeg
  have hC₂ : Subgroup.centralizer (Z₂ : Set ↥H) ≤ Y :=
    centralizer_zpowers_subgroupOf_le_M_of_mul F hN1 hAH (hBA data.hbB) data.hz₁A hHb
      data.hbz_deg
  have hN : Subgroup.normalizer (S : Set ↥H) ≤ Y :=
    normalizer_subgroupOf_le_M F hNA hAH
  exact top_le_sup_pPrimeCore_of_weaklyClosed hK332 hK hS hSe hS27 hZ₁S hZ₂S hZ₁ hZ₂
    hZ₁₂ hw₁ hw₂ hB hgen hC₁ hC₂ hN

private theorem le_inf_sup_relPPrimeCore_of_top_le {H : Subgroup G}
    (h : (⊤ : Subgroup ↥H) ≤ D.M.subgroupOf H ⊔ CFSG.pPrimeCore 3 ↥H) :
    H ≤ (H ⊓ D.M) ⊔ CFSG.Open.relPPrimeCore 3 H := by
  have hmap := Subgroup.map_mono (f := H.subtype) h
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
    Subgroup.subgroupOf_map_subtype,
    ← CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H] at hmap
  simpa [inf_comm] using hmap

private theorem centralizer_le_of_deg_three (F : A10Frame c)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hBdeg : F.deg B = 3) :
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
  have hCM : Subgroup.centralizer (B : Set G) ≤ D.M :=
    le_trans (Subgroup.centralizer_le_normalizer _) (hN1 B hBA hB3 hBdeg)
  exact le_sup_of_le_left (le_inf le_rfl hCM)

theorem centralizer_le_of_deg_six (F : A10Frame c) (hK332 : UCK.K332ThreeAb)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB6 : F.deg B = 6) :
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) :=
  le_inf_sup_relPPrimeCore_of_top_le
    (top_le_sup_pPrimeCore_centralizer F hK332 hN1 hNA hBA hB3 hB6)

theorem centralizer_le_of_deg_ne_nine (F : A10Frame c) (hK332 : UCK.K332ThreeAb)
    (hN1 : ∀ B ≤ F.A, Nat.card B = 3 → F.deg B = 3 → Subgroup.normalizer (B : Set G) ≤ D.M)
    (hNA : Subgroup.normalizer (F.A : Set G) ≤ D.M) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB : F.deg B ≠ 9) :
    Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
      CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)) := by
  obtain ⟨b, hbB, hb1, hB_eq⟩ := F.exists_eq_zpowers_of_card_eq_three hBA hB3
  have hbA : b ∈ F.A := hBA hbB
  rcases F.deg_zpowers_mem hbA hb1 with h3 | h6 | h9
  · exact centralizer_le_of_deg_three F hN1 hBA hB3 (by rw [hB_eq]; exact h3)
  · exact centralizer_le_of_deg_six F hK332 hN1 hNA hBA hB3 (by rw [hB_eq]; exact h6)
  · exact absurd (by rw [hB_eq]; exact h9) hB

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
