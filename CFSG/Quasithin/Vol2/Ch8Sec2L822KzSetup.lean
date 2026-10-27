module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822M22Xi
public import CFSG.Quasithin.Vol2.Ch7Lem734Loc
public import CFSG.Quasithin.Background.A3StructureListNative
public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch8Sec2L8210
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.EmptyFaithfulMultiple
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]
variable {T L I : Subgroup G}

theorem relIndex_oTwoUpper_eq_nine_kz {H : Subgroup G} (φ : ↥H →* S3Wr)
    (hs : Function.Surjective φ) (hk : φ.ker = (pCoreOf 2 H).subgroupOf H) :
    (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 := by
  have hXH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hpX : pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ pCoreOf 2 H := pCoreOf_oTwoUpper_eq H
  have hrange := range_comp_oTwoUpper φ hs
  set ψ : ↥(oTwoUpper H) →* S3Wr := φ.comp (Subgroup.inclusion hXH) with hψ
  have hker' : ψ.ker = (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H) := by
    ext x
    constructor
    · intro hx
      have h1 : (⟨(x : G), hXH x.2⟩ : ↥H) ∈ φ.ker := hx
      rw [hk] at h1
      have h2 : (x : G) ∈ pCoreOf 2 H := h1
      rw [Subgroup.mem_subgroupOf, hpX]
      exact ⟨x.2, h2⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf, hpX] at hx
      have : (⟨(x : G), hXH x.2⟩ : ↥H) ∈ φ.ker := by rw [hk]; exact hx.2
      exact this
  unfold Subgroup.relIndex
  rw [← hker', Subgroup.index_ker, hrange, oddSub_card]

theorem exists_sylow3_oTwoUpper_kz {H : Subgroup G}
    (hrel : (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9) :
    ∃ P : Subgroup G, P ≤ oTwoUpper H ∧ IsPGroup 3 P ∧ Nat.card P = 9 := by
  have hmul := Subgroup.relIndex_mul_card (H := pCoreOf 2 (oTwoUpper H)) (K := oTwoUpper H)
  rw [hrel] at hmul
  have h9 : 3 ^ 2 ∣ Nat.card ↥(oTwoUpper H) :=
    ⟨Nat.card ↥(pCoreOf 2 (oTwoUpper H) ⊓ oTwoUpper H), by rw [← hmul]; norm_num⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  have hinj : Function.Injective (oTwoUpper H).subtype := Subtype.val_injective
  refine ⟨K.map (oTwoUpper H).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have hK3 : IsPGroup 3 K := IsPGroup.of_card (by rw [hK])
    exact hK3.map _
  · rw [Subgroup.card_map_of_injective hinj, hK]
    norm_num

@[expose] def Kz134Concl_kz (Hh S X P : Subgroup G) : Prop :=
  Hh ≤ Subgroup.normalizer (X : Set G) ∨
    ∃ L : Subgroup G, L ∈ cComp Hh ∧ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      X ≤ conjClosure L S ∧
      (
        ((∃ t ∈ S ⊓ Subgroup.normalizer (P : Set G), t ∉ Subgroup.normalizer (L : Set G) ∧
            P = (P ⊓ L) ⊔ conjByElt t (P ⊓ L) ∧ (P ⊓ L) ⊓ conjByElt t (P ⊓ L) = ⊥) ∧
          ((∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
            ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 q 1)) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 (ZMod 3))))) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (∃ n : ℕ, Even n ∧ StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSp 2 2 n) ∧
          AutCyclic S P) ∨
        (S ≤ Subgroup.normalizer (L : Set G) ∧
          (Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
            StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1)) ∨
        (Hh ≤ Subgroup.normalizer (L : Set G) ∧
          Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .He)))

theorem exists_z_prop134_kz (h134 : EmptyFaithfulMultiple.Prop134E9He)
    (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I) (h821 : Hyp8_2_1 T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) (h711n : Stmt7_1_1_normal)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight)
    (hC58 : TheoremC58) (h317 : AS317Sylow)
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hVH : fsuV T I ≤ pCoreOf 2 H)
    (φ : ↥H →* S3Wr) (hφs : Function.Surjective φ) (hφk : φ.ker = (pCoreOf 2 H).subgroupOf H) :
    ∃ z : G, z ≠ 1 ∧ z ∈ fsuV T I ∧ z ∈ quasithinOmegaOneCenter T ∧
      H ≤ Subgroup.centralizer ({z} : Set G) ∧ T ≤ Subgroup.centralizer ({z} : Set G) ∧
      ∃ P : Subgroup G, P ≤ twoResidual H ∧ IsPGroup 3 P ∧ Nat.card P = 9 ∧
        Kz134Concl_kz (Subgroup.centralizer ({z} : Set G)) T (twoResidual H) P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hne := fsuV_inf_omegaOneCenter_ne_bot hyp.fsu hV hN
  obtain ⟨z, hzX, hz1⟩ : ∃ z ∈ fsuV T I ⊓ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hcon
    apply hne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    by_contra hx1
    exact hcon ⟨x, hx, hx1⟩
  have hzV : z ∈ fsuV T I := hzX.1
  have hzΩ : z ∈ quasithinOmegaOneCenter T := hzX.2
  have hz2 : z ^ 2 = 1 := hV.2 z hzV
  have hzc : z ∈ centerOf H := omegaOneCenter_le_center hC58 h317 h37 h38 h39 h3228 hyp hTL hH hzΩ
  have hHz : H ≤ Subgroup.centralizer ({z} : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp hzc.2 h hh).symm
  have hTc : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) := by
    unfold quasithinOmegaOneCenter
    rw [Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx.2
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (Subgroup.mem_centralizer_iff.mp (hTc hzΩ) t ht).symm
  set Gz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hGz
  have hzGz : z ∈ Gz := by
    rw [hGz, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
  have hzpow2 : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hpC : pCoreOf 2 Gz ≠ ⊥ := by
    intro hbot
    have hle : Subgroup.zpowers z ≤ pCoreOf 2 Gz := by
      have hfwd : ∀ g ∈ Gz, ∀ x ∈ Subgroup.zpowers z, g * x * g⁻¹ ∈ Subgroup.zpowers z := by
        intro g hg x hx
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        have hcomm : Commute g z := (Subgroup.mem_centralizer_iff.mp hg z (Set.mem_singleton z)).symm
        have hfix : g * z ^ k * g⁻¹ = z ^ k := by
          rw [(hcomm.zpow_right k).eq, mul_inv_cancel_right]
        rw [hfix]
        exact Subgroup.zpow_mem_zpowers z k
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
      · exact Subgroup.zpowers_le.mpr hzGz
      · intro g hg
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · exact hfwd g hg x
        · intro hx
          have h1 := hfwd g⁻¹ (Subgroup.inv_mem _ hg) _ hx
          have h2 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
          rw [← h2]
          exact h1
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzpow2]; norm_num)
    have hz0 : z ∈ pCoreOf 2 Gz := hle (Subgroup.mem_zpowers z)
    rw [hbot, Subgroup.mem_bot] at hz0
    exact hz1 hz0
  have hSQ : CFSG.SectionRank.IsSQTKCat ↥Gz :=
    SQTKGroup.isSQTKCat (sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian
      hpC)
  have hTsyl : IsSylowTwoOf T Gz := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTz
  have hXH : twoResidual H ≤ H := by
    rw [F6.twoResidual_eq_oTwoUpper H]
    exact oTwoUpper_le H
  have hXGz : twoResidual H ≤ Gz := hXH.trans hHz
  have hX : IsXi T (twoResidual H) :=
    isXi_of_quot_S3Wr (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1) hH.1.2 φ hφs hφk
  have hrelT : (pCoreOf 2 (twoResidual H)).relIndex (twoResidual H) = 9 := by
    rw [F6.twoResidual_eq_oTwoUpper H]
    exact relIndex_oTwoUpper_eq_nine_kz φ hφs hφk
  obtain ⟨P, hPX, hP3, hPcard⟩ :
      ∃ P : Subgroup G, P ≤ twoResidual H ∧ IsPGroup 3 P ∧ Nat.card P = 9 := by
    rw [F6.twoResidual_eq_oTwoUpper H]
    exact exists_sylow3_oTwoUpper_kz (by rw [← F6.twoResidual_eq_oTwoUpper H]; exact hrelT)
  have hcon : Kz134Concl_kz Gz T (twoResidual H) P :=
    h134 G Gz T (twoResidual H) P hSQ hpC hTsyl hXGz hX hrelT hPX hP3 hPcard
  exact ⟨z, hz1, hzV, hzΩ, hHz, hTz, P, hPX, hP3, hPcard, hcon⟩

end CFSG.Quasithin.H13
