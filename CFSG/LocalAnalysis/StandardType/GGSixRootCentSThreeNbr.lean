module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSThreeNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmBasic
public import CFSG.Monster.B.TwoA.Amalgam.CosetGraphLocal
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Base.GeomNative
public import CFSG.Monster.B.TwoA.Sp8.GenActionBase
public import CFSG.Monster.B.TwoA.Sp8.NormalizerBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8Base
public import CFSG.Monster.B.TwoA.Sp8.SubgeomBuildingBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFive
public import CFSG.Monster.B.TwoA.Sp8.SubgeomFiveBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomIsoBase
public import CFSG.Monster.B.TwoA.Sp8.SubgeomStdBase

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggRCSNbr_of_layerQuasi {M Y Q : Subgroup G} {r e : G}
    (h : GGRCSLayerQuasi 3 (M ⊓ Subgroup.centralizer {r}) Y Q) (he : e ∈ Y)
    (he3 : orderOf e = 3) (heM : Subgroup.centralizer {e} ≤ M) : GGRCSNbr M r := by
  have hYC : Y ≤ Subgroup.centralizer ({r} : Set G) := h.1.trans inf_le_right
  have heC : e ∈ Subgroup.centralizer ({r} : Set G) := hYC he
  exact ⟨ggRCSImg r Y, ⟨ggRCSImg r Q, ggRCSPiece_of_layer Nat.prime_three (by norm_num) h⟩,
    ⟨e, heC⟩, he3, heM, mem_ggRCSImg r he⟩

namespace GGRCSSThreeSetting

variable {G₀ : Subgroup G} {r : G} {Q S T : Subgroup G}

theorem layer (h : GGRCSSThreeSetting G₀ r Q S T) {M : Subgroup G} (hG₀M : G₀ ≤ M)
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) : GGRCSLayer 3 G₀ M r := by
  obtain ⟨-, hX, hQ2, hSQ, hTQ, hST, hdQL, hdST, hD, eS, hTq, hTZ, h3T⟩ := h
  exact RCSTOm.ggRCSLayer_three_of_sThree hG₀M hM hX hQ2 hSQ hTQ hST hdQL hdST hD
    (Classical.choice eS) hTq hTZ h3T

theorem layerQuasi (h : GGRCSSThreeSetting G₀ r Q S T) {M : Subgroup G} (hG₀M : G₀ ≤ M)
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) :
    GGRCSLayerQuasi 3 (M ⊓ Subgroup.centralizer {r}) (Q ⊔ T) Q := by
  obtain ⟨h1, hX, hQ2, hSQ, hTQ, hST, hdQL, hdST, hD, eS, hTq, hTZ, h3T⟩ := h
  set X := ggRCSX G₀ r with hXdef
  set V := M ⊓ Subgroup.centralizer ({r} : Set G) with hV
  have hXV : X ≤ V := (ggOTwoPrime_le _).trans (inf_le_inf_right _ hG₀M)
  have hVX : V ≤ Subgroup.normalizer (X : Set G) := fun c hc =>
    ggMem_normalizer_oTwoPrime_inf_centralizer (hM hc.1) hc.2
  have hperfX : CFSG.Quasithin.perfectCore X = Q ⊔ T := hD
  have hVD : V ≤ Subgroup.normalizer ((Q ⊔ T : Subgroup G) : Set G) := by
    have h := hVX.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore X)
    rwa [hperfX] at h
  have hDX : (Q ⊔ T : Subgroup G) ≤ X := by
    rw [hX]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hsn : IsSubnormal (Q ⊔ T : Subgroup G) V :=
    ggIsSubnormal_of_normal (hDX.trans hXV)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hDX.trans hXV)).mpr hVD)
  have hperf : ⁅(Q ⊔ T : Subgroup G), Q ⊔ T⁆ = Q ⊔ T := by
    simpa [hperfX] using CFSG.Quasithin.perfectCore_perfect X
  have h3D : 3 ∣ Nat.card ↥(Q ⊔ T : Subgroup G) :=
    h3T.trans (Subgroup.card_dvd_of_le (le_sup_right : T ≤ Q ⊔ T))
  have hQD : pCoreOf 2 (Q ⊔ T) = Q := by
    refine ggRCST_pCoreOf_eq rfl hQ2 hTQ ?_
    intro N hNT hN2 hTN
    exact (RCSTOm.ggRCSOmSummand_of_isQuasisimple hTq hTZ).2 N hNT hN2 hTN
  have hVQ : V ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hQD]
    exact hVD.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (Q ⊔ T))
  refine ⟨hDX.trans hXV, hsn, hperf, h3D, le_sup_left, hQ2, hVQ, ?_⟩
  intro _
  exact ggRCST_isQuasisimple_quot Nat.prime_three (by norm_num) hTQ le_sup_right le_rfl
    hQ2 inf_le_right hTq h3T

theorem card_le (h : GGRCSSThreeSetting G₀ r Q S T) {P : Subgroup G}
    (hP : P ≤ G₀ ⊓ Subgroup.centralizer {r}) (hP3 : IsPGroup 3 P) :
    Nat.card P ≤ 3 * Nat.card ↥(P ⊓ (Q ⊔ T)) := by
  obtain ⟨h1, hX, hQ2, hSQ, hTQ, hST, hdQL, hdST, hD, eS, hTq, hTZ, h3T⟩ := h
  set X := ggRCSX G₀ r with hXdef
  set D := Q ⊔ T with hDdef
  have hPX : P ≤ X := hP.trans h1
  have hperfX : CFSG.Quasithin.perfectCore X = D := hD
  have hcardS : Nat.card ↥S = 6 := by
    obtain ⟨e⟩ := eS
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  have hTS : T ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.le_centralizer_iff.mp hST).trans (Subgroup.centralizer_le_normalizer (S : Set G))
  have hcardST : Nat.card ↥(S ⊔ T) = Nat.card ↥T * 6 := by
    rw [RCSTSp2.card_sup_of_disjoint hTS hdST, hcardS]
  have hcardD : Nat.card ↥D = Nat.card ↥T * Nat.card ↥Q := by
    rw [hDdef]
    exact RCSTSp2.card_sup_of_disjoint hTQ (hdQL.mono_right le_sup_right)
  have hcardX : Nat.card ↥X = 6 * Nat.card ↥D := by
    rw [hX, RCSTSp2.card_sup_of_disjoint (sup_le hSQ hTQ) hdQL, hcardST, hDdef,
      RCSTSp2.card_sup_of_disjoint hTQ (hdQL.mono_right le_sup_right)]
    ring
  have hDX : D ≤ X := by
    rw [hX, hDdef]
    exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  have hND : X ≤ Subgroup.normalizer (D : Set G) := by
    have h := (Subgroup.le_normalizer (H := X)).trans
      (CFSG.Quasithin.normalizer_le_normalizer_perfectCore X)
    rwa [hperfX] at h
  have hDpos : 0 < Nat.card ↥D := Nat.card_pos
  have hrX : D.relIndex X = 6 := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := X)
    rw [inf_eq_left.mpr hDX, hcardX] at h
    exact Nat.eq_of_mul_eq_mul_right hDpos h
  have hr6 : D.relIndex P ≤ 6 := by
    have hle := Subgroup.relIndex_le_of_le_right (H := D) (K := P) (L := X) hPX
      (by rw [hrX]; norm_num)
    rwa [hrX] at hle
  have hrm : D.relIndex P * Nat.card ↥(P ⊓ D) = Nat.card ↥P := by
    have h := Subgroup.relIndex_mul_card (H := D) (K := P)
    rwa [inf_comm] at h
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3) (G := ↥P)).mp hP3
  have hdiv : D.relIndex P ∣ Nat.card ↥P := ⟨Nat.card ↥(P ⊓ D), hrm.symm⟩
  rw [hk] at hdiv
  obtain ⟨n, hnle, hrn⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdiv
  have hr3 : D.relIndex P ≤ 3 := by
    rw [hrn] at hr6 ⊢
    have hn1 : n ≤ 1 := by
      by_contra hcon
      have h2 : 2 ≤ n := by omega
      have h9 : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h2
      have : (9 : ℕ) ≤ 6 := by simpa using h9.trans hr6
      omega
    calc 3 ^ n ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
      _ = 3 := by norm_num
  calc Nat.card ↥P = D.relIndex P * Nat.card ↥(P ⊓ D) := hrm.symm
    _ ≤ 3 * Nat.card ↥(P ⊓ D) := Nat.mul_le_mul_right _ hr3

theorem exists_mem_of_elemAbelian (h : GGRCSSThreeSetting G₀ r Q S T) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hE9 : 9 ≤ Nat.card E)
    (hEX : E ≤ G₀ ⊓ Subgroup.centralizer {r}) : ∃ e ∈ E, e ∈ Q ⊔ T ∧ orderOf e = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hP3 : IsPGroup 3 E := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx3 : (x : G) ^ 3 = 1 := hE.2 (x : G) x.2
    have hdvd : orderOf (x : G) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    rw [Subgroup.orderOf_coe] at hdvd
    obtain h1 | h3 := (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd
    · exact ⟨0, by simp [h1]⟩
    · exact ⟨1, by simp [h3]⟩
  have hbound := card_le h hEX hP3
  have h9D : 3 ≤ Nat.card ↥(E ⊓ (Q ⊔ T)) := by
    by_contra hcon
    have hle1 : Nat.card ↥(E ⊓ (Q ⊔ T)) ≤ 1 := by omega
    have h1 : Nat.card ↥(E ⊓ (Q ⊔ T)) = 1 := by
      have hpos : 0 < Nat.card ↥(E ⊓ (Q ⊔ T)) := Nat.card_pos
      omega
    have hlt : 3 * Nat.card ↥(E ⊓ (Q ⊔ T)) < 9 := by omega
    omega
  have hne : E ⊓ (Q ⊔ T) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h9D
    omega
  obtain ⟨e, he, he1⟩ : ∃ e ∈ E ⊓ (Q ⊔ T), e ≠ 1 := by
    by_contra hcon
    have hle : (E ⊓ (Q ⊔ T) : Subgroup G) ≤ ⊥ := by
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      exact hcon ⟨x, hx, hx1⟩
    exact hne (le_antisymm hle bot_le)
  exact ⟨e, he.1, he.2, orderOf_eq_prime (hE.2 e he.1) he1⟩

theorem nbr (h : GGRCSSThreeSetting G₀ r Q S T) {M : Subgroup G} (hG₀M : G₀ ≤ M)
    (hM : M ≤ Subgroup.normalizer (G₀ : Set G)) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    (hE9 : 9 ≤ Nat.card E) (hEX : E ≤ G₀ ⊓ Subgroup.centralizer {r})
    (hEM : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer {e} ≤ M) : GGRCSNbr M r := by
  obtain ⟨e, heE, heD, he3⟩ := exists_mem_of_elemAbelian h hE hE9 hEX
  have he1 : e ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at he3
    omega
  exact ggRCSNbr_of_layerQuasi (layerQuasi h hG₀M hM) heD he3 (hEM e heE he1)

end GGRCSSThreeSetting

end CFSG.StandardType
