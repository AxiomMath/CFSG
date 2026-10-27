module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4

import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexBase
import CFSG.Quasithin.Recognition.St84.EdgeStabB
import CFSG.Walter.W67.Section6.Core61
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Wiring
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzPair
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4LemmaS
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Class
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4LocalStructure
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Abelian
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Central
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Disjoint
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Cases
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Frame
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4CaseI
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4CaseII
import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv
import CFSG.GroupTheory.CommutingConjugatePair
import CFSG.Adapters.Certificate43Check

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem centerOf_comm {X : Subgroup G} {x y : G} (hx : x ∈ centerOf X) (hy : y ∈ X) :
    x * y = y * x :=
  ((Subgroup.mem_centralizer_iff.mp hx.2) y hy).symm

private theorem conj_centerOf {X : Subgroup G} {x y : G} (hx : x ∈ centerOf X) (hy : y ∈ X) :
    y * x * y⁻¹ = x := by
  rw [← centerOf_comm hx hy, mul_inv_cancel_right]

private theorem LX_le_sup_of_MX_le {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT) {X : Subgroup G}
    (hle : t.MX t.QT 1 ≤ t.MX X 1) :
    t.LX X 1 ≤ t.LX t.QT 1 ⊔ t.EX X 1 := by
  have h1 : t.LX X 1 ≤ L2 ⊔ t.Qv 1 := LX_one_le_sup t hfr (X := X)
  have h2 : t.LX t.QT 1 ⊔ t.Qv 1 = L2 ⊔ t.Qv 1 := ArcL.LX_sup_Qv_one_eq t hfr hQ
  have hle' : t.LX X 1 ≤ t.LX t.QT 1 ⊔ t.Qv 1 := h2.symm ▸ h1
  have hQLX : t.LX t.QT 1 ≤ t.LX X 1 := CFSG.Quasithin.St84.oTwoPrime_mono hle
  have hQN : t.LX t.QT 1 ≤ normalizer (t.Qv 1 : Set G) :=
    (oTwoPrime_le (t.MX t.QT 1)).trans
      ((inf_le_right : t.MX t.QT 1 ≤ t.Gv 1).trans (t.Gv_le_normalizer_Qv 1))
  have hDed := CFSG.Walter.W67.Sec6.inf_sup_of_le (T := t.LX X 1) (A := t.Qv 1)
    (B := t.LX t.QT 1) hQLX hQN
  rw [sup_comm (t.Qv 1) (t.LX t.QT 1), inf_eq_left.mpr hle'] at hDed
  rw [hDed, LX_one_inf_Qv_one t (X := X)]
  exact le_of_eq (sup_comm (t.EX X 1) (t.LX t.QT 1))

private theorem pair_or_le_sup_Qv_zero_K
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {R : Subgroup G}
    (hK : t.K ≤ normalizer (R : Set G)) :
    (∃ s ∈ normIn R (t.Gv 0), t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) →
      (∀ g ∈ normIn R (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R (t.Gv 0) ⊔ t.Qv 0 := by
  rintro ⟨s, hsR, hs1⟩
  exact t.pair_or_le_sup_Qv_zero hfr inf_le_right (le_inf hK (t.K_le_Gv 0)) hsR hs1

private theorem D2_not_le_EX {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hE : pCoreOf 2 (t.LX t.QT 1) = t.EX t.QT 1) :
    ¬ t.D2 ≤ t.EX t.QT 1 := by
  have hEX2 : IsPGroup 2 (t.EX t.QT 1) := by
    rw [← hE]
    exact pCoreOf_isPGroup 2 (t.LX t.QT 1)
  have hD2odd : Odd (Nat.card t.D2) := by
    rw [t.card_D2 hfr]
    refine (Nat.odd_sub' (Nat.one_le_two_pow (n := f))).mpr ?_
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact absurd hfr.hf (by norm_num)
    have h2 : Even (2 ^ f : ℕ) := (even_two (α := ℕ)).pow_of_ne_zero (n := f) hf0
    simpa using h2
  have hD2ne : t.D2 ≠ ⊥ := by
    intro hbot
    have hcard : 1 < Nat.card t.D2 := by
      rw [t.card_D2 hfr]
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hfr.hf
      omega
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  intro hD2E
  have hinf := CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hEX2 hD2odd
  have hbot : t.D2 = ⊥ := by
    rw [← inf_eq_left.mpr hD2E, inf_comm, hinf]
  exact hD2ne hbot

private theorem YX_map_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hE : pCoreOf 2 (t.LX t.QT 1) = t.EX t.QT 1)
    (hD2 : t.D2 ≤ t.YX t.QT 1) :
    ((t.YX t.QT 1).subgroupOf (t.LX t.QT 1)).map
      (QuotientGroup.mk' (pCore 2 ↥(t.LX t.QT 1))) ≠ ⊥ := by
  intro hbot
  apply D2_not_le_EX t hfr hE
  let L : Subgroup G := t.LX t.QT 1
  let Y : Subgroup G := t.YX t.QT 1
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hker : Y.subgroupOf L ≤ π.ker := (Subgroup.map_eq_bot_iff (Y.subgroupOf L)).mp hbot
  rw [show π.ker = pCore 2 ↥L from QuotientGroup.ker_mk' _,
    ← CFSG.openPCoreOf_subgroupOf 2 L] at hker
  have hYle : Y ≤ pCoreOf 2 L := by
    intro y hy
    have hmem : (⟨y, oTwoRes_le L hy⟩ : ↥L) ∈ Y.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact hy
    simpa using (Subgroup.mem_subgroupOf.mp (hker hmem))
  rw [hE] at hYle
  exact hD2.trans hYle

private theorem YX_map_subgroupOf_eq_top {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX t.QT 1)))
    (hE : pCoreOf 2 (t.LX t.QT 1) = t.EX t.QT 1)
    (hD2 : t.D2 ≤ t.YX t.QT 1) :
    ((t.YX t.QT 1).subgroupOf (t.LX t.QT 1)).map
      (QuotientGroup.mk' (pCore 2 ↥(t.LX t.QT 1))) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (oTwoQuot ↥(t.LX t.QT 1)) :=
    CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hfr.hf hq
  let L : Subgroup G := t.LX t.QT 1
  let Y : Subgroup G := t.YX t.QT 1
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hNne : (Y.subgroupOf L).map π ≠ ⊥ := YX_map_ne_bot t hfr hE hD2
  haveI hNn : ((Y.subgroupOf L).map π).Normal :=
    (Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoRes L)).map π
      (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((Y.subgroupOf L).map π) with h | h
  · exact absurd h hNne
  · exact h

private theorem YX_sup_EX_eq_LX {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX t.QT 1)))
    (hE : pCoreOf 2 (t.LX t.QT 1) = t.EX t.QT 1)
    (hD2 : t.D2 ≤ t.YX t.QT 1) :
    t.YX t.QT 1 ⊔ t.EX t.QT 1 = t.LX t.QT 1 := by
  let L : Subgroup G := t.LX t.QT 1
  let Y : Subgroup G := t.YX t.QT 1
  let E : Subgroup G := t.EX t.QT 1
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  have hYL : Y ≤ L := oTwoRes_le L
  have hEL : E ≤ L := by
    change t.EX t.QT 1 ≤ t.LX t.QT 1
    rw [← hE]
    exact pCoreOf_le 2 L
  have hN : (Y.subgroupOf L).map π = ⊤ := YX_map_subgroupOf_eq_top t hfr hq hE hD2
  have hYle : Y ⊔ E ≤ L := sup_le hYL hEL
  have hpc : pCoreOf 2 L ≤ Y ⊔ E := by
    rw [hE]
    exact le_sup_right
  have himg : ((Y ⊔ E).subgroupOf L).map π = ⊤ := by
    rw [Subgroup.subgroupOf_sup hYL hEL, Subgroup.map_sup, hN,
      show (E.subgroupOf L).map π = ⊥ by
        rw [show E.subgroupOf L = pCore 2 ↥L by
          rw [← CFSG.openPCoreOf_subgroupOf 2 L, hE]]
        exact QuotientGroup.map_mk'_self (pCore 2 ↥L),
      sup_bot_eq]
  exact (CFSG.Quasithin.Stroth.map_oTwoQuot_subgroupOf_eq_top_iff hYle hpc).mp himg

private theorem le_sup_YX_Qv_one {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX t.QT 1)))
    (hcov : L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1) :
    L2 ≤ t.YX t.QT 1 ⊔ t.Qv 1 := by
  have hE := ArcL.pCoreOf_LX_one t hfr hQ
  have hD2 := t.D2_le_YX hQ hcov
  have hEq := t.YX_sup_EX_eq_LX hfr hq hE hD2
  calc L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1 := hcov
    _ = (t.YX t.QT 1 ⊔ t.EX t.QT 1) ⊔ t.Qv 1 := by rw [hEq]
    _ = t.YX t.QT 1 ⊔ t.Qv 1 := by
        rw [sup_assoc,
          show t.EX t.QT 1 ⊔ t.Qv 1 = t.Qv 1 from sup_eq_right.mpr inf_le_left]

private theorem maximal_facts_swap
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcLMax X)
    (hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1))) (hc : CharTwo (t.LX X 1))
    (hE : pCoreOf 2 (t.LX X 1) = t.EX X 1) (hEP : t.EX X 1 ≤ t.PX X)
    (hP : IsSylowTwoOf (t.PX X) (t.LX X 1)) (hMK : t.MX X 1 = t.LX X 1 ⊔ t.K)
    (hLY : t.LX X 1 = t.YX X 1 ⊔ t.PX X)
    (hnc : NoCharNormal (t.PX X) (t.LX X 1)) :
    IsElemAbelian 2 (t.EX X 1) ∧
      St84.NatQuot (t.LX X 1) (t.EX X 1) (centerOf (t.LX X 1)) f ∧
      ¬ ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X (-1) := by
  have hXc : t.ArcL X := IsArcClassMax.isArcClass hX
  obtain ⟨s, hs0, hsK, hs, -, hs2⟩ := ArcL.exists_swap t hfr hXc
  have hsP : s ∈ normalizer (t.PX X : Set G) := ArcL.MX_zero_le_normalizer_pX t hfr hXc hs0
  have hP0 : t.PX X ≠ t.Qv 0 := ArcLMax.pX_ne_Qv_zero_of_frame t hfr hX
  obtain ⟨t', ht', ht'P, ht'N, ht'2, hst'⟩ := exists_t' t hP0 hs0.2 hsP hs2
  have hmax : ∀ R : Subgroup G, R ≠ ⊥ → R ≤ t.EX X 1 →
      t.MX X 1 ≤ normalizer (R : Set G) → t.K ≤ normalizer (R : Set G) →
      s ∈ normalizer (R : Set G) → t' ∉ normalizer (R : Set G) := by
    intro R hR hRE hM hK hsR
    refine ArcLMax.not_mem_normalizer t hfr hX hR hRE hM hK hs0 hs hsR ?_ ht' ?_
    · exact pair_or_le_sup_Qv_zero_K t hfr hK ⟨s, ⟨⟨hsR, hs0.2⟩, hs⟩⟩
    · exact fun hXt' => ht'P ⟨ht', hXt', (t.Qv_le_Gv hfr 0).2 ht'⟩
  have hab := ArcLMax.isElemAbelian_EX t hfr hX hq hc hE hEP hP hMK hLY hnc hs0 hsK hs
    hs2 ht' ht'N hst' hmax
  have hV2 := ArcLMax.not_commutator_le_EX_neg_one t hfr hX hq hc hE hEP hP hMK hLY
    hs0 hsK hs hs2 ht' ht'N hst' hmax
  exact ⟨hab.1, hab.2, hV2⟩

private theorem maximal_facts
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {X : Subgroup G} (hX : t.ArcLMax X) :
    IsElemAbelian 2 (t.EX X 1) ∧
      St84.NatQuot (t.LX X 1) (t.EX X 1) (centerOf (t.LX X 1)) f ∧
      t.MX X 1 = t.LX X 1 ⊔ t.K ∧ t.LX X 1 ⊓ t.Qv 1 = t.EX X 1 ∧
      ¬ ⁅t.EX X 1, t.YX X 1⁆ ≤ t.EX X (-1) := by
  have hXc : t.ArcL X := IsArcClassMax.isArcClass hX
  have hX2 : IsPGroup 2 X := IsArcClassMax.isPGroup hX
  have hq : IsL2Quot f (oTwoQuot ↥(t.LX X 1)) := ArcL.isL2Quot_LX_one t hfr hXc
  have hc : CharTwo (t.LX X 1) := ArcL.charTwo_LX_one t hfr hXc hX2
  have hE : pCoreOf 2 (t.LX X 1) = t.EX X 1 := ArcL.pCoreOf_LX_one t hfr hXc
  have hEP : t.EX X 1 ≤ t.PX X := ArcL.EX_one_le_pX t hfr hXc
  have hP : IsSylowTwoOf (t.PX X) (t.LX X 1) := ArcL.isSylowTwoOf_pX_LX_one t hfr hXc
  have hMK : t.MX X 1 = t.LX X 1 ⊔ t.K := ArcL.MX_one_eq_sup t hfr hXc
  have hLY : t.LX X 1 = t.YX X 1 ⊔ t.PX X := ArcL.LX_one_eq_sup t hfr hXc
  have hinf : t.LX X 1 ⊓ t.Qv 1 = t.EX X 1 := LX_one_inf_Qv_one t
  have hnc : NoCharNormal (t.PX X) (t.LX X 1) :=
    ArcL.noCharNormal_pX_LX_one t hfr hXc (ArcLMax.noCharNormal_of_frame t hfr hX)
  obtain ⟨hab, hnat, hV2⟩ := maximal_facts_swap t hfr hX hq hc hE hEP hP hMK hLY hnc
  exact ⟨hab, hnat, hMK, hinf, hV2⟩

private theorem Zv_inf_QT_of_arcLMax
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hQmax : t.ArcLMax t.QT)
    (hZ : t.QT ≤ centerOf (t.LX t.QT 1)) :
    t.Zv 0 ⊓ t.QT = ⊥ ∧ t.Zv 1 ⊓ t.QT = ⊥ := by
  have hArcL : t.ArcL t.QT := IsArcClassMax.isArcClass hQmax
  have hcovQ : L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1 := ArcL.L2_le_LX_sup_Qv_one t hfr hArcL
  have hqQ : IsL2Quot f (oTwoQuot ↥(t.LX t.QT 1)) := ArcL.isL2Quot_LX_one t hfr hArcL
  have hα : t.YX t.QT 1 ≤ centralizer (t.QT : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact centerOf_comm (hZ hx) (oTwoRes_le (t.LX t.QT 1) hy)
  have hcovYX : L2 ≤ t.YX t.QT 1 ⊔ t.Qv 1 := le_sup_YX_Qv_one t hfr hArcL hqQ hcovQ
  have hS : ∀ R : Subgroup G, R ≤ t.Zv 0 → t.K ≤ normalizer (R : Set G) →
      t.x₁ ∈ normalizer (R : Set G) → CosetTrans (normalizer (R : Set G)) (t.Gv 1) (t.Gv 0) →
      R = ⊥ := fun R hR hK hx htr => t.eq_bot_of_cosetTrans_normalizer hfr hR hK hx htr
  have h0 : t.Zv 0 ⊓ t.QT = ⊥ := Zv_zero_inf_QT t hfr hα hcovYX hS
  exact ⟨h0, Zv_one_inf_QT t hfr hα hcovYX h0⟩

private theorem QT_maximal_facts
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hArcL : t.ArcL t.QT) :
    t.ArcLMax t.QT ∧ IsElemAbelian 2 (t.EX t.QT 1) ∧
      St84.NatQuot (t.LX t.QT 1) (t.EX t.QT 1) (centerOf (t.LX t.QT 1)) f ∧
      t.QT ≤ centerOf (t.LX t.QT 1) := by
  have hmaxAll : ∀ X : Subgroup G, t.ArcLMax X → IsElemAbelian 2 (t.EX X 1) ∧
      t.MX X 1 = t.LX X 1 ⊔ t.K ∧ t.LX X 1 ⊓ t.Qv 1 = t.EX X 1 := by
    intro X hX
    obtain ⟨hab, -, hMK, hinf, -⟩ := maximal_facts t hfr hX
    exact ⟨hab, hMK, hinf⟩
  have hQmax : t.ArcLMax t.QT :=
    arcLMax_QT t hfr hArcL hmaxAll
      (fun X _ hle => LX_le_sup_of_MX_le t hfr hArcL hle)
  obtain ⟨habQ, hnatQ, -, -, hV2Q⟩ := maximal_facts t hfr hQmax
  exact ⟨hQmax, habQ, hnatQ, QT_le_center t hfr hnatQ hV2Q⟩

private theorem caseI_of_facts {a f : ℕ}
    (hfr : Frame L1 L2 S a f) (hQ : t.ArcL t.QT) (hab : IsElemAbelian 2 (t.EX t.QT 1))
    (hZ : t.QT ≤ centerOf (t.LX t.QT 1)) (h1 : t.Zv 1 ⊓ t.QT = ⊥)
    (hI : centerOf (t.LX t.QT 1) = t.QT ∧ t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ t.QT ∧
      t.Zv 0 ≤ t.Zv 1 ∧ (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      (∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ t.QT)) :
    ((∀ x ∈ t.EX t.QT 1, ∀ y ∈ t.EX t.QT 1, x * y = y * x) ∧
      pCoreOf 2 t.GT ≤ t.EX t.QT 1 ∧ t.Zv 1 ≤ t.EX t.QT 1 ∧
      t.Zv 1 ⊓ pCoreOf 2 t.GT = ⊥ ∧ t.EX t.QT 1 ≤ t.Qv 0 ∧ t.EX t.QT 1 < t.Qv 1 ∧
      t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ pCoreOf 2 t.GT ∧ t.Zv 0 ≤ t.Zv 1 ∧
      (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      t.Qv 1 ⊓ normalizer (pCoreOf 2 t.GT : Set G) ≤ t.EX t.QT 1 ∧
      t.LX t.QT 1 ≤ L2 ⊔ t.Qv 1 ∧
      (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → ∀ x ∈ pCoreOf 2 t.GT, l * x * l⁻¹ = x) ∧
      (∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ pCoreOf 2 t.GT)) := by
  have hcomm : ∀ x ∈ t.EX t.QT 1, ∀ y ∈ t.EX t.QT 1, x * y = y * x :=
    fun x hx y hy => CFSG.Open.IsElemAbelian.comm hab hx hy
  have hEXQ0 : t.EX t.QT 1 ≤ t.Qv 0 :=
    (ArcL.EX_one_le_pX t hfr hQ).trans inf_le_left
  have hα : ∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → ∀ x ∈ t.QT, l * x * l⁻¹ = x := by
    intro l hl _ x hx
    exact conj_centerOf (hZ hx) hl
  exact ⟨hcomm, QT_le_EX t hfr, Zv_one_le_EX t hfr, h1, hEXQ0, EX_QT_lt_Qv_one t hfr hEXQ0,
    hI.2.1, hI.2.2.1, hI.2.2.2.1, le_rfl, LX_one_le_sup t (X := t.QT) hfr, hα,
    hI.2.2.2.2⟩

private theorem caseII_of_facts {a f : ℕ}
    (hfr : Frame L1 L2 S a f)
    (hcov : L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1) (hD2 : t.D2 ≤ t.YX t.QT 1)
    (h0 : t.Zv 0 ⊓ t.QT = ⊥)
    (hres : t.QT = centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) ∧
      t.PX t.QT = t.EX t.QT 1 ⊔ t.EX t.QT (-1) ∧
      t.EX t.QT 1 ⊓ t.EX t.QT (-1) = centerOf (t.PX t.QT) ∧
      (t.EX t.QT 1 ⊓ t.EX t.QT (-1)).relIndex (t.EX t.QT 1) = 2 ^ f ∧
      centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ≤ centerOf (t.PX t.QT) ∧
      t.Zv 0 ≤ centerOf (t.PX t.QT))
    (hII : t.Zv 0 ≤ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ∧
      t.QT.relIndex (centerOf (t.LX t.QT 1)) = 2 ^ f ∧
      (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ centerOf (t.LX t.QT (-1)),
        k * x * k⁻¹ * x⁻¹ ∈ t.QT → x ∈ t.QT) ∧
      (∀ x ∈ centerOf (t.LX t.QT (-1)), x ∉ t.QT →
        ∀ y ∈ centerOf (t.LX t.QT (-1)), y ∉ t.QT → ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ t.QT)) :
    (t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥ ∧
      t.Zv 0 ≤ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ∧
      centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) = pCoreOf 2 t.GT ∧
      (pCoreOf 2 t.GT).relIndex (centerOf (t.LX t.QT 1)) = 2 ^ f ∧
      (∀ x ∈ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)),
        ∀ y ∈ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)), x * y = y * x) ∧
      (centerOf (t.LX t.QT 1)).map (MulAut.conj t.x₁).toMonoidHom = centerOf (t.LX t.QT (-1)) ∧
      (centerOf (t.LX t.QT (-1))).map (MulAut.conj t.x₁).toMonoidHom = centerOf (t.LX t.QT 1) ∧
      t.K ≤ normalizer (centerOf (t.LX t.QT 1) : Set G) ∧
      (∀ k ∈ t.D2, ∀ x ∈ centerOf (t.LX t.QT 1), k * x * k⁻¹ = x) ∧
      (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ centerOf (t.LX t.QT (-1)),
        k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT) ∧
      (∀ x ∈ centerOf (t.LX t.QT (-1)), x ∉ pCoreOf 2 t.GT →
        ∀ y ∈ centerOf (t.LX t.QT (-1)), y ∉ pCoreOf 2 t.GT →
          ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ pCoreOf 2 t.GT) ∧
      t.LX t.QT 1 ≤ L2 ⊔ t.Qv 1 ∧ L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1 ∧
      (∀ l ∈ t.LX t.QT 1, ∀ x ∈ centerOf (t.LX t.QT 1), l * x * l⁻¹ = x)) := by
  have hcomm : ∀ x ∈ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)),
      ∀ y ∈ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)), x * y = y * x := by
    intro x hx y hy
    have hx' := hres.2.2.2.2.1 hx
    have hy' : y ∈ t.PX t.QT := (hres.2.2.2.2.1 hy).1
    exact ((Subgroup.mem_centralizer_iff.mp hx'.2) y hy').symm
  have hD2cent : ∀ k ∈ t.D2, ∀ x ∈ centerOf (t.LX t.QT 1), k * x * k⁻¹ = x := by
    intro k hk x hx
    exact conj_centerOf hx (oTwoRes_le (t.LX t.QT 1) (hD2 hk))
  have hLXcent : ∀ l ∈ t.LX t.QT 1, ∀ x ∈ centerOf (t.LX t.QT 1), l * x * l⁻¹ = x :=
    fun l hl x hx => conj_centerOf hx hl
  have hmap := map_centerOf_LX_x₁ t
  exact ⟨h0, hII.1, hres.1.symm, hII.2.1, hcomm, hmap.1, hmap.2,
    K_le_normalizer_centerOf_LX t, hD2cent, hII.2.2.1, hII.2.2.2,
    LX_one_le_sup t (X := t.QT) hfr, hcov, hLXcent⟩

theorem caseI_or_caseII_of_ne_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hQ : pCoreOf 2 t.GT ≠ ⊥) :
    ((∀ x ∈ t.EX t.QT 1, ∀ y ∈ t.EX t.QT 1, x * y = y * x) ∧
      pCoreOf 2 t.GT ≤ t.EX t.QT 1 ∧ t.Zv 1 ≤ t.EX t.QT 1 ∧
      t.Zv 1 ⊓ pCoreOf 2 t.GT = ⊥ ∧ t.EX t.QT 1 ≤ t.Qv 0 ∧ t.EX t.QT 1 < t.Qv 1 ∧
      t.EX t.QT 1 ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ pCoreOf 2 t.GT ∧ t.Zv 0 ≤ t.Zv 1 ∧
      (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) ∧
      t.Qv 1 ⊓ normalizer (pCoreOf 2 t.GT : Set G) ≤ t.EX t.QT 1 ∧
      t.LX t.QT 1 ≤ L2 ⊔ t.Qv 1 ∧
      (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → ∀ x ∈ pCoreOf 2 t.GT, l * x * l⁻¹ = x) ∧
      (∀ e ∈ t.EX t.QT 1, (∀ l ∈ t.LX t.QT 1, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ pCoreOf 2 t.GT)) ∨
    (t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥ ∧
      t.Zv 0 ≤ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)) ∧
      centerOf (t.LX t.QT 1) ⊓ centerOf (t.LX t.QT (-1)) = pCoreOf 2 t.GT ∧
      (pCoreOf 2 t.GT).relIndex (centerOf (t.LX t.QT 1)) = 2 ^ f ∧
      (∀ x ∈ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)),
        ∀ y ∈ centerOf (t.LX t.QT 1) ⊔ centerOf (t.LX t.QT (-1)), x * y = y * x) ∧
      (centerOf (t.LX t.QT 1)).map (MulAut.conj t.x₁).toMonoidHom = centerOf (t.LX t.QT (-1)) ∧
      (centerOf (t.LX t.QT (-1))).map (MulAut.conj t.x₁).toMonoidHom = centerOf (t.LX t.QT 1) ∧
      t.K ≤ normalizer (centerOf (t.LX t.QT 1) : Set G) ∧
      (∀ k ∈ t.D2, ∀ x ∈ centerOf (t.LX t.QT 1), k * x * k⁻¹ = x) ∧
      (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ centerOf (t.LX t.QT (-1)),
        k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT) ∧
      (∀ x ∈ centerOf (t.LX t.QT (-1)), x ∉ pCoreOf 2 t.GT →
        ∀ y ∈ centerOf (t.LX t.QT (-1)), y ∉ pCoreOf 2 t.GT →
          ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ pCoreOf 2 t.GT) ∧
      t.LX t.QT 1 ≤ L2 ⊔ t.Qv 1 ∧ L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1 ∧
      (∀ l ∈ t.LX t.QT 1, ∀ x ∈ centerOf (t.LX t.QT 1), l * x * l⁻¹ = x)) := by
  have hArcL : t.ArcL t.QT := t.arcL_QT_of_ne_bot hfr hQ
  obtain ⟨hQmax, habQ, hnatQ, hZQ⟩ := QT_maximal_facts t hfr hArcL
  have hcovQ : L2 ≤ t.LX t.QT 1 ⊔ t.Qv 1 := ArcL.L2_le_LX_sup_Qv_one t hfr hArcL
  have hEMX : pCoreOf 2 (t.MX t.QT 1) = t.EX t.QT 1 := ArcL.pCoreOf_MX_one t hfr hArcL
  have hEPQ : t.EX t.QT 1 ≤ t.PX t.QT := ArcL.EX_one_le_pX t hfr hArcL
  have hPQ : IsSylowTwoOf (t.PX t.QT) (t.LX t.QT 1) :=
    ArcL.isSylowTwoOf_pX_LX_one t hfr hArcL
  have hD2Q : t.D2 ≤ t.YX t.QT 1 := t.D2_le_YX hArcL hcovQ
  have hZ0 : t.Zv 0 ≤ normIn t.QT (t.Gw (-1) 1) :=
    ArcL.Zv_zero_le t hfr hArcL (IsArcClassMax.isPGroup hQmax)
  obtain ⟨h0, h1⟩ := Zv_inf_QT_of_arcLMax t hfr hQmax hZQ
  have hres := residue_facts t hfr hArcL habQ hZQ hnatQ hPQ hEPQ hEMX hZ0
  rcases caseI_or_caseII t hfr hArcL habQ hnatQ hPQ hD2Q h0 h1 hres with hI | hII
  · exact Or.inl (caseI_of_facts t hfr hArcL habQ hZQ h1 hI)
  · exact Or.inr (caseII_of_facts t hfr hcovQ hD2Q h0 hres hII)

theorem pCoreOf_GT_eq_bot_of_exclusions
    {a f : ℕ} (hfr : Frame L1 L2 S a f)
    (hI : ∀ {E Lstar : Subgroup G},
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → pCoreOf 2 t.GT ≤ E →
      t.Zv 1 ≤ E → t.Zv 1 ⊓ pCoreOf 2 t.GT = ⊥ →
      E ≤ t.Qv 0 → E < t.Qv 1 →
      E ⊓ t.Qv (-1) ≤ t.Zv 0 ⊔ pCoreOf 2 t.GT → t.Zv 0 ≤ t.Zv 1 →
      (∀ x ∈ t.Qv 0, ∀ z ∈ t.Zv 1, x * z * x⁻¹ * z⁻¹ ∈ t.Zv 0) →
      t.Qv 1 ⊓ normalizer (pCoreOf 2 t.GT : Set G) ≤ E →
      Lstar ≤ L2 ⊔ t.Qv 1 →
      (∀ l ∈ Lstar, Odd (orderOf l) → ∀ x ∈ pCoreOf 2 t.GT, l * x * l⁻¹ = x) →
      (∀ e ∈ E, (∀ l ∈ Lstar, Odd (orderOf l) → l * e * l⁻¹ = e) →
        e ∈ pCoreOf 2 t.GT) → False)
    (hII : ∀ {A A₂ Lstar : Subgroup G},
      t.Zv 0 ⊓ pCoreOf 2 t.GT = ⊥ → t.Zv 0 ≤ A ⊔ A₂ →
      A ⊓ A₂ = pCoreOf 2 t.GT → (pCoreOf 2 t.GT).relIndex A = 2 ^ f →
      (∀ x ∈ A ⊔ A₂, ∀ y ∈ A ⊔ A₂, x * y = y * x) →
      A.map (MulAut.conj t.x₁).toMonoidHom = A₂ →
      A₂.map (MulAut.conj t.x₁).toMonoidHom = A →
      t.K ≤ normalizer (A : Set G) →
      (∀ k ∈ t.D2, ∀ x ∈ A, k * x * k⁻¹ = x) →
      (∀ k ∈ t.D2, k ≠ 1 → ∀ x ∈ A₂,
        k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 t.GT → x ∈ pCoreOf 2 t.GT) →
      (∀ x ∈ A₂, x ∉ pCoreOf 2 t.GT → ∀ y ∈ A₂, y ∉ pCoreOf 2 t.GT →
        ∃ k ∈ t.D2, k * x * k⁻¹ * y⁻¹ ∈ pCoreOf 2 t.GT) →
      Lstar ≤ L2 ⊔ t.Qv 1 → L2 ≤ Lstar ⊔ t.Qv 1 →
      (∀ l ∈ Lstar, ∀ x ∈ A, l * x * l⁻¹ = x) → False) :
    pCoreOf 2 t.GT = ⊥ := by
  by_contra hQ
  rcases t.caseI_or_caseII_of_ne_bot hfr hQ with
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ |
    ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  · exact hI h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  · exact hII h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14

end Track

theorem str83RqO4_holds : Str83RqO4 :=
  haveI := CFSG.Adapters.certificate43_holds
  str83RqO4_of_pCoreOf_eq_bot fun _ _ _ _ _ _ _ _ hfr _ t =>
    t.pCoreOf_GT_eq_bot_of_exclusions hfr (t.false_of_caseI hfr) (t.false_of_caseII hfr)

end CFSG.Quasithin.Stroth.Rq

end
