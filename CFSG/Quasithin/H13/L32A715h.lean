module

public import CFSG.Quasithin.H13.L32A715c
public import CFSG.Quasithin.H13.L32A715d
public import CFSG.Quasithin.H13.L32AC52c
public import CFSG.Quasithin.H13.L32A715e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

structure Ctx7153 (G : Type) [Group G] [Finite G] (T L V H : Subgroup G) : Prop where
  S : Setting147 G T L V H
  three : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))
  h331 : Stmt3_3_1
  hThm : Thm14_5_3
  h1222 : Stmt12_2_2
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4
  h75 : Lemma14_7_5
  h77 : Lemma14_7_7
  h3x : NQCore.Prop134ThreeExtraspecial

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
include E

theorem card_v1 : Nat.card (fsuV1 T V) = 2 :=
  (stmtL32NModule_of_inputs E.h1332 E.h1334 G T L V E.S.hyp.hyp E.S.hyp.fsu).2.2.2.1

theorem g1_eq : A6.g1 T V = hz T V := normalizer_eq_centralizer_of_card_eq_two E.card_v1

theorem setting_hz : Setting147 G T L V (hz T V) := by
  have h := L32A.C.setting_g1 E.h1332 E.h1334 E.S
  rwa [E.g1_eq] at h

theorem le_hz : H ≤ hz T V := E.g1_eq ▸ E.S.hz.2.1

theorem t_le_hz : T ≤ hz T V := (le_sup_right.trans E.S.hz.1.1).trans E.le_hz

theorem k_le_hz : oTwoUpper H ≤ hz T V := (oTwoUpper_le H).trans E.le_hz

theorem hz_le_normalizer_K : hz T V ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
  le_normalizer_K E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.h3x E.S E.three E.setting_hz.hz.1.2
    E.k_le_hz E.t_le_hz

theorem hz_le_normalizer_l1 : hz T V ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  obtain ⟨-, hL1eq, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  rw [hL1eq]
  exact (E.hz_le_normalizer_K.trans (normalizer_le_normalizer_o2z _)).trans
    (normalizer_le_normalizer_oTwoUpper _)

theorem isPOnePlusTwo_kdot : IsPOnePlusTwo 3 ↥(modO2Image (hz T V) (oTwoUpper H)) :=
  isPOnePlusTwo_of_mulEquiv (quotEquivStar E.k_le_hz E.hz_le_normalizer_K) (isPOnePlusTwo_K E.three)

theorem kdot_normal : (modO2Image (hz T V) (oTwoUpper H)).Normal :=
  modO2Image_normal E.hz_le_normalizer_K

theorem l1dot_normal : (modO2Image (hz T V) (l1 T L V)).Normal :=
  modO2Image_normal E.hz_le_normalizer_l1

theorem pPrimeCore_eq_bot : CFSG.pPrimeCore 3 (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)) = ⊥ :=
  E.h77 G T L V (hz T V) E.setting_hz E.l1dot_normal

theorem pRank_le :
    Open.pRank 3 (⊤ : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := E.S.hyp.fsu.simple
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥(hz T V) :=
    (QuasithinUnique.qtkeCore_of_cat E.S.hyp.fsu.nonabelian E.S.hyp.fsu.qtke).1 _
      E.setting_hz.hz.1.2
  have h1 := hsqtk.1 3 Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
  have hN : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥(hz T V)) := by
    have hP2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥(hz T V)) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  rw [CFSG.SectionRank.pRank_quotient_eq _ hN]
  exact h1

theorem isPGroup_centralizer :
    IsPGroup 3 ↥(Subgroup.centralizer
      ((modO2Image (hz T V) (oTwoUpper H) : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)))) := by
  have := E.kdot_normal
  exact isPGroup_three_centralizer E.pRank_le E.pPrimeCore_eq_bot E.isPOnePlusTwo_kdot

theorem isPGroup_tdot : IsPGroup 2 ↥(modO2Image (hz T V) T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (E.S.hyp.fsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe E.t_le_hz).symm).map _

theorem faithful_tdot : ∀ g ∈ modO2Image (hz T V) T,
    (∀ x ∈ modO2Image (hz T V) (oTwoUpper H), g * x = x * g) → g = 1 := by
  intro g hg hgc
  have hgC : g ∈ Subgroup.centralizer
      ((modO2Image (hz T V) (oTwoUpper H) : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (hgc x hx).symm
  obtain ⟨a, ha⟩ := E.isPGroup_tdot ⟨g, hg⟩
  obtain ⟨b, hb⟩ := E.isPGroup_centralizer ⟨g, hgC⟩
  have ha' : g ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : g ^ 3 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcop : Nat.Coprime (2 ^ a) (3 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha')
    (orderOf_dvd_of_pow_eq_one hb'))

theorem irr_tdot : ∀ W : Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V)),
    modO2Image (hz T V) (l1 T L V) ≤ W → W ≤ modO2Image (hz T V) (oTwoUpper H) →
    modO2Image (hz T V) T ≤ Subgroup.normalizer (W : Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
    W = modO2Image (hz T V) (l1 T L V) ∨ W = modO2Image (hz T V) (oTwoUpper H) := by
  obtain ⟨hL1K, -, -, hirrK, -⟩ :=
    lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    E.t_le_hz.trans E.hz_le_normalizer_K
  have hAK : l1 T L V ⊔ pCoreOf 2 (oTwoUpper H) ≤ oTwoUpper H := sup_le hL1K (pCoreOf_le 2 _)
  have hA : modO2Image (hz T V) (l1 T L V ⊔ pCoreOf 2 (oTwoUpper H)) =
      modO2Image (hz T V) (l1 T L V) :=
    modO2Image_sup_of_le_pCoreOf (hL1K.trans E.k_le_hz)
      (by rw [pCoreOf_eq_inf_pCoreOf E.k_le_hz E.hz_le_normalizer_K]; exact inf_le_right)
  intro W hLW hWK hTW
  have h := irr_star E.k_le_hz hAK E.t_le_hz hTK hirrK W (by rw [hA]; exact hLW) hWK hTW
  rwa [hA] at h

theorem not_centralizer_tdot : ∃ t ∈ modO2Image (hz T V) T,
    t ∉ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
      Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
        Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) := by
  obtain ⟨-, -, -, -, hR1C, hidx, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  by_contra hno
  push Not at hno
  have heq : modO2Image (hz T V) (pCoreOf 2 (l1 T L V ⊔ T)) = modO2Image (hz T V) T := by
    rw [hR1C]
    exact le_antisymm inf_le_left fun t ht => ⟨ht, hno t ht⟩
  rw [heq, Subgroup.relIndex_self] at hidx
  norm_num at hidx

theorem exists_y :
    (Subgroup.center ↥(modO2Image (hz T V) (oTwoUpper H))).map
        (modO2Image (hz T V) (oTwoUpper H)).subtype = modO2Image (hz T V) (l1 T L V) ∧
    ∃ y ∈ modO2Image (hz T V) T,
      y ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
        Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
          Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) ∧
      y ^ 2 ≠ 1 ∧ y ^ 4 = 1 ∧
      (∀ r ∈ modO2Image (hz T V) T,
        r ∈ Subgroup.centralizer ((modO2Image (hz T V) (l1 T L V) :
          Subgroup (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) :
            Set (↥(hz T V) ⧸ CFSG.pCore 2 ↥(hz T V))) →
        r ^ 2 = 1 → r ≠ 1 → r = y ^ 2) ∧
      (∀ x ∈ modO2Image (hz T V) (oTwoUpper H),
        y ^ 2 * x * (y ^ 2)⁻¹ * x ∈ modO2Image (hz T V) (l1 T L V)) := by
  have := E.kdot_normal
  obtain ⟨hL1K, -⟩ := lemma14_7_15_one E.h331 E.hThm E.h1222 E.h1332 E.h1334 E.S E.three
  obtain ⟨-, -, hcard3, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  obtain ⟨hcen, y, hyT, hyC, hy2, hy4, huniq, hinv, -⟩ :=
    exists_y_of_faithful E.isPOnePlusTwo_kdot (modO2Image_mono hL1K) E.l1dot_normal hcard3
      E.isPGroup_tdot E.faithful_tdot E.irr_tdot E.not_centralizer_tdot
  exact ⟨hcen, y, hyT, hyC, hy2, hy4, huniq, hinv⟩

end Ctx7153

end CFSG.Quasithin.H13.L32A
