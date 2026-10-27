module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpCoreSylow
import CFSG.GH74.GLS.Balance.Bender.ExtSylow
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.Y2ConjugationInvariance
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s2122np_isSylowOf_sup_pCoreOf {M L S : Subgroup G}
    (hLM : L ≤ M) (hS : IsSylowOf 7 S L) :
    IsSylowOf 7 S (L ⊔ pCoreOf 2 M) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hQp : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hLnorm : L ≤ normalizer (pCoreOf 2 M : Set G) :=
    hLM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hbotSyl : CFSG.GH74.GLS.Balance.IsSylowIn 7 (⊥ : Subgroup G) (pCoreOf 2 M) := by
    refine ⟨bot_le, IsPGroup.of_bot, ?_⟩
    intro T hTQ hTp
    have h := CFSG.ABGLocalTools.inf_eq_bot_of_isPGroup_two (p := 7) (by norm_num) hTp hQp
    rw [inf_eq_left.mpr hTQ] at h
    simp [h]
  have hSIn : CFSG.GH74.GLS.Balance.IsSylowIn 7 S L :=
    CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_iff_isSylowOf.mpr hS
  have hbotC : S ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    simp at hy
    subst hy
    simp
  have hIn := CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_sup_of_le_normalizer
    (N := pCoreOf 2 M) (M₀ := L) (M := pCoreOf 2 M ⊔ L)
    (P := ⊥) (R := S) rfl hLnorm hbotSyl hSIn hbotC
  rw [bot_sup_eq, sup_comm] at hIn
  exact CFSG.GH74.GLS.Balance.BenderExt.isSylowIn_iff_isSylowOf.mp hIn

private theorem uc22s2122np_sup_T_mul {D : Data G} {Ē : Subgroup (Bar2 D.M)} {E : Subgroup G}
    (hEM : E ≤ D.M) (hEbar : barImage D.M E = Ē)
    (hĒT : ((Ē ⊔ barImage D.M D.T : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) =
      (Ē : Set (Bar2 D.M)) * (barImage D.M D.T : Set (Bar2 D.M))) :
    ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G) := by
  classical
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hQT : pCoreOf 2 D.M ≤ D.T :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section12.pCoreOf_le_of_isSylowOf D.sylowM
  have hQN : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M
  have hsup_le : E ⊔ D.T ≤ barPreimage D.M (Ē ⊔ barImage D.M D.T) := by
    refine sup_le ?_ ?_
    · intro x hx
      refine uc22p21c_mem_barPreimage.2 ⟨hEM hx, ?_⟩
      rw [← hEbar]
      exact Subgroup.mem_sup_left (uc22p21c_mem_barImage.2 ⟨⟨x, hEM hx⟩, hx, rfl⟩)
    · intro x hx
      refine uc22p21c_mem_barPreimage.2 ⟨hTM hx, ?_⟩
      exact Subgroup.mem_sup_right (uc22p21c_mem_barImage.2 ⟨⟨x, hTM hx⟩, hx, rfl⟩)
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_mul]
    obtain ⟨hxM, hxbar⟩ := uc22p21c_mem_barPreimage.1 (hsup_le hx)
    have hxbar' : (uc22p21cPi D.M ⟨x, hxM⟩) ∈
        (Ē : Set (Bar2 D.M)) * (barImage D.M D.T : Set (Bar2 D.M)) := by
      rw [← hĒT]
      exact hxbar
    obtain ⟨eb, heb, tb, htb, hprod⟩ := hxbar'
    rw [← hEbar] at heb
    obtain ⟨e, heE, hebar⟩ := uc22p21c_mem_barImage.1 heb
    obtain ⟨t, htT, htbar⟩ := uc22p21c_mem_barImage.1 htb
    have hqM : x * ((e : G) * (t : G))⁻¹ ∈ D.M :=
      D.M.mul_mem hxM (D.M.inv_mem (D.M.mul_mem e.2 t.2))
    have hqker : uc22p21cPi D.M ⟨x * ((e : G) * (t : G))⁻¹, hqM⟩ = 1 := by
      have h1 : (⟨x * ((e : G) * (t : G))⁻¹, hqM⟩ : ↥D.M) =
          ⟨x, hxM⟩ * (e * t)⁻¹ := by ext; rfl
      rw [h1, map_mul, map_inv, map_mul, hebar, htbar, ← hprod, mul_inv_cancel]
    have hqQ : x * ((e : G) * (t : G))⁻¹ ∈ pCoreOf 2 D.M :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := D.M) ⟨_, hqM⟩).2
        ((QuotientGroup.eq_one_iff _).1 hqker)
    have hconjQ : (e : G)⁻¹ * (x * ((e : G) * (t : G))⁻¹) * (e : G) ∈
        pCoreOf 2 D.M := by
      have h := (Subgroup.mem_normalizer_iff.mp (hQN (D.M.inv_mem e.2))
        (x * ((e : G) * (t : G))⁻¹)).mp hqQ
      simpa using h
    refine ⟨(e : G), heE, (e : G)⁻¹ * (x * ((e : G) * (t : G))⁻¹) * (e : G) * (t : G),
      D.T.mul_mem (hQT hconjQ) htT, ?_⟩
    group
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

private theorem uc22s2122np_exists_bar_order_seven {D : Data G} {L : Subgroup G}
    {Ē : Subgroup (Bar2 D.M)} (hĒ : Nat.card Ē = 49)
    (hĒL : Ē ⊓ barImage D.M L ≠ ⊥) :
    ∃ ē : ↥(Ē ⊓ barImage D.M L), orderOf ē = 7 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hne1 : Nat.card ↥(Ē ⊓ barImage D.M L) ≠ 1 := by
    intro h
    exact hĒL (Subgroup.card_eq_one.mp h)
  have hdvd : Nat.card ↥(Ē ⊓ barImage D.M L) ∣ 7 ^ 2 := by
    rw [show (7 : ℕ) ^ 2 = 49 by norm_num, ← hĒ]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    exact hne1 hj
  have h7dvd : 7 ∣ Nat.card ↥(Ē ⊓ barImage D.M L) := by
    rw [hj]
    exact dvd_pow_self 7 hj0
  exact exists_prime_orderOf_dvd_card' (G := ↥(Ē ⊓ barImage D.M L)) 7 h7dvd

private theorem uc22s2122np_lift_order_seven {D : Data G} {E : Subgroup G}
    {Ē : Subgroup (Bar2 D.M)} (hEM : E ≤ D.M) (hEbar : barImage D.M E = Ē)
    (hEinfQ : E ⊓ pCoreOf 2 D.M = ⊥) {ē : Bar2 D.M} (hēĒ : ē ∈ Ē)
    (hēord : orderOf ē = 7) :
    ∃ e : ↥D.M, (e : G) ∈ E ∧ uc22p21cPi D.M e = ē ∧ orderOf (e : G) = 7 := by
  classical
  rw [← hEbar] at hēĒ
  obtain ⟨e, heE, hebar⟩ := uc22p21c_mem_barImage.1 hēĒ
  have he7 : (e : G) ^ 7 = 1 := by
    have hmemE : (e : G) ^ 7 ∈ E := E.pow_mem heE 7
    have hker : uc22p21cPi D.M ⟨(e : G) ^ 7, hEM hmemE⟩ = 1 := by
      have h1 : (⟨(e : G) ^ 7, hEM hmemE⟩ : ↥D.M) = e ^ 7 := by ext; rfl
      rw [h1, map_pow, hebar, ← hēord, pow_orderOf_eq_one]
    have hQ : (e : G) ^ 7 ∈ pCoreOf 2 D.M :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := D.M) ⟨_, hEM hmemE⟩).2
        ((QuotientGroup.eq_one_iff _).1 hker)
    have hbot : (e : G) ^ 7 ∈ (⊥ : Subgroup G) := by
      rw [← hEinfQ]
      exact ⟨hmemE, hQ⟩
    exact Subgroup.mem_bot.1 hbot
  have he1 : (e : G) ≠ 1 := by
    intro h
    have he1' : e = 1 := Subtype.ext h
    have h1 : uc22p21cPi D.M e = 1 := by rw [he1', map_one]
    rw [hebar, ← orderOf_eq_one_iff] at h1
    omega
  exact ⟨e, heE, hebar, orderOf_eq_prime he7 he1⟩

private theorem uc22s2122np_mem_sup_pCoreOf_of_mem_barImage {D : Data G} {L : Subgroup G}
    {e : ↥D.M} (hebar : uc22p21cPi D.M e ∈ barImage D.M L) :
    (e : G) ∈ L ⊔ pCoreOf 2 D.M := by
  obtain ⟨l, hlL, hlbar⟩ := uc22p21c_mem_barImage.1 hebar
  have hqM : (e : G) * (l : G)⁻¹ ∈ D.M :=
    D.M.mul_mem e.2 (D.M.inv_mem l.2)
  have hqker : uc22p21cPi D.M ⟨(e : G) * (l : G)⁻¹, hqM⟩ = 1 := by
    have h1 : (⟨(e : G) * (l : G)⁻¹, hqM⟩ : ↥D.M) = e * l⁻¹ := by ext; rfl
    rw [h1, map_mul, map_inv, hlbar, mul_inv_cancel]
  have hqQ : (e : G) * (l : G)⁻¹ ∈ pCoreOf 2 D.M :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := D.M) ⟨_, hqM⟩).2
      ((QuotientGroup.eq_one_iff _).1 hqker)
  have hEq : (e : G) = ((e : G) * (l : G)⁻¹) * (l : G) := by group
  rw [hEq]
  exact mul_mem (Subgroup.mem_sup_right hqQ) (Subgroup.mem_sup_left hlL)

private theorem uc22s2122np_exists_order_seven_of_barE {D : Data G} {L E : Subgroup G}
    {Ē : Subgroup (Bar2 D.M)} (hĒ : Nat.card Ē = 49) (hEM : E ≤ D.M)
    (hEbar : barImage D.M E = Ē) (hEinfQ : E ⊓ pCoreOf 2 D.M = ⊥)
    (hĒL : Ē ⊓ barImage D.M L ≠ ⊥) :
    ∃ e ∈ E, orderOf e = 7 ∧ e ∈ L ⊔ pCoreOf 2 D.M := by
  classical
  obtain ⟨ē, hēord⟩ := uc22s2122np_exists_bar_order_seven hĒ hĒL
  have hēord' : orderOf (ē : Bar2 D.M) = 7 := by
    rw [Subgroup.orderOf_coe]
    exact hēord
  obtain ⟨e, heE, hebar, heord⟩ :=
    uc22s2122np_lift_order_seven hEM hEbar hEinfQ ē.2.1 hēord'
  refine ⟨(e : G), heE, heord, ?_⟩
  exact uc22s2122np_mem_sup_pCoreOf_of_mem_barImage (e := e) (by rw [hebar]; exact ē.2.2)

private theorem uc22s2122np_mem_uniqueSet_of_mem_sup_pCoreOf {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hU : ∀ A ≤ L, Nat.card A = 7 → A ∈ uniqueSet D.M)
    {e : G} (heLQ : e ∈ L ⊔ pCoreOf 2 D.M) (heord : orderOf e = 7) :
    zpowers e ∈ uniqueSet D.M := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hLM : L ≤ D.M := hL.1.le
  have hQM : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hLQM : L ⊔ pCoreOf 2 D.M ≤ D.M := sup_le hLM hQM
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 7 L
  have hSsup : IsSylowOf 7 S (L ⊔ pCoreOf 2 D.M) :=
    uc22s2122np_isSylowOf_sup_pCoreOf hLM hS
  let X : Subgroup G := zpowers e
  have hXcard : Nat.card X = 7 := by
    simp only [X, Nat.card_zpowers, heord]
  have hXp : IsPGroup 7 X := IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  have hXle : X ≤ L ⊔ pCoreOf 2 D.M := zpowers_le.mpr heLQ
  obtain ⟨k, hkLQ, hkX⟩ := UC6.exists_conj_le_of_isSylowOf hSsup hXle hXp
  let X' : Subgroup G := X.map (MulAut.conj k⁻¹).toMonoidHom
  have hX'le : X' ≤ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    simpa [MulAut.conj_apply] using hS.le (hkX x hx)
  have hX'card : Nat.card X' = 7 := by
    rw [show X' = X.map (MulAut.conj k⁻¹).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hXcard]
  have hX'U : X' ∈ uniqueSet D.M := hU X' hX'le hX'card
  have hkM : k⁻¹ ∈ D.M := D.M.inv_mem (hLQM hkLQ)
  exact (CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.mem_uniqueSet_map_iff
    hkM X).mp hX'U

private theorem uc22s2122np_not_dvd_card_pCore {D : Data G} :
    ¬ 7 ∣ Nat.card (pCoreOf 2 D.M) := by
  have hQp : IsPGroup 2 (pCoreOf 2 D.M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  rw [hk]
  intro h
  have h72 : 7 ∣ 2 := (by norm_num : Nat.Prime 7).dvd_of_dvd_pow h
  norm_num at h72

private theorem uc22s2122np_card_sylow_preimage {D : Data G} {Ē : Subgroup (Bar2 D.M)}
    {E : Subgroup G} (hĒ : Nat.card Ē = 49)
    (hEsyl : IsSylowOf 7 E (barPreimage D.M Ē)) : Nat.card E = 49 := by
  have hPcard : Nat.card (barPreimage D.M Ē) = Nat.card (pCoreOf 2 D.M) * 49 := by
    rw [uc22p22u_card_barPreimage, hĒ]
  have hfac : (Nat.card (barPreimage D.M Ē)).factorization 7 = 2 := by
    rw [hPcard, Nat.factorization_mul (Nat.card_pos.ne') (by norm_num : (49 : ℕ) ≠ 0),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd
        (uc22s2122np_not_dvd_card_pCore (D := D)), zero_add]
    have h49 : (49 : ℕ).factorization 7 = 2 := by
      rw [show (49 : ℕ) = 7 ^ 2 by norm_num, Nat.factorization_pow]
      simp [Nat.Prime.factorization_self (by norm_num : Nat.Prime 7)]
    rw [h49]
  rw [hEsyl.card_eq, hfac]
  norm_num

private theorem uc22s2122np_barImage_sylow_preimage {D : Data G} {Ē : Subgroup (Bar2 D.M)}
    {E : Subgroup G} (hĒ : Nat.card Ē = 49)
    (hEsyl : IsSylowOf 7 E (barPreimage D.M Ē)) (hEcard : Nat.card E = 49) :
    barImage D.M E = Ē ∧ E ⊓ pCoreOf 2 D.M = ⊥ := by
  have hQp : IsPGroup 2 (pCoreOf 2 D.M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hEP : E ≤ barPreimage D.M Ē := hEsyl.le
  have hEM : E ≤ D.M := hEP.trans (uc22p21c_barPreimage_le D.M Ē)
  have hEinfQ : E ⊓ pCoreOf 2 D.M = ⊥ :=
    CFSG.ABGLocalTools.inf_eq_bot_of_isPGroup_two (p := 7) (by norm_num)
      hEsyl.isPGroup hQp
  have hdisj : Disjoint (E.subgroupOf D.M) (uc22p21cPi D.M).ker := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hxE : (x : G) ∈ E := hx.1
    have hxQ : (x : G) ∈ pCoreOf 2 D.M :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := D.M) x).2
        ((QuotientGroup.eq_one_iff x).1 hx.2)
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hEinfQ]
      exact ⟨hxE, hxQ⟩
    exact Subgroup.mem_bot.1 hxbot
  have hcardImage : Nat.card (barImage D.M E) = Nat.card E := by
    rw [show barImage D.M E = (E.subgroupOf D.M).map (uc22p21cPi D.M) from rfl,
      UC6S846.card_map_of_disjoint_ker _ _ hdisj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  have hEbar : barImage D.M E = Ē := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
      exact (uc22p21c_mem_barPreimage.1 (hEP hm)).2
    · rw [hĒ, hcardImage, hEcard]
  exact ⟨hEbar, hEinfQ⟩

theorem uc22s2122np_exists_E_of_barE {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hU : ∀ A ≤ L, Nat.card A = 7 → A ∈ uniqueSet D.M) {Ē : Subgroup (Bar2 D.M)}
    (hĒ : Nat.card Ē = 49)
    (hĒT : ((Ē ⊔ barImage D.M D.T : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) =
      (Ē : Set (Bar2 D.M)) * (barImage D.M D.T : Set (Bar2 D.M)))
    {b : G} (hbM : b ∈ D.M) (hb7 : b ^ 7 = 1)
    (hbĒ : uc22p21cPi D.M ⟨b, hbM⟩ ∈ Ē)
    (hĒL : Ē ⊓ barImage D.M L ≠ ⊥) :
    ∃ E : Subgroup G, E ≤ D.M ∧ IsPGroup 7 E ∧ Nat.card E = 49 ∧
      ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G) ∧ b ∈ E ∧
      ∃ X ≤ E, Nat.card X = 7 ∧ X ∈ uniqueSet D.M := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hbP : b ∈ barPreimage D.M Ē := uc22p21c_mem_barPreimage.2 ⟨hbM, hbĒ⟩
  have hbzp : IsPGroup 7 (zpowers b) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hb7
  obtain ⟨E, hEsyl, hbzE⟩ :=
    UC6.exists_isSylowOf_ge (K := barPreimage D.M Ē) (zpowers_le.mpr hbP) hbzp
  have hEP : E ≤ barPreimage D.M Ē := hEsyl.le
  have hEM : E ≤ D.M := hEP.trans (uc22p21c_barPreimage_le D.M Ē)
  have hEcard : Nat.card E = 49 := uc22s2122np_card_sylow_preimage hĒ hEsyl
  obtain ⟨hEbar, hEinfQ⟩ := uc22s2122np_barImage_sylow_preimage hĒ hEsyl hEcard
  have hET : ((E ⊔ D.T : Subgroup G) : Set G) = (E : Set G) * (D.T : Set G) :=
    uc22s2122np_sup_T_mul hEM hEbar hĒT
  obtain ⟨e, heE, heord, heLQ⟩ :=
    uc22s2122np_exists_order_seven_of_barE hĒ hEM hEbar hEinfQ hĒL
  refine ⟨E, hEM, hEsyl.isPGroup, hEcard, hET, hbzE (Subgroup.mem_zpowers b), ?_⟩
  exact ⟨zpowers e, zpowers_le.mpr heE, by rw [Nat.card_zpowers, heord],
    uc22s2122np_mem_uniqueSet_of_mem_sup_pCoreOf hL hU heLQ heord⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
