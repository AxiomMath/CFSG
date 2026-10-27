module

public import CFSG.RankThree.PartTwo.Sec16.Item16Tail23
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.Classical.EvenSurvivingScalarRank

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU localRank)
open CFSG.Assembly (IsTwoLocal)
open scoped Pointwise

@[expose] noncomputable def Step1623EndS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsSimpleGroup ↥L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      Nonempty (↥L ≃* projSU 3 2 n) → omegaA A = {Subgroup.zpowers c} →
    (∀ a ∈ A, a ≠ 1 → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥) →
    (∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2),
      T = ⊥) →
    ∀ R : Subgroup G, Minimal (fun Q => Q ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ Q ≠ ⊥) R →
      IsKleinFour R → R = ⁅R, Subgroup.zpowers c⁆ →
      Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 9 →
      (∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
        R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) →
      ∃ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 ∧
        ∃ S : Subgroup G, S ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ∧
          S ≤ Subgroup.centralizer (R : Set G) ∧ IsPGroup 2 S ∧
          A ≤ Subgroup.normalizer (S : Set G) ∧
          ⁅S, A ⊓ Subgroup.centralizer (R : Set G)⁆ ≠ ⊥

@[expose] noncomputable def Step1623EndT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Ctx169 G A c L → IsSimpleGroup ↥L → ∀ n : ℕ, IsZ3LThreeTwo A c L n →
      Nonempty (↥L ≃* projSU 3 2 n) → omegaA A = {Subgroup.zpowers c} →
    (∀ a ∈ A, a ≠ 1 → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥) →
    (∀ T ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2),
      T = ⊥) →
    ∀ R : Subgroup G, Minimal (fun Q => Q ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ Q ≠ ⊥) R →
      IsKleinFour R → R = ⁅R, Subgroup.zpowers c⁆ →
      Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = 9 →
      (∀ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 →
        R ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G))) →
      ∃ b ∈ A ⊓ Subgroup.centralizer (R : Set G), b ≠ 1 ∧
        ∃ T : Subgroup G, T ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ∧
          IsKleinFour T ∧ T ≤ Subgroup.centralizer (R : Set G) ∧ T ⊓ R = ⊥ ∧
          A ≤ Subgroup.normalizer (T : Set G)

@[expose] def KS1623SzCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A W : Subgroup G) (c : G),
    IsKGroup ↥X → ¬ 3 ∣ Nat.card X → CFSG.Open.pCoreOf 2 X = ⊥ →
    CFSG.Assembly.IsElemAbelian 3 A → A ≤ Subgroup.normalizer (X : Set G) →
    W ≤ X → CFSG.Assembly.IsElemAbelian 2 W → Nat.card W = 16 →
    A ≤ Subgroup.normalizer (W : Set G) → c ∈ A →
    W ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ →
    (∀ t ∈ W, t ≠ 1 → ∀ r : ℕ, r.Prime → 3 < r →
      CFSG.Open.pRank r (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ≤ 2) →
    ¬ Odd (Nat.card (X ⊓ Subgroup.centralizer (A : Set G) : Subgroup G))

namespace Proof1623End

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_eq_mul {T R : Subgroup G} (hTR : T ≤ Subgroup.centralizer (R : Set G))
    (hbot : T ⊓ R = ⊥) : Nat.card (T ⊔ R : Subgroup G) = Nat.card T * Nat.card R := by
  have hcomm : ∀ (t : T) (r : R), Commute (T.subtype t) (R.subtype r) := fun t r =>
    (Subgroup.mem_centralizer_iff.mp (hTR t.2) r r.2).symm
  set φ : T × R →* G := MonoidHom.noncommCoprod T.subtype R.subtype hcomm with hφ
  have hrange : φ.range = T ⊔ R := by
    rw [hφ, MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨t, r⟩ hx
    have h1 : (t : G) * r = 1 := hx
    have htr : (t : G) = (r : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have htR : (t : G) ∈ T ⊓ R := ⟨t.2, by rw [htr]; exact R.inv_mem r.2⟩
    rw [hbot, Subgroup.mem_bot] at htR
    have hr1 : (r : G) = 1 := by
      rw [htR, one_mul] at h1
      exact h1
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext htR) (Subtype.ext hr1)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

omit [Finite G] in
theorem isElemAbelian_sup_of_kleinFour {T R : Subgroup G} [IsKleinFour T] [IsKleinFour R]
    (hTR : T ≤ Subgroup.centralizer (R : Set G)) :
    CFSG.Assembly.IsElemAbelian 2 (T ⊔ R) := by
  have hTc := (IsKleinFour.isMulCommutative (G := T))
  have hRc := (IsKleinFour.isMulCommutative (G := R))
  have hTRn : T ≤ Subgroup.normalizer (R : Set G) :=
    hTR.trans (Subgroup.centralizer_le_normalizer _)
  have hmem : ∀ x ∈ T ⊔ R, ∃ t ∈ T, ∃ r ∈ R, x = t * r := by
    intro x hx
    have hx' : x ∈ ((T : Set G) * (R : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T R hTRn]
      exact hx
    obtain ⟨t, ht, r, hr, rfl⟩ := hx'
    exact ⟨t, ht, r, hr, rfl⟩
  have hTT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hTc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRR : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hRc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hTRc : ∀ t ∈ T, ∀ r ∈ R, t * r = r * t := fun t ht r hr =>
    (Subgroup.mem_centralizer_iff.mp (hTR ht) r hr).symm
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨t, ht, r, hr, hxe⟩ := hmem x x.2
    obtain ⟨t', ht', r', hr', hye⟩ := hmem y y.2
    change (x : G) * y = y * x
    rw [hxe, hye]
    calc t * r * (t' * r') = (t * t') * (r * r') := by
          rw [mul_assoc, ← mul_assoc r, ← hTRc t' ht' r hr, mul_assoc, mul_assoc]
      _ = (t' * t) * (r' * r) := by rw [hTT t ht t' ht', hRR r hr r' hr']
      _ = t' * r' * (t * r) := by
          rw [mul_assoc, ← mul_assoc t, hTRc t ht r' hr', mul_assoc, mul_assoc]
  · obtain ⟨t, ht, r, hr, rfl⟩ := hmem x hx
    have ht2 : t * t = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨t, ht⟩ : T))
    have hr2 : r * r = 1 := congrArg Subtype.val (IsKleinFour.mul_self (⟨r, hr⟩ : R))
    calc (t * r) ^ 2 = t * (r * t) * r := by rw [pow_two]; group
      _ = t * t * (r * r) := by rw [← hTRc t ht r hr]; group
      _ = 1 := by rw [ht2, hr2, one_mul]

end Proof1623End

open Proof1623End

theorem step1623EndT_of (hS : Step1623EndS) : Step1623EndT := by
  intro G _ _ A c L h hLs n hz hU h1614 h1621 hno R hRmin hR4 hRc hB9 hRb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hbB, hb1, S, hSX, hSR, hS2, hAS, hSB⟩ :=
    hS G A c L h hLs n hz hU h1614 h1621 hno R hRmin hR4 hRc hB9 hRb
  set B := A ⊓ Subgroup.centralizer (R : Set G) with hBdef
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRmin.1.1.1.1.1.2.2
  have hCH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hx
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => h.commute hx hy
  obtain ⟨T, hTS, hTmin⟩ := Finite.exists_le_minimal
    (p := fun T : Subgroup G => A ≤ Subgroup.normalizer (T : Set G) ∧ ⁅T, B⁆ ≠ ⊥) ⟨hAS, hSB⟩
  obtain ⟨⟨hAT, hTB⟩, hmin⟩ := hTmin
  have hT2 : IsPGroup 2 T := hS2.to_le hTS
  have hT1 : T ≠ ⊥ := fun h0 => hTB (by rw [h0, Subgroup.commutator_bot_left])
  have hTc : T ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    hno _ ⟨inf_le_right.trans hCH, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hT2.to_le inf_le_left), Proof169.le_normalizer_inf hAT
        (h.A_le_centralizer.trans Subgroup.le_normalizer)⟩
  have hT3 : Nat.Coprime 3 (Nat.card T) := Proof169.coprime_three_of_isPGroup_two hT2
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 2
    Nat.prime_three A T ⟨h.isElemAbelian.1, h.isElemAbelian.2⟩ (by rw [h.card_eq]; norm_num)
    hAT hT3
  obtain ⟨F, ⟨hFA, hF9⟩, hFB⟩ : ∃ F ∈ CFSG.Open.signalizerFunctorEk 3 2 A,
      ¬ T ⊓ Subgroup.centralizer (F : Set G) ≤ Subgroup.centralizer (B : Set G) := by
    by_contra hall
    push Not at hall
    apply hTB
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← hgen]
    exact iSup_le fun D => iSup_le fun hD => hall D hD
  have hAF : A ≤ Subgroup.centralizer (F : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAcomm y (hFA hy) x hx
  have hFT : T ≤ Subgroup.centralizer (F : Set G) := by
    have h1 := hmin (y := T ⊓ Subgroup.centralizer (F : Set G))
      ⟨Proof169.le_normalizer_inf hAT (hAF.trans Subgroup.le_normalizer), fun h0 =>
        hFB (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0)⟩ inf_le_left
    exact h1.trans inf_le_right
  have hcF : c ∉ F := by
    intro hcF
    apply hT1
    have h1 : T ≤ T ⊓ Subgroup.centralizer ({c} : Set G) :=
      le_inf le_rfl (hFT.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcF)))
    rw [hTc] at h1
    exact le_bot_iff.mp h1
  have hFhyp : IsHyperplane A F := ⟨hFA, by rw [h.card_eq, hF9]; norm_num⟩
  have hAcF : A = Subgroup.zpowers c ⊔ F :=
    le_antisymm (Proof169.le_zpowers_sup_of_not_mem hFhyp h.mem_A hcF)
      (sup_le (Subgroup.zpowers_le.mpr h.mem_A) hFA)
  have hBF : ¬ B ≤ F := by
    intro hBF
    have hBeq : B = F := Subgroup.eq_of_le_of_card_ge hBF (by rw [hB9, hF9]; norm_num)
    apply hFB
    rw [hBeq]
    exact inf_le_right
  obtain ⟨β, hβB, hβF⟩ := IsConcreteLE.not_le_iff_exists.mp hBF
  obtain ⟨i, hi3, f, hf, hβ⟩ := exists_pow_mul_of_mem h.isElemAbelian h.mem_A hAcF hβB.1
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hβF
    rw [hβ, pow_zero, one_mul]
    exact hf
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hdich : ∀ W ≤ T, A ≤ Subgroup.normalizer (W : Set G) → W ≠ ⊥ → W = T := by
    intro W hWT hAW hW1
    refine le_antisymm hWT (hmin ⟨hAW, fun h0 => hW1 ?_⟩ hWT)
    have hWB : W ≤ Subgroup.centralizer (B : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    have hWc : W ≤ Subgroup.centralizer ({c} : Set G) := by
      intro w hw
      have h1 : Commute β w := (Subgroup.mem_centralizer_iff.mp (hWB hw) β hβB)
      have h2 : Commute f w := (Subgroup.mem_centralizer_iff.mp (hFT (hWT hw)) f hf)
      have h3 : Commute (c ^ i) w := by
        have : c ^ i = β * f⁻¹ := by rw [hβ, mul_inv_cancel_right]
        rw [this]
        exact h1.mul_left h2.inv_left
      have h4 : Commute c w := by
        interval_cases i
        · exact absurd rfl hi0
        · simpa using h3
        · have : c = (c ^ 2) ^ 2 := by
            rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul]
          rw [this]
          exact h3.pow_left 2
      exact Subgroup.mem_centralizer_singleton_iff.mpr h4.eq.symm
    have h1 := le_inf hWT hWc
    rw [hTc] at h1
    exact le_bot_iff.mp h1
  have hcT : c ∈ Subgroup.normalizer (T : Set G) := hAT h.mem_A
  have hZ : (Subgroup.center ↥T).map T.subtype = T := by
    refine hdich _ (Subgroup.map_subtype_le _)
      (hAT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)) ?_
    have : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hT1
    have hc := hT2.center_nontrivial
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective] at hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hc hbot
  have hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have hxZ : x ∈ (Subgroup.center ↥T).map T.subtype := by rw [hZ]; exact hx
    obtain ⟨x', hx'Z, rfl⟩ := hxZ
    have := Subgroup.mem_center_iff.mp hx'Z ⟨y, hy⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hk0 : k ≠ 0 := by
    intro h0
    apply hT1
    rw [← Subgroup.card_eq_one, hk, h0, pow_zero]
  obtain ⟨⟨t, htT⟩, ht2⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have ht2' : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one (⟨t, htT⟩ : ↥T)
    rw [ht2] at this
    simpa using congrArg Subtype.val this
  have ht1 : t ≠ 1 := by
    intro h1
    have : orderOf (⟨t, htT⟩ : ↥T) = 1 := by
      rw [orderOf_eq_one_iff]
      exact Subtype.ext h1
    omega
  set s := c * t * c⁻¹ with hs
  have hsT : s ∈ T := (Subgroup.mem_normalizer_iff.mp hcT t).mp htT
  set u := c * s * c⁻¹ with hu
  have huT : u ∈ T := (Subgroup.mem_normalizer_iff.mp hcT s).mp hsT
  have hc3' : c * c * c = 1 := by rw [← pow_three', hc3]
  have hcut : c * u * c⁻¹ = t := by
    rw [hu, hs]
    calc c * (c * (c * t * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * t * (c * c * c)⁻¹ := by group
      _ = t := by rw [hc3']; group
  have htsu : t * s * u = 1 := by
    have hmem : t * s * u ∈ T ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine ⟨mul_mem (mul_mem htT hsT) huT, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 : c * (t * s * u) * c⁻¹ = s * u * t := by
        calc c * (t * s * u) * c⁻¹ = (c * t * c⁻¹) * (c * s * c⁻¹) * (c * u * c⁻¹) := by group
          _ = s * u * t := by rw [← hs, ← hu, hcut]
      have h2 : s * u * t = t * s * u := by
        rw [mul_assoc t, ← hTab (s * u) (mul_mem hsT huT) t htT]
      calc t * s * u * c = c * (c⁻¹ * (t * s * u) * c) := by group
        _ = c * (t * s * u) := by
          congr 1
          have h3 : c⁻¹ * (c * (t * s * u) * c⁻¹) * c = t * s * u := by group
          rw [h1, h2] at h3
          exact h3
    rw [hTc] at hmem
    exact Subgroup.mem_bot.mp hmem
  have htt : t * t = 1 := by rw [← pow_two, ht2']
  have hss : s * s = 1 := by
    rw [hs]
    calc c * t * c⁻¹ * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hutt : u = t * s := by
    calc u = (t * s)⁻¹ * (t * s * u) := by group
      _ = s⁻¹ * t⁻¹ := by rw [htsu, mul_one, mul_inv_rev]
      _ = s * t := by rw [inv_eq_of_mul_eq_one_right hss, inv_eq_of_mul_eq_one_right htt]
      _ = t * s := (hTab t htT s hsT).symm
  have hs1 : s ≠ 1 := by
    intro h1
    apply ht1
    calc t = c⁻¹ * s * c := by rw [hs]; group
      _ = 1 := by rw [h1]; group
  have hts : t ≠ s := by
    intro h1
    have hmem : t ∈ T ⊓ Subgroup.centralizer ({c} : Set G) := by
      refine ⟨htT, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc t * c = c * (c⁻¹ * t * c) := by group
        _ = c * t := by
          congr 1
          calc c⁻¹ * t * c = c⁻¹ * s * c := by rw [← h1]
            _ = t := by rw [hs]; group
    rw [hTc] at hmem
    exact ht1 (Subgroup.mem_bot.mp hmem)
  set W₀ := Subgroup.closure ({t, s} : Set G) with hW₀
  have hW₀T : W₀ ≤ T := by
    rw [hW₀, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact htT
    · exact hsT
  have hW₀4 : IsKleinFour W₀ :=
    Proof1623.isKleinFour_closure_pair htt hss ht1 hs1 hts (hTab t htT s hsT)
  have hcW : c ∈ Subgroup.normalizer (W₀ : Set G) := by
    have hle : W₀.map (MulAut.conj c).toMonoidHom ≤ W₀ := by
      rw [hW₀, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g, hg, rfl⟩
      rcases hg with rfl | rfl
      · exact Subgroup.subset_closure (by simp [hs])
      · change c * s * c⁻¹ ∈ _
        rw [← hu, hutt]
        exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    exact Subgroup.mem_normalizer_fintype fun w hw => hle ⟨w, hw, rfl⟩
  have hFW : F ≤ Subgroup.normalizer (W₀ : Set G) :=
    (Subgroup.le_centralizer_iff.mp (hW₀T.trans hFT)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hAW : A ≤ Subgroup.normalizer (W₀ : Set G) := by
    rw [hAcF]
    exact sup_le (Subgroup.zpowers_le.mpr hcW) hFW
  have hW₀1 : W₀ ≠ ⊥ := by
    intro hbot
    have htW : t ∈ W₀ := Subgroup.subset_closure (by simp)
    rw [hbot] at htW
    exact ht1 (Subgroup.mem_bot.mp htW)
  have hW₀eq := hdich W₀ hW₀T hAW hW₀1
  have hTR1 : T ⊓ R = ⊥ := by
    by_contra hne
    have h1 := hdich (T ⊓ R) inf_le_left (Proof169.le_normalizer_inf hAT hAR) hne
    apply hTB
    have hTR' : T ≤ R := h1 ▸ inf_le_right
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 x (hTR' hx)).symm
  refine ⟨b, hbB, hb1, T, hTS.trans hSX, ?_, hTS.trans hSR, hTR1, hAT⟩
  rw [← hW₀eq]
  exact hW₀4

theorem step1623End_of (hT : Step1623EndT) (hSz : KS1623SzCent) : Step1623End := by
  intro G _ _ A c L h hLs n hz hU h1614 h1621 hno R hRmin hR4 hRc hB9 hRb
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hbB, hb1, T, hTX, hT4, hTR, hTRbot, hAT⟩ :=
    hT G A c L h hLs n hz hU h1614 h1621 hno R hRmin hR4 hRc hB9 hRb
  have hbA : b ∈ A := hbB.1
  set X := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) with hXdef
  have hRX : R ≤ X := hRb b hbB hb1
  have hAR : A ≤ Subgroup.normalizer (R : Set G) := hRmin.1.1.1.1.1.2.2
  set W := T ⊔ R with hWdef
  have hWel : CFSG.Assembly.IsElemAbelian 2 W := isElemAbelian_sup_of_kleinFour hTR
  have hW16 : Nat.card W = 16 := by
    rw [hWdef, card_sup_eq_mul hTR hTRbot, IsKleinFour.card_four, IsKleinFour.card_four]
  have hWX : W ≤ X := sup_le hTX hRX
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, hWdef, Subgroup.map_sup,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAT ha),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAR ha)]
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 4) (by rw [hW16]; norm_num)
  have hCH : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hx
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := h.A_le_centralizer
  have hWc : W ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    hno _ ⟨inf_le_right.trans hCH, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hW2.to_le inf_le_left), Proof169.le_normalizer_inf hAW
        (hAC.trans Subgroup.le_normalizer)⟩
  have hCb : Subgroup.centralizer ({b} : Set G) ≠ ⊤ :=
    Sec6.centralizer_ne_top_of_ne_one h.toTheoremFourHyp hb1
  have hXtop : X ≠ ⊤ := fun hX => hCb (top_le_iff.mp (hX ▸ pPrimeCoreOf_le 3 _))
  have hXK : IsKGroup ↥X := (h.toTheoremFourHyp.sectionFourHyp hXtop).kGroup
  have hX3 : ¬ 3 ∣ Nat.card X := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hCbX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_pPrimeCoreOf 3 _
  have hX2 : CFSG.Open.pCoreOf 2 X = ⊥ := by
    have hle : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({b} : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans (pPrimeCoreOf_le 3 _))
        (hCbX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X)
    rw [h1621 b hbA hb1] at hle
    exact le_bot_iff.mp hle
  have hACb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.commute hx hbA)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hACb.trans hCbX
  have hrank : ∀ t ∈ W, t ≠ 1 → ∀ r : ℕ, r.Prime → 3 < r →
      CFSG.Open.pRank r (X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) ≤ 2 := by
    intro t ht ht1 r hr hr3
    have ht2 : IsPGroup 2 (Subgroup.zpowers t) := hW2.to_le (Subgroup.zpowers_le.mpr ht)
    have ht0 : Subgroup.zpowers t ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact ht1
    have hloc : IsTwoLocal (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :=
      ⟨_, ht0, ht2, rfl⟩
    have hle : X ⊓ Subgroup.centralizer ({t} : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := fun x hx =>
      Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer hx.2
    have h1 := (CFSG.SectionRank.pRank_mono hr.one_lt hle).trans
      (CFSG.RankThree.Classical.pRank_le_localRank hr.one_lt hloc)
    have h2 := h.toTheoremFourHyp.localRank_lt r hr hr3
    omega
  have hev := hSz G X A W c hXK hX3 hX2 h.isElemAbelian hAX hWX hWel hW16 hAW h.mem_A hWc hrank
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
  obtain ⟨⟨x, hx⟩, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ Subgroup.centralizer
    (A : Set G) : Subgroup G)) 2 hev
  have hxord : orderOf x = 2 := by rwa [Subgroup.orderOf_mk] at hx2
  have hxA : ∀ a ∈ A, a * x * a⁻¹ = x := fun a ha => by
    rw [Subgroup.mem_centralizer_iff.mp hx.2 a ha, mul_inv_cancel_right]
  have hZ : Subgroup.zpowers x ∈
      invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) := by
    refine ⟨Subgroup.zpowers_le.mpr (hCH (Subgroup.mem_centralizer_singleton_iff.mpr ?_)),
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])), ?_⟩
    · exact (Subgroup.mem_centralizer_iff.mp hx.2 c h.mem_A).symm
    · intro a ha
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [SetLike.mem_coe, ← conj_zpow, hxA a ha]
      exact Subgroup.zpow_mem_zpowers x k
  have h0 := hno _ hZ
  rw [Subgroup.zpowers_eq_bot] at h0
  rw [h0, orderOf_one] at hxord
  omega

theorem step1623End_of_S (hS : Step1623EndS) (hSz : KS1623SzCent) : Step1623End :=
  step1623End_of (step1623EndT_of hS) hSz

end CFSG.RankThree.PartTwo.Sec16
