module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB83Q3Q
public import CFSG.Quasithin.Recognition.Stroth.BenderSylow
public import CFSG.Quasithin.Recognition.Stroth.Str83KernelParts

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R

variable {G : Type} [Group G] [Finite G]

open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

theorem str86_cartan_supplement {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (hL2 : VL2 L2)
    {P : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S) :
    P ⊔ Q2 L1 L2 S = S := by
  classical
  let Q : Subgroup G := Q2 L1 L2 S
  change P ⊔ Q = S
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨n, hL2n⟩ := hL2
  have hn : 2 ≤ n :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2n
  have hE2 : S = (S ⊓ L2) ⊔ Q :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2n⟩))
  have hQleS : Q ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
      (CFSG.Quasithin.F112W.isSylowTwoOf_parabolic' hR)
  have hRleS : P ⊔ Q ≤ S := sup_le hPS hQleS
  obtain ⟨D2, hD2cart, hD2inf, hD2sup⟩ := F1.exists_cartan hF.1.h2.sylow
  have hD2leB2 : D2 ≤ borelOf L2 S := hD2cart.1
  have hD2odd : Odd (Nat.card ↥D2) := hD2cart.2.1
  have hD2leL2 : D2 ≤ L2 := hD2leB2.trans (F1.borelOf_le L2 S)
  have hD2infO : D2 ⊓ pCoreOf 2 L2 = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxD, hxO⟩ := Subgroup.mem_inf.mp hx
    have hxS : x ∈ S :=
      (Subgroup.mem_inf.mp
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow hxO)).1
    have hxL2 : x ∈ L2 := hD2leL2 hxD
    have hxS2 : x ∈ S ⊓ L2 := Subgroup.mem_inf.mpr ⟨hxS, hxL2⟩
    have hxbot : x ∈ D2 ⊓ (S ⊓ L2) := Subgroup.mem_inf.mpr ⟨hxD, hxS2⟩
    rw [hD2inf] at hxbot
    exact Subgroup.mem_bot.mp hxbot
  let K : Type := oTwoQuot ↥L2
  let π : ↥L2 →* K := QuotientGroup.mk' (pCore 2 ↥L2)
  let S2 : Subgroup G := S ⊓ L2
  let Qimg : Subgroup K := (S2.subgroupOf L2).map π
  let Dbar : Subgroup K := (D2.subgroupOf L2).map π
  have hmapB := F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  obtain ⟨hQimg2, hQimgodd, hMmap⟩ := hmapB
  let Qsyl : Sylow 2 K := hQimg2.toSylow hQimgodd
  have hQcoe : (Qsyl : Subgroup K) = Qimg := IsPGroup.toSylow_coe hQimg2 hQimgodd
  obtain ⟨e2⟩ := hL2n
  have hBT2 : BenderType K n 1 1 := BenderType.linear n hn e2
  have hBoreleq : ((borelOf L2 S).subgroupOf L2).map π = borel (Qsyl : Subgroup K) := by
    rw [CFSG.GH74.Uniqueness.Bender.borel, hQcoe, hMmap]
  have hDbarLe : Dbar ≤ borel (Qsyl : Subgroup K) := by
    rw [← hBoreleq]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L2 hD2leB2)
  have hSupD : (Qsyl : Subgroup K) ⊔ Dbar = borel (Qsyl : Subgroup K) := by
    have h1 : ((S2 ⊔ D2).subgroupOf L2).map π = borel (Qsyl : Subgroup K) := by
      rw [hD2sup]
      exact hBoreleq
    have hsub : (S2 ⊔ D2).subgroupOf L2 = S2.subgroupOf L2 ⊔ D2.subgroupOf L2 :=
      CFSG.ComponentClassification.GSThmB.subgroupOf_sup_of_le
        (inf_le_right : S2 ≤ L2) hD2leL2
    have h2 : ((S2.subgroupOf L2) ⊔ (D2.subgroupOf L2)).map π =
        ((S2 ⊔ D2).subgroupOf L2).map π := by
      rw [hsub]
    rw [hQcoe]
    change Qimg ⊔ Dbar = borel (Qsyl : Subgroup K)
    rw [show Qimg ⊔ Dbar = ((S2.subgroupOf L2) ⊔ (D2.subgroupOf L2)).map π from
      (Subgroup.map_sup _ _ _).symm]
    rw [h2]
    exact h1
  have hDbarOdd : Odd (Nat.card ↥Dbar) := by
    let fD : ↥(D2.subgroupOf L2) →* K :=
      π.comp (D2.subgroupOf L2).subtype
    have hinj : Function.Injective fD := by
      intro a b hab
      have h1 : π (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2)) = 1 := by
        have hcoe : ((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) =
            (a : ↥L2)⁻¹ * (b : ↥L2) := by simp
        rw [hcoe, map_mul, map_inv]
        have hab' : π ((a : ↥L2)) = π ((b : ↥L2)) := hab
        rw [hab']
        simp
      have h2 : ((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h1
      have h3 : ((((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2)) : G) ∈ pCoreOf 2 L2 :=
        (F1.mem_pCore_iff_coe _).mp h2
      have h4 : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) ∈ D2 :=
        Subgroup.mem_subgroupOf.mp (a⁻¹ * b).2
      have h5 : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) = 1 := by
        have hx : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) ∈ D2 ⊓ pCoreOf 2 L2 :=
          Subgroup.mem_inf.mpr ⟨h4, h3⟩
        rw [hD2infO] at hx
        exact Subgroup.mem_bot.mp hx
      have h6 : a⁻¹ * b = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact h5
      exact inv_mul_eq_one.mp h6
    have hcard : Nat.card ↥Dbar = Nat.card ↥D2 := by
      have hDbar_eq : Dbar = (⊤ : Subgroup ↥(D2.subgroupOf L2)).map fD := by
        change (D2.subgroupOf L2).map π = Subgroup.map fD ⊤
        rw [← MonoidHom.range_eq_map]
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨(x : ↥L2), x.2, rfl⟩
      rw [hDbar_eq, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD2leL2).toEquiv]
    rw [hcard]
    exact hD2odd
  obtain ⟨t, ht2, htnot, hcartan⟩ :=
    exists_involution_cartan_eq hBT2 Qsyl hDbarLe hDbarOdd hSupD
  obtain ⟨t0, hc0⟩ := hBT2.exists_benderCore Qsyl
  have hc : BenderCore (2 ^ n) 1 1 (Qsyl : Subgroup K) t :=
    hc0.of_involution ht2 htnot
  have hroot : rootCenter (Qsyl : Subgroup K) = (Qsyl : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
    rw [hc0.card_center, hc0.card_eq, pow_one]
  have hTrans : ∀ x ∈ (Qsyl : Subgroup K), x ≠ 1 → ∀ y ∈ (Qsyl : Subgroup K), y ≠ 1 →
      ∃ d ∈ Dbar, d⁻¹ * x * d = y := by
    intro x hx hx1 y hy hy1
    have hxZ : x ∈ rootCenter (Qsyl : Subgroup K) := by rw [hroot]; exact hx
    have hyZ : y ∈ rootCenter (Qsyl : Subgroup K) := by rw [hroot]; exact hy
    obtain ⟨d, hd, hdy⟩ := hc.exists_cartan_conj hxZ hx1 hyZ hy1
    exact ⟨d, by rwa [hcartan] at hd, hdy.symm⟩
  have hD2leB : D2 ≤ bigB L1 L2 S := hD2leB2.trans (le_sup_right.trans le_sup_left)
  have hD2N : D2 ≤ Subgroup.normalizer (Q : Set G) :=
    (hD2leL2.trans le_sup_left).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hSN_Q : S ≤ Subgroup.normalizer (Q : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hcoset : ∀ r s : G, r ∈ P ⊔ Q → r ∉ Q → s ∈ S → s ∉ Q →
      ∃ d ∈ D2, ∃ q ∈ Q, d⁻¹ * r * d = q * s := by
    intro r s hrR hrQ2 hsS hsQ2
    have hrE : r ∈ (S ⊓ L2) ⊔ Q := by rw [← hE2]; exact hRleS hrR
    have hsE : s ∈ (S ⊓ L2) ⊔ Q := by rw [← hE2]; exact hsS
    have hQleP2 : Q ≤ P2 L1 L2 S := CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)
    have hQleB : Q ≤ bigB L1 L2 S := hQleS.trans le_sup_right
    have hQN_S : Q ≤ Subgroup.normalizer (S : Set G) := hQleB.trans hSB
    have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
      sup_le Subgroup.le_normalizer (by
        simpa [bigB_comm] using bigB_le_normalizer_of_hyp111 hF.1.symm)
    have hQN_L2 : Q ≤ Subgroup.normalizer (L2 : Set G) := hQleP2.trans hP2N
    have hQN_S2 : Q ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
      intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        (Subgroup.mem_inf.mpr ⟨hQN_S hx, hQN_L2 hx⟩)
    obtain ⟨r2, hr2S2, qr, hqrQ, hr_eq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQN_S2).mp hrE
    obtain ⟨s2, hs2S2, qs, hqsQ, hs_eq⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes hQN_S2).mp hsE
    have hr2L : r2 ∈ L2 := (Subgroup.mem_inf.mp hr2S2).2
    have hs2L : s2 ∈ L2 := (Subgroup.mem_inf.mp hs2S2).2
    let xbar : K := π ⟨r2, hr2L⟩
    let ybar : K := π ⟨s2, hs2L⟩
    have hxbarQ : xbar ∈ (Qsyl : Subgroup K) := by
      rw [hQcoe]
      exact Subgroup.mem_map.mpr ⟨⟨r2, hr2L⟩, Subgroup.mem_subgroupOf.mpr hr2S2, rfl⟩
    have hybarQ : ybar ∈ (Qsyl : Subgroup K) := by
      rw [hQcoe]
      exact Subgroup.mem_map.mpr ⟨⟨s2, hs2L⟩, Subgroup.mem_subgroupOf.mpr hs2S2, rfl⟩
    have hxbar1 : xbar ≠ 1 := by
      intro h
      apply hrQ2
      have hmem : (⟨r2, hr2L⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h
      have hr2O : r2 ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
      have hr2Q : r2 ∈ Q := by
        simpa [Q, P2, bigB_comm] using
          (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hr2O
      rw [hr_eq]
      exact Q.mul_mem hr2Q hqrQ
    have hybar1 : ybar ≠ 1 := by
      intro h
      apply hsQ2
      have hmem : (⟨s2, hs2L⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h
      have hs2O : s2 ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
      have hs2Q : s2 ∈ Q := by
        simpa [Q, P2, bigB_comm] using
          (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hs2O
      rw [hs_eq]
      exact Q.mul_mem hs2Q hqsQ
    obtain ⟨dbar, hdDbar, hdbarconj⟩ := hTrans xbar hxbarQ hxbar1 ybar hybarQ hybar1
    obtain ⟨d2, hd2mem, hd2eq⟩ := Subgroup.mem_map.mp hdDbar
    let d : G := ((d2 : ↥L2) : G)
    have hdD2 : d ∈ D2 := Subgroup.mem_subgroupOf.mp hd2mem
    have hdL2 : d ∈ L2 := (d2 : ↥L2).2
    have hdπ : π (d2 : ↥L2) = dbar := hd2eq
    have hqQ : d⁻¹ * qr * d ∈ Q := by
      have hdN : d⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem (hD2N hdD2)
      have h := (Subgroup.mem_normalizer_iff.mp hdN qr).mp hqrQ
      simpa using h
    have hA : d⁻¹ * r2 * d * s2⁻¹ ∈ Q := by
      have hdL : d⁻¹ * r2 * d ∈ L2 :=
        L2.mul_mem (L2.mul_mem (L2.inv_mem hdL2) hr2L) hdL2
      have hAL : d⁻¹ * r2 * d * s2⁻¹ ∈ L2 :=
        L2.mul_mem hdL (L2.inv_mem hs2L)
      have himg : π ⟨d⁻¹ * r2 * d * s2⁻¹, hAL⟩ = 1 := by
        have h1 : π ⟨d⁻¹ * r2 * d, hdL⟩ = ybar := by
          have hdπ' : π (d2 : ↥L2) = dbar := hdπ
          have hx : π ⟨r2, hr2L⟩ = xbar := rfl
          have hy : π ⟨s2, hs2L⟩ = ybar := rfl
          have hcoe : (⟨d⁻¹ * r2 * d, hdL⟩ : ↥L2) =
              (d2 : ↥L2)⁻¹ * ⟨r2, hr2L⟩ * (d2 : ↥L2) := by
            apply Subtype.ext
            simp [d]
          rw [hcoe, map_mul, map_mul, map_inv, hdπ', hx]
          exact hdbarconj
        have hcoe2 : (⟨d⁻¹ * r2 * d * s2⁻¹, hAL⟩ : ↥L2) =
            ⟨d⁻¹ * r2 * d, hdL⟩ * ⟨s2, hs2L⟩⁻¹ := by
          apply Subtype.ext
          simp
        rw [hcoe2, map_mul, map_inv, h1]
        rw [show π ⟨s2, hs2L⟩ = ybar from rfl]
        simp
      have hmem : (⟨d⁻¹ * r2 * d * s2⁻¹, hAL⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr himg
      have hO : d⁻¹ * r2 * d * s2⁻¹ ∈ pCoreOf 2 L2 :=
        (F1.mem_pCore_iff_coe _).mp hmem
      simpa [Q, P2, bigB_comm] using
        (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hO
    have hq' : s2 * ((d⁻¹ * qr * d) * qs⁻¹) * s2⁻¹ ∈ Q := by
      have hX : (d⁻¹ * qr * d) * qs⁻¹ ∈ Q := Q.mul_mem hqQ (Q.inv_mem hqsQ)
      have hs2S : s2 ∈ S := hs2S2.1
      have hs2N : s2 ∈ Subgroup.normalizer (Q : Set G) := hSN_Q hs2S
      exact (Subgroup.mem_normalizer_iff.mp hs2N _).mp hX
    have hprod : d⁻¹ * r * d * s⁻¹ ∈ Q := by
      have hgroup : d⁻¹ * r * d * s⁻¹ =
          (d⁻¹ * r2 * d * s2⁻¹) * (s2 * ((d⁻¹ * qr * d) * qs⁻¹) * s2⁻¹) := by
        rw [hr_eq, hs_eq]
        group
      rw [hgroup]
      exact Q.mul_mem hA hq'
    refine ⟨d, hdD2, d⁻¹ * r * d * s⁻¹, hprod, ?_⟩
    group
  obtain ⟨r, hrP, hrQ⟩ : ∃ r : G, r ∈ P ∧ r ∉ Q := by
    by_contra h
    push Not at h
    exact hPQ h
  have hrR : r ∈ P ⊔ Q := Subgroup.mem_sup_left hrP
  have hS_le_R : S ≤ P ⊔ Q := by
    intro s hsS
    by_cases hsQ : s ∈ Q
    · exact (le_sup_right : Q ≤ P ⊔ Q) hsQ
    · obtain ⟨d, hdD2, q, hqQ, hdq⟩ := hcoset r s hrR hrQ hsS hsQ
      have hdR : d⁻¹ * r * d ∈ P ⊔ Q := by
        have hdN : d⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
          (Subgroup.normalizer (P : Set G)).inv_mem (hPB (hD2leB hdD2))
        have hdP : d⁻¹ * r * d ∈ P := by
          simpa using (Subgroup.mem_normalizer_iff.mp hdN r).mp hrP
        exact Subgroup.mem_sup_left hdP
      have hs_eq : s = q⁻¹ * (d⁻¹ * r * d) := by rw [hdq]; group
      rw [hs_eq]
      exact (P ⊔ Q).mul_mem ((le_sup_right : Q ≤ P ⊔ Q) (Q.inv_mem hqQ)) hdR
  exact le_antisymm hRleS hS_le_R

theorem str86_cartan_transitive {L1 L2 S : Subgroup G}
    (hF : F112HypW L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hB2 : VBig L2) (hL2 : VL2 L2)
    {P : Subgroup G} (hPS : P ≤ S)
    (hPB : bigB L1 L2 S ≤ Subgroup.normalizer (P : Set G))
    (hPQ : ¬ P ≤ Q2 L1 L2 S)
    {D2 : Subgroup G} (hD2cart : IsCartanOf D2 (borelOf L2 S))
    (hD2inf : D2 ⊓ (S ⊓ L2) = ⊥)
    (hD2sup : (S ⊓ L2) ⊔ D2 = borelOf L2 S) :
    ∀ x ∈ P, x ∉ Q2 L1 L2 S → ∀ y ∈ P, y ∉ Q2 L1 L2 S →
      ∃ d ∈ D2, d⁻¹ * x * d * y⁻¹ ∈ Q2 L1 L2 S := by
  classical
  let Q : Subgroup G := Q2 L1 L2 S
  change ∀ x ∈ P, x ∉ Q → ∀ y ∈ P, y ∉ Q → ∃ d ∈ D2, d⁻¹ * x * d * y⁻¹ ∈ Q
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨n, hL2n⟩ := hL2
  have hn : 2 ≤ n :=
    CFSG.Quasithin.F112R.two_le_of_isL2Quot_of_vBig hF.1.h2.listed hB2 hL2n
  have hE2 : S = (S ⊓ L2) ⊔ Q :=
    eq_sup_pCoreOf_of_bender_right hF.1 hSB (Or.inr (Or.inr ⟨n, hn, hL2n⟩))
  have hQleS : Q ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le
      (CFSG.Quasithin.F112W.isSylowTwoOf_parabolic' hR)
  have hD2leB2 : D2 ≤ borelOf L2 S := hD2cart.1
  have hD2odd : Odd (Nat.card ↥D2) := hD2cart.2.1
  have hD2leL2 : D2 ≤ L2 := hD2leB2.trans (F1.borelOf_le L2 S)
  have hD2infO : D2 ⊓ pCoreOf 2 L2 = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro z hz
    obtain ⟨hzD, hzO⟩ := Subgroup.mem_inf.mp hz
    have hzS : z ∈ S :=
      (Subgroup.mem_inf.mp
        (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hF.1.h2.sylow hzO)).1
    have hzL2 : z ∈ L2 := hD2leL2 hzD
    have hzS2 : z ∈ S ⊓ L2 := Subgroup.mem_inf.mpr ⟨hzS, hzL2⟩
    have hzbot : z ∈ D2 ⊓ (S ⊓ L2) := Subgroup.mem_inf.mpr ⟨hzD, hzS2⟩
    rw [hD2inf] at hzbot
    exact Subgroup.mem_bot.mp hzbot
  let K : Type := oTwoQuot ↥L2
  let π : ↥L2 →* K := QuotientGroup.mk' (pCore 2 ↥L2)
  let S2 : Subgroup G := S ⊓ L2
  let Qimg : Subgroup K := (S2.subgroupOf L2).map π
  let Dbar : Subgroup K := (D2.subgroupOf L2).map π
  have hmapB := F1.map_borelOf_eq_normalizer hF.1.h2.sylow
  obtain ⟨hQimg2, hQimgodd, hMmap⟩ := hmapB
  let Qsyl : Sylow 2 K := hQimg2.toSylow hQimgodd
  have hQcoe : (Qsyl : Subgroup K) = Qimg := IsPGroup.toSylow_coe hQimg2 hQimgodd
  obtain ⟨e2⟩ := hL2n
  have hBT2 : BenderType K n 1 1 := BenderType.linear n hn e2
  have hBoreleq : ((borelOf L2 S).subgroupOf L2).map π = borel (Qsyl : Subgroup K) := by
    rw [CFSG.GH74.Uniqueness.Bender.borel, hQcoe, hMmap]
  have hDbarLe : Dbar ≤ borel (Qsyl : Subgroup K) := by
    rw [← hBoreleq]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L2 hD2leB2)
  have hSupD : (Qsyl : Subgroup K) ⊔ Dbar = borel (Qsyl : Subgroup K) := by
    have h1 : ((S2 ⊔ D2).subgroupOf L2).map π = borel (Qsyl : Subgroup K) := by
      rw [hD2sup]
      exact hBoreleq
    have hsub : (S2 ⊔ D2).subgroupOf L2 = S2.subgroupOf L2 ⊔ D2.subgroupOf L2 :=
      CFSG.ComponentClassification.GSThmB.subgroupOf_sup_of_le
        (inf_le_right : S2 ≤ L2) hD2leL2
    have h2 : ((S2.subgroupOf L2) ⊔ (D2.subgroupOf L2)).map π =
        ((S2 ⊔ D2).subgroupOf L2).map π := by
      rw [hsub]
    rw [hQcoe]
    change Qimg ⊔ Dbar = borel (Qsyl : Subgroup K)
    rw [show Qimg ⊔ Dbar = ((S2.subgroupOf L2) ⊔ (D2.subgroupOf L2)).map π from
      (Subgroup.map_sup _ _ _).symm]
    rw [h2]
    exact h1
  have hDbarOdd : Odd (Nat.card ↥Dbar) := by
    let fD : ↥(D2.subgroupOf L2) →* K :=
      π.comp (D2.subgroupOf L2).subtype
    have hinj : Function.Injective fD := by
      intro a b hab
      have h1 : π (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2)) = 1 := by
        have hcoe : ((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) =
            (a : ↥L2)⁻¹ * (b : ↥L2) := by simp
        rw [hcoe, map_mul, map_inv]
        have hab' : π ((a : ↥L2)) = π ((b : ↥L2)) := hab
        rw [hab']
        simp
      have h2 : ((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) ∈ pCore 2 ↥L2 := by
        rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
        exact MonoidHom.mem_ker.mpr h1
      have h3 : ((((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2)) : G) ∈ pCoreOf 2 L2 :=
        (F1.mem_pCore_iff_coe _).mp h2
      have h4 : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) ∈ D2 :=
        Subgroup.mem_subgroupOf.mp (a⁻¹ * b).2
      have h5 : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) = 1 := by
        have hz : (((a⁻¹ * b : ↥(D2.subgroupOf L2)) : ↥L2) : G) ∈ D2 ⊓ pCoreOf 2 L2 :=
          Subgroup.mem_inf.mpr ⟨h4, h3⟩
        rw [hD2infO] at hz
        exact Subgroup.mem_bot.mp hz
      have h6 : a⁻¹ * b = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact h5
      exact inv_mul_eq_one.mp h6
    have hcard : Nat.card ↥Dbar = Nat.card ↥D2 := by
      have hDbar_eq : Dbar = (⊤ : Subgroup ↥(D2.subgroupOf L2)).map fD := by
        change (D2.subgroupOf L2).map π = Subgroup.map fD ⊤
        rw [← MonoidHom.range_eq_map]
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact ⟨⟨y, hy⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨(x : ↥L2), x.2, rfl⟩
      rw [hDbar_eq, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD2leL2).toEquiv]
    rw [hcard]
    exact hD2odd
  obtain ⟨t, ht2, htnot, hcartan⟩ :=
    exists_involution_cartan_eq hBT2 Qsyl hDbarLe hDbarOdd hSupD
  obtain ⟨t0, hc0⟩ := hBT2.exists_benderCore Qsyl
  have hc : BenderCore (2 ^ n) 1 1 (Qsyl : Subgroup K) t :=
    hc0.of_involution ht2 htnot
  have hroot : rootCenter (Qsyl : Subgroup K) = (Qsyl : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
    rw [hc0.card_center, hc0.card_eq, pow_one]
  have hTrans : ∀ a ∈ (Qsyl : Subgroup K), a ≠ 1 → ∀ b ∈ (Qsyl : Subgroup K), b ≠ 1 →
      ∃ d ∈ Dbar, d⁻¹ * a * d = b := by
    intro a ha ha1 b hb hb1
    have haZ : a ∈ rootCenter (Qsyl : Subgroup K) := by rw [hroot]; exact ha
    have hbZ : b ∈ rootCenter (Qsyl : Subgroup K) := by rw [hroot]; exact hb
    obtain ⟨d, hd, hdb⟩ := hc.exists_cartan_conj haZ ha1 hbZ hb1
    exact ⟨d, by rwa [hcartan] at hd, hdb.symm⟩
  have hD2N : D2 ≤ Subgroup.normalizer (Q : Set G) :=
    (hD2leL2.trans le_sup_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  have hSN_Q : S ≤ Subgroup.normalizer (Q : Set G) :=
    ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (P2 L1 L2 S))
  intro x hxP hxQ y hyP hyQ
  have hxS : x ∈ S := hPS hxP
  have hyS : y ∈ S := hPS hyP
  have hxE : x ∈ (S ⊓ L2) ⊔ Q := by rw [← hE2]; exact hxS
  have hyE : y ∈ (S ⊓ L2) ⊔ Q := by rw [← hE2]; exact hyS
  have hQleP2 : Q ≤ P2 L1 L2 S := CFSG.LieType.BorelTits.pCoreOf_le 2 (P2 L1 L2 S)
  have hQleB : Q ≤ bigB L1 L2 S := hQleS.trans le_sup_right
  have hQN_S : Q ≤ Subgroup.normalizer (S : Set G) := hQleB.trans hSB
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer (by
      simpa [bigB_comm] using bigB_le_normalizer_of_hyp111 hF.1.symm)
  have hQN_L2 : Q ≤ Subgroup.normalizer (L2 : Set G) := hQleP2.trans hP2N
  have hQN_S2 : Q ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) := by
    intro z hz
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hQN_S hz, hQN_L2 hz⟩)
  obtain ⟨x2, hx2S2, qx, hqxQ, hx_eq⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQN_S2).mp hxE
  obtain ⟨y2, hy2S2, qy, hqyQ, hy_eq⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hQN_S2).mp hyE
  have hx2L : x2 ∈ L2 := (Subgroup.mem_inf.mp hx2S2).2
  have hy2L : y2 ∈ L2 := (Subgroup.mem_inf.mp hy2S2).2
  let xbar : K := π ⟨x2, hx2L⟩
  let ybar : K := π ⟨y2, hy2L⟩
  have hxbarQ : xbar ∈ (Qsyl : Subgroup K) := by
    rw [hQcoe]
    exact Subgroup.mem_map.mpr ⟨⟨x2, hx2L⟩, Subgroup.mem_subgroupOf.mpr hx2S2, rfl⟩
  have hybarQ : ybar ∈ (Qsyl : Subgroup K) := by
    rw [hQcoe]
    exact Subgroup.mem_map.mpr ⟨⟨y2, hy2L⟩, Subgroup.mem_subgroupOf.mpr hy2S2, rfl⟩
  have hxbar1 : xbar ≠ 1 := by
    intro h
    apply hxQ
    have hmem : (⟨x2, hx2L⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
      exact MonoidHom.mem_ker.mpr h
    have hx2O : x2 ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
    have hx2Q : x2 ∈ Q := by
      simpa [Q, P2, bigB_comm] using
        (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hx2O
    rw [hx_eq]
    exact Q.mul_mem hx2Q hqxQ
  have hybar1 : ybar ≠ 1 := by
    intro h
    apply hyQ
    have hmem : (⟨y2, hy2L⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
      exact MonoidHom.mem_ker.mpr h
    have hy2O : y2 ∈ pCoreOf 2 L2 := (F1.mem_pCore_iff_coe _).mp hmem
    have hy2Q : y2 ∈ Q := by
      simpa [Q, P2, bigB_comm] using
        (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hy2O
    rw [hy_eq]
    exact Q.mul_mem hy2Q hqyQ
  obtain ⟨dbar, hdDbar, hdbarconj⟩ := hTrans xbar hxbarQ hxbar1 ybar hybarQ hybar1
  obtain ⟨d2, hd2mem, hd2eq⟩ := Subgroup.mem_map.mp hdDbar
  let d : G := ((d2 : ↥L2) : G)
  have hdD2 : d ∈ D2 := Subgroup.mem_subgroupOf.mp hd2mem
  have hdL2 : d ∈ L2 := (d2 : ↥L2).2
  have hdπ : π (d2 : ↥L2) = dbar := hd2eq
  have hconjqx : d⁻¹ * qx * d ∈ Q := by
    have hdN : d⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem (hD2N hdD2)
    have h := (Subgroup.mem_normalizer_iff.mp hdN qx).mp hqxQ
    simpa using h
  have hA : d⁻¹ * x2 * d * y2⁻¹ ∈ Q := by
    have hdL : d⁻¹ * x2 * d ∈ L2 :=
      L2.mul_mem (L2.mul_mem (L2.inv_mem hdL2) hx2L) hdL2
    have hAL : d⁻¹ * x2 * d * y2⁻¹ ∈ L2 :=
      L2.mul_mem hdL (L2.inv_mem hy2L)
    have himg : π ⟨d⁻¹ * x2 * d * y2⁻¹, hAL⟩ = 1 := by
      have h1 : π ⟨d⁻¹ * x2 * d, hdL⟩ = ybar := by
        have hdπ' : π (d2 : ↥L2) = dbar := hdπ
        have hx : π ⟨x2, hx2L⟩ = xbar := rfl
        have hy : π ⟨y2, hy2L⟩ = ybar := rfl
        have hcoe : (⟨d⁻¹ * x2 * d, hdL⟩ : ↥L2) =
            (d2 : ↥L2)⁻¹ * ⟨x2, hx2L⟩ * (d2 : ↥L2) := by
          apply Subtype.ext
          simp [d]
        rw [hcoe, map_mul, map_mul, map_inv, hdπ', hx]
        exact hdbarconj
      have hcoe2 : (⟨d⁻¹ * x2 * d * y2⁻¹, hAL⟩ : ↥L2) =
          ⟨d⁻¹ * x2 * d, hdL⟩ * ⟨y2, hy2L⟩⁻¹ := by
        apply Subtype.ext
        simp
      rw [hcoe2, map_mul, map_inv, h1]
      rw [show π ⟨y2, hy2L⟩ = ybar from rfl]
      simp
    have hmem : (⟨d⁻¹ * x2 * d * y2⁻¹, hAL⟩ : ↥L2) ∈ pCore 2 ↥L2 := by
      rw [← QuotientGroup.ker_mk' (pCore 2 ↥L2)]
      exact MonoidHom.mem_ker.mpr himg
    have hO : d⁻¹ * x2 * d * y2⁻¹ ∈ pCoreOf 2 L2 :=
      (F1.mem_pCore_iff_coe _).mp hmem
    simpa [Q, P2, bigB_comm] using
      (CFSG.Quasithin.Hyp111.pCoreOf_le_pCoreOf_vertex hF.1.symm) hO
  have hq' : y2 * ((d⁻¹ * qx * d) * qy⁻¹) * y2⁻¹ ∈ Q := by
    have hX : (d⁻¹ * qx * d) * qy⁻¹ ∈ Q := Q.mul_mem hconjqx (Q.inv_mem hqyQ)
    have hy2S : y2 ∈ S := hy2S2.1
    have hy2N : y2 ∈ Subgroup.normalizer (Q : Set G) := hSN_Q hy2S
    exact (Subgroup.mem_normalizer_iff.mp hy2N _).mp hX
  have hprod : d⁻¹ * x * d * y⁻¹ ∈ Q := by
    have hgroup : d⁻¹ * x * d * y⁻¹ =
        (d⁻¹ * x2 * d * y2⁻¹) * (y2 * ((d⁻¹ * qx * d) * qy⁻¹) * y2⁻¹) := by
      rw [hx_eq, hy_eq]
      group
    rw [hgroup]
    exact Q.mul_mem hA hq'
  exact ⟨d, hdD2, hprod⟩

end CFSG.Quasithin.Stroth

end
