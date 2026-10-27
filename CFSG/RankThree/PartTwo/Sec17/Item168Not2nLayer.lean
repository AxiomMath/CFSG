module

public import CFSG.RankThree.PartTwo.Sec17.Item174KFact26
public import CFSG.RankThree.PartTwo.Sec16.Ronan168Not2n
import CFSG.RankThree.PartTwo.Sec17.Item174HostPerfect
import CFSG.GH74.Generic.S1.TQ3BarVert
import CFSG.GH74.Generic.BProg.B3.S3Sec29I
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.RankThree.PartTwo.Sec15.HypS
public import CFSG.RankThree.PartTwo.Sec17.Item174LayerE

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof168Omega

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec16
  CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank
  CFSG.RankThree.PartTwo.Sec17.Proof174Host CFSG.RankThree.PartTwo.Sec16.Proof165

theorem eq_bot_of_perfect_of_le_centralizer {H : Type*} [Group H] [Finite H]
    (hE : CFSG.layer H = ⊥) {K : Subgroup H} (hK : ⁅K, K⁆ = K)
    (hKr : ∀ r : ℕ, r.Prime → K ≤ Subgroup.centralizer (CFSG.pCore r H : Set H)) :
    K = ⊥ := by
  have hF : K ≤ Subgroup.centralizer (CFSG.fittingSubgroup H : Set H) := by
    rw [Subgroup.le_centralizer_iff, CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    exact Subgroup.le_centralizer_iff.mp (hKr q.1.1 (Nat.prime_of_mem_primeFactors q.1.2))
  have hFs : CFSG.generalizedFitting H = CFSG.fittingSubgroup H := by
    rw [CFSG.generalizedFitting, hE, sup_bot_eq]
  have hKF : K ≤ CFSG.fittingSubgroup H := by
    have := (hF.trans (le_of_eq (by rw [hFs]))).trans (CFSG.centralizer_generalizedFitting_le H)
    rwa [hFs] at this
  refine CFSG.GH74.Generic.BProg.B3.S3Sec29I.eq_bot_of_perfect_of_solvable hK ?_
  exact solvable_of_solvable_injective (f := Subgroup.inclusion hKF)
    (Subgroup.inclusion_injective hKF)

theorem centralizer_oTwo_quotient_pPrimeCore_le_of_layer {H : Type*} [Group H] [Finite H]
    (hE : CFSG.layer H = ⊥)
    (hperf : ∀ K : Subgroup H, ⁅K, K⁆ = K → ∀ r : ℕ, r.Prime → r ≠ 2 →
      K ≤ Subgroup.centralizer (CFSG.pCore r H : Set H)) :
    Subgroup.centralizer (S4Free.oTwo (H ⧸ CFSG.pPrimeCore 2 H) :
        Set (H ⧸ CFSG.pPrimeCore 2 H)) ≤
      S4Free.oTwo (H ⧸ CFSG.pPrimeCore 2 H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := CFSG.pPrimeCore 2 H with hR
  haveI : R.Normal := CFSG.pPrimeCore_normal
  set P := CFSG.pCore 2 H with hP
  haveI : P.Normal := CFSG.pCore_normal
  set π : H →* H ⧸ R := QuotientGroup.mk' R with hπ
  rw [← pCore_two_eq_oTwo]
  set CP := Subgroup.centralizer (P : Set H) with hCP
  have hCPs : Group.IsSolvable ↥CP := by
    refine CFSG.GH74.Generic.S1.isSolvable_of_forall_perfect fun T hT => ?_
    have hK : ⁅T.map CP.subtype, T.map CP.subtype⁆ = T.map CP.subtype := by
      rw [← Subgroup.map_commutator, hT]
    have hKP : T.map CP.subtype ≤ CP := Subgroup.map_subtype_le T
    have h0 := eq_bot_of_perfect_of_le_centralizer hE hK fun r hr => by
      by_cases hr2 : r = 2
      · subst hr2
        exact hKP
      · exact hperf _ hK r hr hr2
    exact (Subgroup.map_eq_bot_iff_of_injective _ CP.subtype_injective).mp h0
  have hPR : P ⊓ R = ⊥ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := H))
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hk]
    exact Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
  have hPQ : P.map π ≤ CFSG.pCore 2 (H ⧸ R) :=
    le_sSup ⟨Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective R),
      (CFSG.pCore_isPGroup (p := 2) (G := H)).map π⟩
  set Nc := Subgroup.centralizer (CFSG.pCore 2 (H ⧸ R) : Set (H ⧸ R)) with hNc
  have hN : Nc ≤ (π.comp CP.subtype).range := by
    intro xb hxb
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R xb
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := Subgroup.mem_centralizer_iff.mp hxb (π u) (hPQ ⟨u, hu, rfl⟩)
    have hcR : u * x * u⁻¹ * x⁻¹ ∈ R := by
      rw [← QuotientGroup.ker_mk' R]
      have h1' : π u * π x = π x * π u := h1
      change π (u * x * u⁻¹ * x⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1']
      group
    have hcP : u * x * u⁻¹ * x⁻¹ ∈ P := by
      have : x * u⁻¹ * x⁻¹ ∈ P := ‹P.Normal›.conj_mem _ (inv_mem hu) x
      have h2 := mul_mem hu this
      rwa [show u * (x * u⁻¹ * x⁻¹) = u * x * u⁻¹ * x⁻¹ by group] at h2
    have hc1 : u * x * u⁻¹ * x⁻¹ = 1 := by
      have : u * x * u⁻¹ * x⁻¹ ∈ P ⊓ R := ⟨hcP, hcR⟩
      rwa [hPR, Subgroup.mem_bot] at this
    calc u * x = (u * x * u⁻¹ * x⁻¹) * (x * u) := by group
      _ = x * u := by rw [hc1, one_mul]
  have hNs : Group.IsSolvable ↥Nc := by
    haveI : Group.IsSolvable ↥(π.comp CP.subtype).range :=
      solvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
    exact solvable_of_solvable_injective (Subgroup.inclusion_injective hN)
  haveI : (CFSG.pCore 2 (H ⧸ R)).Normal := CFSG.pCore_normal
  haveI : Nc.Normal := Subgroup.normal_centralizer
  have hQ0 : CFSG.pPrimeCore 2 (H ⧸ R) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hN0 : CFSG.pPrimeCore 2 ↥Nc = ⊥ := by
    have hle : (CFSG.pPrimeCore 2 ↥Nc).map Nc.subtype ≤ CFSG.pPrimeCore 2 (H ⧸ R) := by
      refine le_sSup ⟨inferInstance, ?_⟩
      rw [Subgroup.card_map_of_injective Nc.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    rw [hQ0, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ Nc.subtype_injective] at hle
    exact hle
  have hc : IsCharacteristicP 2 ↥Nc :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2 hN0
      (haveI := hNs; CFSG.WholeGroup.layer_eq_bot_of_isSolvable)
  have hPN : (CFSG.pCore 2 ↥Nc).map Nc.subtype ≤ CFSG.pCore 2 (H ⧸ R) :=
    le_sSup ⟨inferInstance, (CFSG.pCore_isPGroup (p := 2) (G := ↥Nc)).map _⟩
  intro n hn
  have hmem : (⟨n, hn⟩ : ↥Nc) ∈ CFSG.pCore 2 ↥Nc := by
    apply hc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hn _ (hPN ⟨y, hy, rfl⟩)
  exact hPN ⟨_, hmem, rfl⟩

variable {G : Type} [Group G] [Finite G]

theorem core168At_of_layer {A : Subgroup G} {Y₀ : Subgroup G}
    (hG : TheoremFourHyp G)
    (hE : ∀ Ŷ ∈ scriptY1Star A (lB A), Ŷ ≤ Subgroup.normalizer (Y₀ : Set G) →
      CFSG.layer ↥Ŷ = ⊥)
    (hC : ∀ Ŷ ∈ scriptY1Star A (lB A), Ŷ ≤ Subgroup.normalizer (Y₀ : Set G) →
      ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≤ Ŷ → ∀ p : ℕ, p.Prime → p ≠ 2 →
        stellmacherSub S ≤ Subgroup.centralizer (CFSG.Open.pCoreOf p Ŷ : Set G)) :
    Core168At A Y₀ := by
  intro Ŷ hŶ hŶM S hS hSŶ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup ↥Ŷ := CFSG.pPrimeCore 2 ↥Ŷ with hP
  have hPn : P.Normal := CFSG.pPrimeCore_normal
  have he : (P.map Ŷ.subtype).subgroupOf Ŷ = P :=
    Subgroup.comap_map_eq_self_of_injective Ŷ.subtype_injective P
  have hperf : ∀ K : Subgroup ↥Ŷ, ⁅K, K⁆ = K → ∀ r : ℕ, r.Prime → r ≠ 2 →
      K ≤ Subgroup.centralizer (CFSG.pCore r ↥Ŷ : Set ↥Ŷ) := by
    intro K hK r hr hr2
    haveI : Fact r.Prime := ⟨hr⟩
    have hK' : ⁅K.map Ŷ.subtype, K.map Ŷ.subtype⁆ = K.map Ŷ.subtype := by
      rw [← Subgroup.map_commutator, hK]
    have hc := le_centralizer_pCoreOf_of_perfect hG hŶ (Subgroup.map_subtype_le K) hK' hr hr2
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxG : (x : G) ∈ CFSG.Open.pCoreOf r Ŷ := by
      refine ⟨x, ?_, rfl⟩
      rw [← CFSG.pCore_eq_open]
      exact hx
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hc ⟨k, hk, rfl⟩) (x : G) hxG)
  refine ⟨P.map Ŷ.subtype, Subgroup.map_subtype_le P, ?_⟩
  rw [he]
  refine ⟨hPn, ?_, centralizer_oTwo_quotient_pPrimeCore_le_of_layer (hE Ŷ hŶ hŶM) hperf, ?_⟩
  · rw [Nat.card_congr (Subgroup.equivMapOfInjective P Ŷ.subtype Ŷ.subtype_injective).toEquiv.symm]
    exact CFSG.pPrimeCore_coprime_card
  · rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hgS : g ∈ S := Subgroup.map_subtype_le _ hg
    have hgŶ : g ∈ Ŷ := hSŶ hgS
    have hC' := hC Ŷ hŶ hŶM S hS hSŶ
    obtain ⟨k, hk⟩ := hS2 ⟨g, hgS⟩
    have hgk : (⟨g, hgŶ⟩ : ↥Ŷ) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card P) :=
      Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
    have key := commute_pPrimeCore_of_commute_pCore hgk hcop (by
      intro p hp hp2 x hx
      haveI : Fact p.Prime := ⟨hp⟩
      have hxG : (x : G) ∈ CFSG.Open.pCoreOf p Ŷ := by
        refine ⟨x, ?_, rfl⟩
        rw [← CFSG.pCore_eq_open]
        exact hx
      have := Subgroup.mem_centralizer_iff.mp (hC' p hp hp2 hg) (x : G) hxG
      exact Subtype.ext this.symm) r hr
    exact (congrArg Subtype.val key)

theorem two168Out_of_layer {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) (h167 : Item167 A (lB A) c L) (h176 : Item176 A (lB A) c L)
    (hE : IsHyperplane A (A ⊓ L)) (hcL : c ∉ L)
    (hQ : CFSG.Open.pCoreOf 2 Y₀ ∈ scriptQ A (lB A)) (hStar : KFactStar) (hL3 : KFactL3Aut)
    (hL : ¬ IsL3TwoPow L) : Two168Out A Y₀ := by
  have hF := generalizedFitting_y0 h
  have hK39 : KFact39At A c L Y₀ :=
    kfact39At_of h (kfact26At_of_star h h176 hE hStar) hL3
  have hLay := layer_eq_bot_of_kfact h h149 h146 hE hcL hQ hF (kfact35PerfAt_of_kfact39At hK39)
  refine two168Out_of_core168At h hst h146 h167 ?_
  exact core168At_of_layer h.toTheoremFourHyp (hLay hL) fun Ŷ hŶ hŶM S hS hSŶ p hp hp2 =>
    stellmacherSub_le_centralizer_pCoreOf h hst h149 h146 hŶ hS hSŶ hp hp2
      (stellmacherSub_inf_le_centralizer h h149 h146 hE hcL hQ hF hK39 hL hŶ hŶM hS hSŶ hp hp2)

theorem step168TwoOutNot2n_of_layer
    (hst : StellmacherKP) (h146 : Item146S14)
    (h149 : Sec16.Item149S14) (h167 : Item167R) (h176 : Item176R) (h9 : CardInfNineS17)
    (hQ0 : Claim17Q0) (hStar : KFactStar) (hL3 : KFactL3Aut) : Step168TwoOutNot2n := by
  intro G _ _ A c L Y₀ hs hL
  have hA : IsE27 A := hs.toSec14Std.isE27
  exact two168Out_of_layer hs hst (h146 G A c L hs.toSec14Std) (h149 G A c L hs.toSec14Std)
    (h167 G A c L hs.toSec15R) (h176 G A c L hs.toSec15R)
    ⟨inf_le_left, by rw [hA.2, h9 G A c L Y₀ hs]⟩
    (hs.toSec15R.hypS.2.2 c hs.zpowers_mem_omegaA L hs.mem_lA) (hQ0 G A c L Y₀ hs) hStar hL3 hL

theorem step168TwoOutNot2nOmega_of_layer
    (hst : StellmacherKP) (h146 : Item146S14)
    (h149 : Sec16.Item149S14) (h167 : Item167R) (h176 : Item176R) (h9 : CardInfNineS17)
    (hQ0 : Claim17Q0) (hStar : KFactStar) (hL3 : KFactL3Aut) : Step168TwoOutNot2nOmega :=
  fun G _ _ A c L Y₀ hs hL _ =>
    step168TwoOutNot2n_of_layer hst h146 h149 h167 h176 h9 hQ0 hStar hL3 G A c L Y₀ hs hL

end CFSG.RankThree.PartTwo.Sec17.Proof168Omega
