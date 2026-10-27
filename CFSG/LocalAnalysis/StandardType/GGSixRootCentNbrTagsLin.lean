module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNbr
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSUOuter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

namespace RCSPSL

open CFSG.SeitzReduction.LinearPilot Matrix

variable {m : ℕ} {F : Type} [Field F] {G : Type} [Group G]

theorem derivedAtQ_of_transvection [Finite G] [Finite F] [CharP F 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hm : 2 ≤ m) (hmq : m = 2 ∨ 4 ≤ m ∨ 4 ≤ Nat.card F)
    (ψ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (m + 1)) F)) {r : G}
    (hr : r = ψ (ggInvSL (m + 1) 1 F)) : GGRootCentDerivedAtQ p ψ.range r := by
  subst hr
  have hm1 : 1 ≤ m := by omega
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hX : ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) = (P.core F).map ψ := oTwoPrime_eq hm1 ψ hker
  have hcardJ : P.free.card = m - 1 := by rw [P.card_free]; omega
  have hR2 : IsPGroup 2 ((P.radical F).map ψ) := (radical_isPGroup hm1).map ψ
  have : Subsingleton (SpecialLinearGroup (Fin 1) F) :=
    ⟨fun a b => by rw [LinFusion.eq_one_of_specialLinearGroup_fin_one a,
      LinFusion.eq_one_of_specialLinearGroup_fin_one b]⟩
  by_cases hm2 : m = 2
  ·
    left
    have hc : Fintype.card ↥P.free = 1 := by rw [Fintype.card_coe, hcardJ, hm2]
    have : Subsingleton (SpecialLinearGroup P.free F) :=
      (reindexSpecialLinear (K := F) (Fintype.equivFinOfCardEq hc)).injective.subsingleton
    have hJ : blockSpecialLinear (K := F) P.free = ⊥ := by
      rw [← range_blockEmbed, eq_bot_iff]
      rintro _ ⟨a, rfl⟩
      rw [Subsingleton.elim a 1, map_one]
      exact one_mem _
    have hcore : P.core F = P.radical F := by
      rw [InvPlacement.core, leviOne_eq_bot P, hJ, sup_bot_eq, sup_bot_eq]
    intro y hy hyp
    rw [hX, hcore] at hy
    exact ggRCS_eq_one_of_mem_two hp hp2 hR2 hy hyp
  have hJ2 : 2 ≤ P.free.card := by omega
  have hSLJ : CFSG.IsQuasisimple (SpecialLinearGroup P.free F) := by
    refine isQuasisimple_free P hJ2 ?_
    rcases hmq with h | h | h
    · exact absurd h hm2
    · left; omega
    · right; exact h
  have : Group.IsPerfect (SpecialLinearGroup P.free F) := hSLJ.1
  have hcperf : ⁅P.core F, P.core F⁆ = P.core F := P.commutator_core hJ2
  have hXperf : ⁅ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)),
      ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))⁆ = ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F)) := by
    rw [hX, ← Subgroup.map_commutator, hcperf]
  have hQn := radical_normal_X hm1 ψ hker
  refine ggRootCentDerivedAtQ_of_perfect hp hXperf (radical_le_X hm1 ψ hker) hR2 fun hpX => ?_
  set f := freeQuotHom hm1 ψ hker with hf
  have hfs : Function.Surjective f := freeQuotHom_surjective hm1 ψ hker
  have hfker : f.ker ≤ Subgroup.center (SpecialLinearGroup P.free F) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hSLJ (MonoidHom.normal_ker f) with h | h
    · exfalso
      have hall : ∀ x : ↥(ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))),
          (x : G) ∈ (P.radical F).map ψ := by
        intro x
        obtain ⟨d, hd⟩ := hfs (QuotientGroup.mk x)
        have hd1 : f d = 1 := by
          rw [← MonoidHom.mem_ker, h]
          exact Subgroup.mem_top d
        rw [hd1] at hd
        exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff x).mp hd.symm)
      have hX2 : IsPGroup 2 (ggRCSX ψ.range (ψ (ggInvSL (m + 1) 1 F))) := by
        intro x
        obtain ⟨k, hk⟩ := hR2 ⟨x, hall x⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      exact ggNot_dvd_card_of_isPGroup_two hp hp2 hX2 hpX
    · exact h
  exact CFSG.LocalCores.isQuasisimple_of_surjective hSLJ f hfs hfker

end RCSPSL

section TagPSL

theorem ggRootCentDerivedQTag_PSL : GGRootCentDerivedQTag .PSL := by
  intro G _ _ n f ψ hadm hrk hker _ _ hnr r hr
  obtain ⟨-, hf1, hn, -⟩ := hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := hrk
  obtain ⟨ψ', hrange, hker', hr'⟩ :=
    RCSPSL.exists_conj (F := GaloisField 2 f) (by omega) ψ hker hr
  have hR : ψ'.range = ψ.range := hrange
  rw [← hR]
  by_cases hcase : m = 2 ∨ 4 ≤ m ∨ 4 ≤ Nat.card (GaloisField 2 f)
  · exact RCSPSL.derivedAtQ_of_transvection Nat.prime_three (by norm_num) hm hcase ψ' hker' hr'
  · push Not at hcase
    obtain ⟨h2, h4, hq⟩ := hcase
    obtain rfl : m = 3 := by omega
    have hF2 : Nat.card (GaloisField 2 f) = 2 := by
      have h1 : 1 < Nat.card (GaloisField 2 f) := Finite.one_lt_card
      have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
      obtain ⟨k, -, hk⟩ := FiniteField.card (GaloisField 2 f) 2
      rw [Nat.card_eq_fintype_card] at h1 hq ⊢
      rw [hk] at h1 hq ⊢
      have hk1 : (k : ℕ) < 2 := by
        by_contra hk2
        push Not at hk2
        have : 2 ^ 2 ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) hk2
        omega
      have hk0 : (k : ℕ) ≠ 0 := k.ne_zero
      have : (k : ℕ) = 1 := by omega
      rw [this, pow_one]
    have h2f : 2 ^ f = 2 :=
      (GaloisField.card 2 f (by omega)).symm.trans hF2
    have hfone : f = 1 :=
      Nat.pow_right_injective (le_refl 2) (by simp only [h2f, pow_one])
    exact absurd hfone (hnr (Or.inl rfl) (by omega))

end TagPSL

namespace RCSTSU

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.BorelTits OTwoGen RootCentSU
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom mat_iotaHom iotaMat
  iotaMat_isBlkOn mid mem_range_mid mid_injective mid_ne_zero mid_ne_last submatrix_iotaMat)

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f k : ℕ} {G : Type} [Group G] [Finite G]

theorem derivedAtQ_su (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hk : 2 ≤ k) (hU4 : k = 2 → 2 ^ f ≠ 2) (hU5 : k = 3 → 2 ^ f = 2 → p ≠ 3)
    (ψ : SU (unitaryInvolution F 2 f) (k + 2) →* G)
    (hker : ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2))) :
    GGRootCentDerivedAtQ p ψ.range (ψ (ggInvSU (unitaryInvolution F 2 f) (k + 2) 1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · exfalso
      have h1 := Finite.one_lt_card (α := F)
      rw [hF] at h1
      norm_num at h1
    · exact h
  have hQ2 : IsPGroup 2 ((suRad (unitaryInvolution F 2 f) k).map ψ) := suRad_isPGroup.map ψ
  have hQX := ggRCST_map_le_ggRCSX_of_isPGroup ψ (suRad_le_centralizer (k := k)) suRad_isPGroup
  have hXQ := ggRCST_ggRCSX_le_normalizer hker (hZ_su _) ggInvSU_mul_self
    (centralizer_le_normalizer_suRad (σ := unitaryInvolution F 2 f) (k := k))
  have hL₀X := ggRCST_range_le_ggRCSX ψ iotaHom range_iotaHom_le_centralizer
    (top_le_closure_SU hF hk)
  have hX := ggRCSX_le_sup hf ψ hker
  have hkerι := ker_comp_iotaHom_le ψ hker
  by_cases hq : (3 ≤ k ∧ (k, 2 ^ f) ≠ (3, 2)) ∨ (k = 2 ∧ 4 ≤ 2 ^ f)
  · exact ggRootCentDerivedAtQ_of_quasisimple hp hp2 hQX hQ2 hXQ hL₀X
      (ggRCST_isQuasisimple_range _ (isQuasisimple_su hF hq) hkerι)
      ((CFSG.Quasithin.perfectCore_le _).trans hX) (fun y hy _ => hX hy)
  have hq2 : 2 ^ f = 2 := by
    have h2 : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    by_contra hne
    have h4 : 4 ≤ 2 ^ f := by
      have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by
        by_contra hf2
        push Not at hf2
        have : f = 1 := by omega
        exact hne (by rw [this, pow_one]))
      simpa using this
    apply hq
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · exact Or.inr ⟨by omega, h4⟩
    · exact Or.inl ⟨hk3, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  have hk23 : k = 2 ∨ k = 3 := by
    by_contra hk23
    apply hq
    exact Or.inl ⟨by omega, fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  rcases hk23 with rfl | rfl
  ·
    exact absurd hq2 (hU4 rfl)
  ·
    have hp3 := hU5 rfl hq2
    refine ggRootCentDerivedAtQ_of_not_dvd hp hp2 hQ2 (hL₀X.trans hXQ) hX fun hpL => ?_
    have h1 : Nat.card (ψ.comp (iotaHom (σ := unitaryInvolution F 2 f) (m := 3))).range ∣
        Nat.card (SU (unitaryInvolution F 2 f) 3) := Subgroup.card_range_dvd _
    have h216 : Nat.card (SU (unitaryInvolution F 2 f) 3) = 2 ^ 3 * 3 ^ 3 := by
      rw [CFSG.LieType.Steinberg.card_SU_three hF, hq2]
      norm_num
    rw [h216] at h1
    rcases (Nat.Prime.dvd_mul hp).mp (hpL.trans h1) with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h))

theorem derivedAtQ_of_longRoot (hF : Nat.card F = (2 ^ f) ^ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hk : 2 ≤ k) (hU4 : k = 2 → 2 ^ f ≠ 2)
    (hU5 : k = 3 → 2 ^ f = 2 → p ≠ 3)
    (ψ : SU (unitaryInvolution F 2 f) (k + 2) →* G)
    (hker : ψ.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2))) {r : G}
    (hr : GGRootInvolution (rootDatum hF (k + 2)) .PSU ψ r) :
    GGRootCentDerivedAtQ p ψ.range r := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hr2, γ, ⟨-, hlong⟩, u₀, hru⟩ := hr
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hru
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hr2
  obtain ⟨a, ha⟩ := exists_conj_ggInvSU_of_longRoot hF (hlong (Or.inl rfl)) hx hx1
  set h := u₀ * a with hh
  set ψ' := ψ.comp (MulAut.conj h).toMonoidHom with hψ'
  have hr' : ψ' (ggInvSU (unitaryInvolution F 2 f) (k + 2) 1) =
      ψ ((MulAut.conj u₀).toMonoidHom x) := by
    simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ha, hh]
    congr 1
    group
  have hrange : ψ'.range = ψ.range := by
    rw [hψ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  have hker' : ψ'.ker ≤ center (SU (unitaryInvolution F 2 f) (k + 2)) := by
    intro v hv
    have hz : h * v * h⁻¹ ∈ center (SU (unitaryInvolution F 2 f) (k + 2)) := hker hv
    have h1 := (inferInstance :
      (center (SU (unitaryInvolution F 2 f) (k + 2))).Normal).conj_mem _ hz h⁻¹
    rwa [inv_inv, show h⁻¹ * (h * v * h⁻¹) * h = v by group] at h1
  have := derivedAtQ_su hF hp hp2 hk hU4 hU5 ψ' hker'
  rwa [hrange, hr'] at this

end RCSTSU

section TagPSU

open CFSG.LieType.BorelTits

theorem ggRootCentDerivedQTag_PSU : GGRootCentDerivedQTag .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have h5 : ∀ ψ : (ggU .PSU n f).K →* G, n = 5 → f = 1 →
        ψ.ker ≤ Subgroup.center (ggU .PSU n f).K →
          Subgroup.centralizer (ψ.range : Set G) = ⊥ →
            ¬ GGTwoLocalRankFour 3 (Subgroup.normalizer (ψ.range : Set G)) := by
      rintro ψ rfl rfl hker hC h4
      exact ggUFiveTwoRankInput_holds G ψ hker hC h4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e] at h5 ⊢
    intro ψ _ hrk hker hC h4 hnr r hr
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrk
      omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    refine RCSTSU.derivedAtQ_of_longRoot (card_galoisField_two_mul 2 f hf) Nat.prime_three
      (by norm_num) (by omega) ?_ (fun hk3 hq => ?_) ψ hker hr
    ·
      intro hk2 hq
      have hfone : f = 1 :=
        Nat.pow_right_injective (le_refl 2) (by simp only [hq, pow_one])
      exact absurd hfone (hnr (Or.inr (Or.inl rfl)) (by omega))
    ·
      have hfone : f = 1 :=
        Nat.pow_right_injective (le_refl 2) (by simp only [hq, pow_one])
      exact absurd h4 (h5 ψ (by omega) hfone hker hC)
  · intro ψ hadm
    exact absurd hadm.2.1 hf

end TagPSU

end CFSG.StandardType
