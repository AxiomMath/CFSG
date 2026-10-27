module

public import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Local
import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Lin
import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Lift
import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Act
import CFSG.RankThree.PartTwo.Sec12.Hering129LOTwoL3Four
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCases
import CFSG.RankThree.OddKernel.InvolutionDims
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

open CFSG CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Census (CriticalAt)
open CFSG.Assembly.RankThreeEven (localRank)

namespace CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3

open CFSG.RankThree.OddKernel in
theorem finrank_le_six_of_four_group {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] (h2 : (2 : 𝕜) ≠ 0) (σ τ : Module.End 𝕜 V) (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hστ : σ * τ = τ * σ)
    (hs : Module.finrank 𝕜 (σ.eigenspace 1) ≤ 2) (ht : Module.finrank 𝕜 (τ.eigenspace 1) ≤ 2)
    (hst : Module.finrank 𝕜 ((σ * τ).eigenspace 1) ≤ 2) : Module.finrank 𝕜 V ≤ 6 := by
  have hσ' : ∀ w, σ (σ w) = w := fun w => by
    have := congrArg (fun f : Module.End 𝕜 V => f w) hσ
    simpa using this
  have hτ' : ∀ w, τ (τ w) = w := fun w => by
    have := congrArg (fun f : Module.End 𝕜 V => f w) hτ
    simpa using this
  have hστ' : ∀ w, σ (τ w) = τ (σ w) := fun w => by
    have := congrArg (fun f : Module.End 𝕜 V => f w) hστ
    simpa using this
  have hfix : ∀ f : Module.End 𝕜 V, f.eigenspace 1 = fixSpace f := fun f => by
    ext v
    simp [Module.End.mem_eigenspace_iff, mem_fixSpace]
  obtain ⟨h0, h1, h2', h3⟩ := finrank_four_group h2 σ τ hσ' hτ' hστ' ⊤ (fun _ _ => trivial)
    (fun _ _ => trivial)
  rw [hfix] at hs ht hst
  have hTop : ∀ X : Submodule 𝕜 V, Module.finrank 𝕜 ↥(⊤ ⊓ X) = Module.finrank 𝕜 ↥X := fun X => by
    rw [top_inf_eq]
  rw [finrank_top] at h0
  simp only [hTop] at h1 h2' h3 h0
  have e : fixSpace (σ ∘ₗ τ) = fixSpace (σ * τ) := rfl
  rw [e] at h3
  omega


structure LData (L : Type) [Group L] : Prop where
  simple : IsSimpleGroup L
  e9q8 : E9Q8 L
  four : FourGroup L
  mult : ∀ (Y : Type) [Group Y] [Finite Y] (Z : Subgroup Y) [Z.Normal], Group.IsPerfect Y →
    Z ≤ Subgroup.center Y → Nat.Coprime 6 (Nat.card Z) → Nonempty (Y ⧸ Z ≃* L) → Z = ⊥

section Critical

variable {Y L : Type} [Group Y] [Finite Y] [Group L]

theorem isSimpleGroup_quotient_ker_L3 (hL : LData L) (φ : Y →* L) (hφ : Function.Surjective φ) :
    IsSimpleGroup (Y ⧸ φ.ker) :=
  @MulEquiv.isSimpleGroup _ _ _ _ hL.simple (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem exists_critical_L3 [hY : Group.IsPerfect Y] (hL : LData L) (φ : Y →* L)
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) (h3 : ¬ 3 ∣ Nat.card φ.ker)
    (hO2 : CFSG.pCore 2 Y = ⊥) (hne : φ.ker ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ D : Subgroup Y, ∃ hD : CriticalAt p D,
      hD.frattiniKer ≤ φ.ker := by
  have hs := isSimpleGroup_quotient_ker_L3 hL φ hφ
  have htop : φ.ker ≠ ⊤ := by
    have := hs
    exact QuotientGroup.nontrivial_iff.mp inferInstance
  by_cases hq : IsQuasisimple Y
  · exfalso
    obtain ⟨-, hZs, a, b, hab⟩ := hq
    have hKZ : φ.ker ≤ Subgroup.center Y := by
      have hn : (φ.ker.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
        (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective _)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (φ.ker.map (QuotientGroup.mk' (Subgroup.center Y))) with h | h
      · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
      · have hsurj : Function.Surjective
            ((QuotientGroup.mk' (Subgroup.center Y)).comp φ.ker.subtype) := by
          intro x
          have hx : x ∈ φ.ker.map (QuotientGroup.mk' (Subgroup.center Y)) := by
            rw [h]
            trivial
          obtain ⟨k, hk, rfl⟩ := hx
          exact ⟨⟨k, hk⟩, rfl⟩
        have hsol : Group.IsSolvable (Y ⧸ Subgroup.center Y) :=
          Group.isSolvable_of_surjective hsurj
        exact absurd ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b) hab
    have h2 : ¬ 2 ∣ Nat.card φ.ker := by
      intro h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := φ.ker) 2 h2
      have ht' : orderOf (t : Y) = 2 := by rw [Subgroup.orderOf_coe, ht]
      have hnorm : (Subgroup.zpowers (t : Y)).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (hKZ t.2))
      have hpg : IsPGroup 2 (Subgroup.zpowers (t : Y)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
      have hle : Subgroup.zpowers (t : Y) ≤ CFSG.pCore 2 Y := le_sSup ⟨hnorm, hpg⟩
      rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
      rw [hle, orderOf_one] at ht'
      exact absurd ht' (by norm_num)
    have hcop : Nat.Coprime 6 (Nat.card φ.ker) := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    exact hne (hL.mult Y φ.ker hY hKZ hcop ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩)
  · obtain ⟨p, hp, hpS⟩ := Sec4.Census.exists_centralizer_pCore_le hK hq
    have : Fact p.Prime := ⟨hp⟩
    have hPne : CFSG.pCore p Y ≠ ⊥ := by
      intro h
      apply htop
      refine top_le_iff.mp (le_trans (fun g _ => ?_) hpS)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [h, SetLike.mem_coe, Subgroup.mem_bot] at hx
      rw [hx, one_mul, mul_one]
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hPne hO2
    have hp3 : p ≠ 3 := by
      rintro rfl
      apply hPne
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 3 (CFSG.pCore 3 Y)).exists_card_eq
      have hdvd : 3 ^ k ∣ Nat.card φ.ker := hk ▸ Subgroup.card_dvd_of_le (Sec4.Census.pCore_le 3)
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq _ hk
      · exact absurd ((dvd_pow_self 3 hk0.ne').trans hdvd) h3
    obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt hp2 hPne
    exact ⟨p, hp, by have := hp.two_le; omega, D, hD, hD.frattiniKer_le hK hpS⟩

end Critical


theorem exists_commuting_involutions_of_lift {Y L : Type} [Group Y] [Finite Y] [Group L]
    (φ : Y →* L) (hφ : Function.Surjective φ) (hF : FourGroup L)
    {b₁ b₂ h₁ h₂ : Y} (hb₁1 : b₁ ≠ 1) (hb₂n : b₂ ∉ Subgroup.zpowers b₁) (hb₁ : b₁ ^ 3 = 1)
    (hb₂ : b₂ ^ 3 = 1) (hbc : b₁ * b₂ = b₂ * b₁)
    (r11 : h₁ * b₁ * h₁⁻¹ = b₂⁻¹) (r12 : h₁ * b₂ * h₁⁻¹ = b₁)
    (r21 : h₂ * b₁ * h₂⁻¹ = b₁⁻¹ * b₂⁻¹) (r22 : h₂ * b₂ * h₂⁻¹ = b₁⁻¹ * b₂)
    (hinj : ∀ b ∈ Subgroup.closure ({b₁, b₂} : Set Y), φ b = 1 → b = 1) :
    ∃ s t : Y, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t ∧ s * t = t * s := by
  obtain ⟨P, u₁, u₂, hP2, hu₁, hu₂, hPB, hact₁, hact₂⟩ :=
    exists_two_subgroup_acting hb₁ hb₂ hbc r11 r12 r21 r22
  exact exists_commuting_involutions_of_acting φ hφ hF hb₁1 hb₂n hb₁ hb₂ hbc r11 r12 r21 r22
    hinj P u₁ u₂ hP2 hu₁ hu₂ hPB hact₁ hact₂

section Branches

variable {Y L : Type} [Group Y] [Finite Y] [Group L]

theorem false_of_finrank_lt_eight (φ : Y →* L) (hφ : Function.Surjective φ)
    (h3 : ¬ 3 ∣ Nat.card φ.ker) (hE : E9Q8 L) {r : ℕ} [hr : Fact r.Prime] (hr3 : 3 < r)
    {V : Type} [AddCommGroup V] [Module (ZMod r) V] [FiniteDimensional (ZMod r) V]
    (ρ : Y →* Module.End (ZMod r) V) (hker : ∀ g, ρ g = 1 → φ g = 1)
    (hdim : Module.finrank (ZMod r) V < 8) : False := by
  obtain ⟨b₁, b₂, h₁, h₂, hb1, -, hb₁, hb₂, hbc, r11, r12, r21, r22, -⟩ :=
    exists_lift_e9Q8 φ hφ h3 hE
  have h3r : (3 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  obtain ⟨hρ, -⟩ := rho_eq_one_of_finrank_lt_eight h3r ρ hb₁ hb₂ hbc r11 r12 r21 r22 hdim
  exact hb1 (hker b₁ hρ)

variable [Finite L]

theorem ker_eq_bot_of_pRank_le_two_L3 [Group.IsPerfect Y] (hL : LData L) (φ : Y →* L)
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) (h3 : ¬ 3 ∣ Nat.card φ.ker)
    (hO2 : CFSG.pCore 2 Y = ⊥) (hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p Y ≤ 2) :
    φ.ker = ⊥ := by
  by_contra hne
  obtain ⟨p, hp, hp3, D, hD, hDK⟩ := exists_critical_L3 hL φ hφ hK h3 hO2 hne
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hDr : CFSG.pRank p D ≤ 2 := by
    have h1 := Sec4.Census.pRank_le_pRank_top hp D
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1
    exact h1.trans (hrank p hp hp3)
  obtain ⟨V, _, _, _, ρ, hρ, hdim, -⟩ := Gap128OTwoHJ.exists_frattiniModule hp2 hD
  have hDp : IsPGroup p D := (pCore_isPGroup (p := p) (G := Y)).to_le hD.le
  have hexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, hD.exp x x.2, Subgroup.coe_one])
  have h1 := (class_two_small_rank_order_bounds hDp hexp hD.commutator_le_center).1 hDr
  have hfc := frattini_eq_commutator hDp hexp
  have h2 : CFSG.pRank p (D ⧸ frattini D) ≤ 2 := by
    rw [pRank_congr_mulEquiv hp.one_lt (QuotientGroup.quotientMulEquivOfEq hfc)]
    exact h1
  exact false_of_finrank_lt_eight φ hφ h3 hL.e9q8 hp3 ρ (fun g hg => hDK (hρ g hg))
    (by omega)


theorem ker_eq_bot_of_localRank_L3 [Group.IsPerfect Y] (hL : LData L) (φ : Y →* L)
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) (h3 : ¬ 3 ∣ Nat.card φ.ker)
    (hO2 : CFSG.pCore 2 Y = ⊥) (hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p Y < 3) :
    φ.ker = ⊥ := by
  by_contra hne
  obtain ⟨p, hp, hp3, D, hD, hDK⟩ := exists_critical_L3 hL φ hφ hK h3 hO2 hne
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hlocp := hloc p hp hp3
  obtain ⟨V, _, _, _, ρ, hρ, -, hfixV⟩ := Gap128OTwoHJ.exists_frattiniModule hp2 hD
  have hker : ∀ g, ρ g = 1 → φ g = 1 := fun g hg => hDK (hρ g hg)
  have hfix : ∀ t : Y, t ^ 2 = 1 → t ≠ 1 →
      Module.finrank (ZMod p) ((ρ t).eigenspace 1) ≤ 2 := fun t ht2 ht1 =>
    hfixV t ht2 (by have := Gap128OTwoHJ.pRank_fixedSubgroupOf_le hp2 hD ht2 ht1; omega)
  obtain ⟨b₁, b₂, h₁, h₂, hb1, hb2n, hb₁, hb₂, hbc, r11, r12, r21, r22, hinj⟩ :=
    exists_lift_e9Q8 φ hφ h3 hL.e9q8
  have hb₁1 : b₁ ≠ 1 := fun h => hb1 (by rw [h, map_one])
  obtain ⟨s, t, hs2, ht2, hs1, ht1, hst, hcomm⟩ := exists_commuting_involutions_of_lift φ hφ
    hL.four hb₁1 hb2n hb₁ hb₂ hbc r11 r12 r21 r22 hinj
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (a := t) (b := t) (by
    rw [← pow_two]
    exact ht2)
  have hst1 : s * t ≠ 1 := fun h => hst (by
    have : s = t⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, htinv])
  have hst2 : (s * t) ^ 2 = 1 := by
    rw [pow_two, mul_assoc, ← mul_assoc t s t, ← hcomm, mul_assoc, ← pow_two t, ht2, mul_one,
      ← pow_two, hs2]
  have hsq : ∀ g : Y, g ^ 2 = 1 → ρ g * ρ g = 1 := fun g hg => by
    rw [← map_mul, ← pow_two, hg, map_one]
  have hdim6 : Module.finrank (ZMod p) V ≤ 6 :=
    finrank_le_six_of_four_group h2p (ρ s) (ρ t) (hsq s hs2) (hsq t ht2)
      (by rw [← map_mul, ← map_mul, hcomm]) (hfix s hs2 hs1) (hfix t ht2 ht1)
      (by rw [← map_mul]; exact hfix (s * t) hst2 hst1)
  exact false_of_finrank_lt_eight φ hφ h3 hL.e9q8 hp3 ρ hker (by omega)


theorem ker_le_pCore_two_of_pRank_le_two_L3 [Group.IsPerfect Y] (hL : LData L) (φ : Y →* L)
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) (h3 : ¬ 3 ∣ Nat.card φ.ker)
    (hrank : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p Y ≤ 2) : φ.ker ≤ CFSG.pCore 2 Y := by
  have hs := isSimpleGroup_quotient_ker_L3 hL φ hφ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 Y with hQ
  have : Q.Normal := pCore_normal
  have hQK : Q ≤ φ.ker := Sec4.Census.pCore_le 2
  set φ' : Y ⧸ Q →* L := QuotientGroup.lift Q φ hQK with hφ'def
  have hφ' : Function.Surjective φ' := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hker' : φ'.ker = φ.ker.map (QuotientGroup.mk' Q) := QuotientGroup.ker_lift Q φ hQK
  have hK' : Group.IsSolvable φ'.ker := by
    rw [hker']
    exact Group.isSolvable_of_surjective ((QuotientGroup.mk' Q).subgroupMap_surjective φ.ker)
  have h3' : ¬ 3 ∣ Nat.card φ'.ker := by
    rw [hker']
    exact fun h => h3 (h.trans (Subgroup.card_map_dvd _ _))
  have hO2' : CFSG.pCore 2 (Y ⧸ Q) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hrank' : ∀ p : ℕ, p.Prime → 3 < p → CFSG.pRank p (Y ⧸ Q) ≤ 2 := by
    intro p hp hp3
    have : Fact p.Prime := ⟨hp⟩
    have hQp : ¬ p ∣ Nat.card Q := by
      obtain ⟨k, hk⟩ := (pCore_isPGroup : IsPGroup 2 Q).exists_card_eq
      rw [hk]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      omega
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq Q hQp,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hrank p hp hp3
  have hbot := ker_eq_bot_of_pRank_le_two_L3 hL φ' hφ' hK' h3' hO2' hrank'
  rw [hker', Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem ker_le_pCore_two_L3 [Group.IsPerfect Y] (hL : LData L) (φ : Y →* L)
    (hφ : Function.Surjective φ) (hK : Group.IsSolvable φ.ker) (h3 : ¬ 3 ∣ Nat.card φ.ker)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p Y < 3) : φ.ker ≤ CFSG.pCore 2 Y := by
  by_cases hO2 : CFSG.pCore 2 Y = ⊥
  · rw [ker_eq_bot_of_localRank_L3 hL φ hφ hK h3 hO2 hloc]
    exact bot_le
  · refine ker_le_pCore_two_of_pRank_le_two_L3 hL φ hφ hK h3 fun p hp hp3 => ?_
    have h1 := Gap128OTwoHJ.pRank_le_localRank_of_le_normalizer hp hO2 pCore_isPGroup
      (H := ⊤) (Subgroup.normalizer_eq_top (CFSG.pCore 2 Y)).ge
    rw [pRank_congr_mulEquiv hp.one_lt Subgroup.topEquiv] at h1
    have h2 := hloc p hp hp3
    omega

end Branches

end CFSG.RankThree.PartTwo.Sec12.Hering129L.OTwoL3
