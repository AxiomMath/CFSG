module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SInnerRes
public import CFSG.RankThree.PartTwo.Sec13.Item138ProofPGL
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.KFacts.KS18M12
public import CFSG.RankThree.PartTwo.Toolkit.Statements
import CFSG.RankThree.PartTwo.Sec13.Ronan138SInnerFrame
import CFSG.RankThree.PartTwo.Sec13.Ronan138SENeDRed
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
import CFSG.RankThree.PartTwo.Sec13.Ronan138SSN
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SEnd
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKIn
public import CFSG.RankThree.PartTwo.Sec4.Statements417

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem item138OuterN_of_inner (h131 : Item131) (hspor : SporadicModels131)
    (hK18 : KFacts.KS18M12)
    (hM12D : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M12) →
      Toolkit.M12ThreeLocalData X)
    (hENeD : Step138ENeDBase) (hKS : Step138KStrIn) (hOut : KF138OutAbelian) :
    Item138OuterN := by
  intro G _ _ A c L E hH hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, x, y, t, n, hfr⟩ := exists_innerFrame138 hH hle
  have hb := hfr.base
  set d := ⁅x, y⁆ with hd
  have hdΩ := hENeD G A c L E F x y t hb
  obtain ⟨e, K, heΩ, hK, heF, -, heL, hcase⟩ := hKS G A c L E F x y t hb hle hdΩ
    ⟨n, Subgroup.mem_inf.mpr ⟨hfr.hnL, hfr.hnC⟩, ⟨2, hfr.hn9⟩, hfr.hn3d, hfr.hn3⟩
  have h := hb.hH.1
  have hXF := mem_partTwoF_of_hyp138 hb.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hb.hE3 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hEN : E ≤ Subgroup.normalizer (K : Set G) := hK.2.1
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hed : Subgroup.zpowers e ⊓ Subgroup.zpowers d = ⊥ :=
    zpowers_inf_zpowers_eq_bot he3 heL hb.hdL
  have hye : y * e = e * y := hb.hFab y hb.hyF e heF
  have hne : n * e = e * n := (Subgroup.mem_centralizer_iff.mp hfr.hnC e heE).symm
  have hnorm : ¬ E ⊓ K ≤ Subgroup.zpowers e → y ∈ Subgroup.normalizer (K : Set G) ∧
      n ∈ Subgroup.normalizer (K : Set G) := by
    intro hEK
    obtain ⟨b, hbEK, hbe⟩ := SetLike.not_le_iff_exists.mp hEK
    obtain ⟨hbE, hbK⟩ := Subgroup.mem_inf.mp hbEK
    refine ⟨mem_normalizer_of_mem_lA_of_not_mem hK hbE hbK hbe (hb.hFN hb.hyF)
      (centralizer_le_normalizer_zpowers _ (Subgroup.mem_centralizer_singleton_iff.mpr hye)),
      mem_normalizer_of_mem_lA_of_not_mem hK hbE hbK hbe
        (Subgroup.centralizer_le_normalizer _ hfr.hnC)
        (centralizer_le_normalizer_zpowers _ (Subgroup.mem_centralizer_singleton_iff.mpr hne))⟩
  set ρ : Subgroup.normalizer (K : Set G) →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hρ
  have hρpow : ∀ (z : G) (hz : z ∈ Subgroup.normalizer (K : Set G)) (k : ℕ), z ^ 3 ^ k = 1 →
      ρ ⟨z, hz⟩ ^ 3 ^ k = 1 := by
    intro z hz k hzk
    rw [← map_pow]
    have : (⟨z, hz⟩ : Subgroup.normalizer (K : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using hzk)
    rw [this, map_one]
  rcases hcase with hPGLK | hM12
  ·
    obtain ⟨heK, hAut, -⟩ := facts131_of_isZ3PGLThreePi h131 hspor hD hPGLK
    have hEK : ¬ E ⊓ K ≤ Subgroup.zpowers e := by
      intro hle'
      apply inf_ne_bot_of_autIn hEN hAut
      rw [eq_bot_iff, ← zpowers_inf_eq_bot he3 heK]
      exact le_inf hle' inf_le_right
    obtain ⟨hyK, hnK⟩ := hnorm hEK
    obtain ⟨hL3K, -⟩ := facts_of_isZ3PGLThreePi hD hPGLK
    have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
    set Hin : Subgroup G := (((MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* _).range).comap
      ρ).map (Subgroup.normalizer (K : Set G)).subtype with hHin
    have hcommIn : ∀ (z₁ z₂ : G) (h₁ : z₁ ∈ Subgroup.normalizer (K : Set G))
        (h₂ : z₂ ∈ Subgroup.normalizer (K : Set G)) (k₁ k₂ : ℕ), z₁ ^ 3 ^ k₁ = 1 →
        z₂ ^ 3 ^ k₂ = 1 → ⁅z₁, z₂⁆ ∈ Hin := by
      intro z₁ z₂ h₁ h₂ k₁ k₂ hk₁ hk₂
      have hc := hOut _ hL3K hKq (ρ ⟨z₁, h₁⟩) (ρ ⟨z₂, h₂⟩) ⟨k₁, hρpow z₁ h₁ k₁ hk₁⟩
        ⟨k₂, hρpow z₂ h₂ k₂ hk₂⟩
      refine ⟨⁅(⟨z₁, h₁⟩ : Subgroup.normalizer (K : Set G)), ⟨z₂, h₂⟩⁆,
        Subgroup.mem_comap.mpr ?_, ?_⟩
      · rw [map_commutatorElement, commutatorElement_def]
        exact hc
      · simp [commutatorElement_def]
    have heIn : e ∈ Hin := by
      have heC : e ∈ Sec4.thetaQuotCentralizer K := by
        have : e ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) := by
          rw [← hCEset]
          exact Subgroup.mem_zpowers e
        exact (Subgroup.mem_inf.mp this).2
      obtain ⟨⟨e', he'N⟩, hker, he'⟩ := Subgroup.mem_map.mp heC
      refine ⟨⟨e', he'N⟩, Subgroup.mem_comap.mpr ?_, he'⟩
      have h1 : ρ ⟨e', he'N⟩ = 1 := hker
      rw [h1]
      exact one_mem _
    have hdIn : d ∈ Hin := hcommIn x y (hEN hb.hxE) hyK 1 1 (by simpa using hb.frame.x3)
      (by simpa using hb.frame.y3)
    have hbIn : ⁅n, y⁆ ∈ Hin := hcommIn n y hnK hyK 2 1 hfr.hn9 (by simpa using hb.frame.y3)
    have hedZ : Subgroup.zpowers d ⊔ Subgroup.zpowers e = E ⊓ F := by
      have hcard := Sec4.card_zpowers_sup_zpowers he3 (orderOf_eq_prime hb.hd3 hb.hd1)
        (fun h' => by
          have : e ∈ Subgroup.zpowers e ⊓ Subgroup.zpowers d :=
            Subgroup.mem_inf.mpr ⟨Subgroup.mem_zpowers e, h'⟩
          rw [hed, Subgroup.mem_bot] at this
          exact he1 this)
        (hb.hEab e heE d hb.hdE)
      exact Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hb.hdZ)
        (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨heE, heF⟩))) (by rw [hb.h9, hcard])
    have hZab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ F) :=
      ⟨⟨⟨fun a b => Subtype.ext (hb.hEab a (Subgroup.mem_inf.mp a.2).1 b
        (Subgroup.mem_inf.mp b.2).1)⟩⟩, fun z hz => hb.hE3 z (Subgroup.mem_inf.mp hz).1⟩
    obtain ⟨-, hcard27⟩ := Sec5.isElemAbelian_sup_zpowers hZab hfr.hnyZ (hb.hE3 _ hfr.hnyE)
      (fun a ha => hb.hEab a (Subgroup.mem_inf.mp ha).1 _ hfr.hnyE)
    have hEb : (E ⊓ F) ⊔ Subgroup.zpowers ⁅n, y⁆ = E :=
      Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.mpr hfr.hnyE))
        (by rw [hcard27, hb.h9, hb.hE27])
    have hEIn : E ≤ Hin := by
      rw [← hEb, ← hedZ]
      exact sup_le (sup_le (Subgroup.zpowers_le.mpr hdIn) (Subgroup.zpowers_le.mpr heIn))
        (Subgroup.zpowers_le.mpr hbIn)
    have hinn : ∀ e' ∈ E, ∀ hN : e' ∈ Subgroup.normalizer (K : Set G),
        ∃ w : K ⧸ aschbacherSolvableCore 3 K, ∀ z,
          Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨e', hN⟩) z = w * z * w⁻¹ := by
      intro e' he' hN
      obtain ⟨⟨e'', hN''⟩, hρ', he''⟩ := hEIn he'
      obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hρ'
      change e'' = e' at he''
      subst he''
      refine ⟨w, fun z => ?_⟩
      change ρ ⟨e'', hN⟩ z = _
      rw [← hw, MulAut.conj_apply]
    have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := fun a ha =>
      centralizer_le_normalizer_zpowers e
        (Subgroup.mem_centralizer_singleton_iff.mpr (hb.hEab a ha e heE))
    exact false_of_inner_of_isZ3PGLThreePi hD hEN hEH hb.hEab
      (fun z hz => exists_lBar_conj_eq_of_inner hD.mem_thetaComponentsAt hEN hEH hinn hz) hPGLK
  ·
    have hspor' := hspor
    obtain ⟨-, ⟨hM12p, -⟩, -⟩ := hspor'
    obtain ⟨φ⟩ := hM12
    obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hM12p φ
    obtain ⟨-, hEK9, -⟩ := facts_of_m12 h131 hspor hD ⟨φK⟩
    have hEK : ¬ E ⊓ K ≤ Subgroup.zpowers e := fun hle' => by
      have := Subgroup.card_le_of_le hle'
      rw [hEK9, card_zpowers_of_pow_three he3 he1] at this
      norm_num at this
    obtain ⟨-, hnK⟩ := hnorm hEK
    obtain ⟨-, hZK, hinner, -⟩ := hK18 _ ⟨φK⟩
    obtain ⟨m, hm⟩ := hinner (ρ ⟨n, hnK⟩) ⟨2, hρpow n hnK 2 hfr.hn9⟩
    have hm9 : m ^ 9 = 1 := by
      have h1 : MulAut.conj (m ^ 9) = 1 := by
        rw [map_pow, ← hm]
        exact hρpow n hnK 2 hfr.hn9
      have h2 : m ^ 9 ∈ Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have := congrArg (fun σ : MulAut _ => σ z) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc z * m ^ 9 = m ^ 9 * z * (m ^ 9)⁻¹ * m ^ 9 := by rw [this]
          _ = m ^ 9 * z := by group
      rw [hZK, Subgroup.mem_bot] at h2
      exact h2
    have hm3 : m ^ 3 = 1 := by
      have hmp : IsPGroup 3 (Subgroup.zpowers m) := by
        rintro ⟨u, hu⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        refine ⟨2, Subtype.ext ?_⟩
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
          show (((3 : ℕ) ^ 2 : ℕ) : ℤ) = ((9 : ℕ) : ℤ) by norm_num, zpow_natCast, hm9, one_zpow]
      obtain ⟨P, hP⟩ := hmp.exists_le_sylow
      have hexp : Monoid.exponent (P : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) = 3 :=
        (hM12D _ ⟨φK⟩ P).2.2.1
      have h1 := Monoid.pow_exponent_eq_one
        (⟨m, hP (Subgroup.mem_zpowers m)⟩ : (P : Subgroup (K ⧸ aschbacherSolvableCore 3 K)))
      rw [hexp] at h1
      simpa using congrArg Subtype.val h1
    have hn3C : n ^ 3 ∈ Sec4.thetaQuotCentralizer K := by
      refine Subgroup.mem_map.mpr ⟨⟨n, hnK⟩ ^ 3, ?_, by simp⟩
      change ρ (⟨n, hnK⟩ ^ 3) = 1
      rw [map_pow, hm, ← map_pow, hm3, map_one]
    have hn3E : n ^ 3 ∈ E := Subgroup.zpowers_le.mpr hb.hdE hfr.hn3d
    have hn3e : n ^ 3 ∈ Subgroup.zpowers e := by
      have : n ^ 3 ∈ ((E ⊓ Sec4.thetaQuotCentralizer K : Subgroup G) : Set G) :=
        Subgroup.mem_inf.mpr ⟨hn3E, hn3C⟩
      rw [← hCEset] at this
      exact this
    have h1 : n ^ 3 ∈ Subgroup.zpowers e ⊓ Subgroup.zpowers d :=
      Subgroup.mem_inf.mpr ⟨hn3e, hfr.hn3d⟩
    rw [hed, Subgroup.mem_bot] at h1
    exact hfr.hn3 h1

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
