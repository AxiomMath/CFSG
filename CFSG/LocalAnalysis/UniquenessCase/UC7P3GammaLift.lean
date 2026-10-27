module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Input
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePointLifting
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree (gammaCore)
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
  (surjective_normalizer_image_of_sylow_intersection)

theorem ne_bot_of_one_le_pRank_aux {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
    {Q : Subgroup Y} (h : 1 ≤ CFSG.Open.pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup Y) ≤ 0 :=
    CFSG.SectionRank.pRank_le hp.out.one_lt fun E hE _ => by
      rw [le_bot_iff.mp hE, Subgroup.card_bot, pow_zero]
  omega

theorem one_le_pRank_of_isPGroup_ne_bot {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y]
    [Finite Y] {S : Subgroup Y} (hS : IsPGroup p S) (hS1 : S ≠ ⊥) :
    1 ≤ CFSG.Open.pRank p S := by
  have hdvd : p ∣ Nat.card S := by
    rcases hS.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hS1
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) p hdvd
  have hxo : orderOf (x : Y) = p := by rw [Subgroup.orderOf_coe, hx]
  have hxp : (x : Y) ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  refine CFSG.SectionRank.le_pRank hp.out.one_lt (E := Subgroup.zpowers (x : Y))
    ((Subgroup.zpowers_le).2 x.2) ⟨inferInstance, fun y hy => ?_⟩ ?_
  · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  · rw [Nat.card_zpowers, hxo, pow_one]

variable {J L : Type*} [Group J] [Finite J] [Group L] [Finite L]

theorem gammaCore_eq_top_of_central_cover (p : ℕ) [Fact p.Prime] (hJ : Group.IsPerfect J)
    (φ : J →* L) (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center J)
    (R : Sylow p J) (hL : gammaCore p 1 ⊤ ((R : Subgroup J).map φ) = ⊤) :
    gammaCore p 1 ⊤ (R : Subgroup J) = ⊤ := by
  classical
  set Γ : Subgroup J := gammaCore p 1 ⊤ (R : Subgroup J) with hΓ
  have hmap : ∀ X : Subgroup L, X ≤ (R : Subgroup J).map φ → 1 ≤ CFSG.Open.pRank p X →
      ∀ n ∈ Subgroup.normalizer (X : Set L), n ∈ Γ.map φ := by
    intro X hXR hrk n hn
    have hX1 : X ≠ ⊥ := ne_bot_of_one_le_pRank_aux hrk
    set S : Subgroup J := (R : Subgroup J) ⊓ X.comap φ with hS
    have hSmap : S.map φ = X := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact hs.2
      · intro hx
        obtain ⟨r, hr, hrx⟩ := hXR hx
        exact ⟨r, ⟨hr, Subgroup.mem_comap.mpr (hrx ▸ hx)⟩, hrx⟩
    have hS1 : S ≠ ⊥ := fun h => hX1 (by rw [← hSmap, h, Subgroup.map_bot])
    have hSp : IsPGroup p S := R.isPGroup'.to_inf_left
    have hSrk : 1 ≤ CFSG.Open.pRank p S := one_le_pRank_of_isPGroup_ne_bot hSp hS1
    have hker : φ.ker ≤ X.comap φ := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact X.one_mem
    have hSker : S ⊓ φ.ker = (R : Subgroup J) ⊓ φ.ker := by
      ext x
      simp only [hS, Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hker h.2⟩, h.2⟩⟩
    obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal R (N := φ.ker)
    have hinter : ∃ T : Sylow p φ.ker,
        (T : Subgroup φ.ker).map φ.ker.subtype = S ⊓ φ.ker := by
      refine ⟨T, ?_⟩
      rw [hSker, hT, Subgroup.subgroupOf_map_subtype]
      exact inf_of_le_left inf_le_right
    have hnorm := surjective_normalizer_image_of_sylow_intersection (Fact.out : p.Prime) φ hφ S
      hSp hinter
    rw [hSmap] at hnorm
    have hn' : n ∈ (Subgroup.normalizer (S : Set J)).map φ := by
      rw [hnorm]
      exact hn
    obtain ⟨m, hm, rfl⟩ := hn'
    exact ⟨m, Subgroup.subset_closure ⟨Subgroup.mem_top m, S, inf_le_left, hSrk, hm⟩, rfl⟩
  have htop : Γ.map φ = ⊤ := by
    rw [eq_top_iff, ← hL]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨-, X, hXR, hrk, hx⟩
    exact hmap X hXR hrk x hx
  have hsup : Γ ⊔ φ.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, htop, Subgroup.comap_top]
  have hΓn : Γ.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer (hZ.trans (Subgroup.center_le_normalizer _))
  have hcomm : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ ≤ Γ := by
    have hZ' : ⁅φ.ker, (⊤ : Subgroup J)⁆ = ⊥ :=
      Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hZ
    calc ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⁅Γ ⊔ φ.ker, (⊤ : Subgroup J)⁆ := by rw [hsup]
      _ = ⁅Γ, (⊤ : Subgroup J)⁆ ⊔ ⁅φ.ker, (⊤ : Subgroup J)⁆ := Subgroup.commutator_sup_right _ _ _
      _ ≤ Γ := by rw [hZ', sup_bot_eq]; exact Subgroup.commutator_le_left _ _
  have hperf : ⁅(⊤ : Subgroup J), (⊤ : Subgroup J)⁆ = ⊤ := by
    rw [← _root_.commutator_def]
    exact hJ.commutator_eq_top
  exact top_le_iff.mp (hperf ▸ hcomm)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
