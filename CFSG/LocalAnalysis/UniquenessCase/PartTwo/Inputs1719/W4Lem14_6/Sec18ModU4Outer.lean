module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4
public import CFSG.Quasithin.Background.E3MParamAttained
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
open CFSG.HardMathSupport.U4FF (NaturalSU4 NaturalOmega6 disp)
open scoped commutatorElement Pointwise

@[expose] def K146ModU4Omega6 : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsU4 ↥S n → 1 < n → IsIrrOn S ⊤ ⊥ → NaturalOmega6 n S → n ≤ E3.mParam N

@[expose] def K146ModU4Outer : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) →
    ∀ (N S : Subgroup (MulAut U)) (n : ℕ), S ≤ N → (S.subgroupOf N).Normal →
      IsU4 ↥S n → 1 < n → IsIrrOn S ⊤ ⊥ →
      (∀ t ∈ S, t ≠ 1 → t * t = 1 →
        4 * n + 2 ≤ rkIdx (fixV (Subgroup.zpowers t))) →
      E3.mParam N ≤ 3 * n + 2 →
      n = 2 ∧ 3 * n + 2 < 2 * E3.mParam N ∧ E3.aParam N + 2 < E3.mParam N

private theorem isU4Group_of_isU4 {U : Type} [CommGroup U] [Finite U]
    {S : Subgroup (MulAut U)} {n : ℕ} (h : IsU4 ↥S n) :
    CFSG.LocalAnalysis.RankThreeUC.IsU4Group n S := by
  have hC := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨q, hv, hp, he, ⟨φ⟩⟩ :=
    KSExact.exists_twistedA_of_statedClassicalModel_PSU (m := 3) hC
  exact ⟨⟨_, hv⟩, ⟨q, hp, he, rfl⟩, ⟨φ⟩⟩

theorem two_mul_le_mParam_of_naturalSU4
    (U : Type) [CommGroup U] [Finite U] (hU2 : ∀ u : U, u ^ 2 = 1)
    (N S : Subgroup (MulAut U)) (n : ℕ)
    (hSN : S ≤ N) (hSnormal : (S.subgroupOf N).Normal)
    (hU4 : IsU4 ↥S n) (hirr : IsIrrOn S ⊤ ⊥) (hnat : NaturalSU4 n S) :
    2 * n ≤ E3.mParam N := by
  classical
  haveI : Fact (∀ s : U, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hU2 s⟩
  have hevS : Even (Nat.card ↥S) := Thm14_5.even_card_of_isU4 hU4
  have hevN : Even (Nat.card N) := by
    rw [even_iff_two_dvd] at hevS ⊢
    exact hevS.trans (Subgroup.card_dvd_of_le hSN)
  obtain ⟨t₀, ht₀N, ht₀o, -⟩ := CFSG.Quasithin.E3.exists_involution_rkIdx_fixV_eq_mParam N hevN
  refine le_mParam_of_forall_involutions N (2 * n) hevN ⟨t₀, ht₀N, ht₀o⟩ ?_
  intro t htN hto
  have ht2 : t * t = 1 := by rw [← pow_two, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by rintro rfl; rw [orderOf_one] at hto; omega
  have hnorm : t ∈ Subgroup.normalizer (S : Set (MulAut U)) :=
    (CFSG.Quasithin.BlueprintB2.normal_subgroupOf_iff_le_normalizer hSN).mp hSnormal htN
  have hdisp : 2 * n ≤ disp t :=
    Thm14_5.two_mul_le_disp_of_naturalSU4 hirr hnat ht2 ht1 hnorm
  simpa only [← Thm14_5.rkIdx_fixV_zpowers_eq_disp] using hdisp

theorem k146ModU4_of_inputs (hdich : CFSG.HardMathSupport.U4FF.U4RankDichotomy)
    (hO : K146ModU4Omega6) (hout : K146ModU4Outer) : K146ModU4 := by
  intro U _ _ hU2 N S n hSN hSnormal hU4 hn hirr hm
  classical
  haveI : Fact (∀ s : U, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hU2 s⟩
  have hn1 : 1 ≤ n := le_of_lt hn
  have hU4G : CFSG.LocalAnalysis.RankThreeUC.IsU4Group n S := isU4Group_of_isU4 hU4
  have hirrG : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn S := fun J hJ =>
    hirr.2.2.2 J hJ bot_le le_top
  rcases hdich U n S hn1 hU4G hirrG with hnat | hbig
  · rcases hnat with hSU4 | hOm6
    · obtain ⟨hSUn, hNatSUn⟩ := Thm14_5.isSUn_natSUn_of_naturalSU4 hSU4
      exact Or.inl ⟨hSUn, hNatSUn,
        two_mul_le_mParam_of_naturalSU4 U hU2 N S n hSN hSnormal hU4 hirr hSU4⟩
    · obtain ⟨hOm, hNatOm⟩ := Thm14_5.isOmegaMinus_natOmegaMinus_of_naturalOmega6 hOm6
      exact Or.inr (Or.inl ⟨hOm, hNatOm, hO U hU2 N S n hSN hSnormal hU4 hn hirr hOm6⟩)
  · have hbig' : ∀ t ∈ S, t ≠ 1 → t * t = 1 →
        4 * n + 2 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
      intro t ht ht1 ht2
      have hdisp : 4 * n + 2 ≤ disp t := hbig t ht ht1 ht2
      simpa only [← Thm14_5.rkIdx_fixV_zpowers_eq_disp] using hdisp
    exact Or.inr (Or.inr (hout U hU2 N S n hSN hSnormal hU4 hn hirr hbig' hm))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
