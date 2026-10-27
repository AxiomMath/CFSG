module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829Red
public import CFSG.Quasithin.Vol2.Ch8Sec2Steps
public import CFSG.Quasithin.Background.E2TwoC
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
public import CFSG.Quasithin.Background.HSecQuot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative

section L829CS1

variable {G : Type} [Group G] [Finite G]

theorem k_eq_two_cocode_829 {T L I : Subgroup G} [IsMulCommutative ↥(fsuV T I)] {h : G} {k : ℕ}
    (hC5 : Concl825 T L I h k) (hcoc : Row711M24Cocode T L I) : k = 2 := by
  obtain ⟨h1, -, -, -, -, -, h7, -, -, -, -, -, -⟩ := hC5
  have h2 := (h7 hcoc).1
  rw [h1] at h2
  exact_mod_cast h2

theorem concl822_cocode_829 {T L I H : Subgroup G} {h : G} {k : ℕ}
    (hC : Concl822 T L I H h k) (hk : k = 2) :
    IsPSL 2 2 2 (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) ∧
      ∃ m : ℕ, E1.nParam H = ((2 * m : ℕ) : ℕ∞) := by
  subst hk
  obtain ⟨-, -, -, -, -, -, -, -, hm, hcases, -, -, -, -, -, -, -, -, -, -, -⟩ := hC
  obtain ⟨m, hm'⟩ := hm
  refine ⟨?_, m, hm'⟩
  rcases hcases with ⟨hk1, -⟩ | hP | hS
  · omega
  · exact hP
  · obtain ⟨-, a, -, -, -, -, hf, -, -⟩ := hS
    omega

theorem not_isSolvable_of_isPSL_two_two_two_829 {X : Type} [Group X] (h : IsPSL 2 2 2 X) :
    ¬ Group.IsSolvable X := by
  obtain ⟨-, K, hKF, hKfin, hK, ⟨e⟩⟩ := h
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  obtain ⟨-, hns⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable h4
  intro hX
  apply hns
  have hiso : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hsur : Function.Surjective hiso.toMonoidHom := hiso.surjective
  haveI := hX
  exact Group.isSolvable_of_surjective hsur

theorem not_isSolvable_H_cocode_829 {T L I H : Subgroup G} {h : G} {k : ℕ}
    (hVH : fsuV T I ≤ H) (hh : h ∈ H) (hC : Concl822 T L I H h k) (hk : k = 2) :
    ¬ Group.IsSolvable ↥H := by
  intro hs
  haveI := hs
  have hIH : ch82I (fsuV T I) h ≤ H := ch82I_le_829 hVH hh
  have hsI : Group.IsSolvable ↥(ch82I (fsuV T I) h) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hIH)
  have hsQ : Group.IsSolvable
      (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h)) := by
    haveI := hsI
    exact Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  exact not_isSolvable_of_isPSL_two_two_two_829 (concl822_cocode_829 hC hk).1 hsQ

theorem e22_inst_cocode_829 (hE22 : E2.E22StatementC) {H T M : Subgroup G}
    (hmin : MinParabolic H T M) (hSQ : SQTKGroup ↥H) (hns : ¬ Group.IsSolvable ↥H) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ E2.E22CasesNoN H T M K ∧
      E2.E22NParamCases H T M K := by
  obtain ⟨⟨K, hKc, hHK, hq, hc⟩, hSQs⟩ := hE22.1 G H T M hmin hSQ hns
  exact ⟨K, hKc, hHK, hq, hc, hE22.2 G H T M K hmin hSQ hns hKc hHK hq hc hSQs⟩

@[expose] def E22Surv1a (H T M K : Subgroup G) : Prop :=
  kerIn M H = pCoreOf 2 H ∧ (∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) ∧
    ∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥(E2.star M H K) ∨ IsSz n ↥(E2.star M H K)) ∧
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))

@[expose] def E22Surv2a (H T M K : Subgroup G) : Prop :=
  T ≤ Subgroup.normalizer (K : Set G) ∧
    (∀ x : G, x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
    ∃ n : ℕ, E2.IsBenderOf n ↥(E2.star M H K) ∧ E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))

@[expose] def E22Surv2b (H T M K : Subgroup G) : Prop :=
  T ≤ Subgroup.normalizer (K : Set G) ∧
    (∀ x : G, x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
    ∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥(E2.star M H K) ∨ E2.IsSp4Prime n ↥(E2.star M H K)) ∧
      E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) ∧
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))

theorem surv_cocode_829 {H T M K : Subgroup G} {m : ℕ}
    (hn : E1.nParam H = ((2 * m : ℕ) : ℕ∞)) (hc : E2.E22CasesNoN H T M K)
    (hp : E2.E22NParamCases H T M K) :
    E22Surv1a H T M K ∨ E22Surv2a H T M K ∨ E22Surv2b H T M K := by
  dsimp only [E2.E22CasesNoN] at hc
  dsimp only [E2.E22NParamCases] at hp
  rcases hc with ⟨hJ, t, ht, hne, hM, hAB⟩ | ⟨hTN, hJ2, h2⟩
  · rcases hAB with ⟨n, hn2, hty, hB⟩ | ⟨p, hp', hp8, hK, hMK, h8⟩
    · exact Or.inl ⟨hJ, ⟨t, ht, hne, hM⟩, n, hn2, hty, hB⟩
    · exfalso
      have h1 : E1.nParam H = 1 := (hp.1 hJ ⟨t, ht, hne, hM⟩).2 p hp' hp8 hK hMK h8
      rw [hn] at h1
      have h2m : 2 * m = 1 := by exact_mod_cast h1
      omega
  · have hp2 := hp.2 hTN hJ2
    rcases h2 with ⟨n, hB, hBor⟩ | ⟨n, hn1, hX, hD, hBor⟩ |
        ⟨p, e, hp', hp3, he, hpe, hK, hMK, h8⟩ | ⟨p, hp', hp2', hcond, hMK⟩
    · exact Or.inr (Or.inl ⟨hTN, hJ2, n, hB, hBor⟩)
    · exact Or.inr (Or.inr ⟨hTN, hJ2, n, hn1, hX, hD, hBor⟩)
    · exfalso
      have h1 : E1.nParam H = 1 := hp2.2.2.1 p e hp' hp3 he hpe hK hMK h8
      rw [hn] at h1
      have h2m : 2 * m = 1 := by exact_mod_cast h1
      omega
    · exfalso
      have h1 : E1.nParam H = 1 := hp2.2.2.2 p hp' hp2' hcond hMK
      rw [hn] at h1
      have h2m : 2 * m = 1 := by exact_mod_cast h1
      omega

theorem step2_entry_cocode_829 (hE22 : E2.E22StatementC) {T L I H : Subgroup G}
    [IsMulCommutative ↥(fsuV T I)] {h : G} {k : ℕ}
    (hVH : fsuV T I ≤ H) (hh : h ∈ H) (hmin : MinParabolic H T (H ⊓ fsuM T L))
    (hSQ : SQTKGroup ↥H) (hC5 : Concl825 T L I h k) (hcoc : Row711M24Cocode T L I)
    (hC : Concl822 T L I H h k) :
    ∃ K : Subgroup G, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧
      (E22Surv1a H T (H ⊓ fsuM T L) K ∨ E22Surv2a H T (H ⊓ fsuM T L) K ∨
        E22Surv2b H T (H ⊓ fsuM T L) K) := by
  have hk : k = 2 := k_eq_two_cocode_829 hC5 hcoc
  have hns := not_isSolvable_H_cocode_829 hVH hh hC hk
  obtain ⟨K, hKc, hHK, hq, hcases, hparam⟩ := e22_inst_cocode_829 hE22 hmin hSQ hns
  obtain ⟨-, m, hm⟩ := concl822_cocode_829 hC hk
  exact ⟨K, hKc, hHK, hq, surv_cocode_829 hm hcases hparam⟩

end L829CS1

end CFSG.Quasithin.H13
