module

public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
import CFSG.RankThree.PartTwo.Sec14.Ronan148DRank
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec13.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148D

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def lbMembers (A : Subgroup G) (a : G) : Set (Subgroup G) :=
  {K | K ∈ thetaComponentsAt 3 a ∧ ∃ (D : Subgroup G) (b d : G) (Lb : Subgroup G),
    IsHyperplane A D ∧ a ∈ D ∧ IsLBConfig A D b d Lb ∧ lB A D ≤ K}

theorem not_mem_zpowers_of_mem_omegaA' {A : Subgroup G} (hA : Late.IsE27 A) {a e : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    (he : Subgroup.zpowers e ∈ omegaA A) : a ∉ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hae
  obtain ⟨-, he3, -⟩ := zpowers_mem_omegaA_iff.mp he
  have hoe : orderOf e = 3 := by rwa [Nat.card_zpowers] at he3
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a ha) ha1
  exact hΩ (Desc143X.zpowers_eq_of_mem hoa hoe hae ▸ he)

section Members

theorem exists_mem_lbMembers (h48 : Sec4.Item4_8) {A L : Subgroup G} {c a : G}
    (h : Sec14Std G A c L) (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hc : IsLBConfig A D b d Lb) : ∃ K ∈ lbMembers A a, lB A D ≤ K := by
  have hab : a ∉ Subgroup.zpowers b :=
    not_mem_zpowers_of_mem_omegaA' h.isE27' ha ha1 hΩ hc.2.1
  obtain ⟨K, hK, hJK⟩ := Desc143X.exists_mem_le_residual h48 h hD hc haD ha1 hab
  rw [← Item148HJ.lB_eq_residual h hD hc] at hJK
  exact ⟨K, ⟨hK, D, b, d, Lb, hD, haD, hc, hJK⟩, hJK⟩

theorem lB_le_sSup (h48 : Sec4.Item4_8) {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    (ha : a ∈ A) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A) {D : Subgroup G}
    (hD : IsHyperplane A D) (haD : a ∈ D) : lB A D ≤ sSup (lbMembers A a) := by
  by_cases hconf : ∃ (b d : G) (Lb : Subgroup G), IsLBConfig A D b d Lb
  · obtain ⟨b, d, Lb, hc⟩ := hconf
    obtain ⟨K, hK, hDK⟩ := exists_mem_lbMembers h48 h ha ha1 hΩ hD haD hc
    exact hDK.trans (le_sSup hK)
  · push Not at hconf
    rw [lB_eq_bot hconf]
    exact bot_le

theorem member_cases (h134 : Item134) {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (hc : IsLBConfig A D b d Lb)
    (had : Subgroup.zpowers a = Subgroup.zpowers d) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 a) (hDK : lB A D ≤ K) :
    (K = lB A D ⊔ inSubgroup (aschbacherSolvableCore 3) K ∧
        Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) ∧
        (omegaA A).ncard ≠ 12) ∨
      (Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) CFSG.Blueprint.NativeSporadic.ON ∧
        (omegaA A).ncard = 12) := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA := h.isE27'
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨-, hd1⟩ := hc.ne_one hD hA
  have hdA : d ∈ A := hD.1 (hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hLb : Lb ∈ lA A b := hc.2.2.1 ▸ Set.mem_singleton Lb
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hc.2.1, mem_lA := hLb }
  have hres := Item148HJ.lB_eq_residual h hD hc
  obtain ⟨-, -, -, -, hdL, S, hdS, hSd⟩ := hc
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hKd : K ∈ thetaComponentsAt 3 d := by
    rwa [← thetaComponentsAt_congr (p := 3) (centralizer_singleton_eq_of_zpowers_eq had)]
  rw [hres] at hDK ⊢
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hS⟩ K hKd hDK with
    ⟨hKeq, htc, hΩ1⟩ | ⟨hKeq, htc, -, -, -, -, hΩ⟩ | ⟨htc, -, -, hΩ12⟩
  · refine Or.inl ⟨hKeq, htc, ?_⟩
    rw [hΩ1, Set.ncard_singleton]
    norm_num
  · refine Or.inl ⟨hKeq, htc, ?_⟩
    rcases hΩ with ⟨-, h3⟩ | ⟨-, -, -, -, -, -, -, -, h6, -⟩
    · rw [h3]; norm_num
    · rw [h6]; norm_num
  · exact Or.inr ⟨htc, hΩ12⟩

theorem false_of_commutator_mem {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {D Lb : Subgroup G} {b d : G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hc : IsLBConfig A D b d Lb) {K : Subgroup G} (hDK : lB A D ≤ K) {S : Subgroup G}
    (hAS : A ⊓ Lb ≤ S)
    (hKS : ∀ y ∈ K, ∀ s ∈ S, ⁅y, s⁆ ∈
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) : False := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  have hres := Item148HJ.lB_eq_residual h hD hc
  obtain ⟨e, he, hed, -⟩ := Item148HJ.exists_mem_not_mem_zpowers h hD hc
  obtain ⟨j, hj, hjθ⟩ := Item148HJ.exists_commutator_not_mem h hD hc he hed
  have heJ : e ∈ J := Item148HJ.inf_le_residual h hD hc he
  have hjK : j ∈ K := hDK (hres ▸ hj)
  have h1 := hKS j hjK e (hAS he)
  have hJC : J ≤ C := (Item148HJ.residual_le_centralizer hc).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD))
  have h5 : ⁅j, e⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj heJ) (J.inv_mem hj)) (J.inv_mem heJ)
  exact hjθ (Desc143X.residual_inf_le_theta h hD hc (hJC.trans (Sec6.le_normalizer_theta C))
    (Sec6.theta_solvable_and_not_dvd C).2 ⟨h5, h1⟩)

theorem commutator_mem_theta_of_ne_sup {a : G} {Y K₁ K₂ : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) (hK₁ : K₁ ∈ thetaComponentsAt 3 a)
    (hK₂ : K₂ ∈ thetaComponentsAt 3 a) (h₁ : Y ≠ K₁) (h₂ : Y ≠ K₂) {y : G} (hy : y ∈ Y)
    {g : G} (hg : g ∈ K₁ ⊔ K₂) :
    ⁅y, g⁆ ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  have hYC : Y ≤ C := le_centralizer_of_mem_thetaComponentsAt hY
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta C
  have hyC := hYC hy
  let S : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ⁅y, g⁆ ∈ T}
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨C.mul_mem hg₁ hg₂, ?_⟩
        have e : ⁅y, g₁ * g₂⁆ = ⁅y, g₁⁆ * (g₁ * ⁅y, g₂⁆ * g₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact T.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hCT hg₁) _).mp h₂)
      one_mem' := ⟨C.one_mem, by simp only [commutatorElement_def]; group; exact T.one_mem⟩
      inv_mem' := by
        rintro g ⟨hg, h₁⟩
        refine ⟨C.inv_mem hg, ?_⟩
        have e : ⁅y, g⁻¹⁆ = g⁻¹ * ⁅y, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hCT (C.inv_mem hg)) _).mp (T.inv_mem h₁) }
  have hKS : ∀ {K : Subgroup G}, K ∈ thetaComponentsAt 3 a → Y ≠ K → K ≤ S := by
    intro K hK hne ξ hξ
    exact ⟨le_centralizer_of_mem_thetaComponentsAt hK hξ,
      Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hY hK hne
        (Subgroup.commutator_mem_commutator hy hξ)⟩
  exact (sup_le (hKS hK₁ h₁) (hKS hK₂ h₂) hg).2

theorem le_sup_of_ne {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ thetaComponentsAt 3 a) (hK₂ : K₂ ∈ thetaComponentsAt 3 a)
    (hne : K₁ ≠ K₂) {D₁ D₂ L₁ L₂ : Subgroup G} {b₁ d₁ b₂ d₂ : G}
    (hD₁ : IsHyperplane A D₁) (haD₁ : a ∈ D₁) (hc₁ : IsLBConfig A D₁ b₁ d₁ L₁)
    (hD₁K : lB A D₁ ≤ K₁) (hD₂ : IsHyperplane A D₂) (haD₂ : a ∈ D₂)
    (hc₂ : IsLBConfig A D₂ b₂ d₂ L₂) (hD₂K : lB A D₂ ≤ K₂) : A ≤ K₁ ⊔ K₂ := by
  have hA := h.isE27'
  have hE₁K : A ⊓ L₁ ≤ K₁ :=
    (Item148HJ.inf_le_residual h hD₁ hc₁).trans ((Item148HJ.lB_eq_residual h hD₁ hc₁) ▸ hD₁K)
  have hE₂K : A ⊓ L₂ ≤ K₂ :=
    (Item148HJ.inf_le_residual h hD₂ hc₂).trans ((Item148HJ.lB_eq_residual h hD₂ hc₂) ▸ hD₂K)
  have h9₁ : Nat.card (A ⊓ L₁ : Subgroup G) = 9 :=
    (j2_point_facts (Item148HJ.sec14Std_of_isLBConfig h hc₁).toSec13Data
      (Item148HJ.j2_of_isLBConfig hc₁)).2.1
  have h9₂ : Nat.card (A ⊓ L₂ : Subgroup G) = 9 :=
    (j2_point_facts (Item148HJ.sec14Std_of_isLBConfig h hc₂).toSec13Data
      (Item148HJ.j2_of_isLBConfig hc₂)).2.1
  have hle : ¬ A ⊓ L₂ ≤ A ⊓ L₁ := by
    intro hle
    have heq : A ⊓ L₂ = A ⊓ L₁ := Subgroup.eq_of_le_of_card_ge hle (by rw [h9₁, h9₂])
    refine false_of_commutator_mem h hD₂ haD₂ hc₂ hD₂K (S := K₁) (heq ▸ hE₁K) fun y hy s hs => ?_
    exact Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK₂ hK₁ (Ne.symm hne)
      (Subgroup.commutator_mem_commutator hy hs)
  have hsup : (A ⊓ L₁) ⊔ (A ⊓ L₂) = A := by
    have hle₁ : A ⊓ L₁ ≤ (A ⊓ L₁) ⊔ (A ⊓ L₂) := le_sup_left
    have hlt : A ⊓ L₁ < (A ⊓ L₁) ⊔ (A ⊓ L₂) :=
      lt_of_le_of_ne hle₁ fun heq => hle (heq ▸ le_sup_right)
    have hdvd : Nat.card ((A ⊓ L₁) ⊔ (A ⊓ L₂) : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le (sup_le inf_le_left inf_le_left)
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have h9 : 9 ∣ Nat.card ((A ⊓ L₁) ⊔ (A ⊓ L₂) : Subgroup G) :=
      h9₁ ▸ Subgroup.card_dvd_of_le hle₁
    have hne' : Nat.card ((A ⊓ L₁) ⊔ (A ⊓ L₂) : Subgroup G) ≠ 9 := by
      intro h9'
      exact hlt.ne (Subgroup.eq_of_le_of_card_ge hle₁ (by rw [h9', h9₁]))
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    rw [hA.2, hik]
    rw [hik] at h9 hne'
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · norm_num at h9
    · norm_num at h9
    · exact absurd rfl hne'
    · norm_num
  rw [← hsup]
  exact sup_le_sup hE₁K hE₂K

theorem eq_or_eq_of_mem_lbMembers {A L : Subgroup G} {c a : G} (h : Sec14Std G A c L)
    {K₁ K₂ K₃ : Subgroup G} (hK₁ : K₁ ∈ lbMembers A a) (hK₂ : K₂ ∈ lbMembers A a)
    (hK₃ : K₃ ∈ lbMembers A a) (hne : K₁ ≠ K₂) : K₃ = K₁ ∨ K₃ = K₂ := by
  by_contra h3
  push Not at h3
  obtain ⟨hK₁a, D₁, b₁, d₁, L₁, hD₁, haD₁, hc₁, hD₁K⟩ := hK₁
  obtain ⟨hK₂a, D₂, b₂, d₂, L₂, hD₂, haD₂, hc₂, hD₂K⟩ := hK₂
  obtain ⟨hK₃a, D₃, b₃, d₃, L₃, hD₃, haD₃, hc₃, hD₃K⟩ := hK₃
  have hA12 := le_sup_of_ne h hK₁a hK₂a hne hD₁ haD₁ hc₁ hD₁K hD₂ haD₂ hc₂ hD₂K
  refine false_of_commutator_mem h hD₃ haD₃ hc₃ hD₃K (S := K₁ ⊔ K₂)
    (inf_le_left.trans hA12) fun y hy s hs => ?_
  exact commutator_mem_theta_of_ne_sup hK₃a hK₁a hK₂a h3.1 h3.2 hy hs

end Members

end CFSG.RankThree.PartTwo.Sec14.Ronan148D
