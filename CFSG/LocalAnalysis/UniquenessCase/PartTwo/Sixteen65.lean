module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Case
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67Wreath
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Unique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenUniqueMax
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s1665_centralizer_le_of_mem (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) {x : G} (hxM : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V hV L) {u : G}
    (hu : u ∈ wSub V₀ V hV L ∨ u ∈ conjSubgroup (wSub V₀ V hV L) x) (hu1 : u ≠ 1) :
    centralizer ({u} : Set G) ≤ D.M := by
  have key : ∀ u ∈ wSub V₀ V hV L, u ≠ 1 → centralizer ({u} : Set G) ≤ D.M := by
    intro u huW hu1
    have huniq : UniqueMax D.M (D.M ⊓ centralizer ({u} : Set G)) :=
      hs.2.unique₁ u (Subgroup.mem_sup_left huW) hu1
    have huV : u ∈ V := preTil_le V₀ V hV (wTil V₀ V hV L) huW
    have hu2 : u ^ (2 ^ 1) = 1 := by simpa using hV.2 u huV
    exact (centralizer_le_of_uniqueMax D.maxLocal hu1 ⟨1, hu2⟩ huniq).1
  rcases hu with huW | huWx
  · exact key u huW hu1
  · have huxW : x * u * x⁻¹ ∈ wSub V₀ V hV L := mem_conjSubgroup_iff.mp huWx
    have hux1 : x * u * x⁻¹ ≠ 1 := by
      intro h
      apply hu1
      have : u = x⁻¹ * (x * u * x⁻¹) * x := by group
      rw [this, h]
      simp
    have hC := key (x * u * x⁻¹) huxW hux1
    intro c hc
    have hcx : x * c * x⁻¹ ∈ centralizer ({x * u * x⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      calc (x * c * x⁻¹) * (x * u * x⁻¹) = x * (c * u) * x⁻¹ := by group
        _ = x * (u * c) * x⁻¹ := by rw [hc]
        _ = (x * u * x⁻¹) * (x * c * x⁻¹) := by group
    have hcxM : x * c * x⁻¹ ∈ D.M := hC hcx
    have : c = x⁻¹ * (x * c * x⁻¹) * x := by group
    rw [this]
    exact D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) hcxM) hxM

theorem s1665_normalizer_le_of_generic (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {x : G}
    (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M V₀ V hV L) {U : Subgroup G} (hUV : U ≤ V)
    (hU : Nat.card U = 4) (hU₁ : U ⊓ wSub V₀ V hV L = ⊥)
    (hU₂ : U ⊓ conjSubgroup (wSub V₀ V hV L) x = ⊥) :
    normalizer (U : Set G) ≤ D.M := by
  have hinf : wSub V₀ V hV L ⊓ conjSubgroup (wSub V₀ V hV L) x = ⊥ := by
    rw [s1667_inf_conj_eq D hS hs.1 hxM hxn, h0]
  have hsup : wSub V₀ V hV L ⊔ conjSubgroup (wSub V₀ V hV L) x = V :=
    s1667_sup_conj_eq D h1217 hS hs.1 hxM hxn
  have hWcard : Nat.card (wSub V₀ V hV L) = 4 := by
    have hV0 : Nat.card V₀ = 1 := by rw [h0, Subgroup.card_bot]
    have h := s1667_card_wSub D hS hs.1
    rw [hV0, mul_one] at h
    exact h
  have hW₂card : Nat.card (conjSubgroup (wSub V₀ V hV L) x) = 4 := by
    rw [E3.card_conjSubgroup]
    exact hWcard
  have hne : wSub V₀ V hV L ≠ conjSubgroup (wSub V₀ V hV L) x := by
    intro heq
    have hbot : wSub V₀ V hV L = ⊥ := by
      have h1 : wSub V₀ V hV L ⊓ conjSubgroup (wSub V₀ V hV L) x = wSub V₀ V hV L := by
        rw [← heq, inf_idem]
      rw [← h1, hinf]
    have h2 : Nat.card (wSub V₀ V hV L) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have h3sig : 3 ∈ D.sig := by
    rw [hs.1.2.2.2]
    exact Set.mem_singleton 3
  obtain ⟨E, hEM, hEea, hEcard⟩ := c23_exists_elemAbelian_card_pow (p := 3) (M := D.M) (k := 3)
    (by norm_num) (by rw [UC6.groupPRank_eq_pRank]; exact hSg.three_le 3 h3sig)
  have hodd : Odd (Nat.card E) := by rw [hEcard]; norm_num
  have hfix : ∀ a ∈ E, conjSubgroup (wSub V₀ V hV L) a = wSub V₀ V hV L ∧
      conjSubgroup (conjSubgroup (wSub V₀ V hV L) x) a = conjSubgroup (wSub V₀ V hV L) x :=
    s1667_forall_conj_eq_of_odd (W₁ := wSub V₀ V hV L)
      (W₂ := conjSubgroup (wSub V₀ V hV L) x) hne hodd
      (fun a ha => s1667_conj_cases D hS hs.1 hxM hxn (hEM ha))
  have hrel : (normalizer (U : Set G)).relIndex E ≤ 3 :=
    s1667_relIndex_normalizer_le_three (W₁ := wSub V₀ V hV L)
      (W₂ := conjSubgroup (wSub V₀ V hV L) x) (E := E) (U := U)
      hV hsup hinf hWcard hW₂card hEea.isPGroup (fun e he => (hfix e he).1)
      (fun e he => (hfix e he).2) hUV hU hU₁ hU₂
  let F : Subgroup G := E ⊓ normalizer (U : Set G)
  have hFle : F ≤ E := inf_le_left
  have hrelF : F.relIndex E ≤ 3 :=
    (Subgroup.inf_relIndex_left (H := E) (K := normalizer (U : Set G))).trans_le hrel
  have hFcard : Nat.card F * F.relIndex E = 27 := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := E)
    rw [inf_eq_left.2 hFle] at h
    rw [mul_comm (Nat.card F) (F.relIndex E), h, hEcard]
    norm_num
  have h9 : 9 ≤ Nat.card F := by
    have h273 : 27 ≤ Nat.card F * 3 := by
      calc 27 = Nat.card F * F.relIndex E := hFcard.symm
        _ ≤ Nat.card F * 3 := Nat.mul_le_mul_left _ hrelF
    omega
  have hFc : ¬ IsCyclic ↥F := by
    intro hcyc
    have hexp : Monoid.exponent ↥F ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun y : ↥F => by
        have hy := (hEea.mono hFle).2 (y : G) y.2
        exact Subtype.ext (by simpa using hy)
    haveI : IsCyclic ↥F := hcyc
    rw [IsCyclic.exponent_eq_card] at hexp
    have : Nat.card F ≤ 3 := Nat.le_of_dvd (by norm_num) hexp
    omega
  have huniq : UniqueMax D.M (D.M ⊓ normalizer (U : Set G)) :=
    c23_uniqueMax_of_noncyclic D h61 h3sig (hEea.mono hFle).isPGroup hFc
      (le_inf (hFle.trans hEM) inf_le_right) inf_le_left
  have hUng : U ≠ ⊥ := by
    intro hb
    have h1 : Nat.card U = 1 := by rw [hb, Subgroup.card_bot]
    omega
  have hUpg : IsPGroup 2 U := hV.isPGroup.to_le hUV
  have hTwoLocal : IsTwoLocal (normalizer (U : Set G)) := ⟨U, hUng, hUpg, rfl⟩
  exact uc22p22p_le_of_uniqueMax huniq hTwoLocal inf_le_right

theorem s1665_centralizer_le_of_card_four (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h1217 : R1217 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hs : Sit1665 D V₀ V hV L) (h0 : V₀ = ⊥) {U : Subgroup G}
    (hUV : U ≤ V) (hU : Nat.card U = 4) :
    centralizer (U : Set G) ≤ D.M := by
  obtain ⟨x, hxM, hxn⟩ :=
    c23_exists_mem_not_nBar D hS.setting.hyp151 hV hs.1.2.2.1
  by_cases h1 : U ⊓ wSub V₀ V hV L = ⊥
  · by_cases h2 : U ⊓ conjSubgroup (wSub V₀ V hV L) x = ⊥
    · have hN := s1665_normalizer_le_of_generic D hSg h61 h1217 hS hs h0 hxM hxn hUV hU h1 h2
      exact (Subgroup.centralizer_le_normalizer (U : Set G)).trans hN
    · obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h2
      have huU : (u : G) ∈ U := (Subgroup.mem_inf.mp u.2).1
      have huW : (u : G) ∈ conjSubgroup (wSub V₀ V hV L) x := (Subgroup.mem_inf.mp u.2).2
      have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
      have hC := s1665_centralizer_le_of_mem D hS hs hxM hxn (Or.inr huW) hu1'
      exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huU)).trans hC
  · obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h1
    have huU : (u : G) ∈ U := (Subgroup.mem_inf.mp u.2).1
    have huW : (u : G) ∈ wSub V₀ V hV L := (Subgroup.mem_inf.mp u.2).2
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hC := s1665_centralizer_le_of_mem D hS hs hxM hxn (Or.inl huW) hu1'
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huU)).trans hC

theorem r16_65_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h1217 : R1217 D) :
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Sit1665 D V₀ V hV L → V₀ = ⊥ → (2 : ℕ∞) < rMV D.M V := by
  intro V₀ V L hV hS hs h0
  suffices h : (3 : ℕ∞) ≤ rMV D.M V by
    exact lt_of_lt_of_le (by norm_num : (2 : ℕ∞) < 3) h
  unfold rMV
  refine le_iInf₂ fun U hU => ?_
  suffices h3 : (3 : ℕ) ≤ E3.mQuot V U by exact_mod_cast h3
  by_contra hcon
  push Not at hcon
  have hm2 : E3.mQuot V U ≤ 2 := by omega
  have hVcard : Nat.card V = 16 := by
    have h := s1667_card_eq D h1217 hS hs.1
    rw [h0] at h
    simpa using h
  have hVU : Nat.card V = 2 ^ E3.mQuot V U * Nat.card U :=
    E3.card_eq_two_pow_mul hV.isPGroup hU.1
  have hpow : 2 ^ E3.mQuot V U ≤ 4 := by
    calc 2 ^ E3.mQuot V U ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
      _ = 4 := by norm_num
  have hU4 : 4 ≤ Nat.card U := by
    have h16 : 16 ≤ Nat.card U * 4 := by
      calc 16 = Nat.card V := hVcard.symm
        _ = 2 ^ E3.mQuot V U * Nat.card U := hVU
        _ ≤ 4 * Nat.card U := Nat.mul_le_mul_right _ hpow
        _ = Nat.card U * 4 := by ring
    omega
  have hUpg : IsPGroup 2 U := hV.isPGroup.to_le hU.1
  obtain ⟨H', hH'card⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (G := ↥U) (p := 2) (n := 2) (by norm_num) hUpg (by simpa using hU4)
  let U' : Subgroup G := H'.map U.subtype
  have hU'U : U' ≤ U := Subgroup.map_subtype_le H'
  have hU'card : Nat.card U' = 4 := by
    change Nat.card (H'.map U.subtype) = 4
    rw [Subgroup.card_map_of_injective U.subtype_injective, hH'card]
    norm_num
  exact hU.2 ((Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU'U)).trans
    (s1665_centralizer_le_of_card_four D hSg h61 h1217 hS hs h0 (hU'U.trans hU.1) hU'card))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
