module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJ

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open scoped commutatorElement

section Transvection

variable {P : Type*} [Group P]

theorem j217_isTransvectionOn_sq {φ : MulAut P} (h : IsTransvectionOn φ) :
    IsTransvectionOn (φ * φ) := by
  obtain ⟨hcard, hfix⟩ := h
  have hn : ∀ z : P, z⁻¹ * φ z ∈ commOf φ := fun z => mem_commOf φ z
  have hnfix : ∀ z : P, φ (z⁻¹ * φ z) = z⁻¹ * φ z := fun z =>
    (mem_fixedSubgroupOf φ _).mp (hfix (hn z))
  have hn3 : ∀ z : P, (z⁻¹ * φ z) ^ 3 = 1 := by
    intro z
    have := pow_card_eq_one' (G := ↥(commOf φ)) (x := ⟨z⁻¹ * φ z, hn z⟩)
    rw [hcard] at this
    exact congrArg Subtype.val this
  have hsq : ∀ z : P, (φ * φ) z = z * ((z⁻¹ * φ z) * (z⁻¹ * φ z)) := by
    intro z
    have h1 : φ z = z * (z⁻¹ * φ z) := by group
    have h2 : (φ * φ) z = φ (φ z) := rfl
    have h3 : φ (φ z) = φ z * (z⁻¹ * φ z) := by
      have := congrArg φ h1
      rw [map_mul, hnfix z] at this
      exact this
    rw [h2, h3]
    group
  have hcomm : commOf (φ * φ) = commOf φ := by
    apply le_antisymm
    · rw [commOf, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      show a⁻¹ * (φ * φ) a ∈ commOf φ
      rw [hsq a]
      have : a⁻¹ * (a * ((a⁻¹ * φ a) * (a⁻¹ * φ a))) = (a⁻¹ * φ a) * (a⁻¹ * φ a) := by group
      rw [this]
      exact Subgroup.mul_mem _ (hn a) (hn a)
    · rw [commOf, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      have h3 : a⁻¹ * (φ * φ) a = (a⁻¹ * φ a) * (a⁻¹ * φ a) := by
        rw [hsq a]; group
      have h4 : a⁻¹ * φ a = (a⁻¹ * (φ * φ) a) * (a⁻¹ * (φ * φ) a) := by
        rw [h3]
        have hna := hn3 a
        generalize a⁻¹ * φ a = n at hna ⊢
        calc n = n ^ 3 * n := by rw [hna, one_mul]
          _ = n * n * (n * n) := by simp [pow_succ, mul_assoc]
      show a⁻¹ * φ a ∈ commOf (φ * φ)
      rw [h4]
      exact Subgroup.mul_mem _ (mem_commOf (φ * φ) a) (mem_commOf (φ * φ) a)
  refine ⟨by rw [hcomm]; exact hcard, ?_⟩
  rw [hcomm]
  intro x hx
  rw [mem_fixedSubgroupOf]
  have hx' : φ x = x := (mem_fixedSubgroupOf φ x).mp (hfix hx)
  show φ (φ x) = x
  rw [hx', hx']

end Transvection

section Normalizer

variable {G : Type} [Group G] [Finite G] {A E U : Subgroup G} {c : G} {L : Subgroup G}


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem CoverOut.normalizer_of_fixes (h45 : Sec4.Item4_5) (h : CoverOut A E U c L) {a : G}
    (hfr : Frame217 E c L a) {d : G} {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 d)
    (hIJ : iCore L a ≤ J) {t : G} (htd : t * d * t⁻¹ = d)
    (htI : ∀ y ∈ A ⊓ iCore L a, t * y * t⁻¹ = y) : t ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨⟨e⟩, hIA, hIcen, hIcomm, hcardAI, hAC⟩ := h.iCore_structure h45 hfr
  have hqn : t ∈ Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    have hqC : t ∈ Subgroup.centralizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hc : Commute d t := by
        have h1 : t * d = d * t := by
          calc t * d = t * d * t⁻¹ * t := by group
            _ = d * t := by rw [htd]
        exact h1.symm
      exact (hc.zpow_left k).eq
    exact Subgroup.centralizer_le_normalizer _ hqC
  have hJ' := CFSG.RankThree.PartOne.Sec12TwoAssembly.conj_mem_thetaComponentsAt
    Nat.prime_three hqn hJ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hJ' hJ hne
  have hI₀ : ∀ y ∈ A ⊓ iCore L a, y ∈ J.map (MulAut.conj t).toMonoidHom := by
    intro y hy
    refine ⟨y, hIJ hy.2, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact htI y hy
  have hbot : A ⊓ iCore L a = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hwI : w ∈ iCore L a := hw.2
    have hcen : ∀ x ∈ iCore L a, w * x = x * w := by
      intro x hx
      have h1 : ⁅w, x⁆ ∈ ⁅J.map (MulAut.conj t).toMonoidHom, J⁆ :=
        Subgroup.commutator_mem_commutator (hI₀ w hw) (hIJ hx)
      have h2 := hcomm h1
      have h3 : ⁅w, x⁆ ∈ iCore L a := by
        rw [commutatorElement_def]
        exact (iCore L a).mul_mem ((iCore L a).mul_mem ((iCore L a).mul_mem hwI hx)
          ((iCore L a).inv_mem hwI)) ((iCore L a).inv_mem hx)
      have h5 : ⁅w, x⁆ ∈ inSubgroup (aschbacherSolvableCore 3) J := by
        rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hJ]
        exact ⟨hIJ h3, h2⟩
      have h6 : ⁅w, x⁆ ∈ iCore L a ⊓ inSubgroup (aschbacherSolvableCore 3) J := ⟨h3, h5⟩
      rw [inf_theta_eq_bot_of_A6 hIJ e, Subgroup.mem_bot] at h6
      exact commutatorElement_eq_one_iff_mul_comm.mp h6
    exact Subgroup.mem_bot.2 (hIcen w hwI hcen)
  rw [hbot, Subgroup.card_bot] at hcardAI
  omega

end Normalizer

section Contradiction

variable {G : Type} [Group G] [Finite G]

theorem j217_mem_zpowers_of_cube {g x : G} (hg : g ^ 3 = 1) (hx : x ∈ Subgroup.zpowers g)
    (hx1 : x ≠ 1) : g ∈ Subgroup.zpowers x := by
  rcases mem_zpowers_of_pow_three hg hx with h | h | h
  · exact absurd h hx1
  · rw [← h]
    exact Subgroup.mem_zpowers x
  · have hgg : g = x ^ 2 := by
      rw [h]
      calc g = g ^ 3 * g := by rw [hg, one_mul]
        _ = (g ^ 2) ^ 2 := by group
    rw [hgg]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2

theorem j217_false_of_card_inf_le {A F J : Subgroup G} {d t : G} (hdF : d ∈ F) (hFA : F ≤ A)
    (hF27 : Nat.card F = 27) (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) (hdJ : d ∉ J)
    (htJ : t ∈ Subgroup.normalizer (J : Set G))
    (hfix : ∀ y ∈ A, (t * y * t⁻¹ = y ↔ y ∈ F))
    (htn : ∀ y ∈ A, ∃ n : ℤ, t * y * t⁻¹ = y * d ^ n)
    (h27 : 27 ≤ Nat.card (A ⊓ J : Subgroup G)) : False := by
  have hAJF : A ⊓ J ≤ F ⊓ J := by
    rintro y ⟨hyA, hyJ⟩
    refine ⟨?_, hyJ⟩
    obtain ⟨n, hn⟩ := htn y hyA
    have hty : t * y * t⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 htJ y).1 hyJ
    have hdn : d ^ n ∈ J := by
      have : d ^ n = y⁻¹ * (t * y * t⁻¹) := by rw [hn]; group
      rw [this]
      exact J.mul_mem (J.inv_mem hyJ) hty
    by_cases h1 : d ^ n = 1
    · exact (hfix y hyA).1 (by rw [hn, h1, mul_one])
    · exfalso
      apply hdJ
      have hmem : d ∈ Subgroup.zpowers (d ^ n) :=
        j217_mem_zpowers_of_cube hd3 (Subgroup.zpow_mem_zpowers d n) h1
      exact Subgroup.zpowers_le.2 hdn hmem
  have hdisj : Disjoint (F ⊓ J) (Subgroup.zpowers d) := by
    rw [Subgroup.disjoint_def]
    rintro x ⟨-, hxJ⟩ hxd
    by_contra hx1
    apply hdJ
    have hmem : d ∈ Subgroup.zpowers x :=
      j217_mem_zpowers_of_cube hd3 hxd hx1
    exact Subgroup.zpowers_le.2 hxJ hmem
  have hcard := card_mul_le_card_sup_of_disjoint (F ⊓ J) (Subgroup.zpowers d) hdisj
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  rw [Nat.card_zpowers, hord] at hcard
  have hsup : (F ⊓ J) ⊔ Subgroup.zpowers d ≤ F :=
    sup_le inf_le_left (Subgroup.zpowers_le.2 hdF)
  have hle := Subgroup.card_le_of_le hsup
  have hle2 := Subgroup.card_le_of_le hAJF
  omega

end Contradiction

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
