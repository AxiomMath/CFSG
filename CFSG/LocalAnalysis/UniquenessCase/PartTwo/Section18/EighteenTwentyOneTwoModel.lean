module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankD
import CFSG.LieType.Universal.Unitary.SiegelRadical
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelTv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.LocalAnalysis.RankThreeUC CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

private theorem finrank_commSp_eq_two_T3J3 (hσ : IsUnitaryInvolution σ)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : 2 ^ (4 * n - 1) ≤ Nat.card ↥E) :
    Module.finrank F ↥(commSp E) = 2 := by
  have hlt0 : 1 < 2 ^ (4 * n - 1) := Nat.one_lt_two_pow (by omega)
  have hlt1 : 2 ^ n < 2 ^ (4 * n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt3 : 2 ^ (3 * n) < 2 ^ (4 * n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases card_cases hσ hE2 hEc (by omega) hF with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hu, _⟩ | ⟨_, h⟩
  · omega
  · omega
  · exact hu
  · omega

theorem exists_siegel_of_card_ge (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : 2 ^ (4 * n - 1) ≤ Nat.card ↥E) :
    ∃ U : Submodule F (Fin 4 → F), Module.finrank F U = 2 ∧ E ≤ PW U ∧
      Nat.card ↥(PW (σ := σ) U) = 2 ^ (4 * n) := by
  have hu := finrank_commSp_eq_two_T3J3 hσ hE2 hEc hn hF hcard
  have hle := commSp_le_fixSp_of_finrank_eq_two hσ h2 hE2 hEc hu
  have hsum := finrank_commSp_add_finrank_fixSp hσ hE2
  have heq : commSp E = fixSp E := Submodule.eq_of_le_of_finrank_eq hle (by omega)
  have htisot : ∀ x ∈ commSp E, ∀ y ∈ commSp E, herm σ x y = 0 := by
    intro x hx y hy
    have hxorth : x ∈ horth σ (commSp E) := by
      rw [← fixSp_eq_horth hσ hE2, ← heq]; exact hx
    have h0 : herm σ y x = 0 := mem_horth.mp hxorth y hy
    rw [herm_conj σ hσ.invol y x, h0, map_zero]
  have hmax : ∀ x, (∀ y ∈ commSp E, herm σ x y = 0) → x ∈ commSp E := by
    intro x hx
    have hx' : ∀ y ∈ commSp E, herm σ y x = 0 := by
      intro y hy
      rw [herm_conj σ hσ.invol x y, hx y hy, map_zero]
    have hmem : x ∈ fixSp E := by
      rw [fixSp_eq_horth hσ hE2]
      exact mem_horth.mpr hx'
    rwa [heq]
  refine ⟨commSp E, hu, fun a ha => mem_PW.mpr ⟨fun x => sub_mem_commSp ha x,
    fun w hw => mem_fixSp.mp (heq ▸ hw) a ha⟩, ?_⟩
  exact CFSG.LieType.Universal.Unitary.card_PW_eq_two_pow_four_mul hσ h2 hF hu htisot hmax

private theorem two_le_card_inf_T3J3 {G : Type} [Group G] [Finite G] {E P B : Subgroup G}
    {m k : ℕ} (hEP : E ≤ P) (hBP : B ≤ P) (hP : Nat.card ↥P = 2 ^ (m + 1))
    (hE : 2 ^ m ≤ Nat.card ↥E) (hB : Nat.card ↥B = 2 ^ k) (hk : 2 ≤ k) :
    2 ≤ Nat.card ↥(E ⊓ B) := by
  have h1 : E.relIndex P * Nat.card ↥(E ⊓ P) = Nat.card ↥P := Subgroup.relIndex_mul_card E P
  rw [inf_of_le_left hEP, hP] at h1
  have hpos : 0 < 2 ^ m := Nat.two_pow_pos m
  have hrP : E.relIndex P ≤ 2 := by
    have h3 : E.relIndex P * 2 ^ m ≤ 2 * 2 ^ m := by
      calc E.relIndex P * 2 ^ m ≤ E.relIndex P * Nat.card ↥E := Nat.mul_le_mul_left _ hE
        _ = 2 ^ (m + 1) := h1
        _ = 2 * 2 ^ m := by ring
    exact Nat.le_of_mul_le_mul_right h3 hpos
  have hne : E.relIndex P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (pow_pos (by norm_num : 0 < 2) (m + 1)).ne h1
  have hrB : E.relIndex B ≤ 2 := (Subgroup.relIndex_le_of_le_right hBP hne).trans hrP
  have h4 : E.relIndex B * Nat.card ↥(E ⊓ B) = 2 ^ k := by
    rw [Subgroup.relIndex_mul_card, hB]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hj : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  by_contra hc
  have hc' : Nat.card ↥(E ⊓ B) < 2 := Nat.lt_of_not_le hc
  have h5 : E.relIndex B * Nat.card ↥(E ⊓ B) ≤ 2 * 1 := Nat.mul_le_mul hrB (by omega)
  rw [pow_add] at h4
  omega

private theorem ne_top_T3J3 {n : ℕ} (hF : Nat.card F = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    {S : Submodule F (Fin 4 → F)} (hS6 : Nat.card ↥S = 2 ^ (6 * n)) : S ≠ ⊤ := by
  intro h
  rw [h] at hS6
  have h1 : Nat.card ↥(⊤ : Submodule F (Fin 4 → F)) = Nat.card (Fin 4 → F) :=
    Nat.card_congr Submodule.topEquiv.toEquiv
  rw [h1, Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hF, ← pow_mul,
    ← pow_mul] at hS6
  have := Nat.pow_right_injective (le_refl 2) hS6
  omega

private theorem transvection_T3J3 (hσ : IsUnitaryInvolution σ) {E B : Subgroup (SUid σ 4)}
    (hE2 : ∀ a ∈ E, a * a = 1) {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = (2 ^ n) ^ 2)
    (hfixB : Nat.card ↥(fixSp B) = 2 ^ (6 * n)) {a : SUid σ 4} (haE : a ∈ E) (haB : a ∈ B)
    (ha1 : a ≠ 1) :
    fixSp (Subgroup.zpowers a) = fixSp B ∧
      Nat.card ↥(commSp (Subgroup.zpowers a)) = 2 ^ (2 * n) := by
  have hF2 : Nat.card F = 2 ^ (2 * n) := by rw [hF, ← pow_mul, mul_comm]
  have hza : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr haB
  have hle : fixSp B ≤ fixSp (Subgroup.zpowers a) := fun x hx b hb => hx b (hza hb)
  have hfr : Module.finrank F ↥(fixSp B) = 3 := by
    have hc : Nat.card ↥(fixSp B) = Nat.card F ^ Module.finrank F ↥(fixSp B) :=
      Module.natCard_eq_pow_finrank
    rw [hfixB, hF2, ← pow_mul] at hc
    have hexp : 6 * n = 2 * n * Module.finrank F ↥(fixSp B) :=
      Nat.pow_right_injective (le_refl 2) hc
    have h3 : 2 * n * 3 = 2 * n * Module.finrank F ↥(fixSp B) := by rw [← hexp]; ring
    exact (Nat.eq_of_mul_eq_mul_left (by omega) h3).symm
  have hne : fixSp (Subgroup.zpowers a) ≠ ⊤ := by
    intro htop
    apply ha1
    refine ext_smul σ fun v => ?_
    have hv : v ∈ fixSp (Subgroup.zpowers a) := by rw [htop]; exact Submodule.mem_top
    rw [one_smul]
    exact mem_fixSp.mp hv a (Subgroup.mem_zpowers a)
  have hge : 3 ≤ Module.finrank F ↥(fixSp (Subgroup.zpowers a)) :=
    hfr ▸ Submodule.finrank_mono hle
  have hle4 : Module.finrank F ↥(fixSp (Subgroup.zpowers a)) ≤ 4 := by
    have := Submodule.finrank_le (fixSp (Subgroup.zpowers a))
    simpa using this
  have hne4 : Module.finrank F ↥(fixSp (Subgroup.zpowers a)) ≠ 4 := by
    intro h4
    apply hne
    apply Submodule.eq_top_of_finrank_eq
    simpa using h4
  have hfr' : Module.finrank F ↥(fixSp (Subgroup.zpowers a)) = 3 := by omega
  have heq : fixSp (Subgroup.zpowers a) = fixSp B :=
    (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  refine ⟨heq, ?_⟩
  have hE2' : ∀ b ∈ Subgroup.zpowers a, b * b = 1 := fun b hb =>
    hE2 b ((Subgroup.zpowers_le.mpr haE) hb)
  have hsum := finrank_commSp_add_finrank_fixSp hσ hE2'
  have hc1 : Module.finrank F ↥(commSp (Subgroup.zpowers a)) = 1 := by omega
  have hc : Nat.card ↥(commSp (Subgroup.zpowers a)) =
      Nat.card F ^ Module.finrank F ↥(commSp (Subgroup.zpowers a)) :=
    Module.natCard_eq_pow_finrank
  rw [hc, hc1, pow_one, hF2]

private theorem exists_ne_one_T3J3 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (h : 2 ≤ Nat.card ↥K) : ∃ a ∈ K, a ≠ 1 := by
  have hnt : Nontrivial ↥K := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨a, ha⟩, hne⟩ := exists_ne (1 : ↥K)
  exact ⟨a, ha, fun h1 => hne (Subtype.ext h1)⟩

theorem exists_two_transvections_of_card_ge (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    {E : Subgroup (SUid σ 4)} (hE2 : ∀ a ∈ E, a * a = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hcard : 2 ^ (4 * n - 1) ≤ Nat.card ↥E) :
    ∃ a₁ a₂ : SUid σ 4, a₁ ∈ E ∧ a₂ ∈ E ∧
      Nat.card ↥(commSp (Subgroup.zpowers a₁)) = 2 ^ (2 * n) ∧
      Nat.card ↥(fixSp (Subgroup.zpowers a₁)) = 2 ^ (6 * n) ∧
      Nat.card ↥(commSp (Subgroup.zpowers a₂)) = 2 ^ (2 * n) ∧
      Nat.card ↥(fixSp (Subgroup.zpowers a₂)) = 2 ^ (6 * n) ∧
      fixSp (Subgroup.zpowers a₁) ≠ fixSp (Subgroup.zpowers a₂) ∧
      fixSp (Subgroup.zpowers a₁) ⊔ fixSp (Subgroup.zpowers a₂) = ⊤ := by
  obtain ⟨U, -, hEU, hPW⟩ := exists_siegel_of_card_ge hσ h2 hE2 hEc hn hF hcard
  have hn1 : 1 ≤ n := by omega
  obtain ⟨B₁, B₂, hB₁U, hB₂U, hB₁c, hB₂c, -, -, hfix₁, hfix₂, hsup⟩ :=
    s16_C4ModelTv_two_root_groups hσ h2 (fun a ha => PW_sq h2 ha)
      (fun a ha b hb => PW_comm ha hb) hn1 hF hPW
  have hP' : Nat.card ↥(PW (σ := σ) U) = 2 ^ (4 * n - 1 + 1) := by
    rw [hPW]
    congr 1
    omega
  have hcnt₁ := two_le_card_inf_T3J3 hEU hB₁U hP' hcard hB₁c (by omega)
  have hcnt₂ := two_le_card_inf_T3J3 hEU hB₂U hP' hcard hB₂c (by omega)
  obtain ⟨a₁, ha₁, ha₁1⟩ := exists_ne_one_T3J3 hcnt₁
  obtain ⟨a₂, ha₂, ha₂1⟩ := exists_ne_one_T3J3 hcnt₂
  obtain ⟨ha₁E, ha₁B⟩ := Subgroup.mem_inf.1 ha₁
  obtain ⟨ha₂E, ha₂B⟩ := Subgroup.mem_inf.1 ha₂
  obtain ⟨hfx₁, hcm₁⟩ := transvection_T3J3 hσ hE2 hn1 hF hfix₁ ha₁E ha₁B ha₁1
  obtain ⟨hfx₂, hcm₂⟩ := transvection_T3J3 hσ hE2 hn1 hF hfix₂ ha₂E ha₂B ha₂1
  refine ⟨a₁, a₂, ha₁E, ha₂E, hcm₁, ?_, hcm₂, ?_, ?_, ?_⟩
  · rw [hfx₁]
    exact hfix₁
  · rw [hfx₂]
    exact hfix₂
  · rw [hfx₁, hfx₂]
    intro h
    rw [h, sup_idem] at hsup
    exact ne_top_T3J3 hF hn1 hfix₂ hsup
  · rw [hfx₁, hfx₂]
    exact hsup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
