module

public import CFSG.RankThree.PartTwo.Sec21.Item229Pre

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp localRank)
open CFSG.Assembly (IsElemAbelian)
open Matrix

variable {G : Type} [Group G]

theorem kOf_sup_cases_of_orderOf_eq_four [Finite G] (h222 : Item222) (h228 : Item228)
    (hR4 : Item229UnitaryRoots) {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) (hK : KOfWellDefined A) {φ ψ : MulAut A} (hφ : φ ∈ dStar A)
    (hψ : ψ ∈ dStar A) (h4 : orderOf (φ * ψ) = 4) {m : ℕ} (hm0 : 0 < m) (hme : Even m)
    (eφ : kOf A φ ≃* projSL 2 (GaloisField 2 m)) :
    (Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSp 2 (GaloisField 2 m)) ∧
        Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m))) ∨
      (Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 m) ∧
        Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 (2 * m)))) ∨
      (∃ k : ℕ, 0 < k ∧ Even k ∧ m = 2 * k ∧
        Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 k) ∧
        Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 k))) := by
  have hφ2 := mul_self_of_mem_dStar hφ
  have hψ2 := mul_self_of_mem_dStar hψ
  have hm2 : 2 ≤ m := by obtain ⟨k, hk⟩ := hme; omega
  have hnc : ψ * φ ≠ φ * ψ := by
    intro hc
    have h2 : (φ * ψ) ^ 2 = 1 := by
      rw [sq, mul_assoc, ← mul_assoc ψ, hc, mul_assoc, hψ2, mul_one, hφ2]
    have := orderOf_dvd_of_pow_eq_one h2
    rw [h4] at this
    norm_num at this
  have hne : ψ ≠ φ := by
    intro h
    apply hnc
    rw [h]
  have h4Y : 4 ∣ Nat.card (starOf A (kOf A φ ⊔ kOf A ψ)) := by
    obtain ⟨h1, h2⟩ := mem_starOf_sup h222 hpair hK hφ hψ
    have := dvd_card_starOf ((starOf A _).mul_mem h1 h2)
    rwa [h4] at this
  have hroots := hR4 G A E U c L hpair hA27 φ hφ ψ hψ h4
  obtain ⟨-, -, hX3⟩ := h228 G A E U c L hpair hA27 φ hφ ψ hψ hne
  obtain ⟨hX1ψ, -, -⟩ := h228 G A E U c L hpair hA27 ψ hψ φ hφ hne.symm
  rcases hX3 hnc with ⟨hYL, hcase, hnU5⟩ | ⟨⟨eU⟩, -⟩
  · rcases hcase with ⟨-, -, -, -, -, -, ⟨e6⟩⟩ | ⟨-, n, hn0, hne', ⟨eY⟩, ⟨eK⟩, -⟩ |
        ⟨-, n, hn0, hne', ⟨eY⟩, -, -⟩ | ⟨-, ⟨eY⟩, -⟩ | ⟨h81, -⟩
    · rw [card_of_mulEquiv_perm_three e6] at h4Y
      norm_num at h4Y
    ·
      have hn : n = m := eq_of_mulEquiv_projSL_two (by omega) (by omega) (eK.symm.trans eφ)
      subst hn
      left
      refine ⟨⟨eY⟩, ?_⟩
      rw [sup_comm] at hYL
      obtain ⟨m₃, hm₃0, hm₃e, ⟨e₃⟩, hX⟩ := hX1ψ _ hYL le_sup_left
      have hm₃2 : 2 ≤ m₃ := by obtain ⟨k, hk⟩ := hm₃e; omega
      have eY' : (kOf A ψ ⊔ kOf A φ : Subgroup G) ≃* projSp 2 (GaloisField 2 n) :=
        (MulEquiv.subgroupCongr (sup_comm _ _)).trans eY
      have := isSimpleGroup_projSp_two hm2
      rcases hX with hS | hS | hS | ⟨-, hS⟩ | ⟨-, hS⟩
      · obtain ⟨eS⟩ := hS
        have : IsSimpleGroup (SL3 m₃) := (eS.symm.trans eY').isSimpleGroup
        exact absurd this (not_isSimpleGroup_SL3 hm₃0 hm₃e)
      · obtain ⟨eS⟩ := hS
        rw [eq_of_mulEquiv_projSp_two hm₃2 hm2 (eS.symm.trans eY')] at e₃
        exact ⟨e₃⟩
      · obtain ⟨eS⟩ := hS
        exact (not_mulEquiv_projSp_two_projSU_four hm2 (by omega)).elim (eY'.symm.trans eS)
      · obtain ⟨eS⟩ := hS
        exact (not_mulEquiv_projSp_two_projSU_four hm2 (by omega)).elim (eY'.symm.trans eS)
      · obtain ⟨eS⟩ := hS
        exact hnU5.elim ((MulEquiv.subgroupCongr (sup_comm _ _)).trans eS)
    ·
      rcases hroots n hn0 ⟨eY⟩ with ⟨⟨e1⟩, ⟨e2⟩⟩ | ⟨⟨e1⟩, ⟨e2⟩⟩
      · have hn : n = m := eq_of_mulEquiv_projSL_two (by omega) (by omega) (e1.symm.trans eφ)
        subst hn
        exact Or.inr (Or.inl ⟨⟨eY⟩, ⟨e2⟩⟩)
      · have hn : 2 * n = m := eq_of_mulEquiv_projSL_two (by omega) (by omega) (e1.symm.trans eφ)
        exact Or.inr (Or.inr ⟨n, hn0, hne', hn.symm, ⟨eY⟩, ⟨e2⟩⟩)
    · exact (hnU5.elim eY)
    · rw [hA27] at h81
      norm_num at h81
  ·
    rcases hroots 2 (by norm_num) ⟨eU⟩ with ⟨⟨e1⟩, ⟨e2⟩⟩ | ⟨⟨e1⟩, ⟨e2⟩⟩
    · have hn : 2 = m := eq_of_mulEquiv_projSL_two (by norm_num) (by omega) (e1.symm.trans eφ)
      subst hn
      exact Or.inr (Or.inl ⟨⟨eU⟩, ⟨e2⟩⟩)
    · have hn : 2 * 2 = m := eq_of_mulEquiv_projSL_two (by norm_num) (by omega)
        (e1.symm.trans eφ)
      exact Or.inr (Or.inr ⟨2, by norm_num, even_two, hn.symm, ⟨eU⟩, ⟨e2⟩⟩)

theorem nonempty_mulEquiv_of_quotient_center {I : Subgroup G} [Finite I] {X : Type*} [Group X]
    (hc : Subgroup.center I = ⊥) (e : I ⧸ Subgroup.center I ≃* X) : Nonempty (I ≃* X) :=
  ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc.symm)).trans e⟩

theorem center_eq_bot_of_sup [Finite G] (hZ : CentralExtensionTrivial229) {A : Subgroup G}
    {t₁ t₂ t₃ : MulAut A} {I : Subgroup G} (hIeq : I = kOf A t₁ ⊔ kOf A t₂ ⊔ kOf A t₃)
    {n₁ n₂ n₃ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hn₃ : 2 ≤ n₃)
    (k₁ : kOf A t₁ ≃* projSL 2 (GaloisField 2 n₁)) (k₂ : kOf A t₂ ≃* projSL 2 (GaloisField 2 n₂))
    (k₃ : kOf A t₃ ≃* projSL 2 (GaloisField 2 n₃)) {m : ℕ} (hm0 : 0 < m) (hme : Even m)
    (hq : Nonempty (I ⧸ Subgroup.center I ≃* projSL 4 (GaloisField 2 m)) ∨
      Nonempty (I ⧸ Subgroup.center I ≃* projSp 3 (GaloisField 2 m)) ∨
      (∃ b c : GaloisField 2 m, (∀ s : GaloisField 2 m, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (I ⧸ Subgroup.center I ≃*
          CFSG.Assembly.RankThreeEven.projOmegaMinus 3 (GaloisField 2 m) b c)) ∨
      Nonempty (I ⧸ Subgroup.center I ≃* projSU 6 2 m)) :
    Subgroup.center I = ⊥ := by
  have hperf : Group.IsPerfect I := by
    rw [hIeq]
    exact isPerfect_sup (isPerfect_sup (isPerfect_of_mulEquiv_projSL hn₁ k₁)
      (isPerfect_of_mulEquiv_projSL hn₂ k₂)) (isPerfect_of_mulEquiv_projSL hn₃ k₃)
  exact hZ I hperf m hm0 hme hq

theorem not_commOf_le_fixedSubgroupOf_of_coord {A : Subgroup G}
    (f : Multiplicative (Fin 3 → ZMod 3) ≃* A) {φ ψ : MulAut A} {M N : GL (Fin 3) (ZMod 3)}
    (hφ : coordGL f φ = M) (hψ : coordGL f ψ = N) (v : Fin 3 → ZMod 3)
    (hv : (N : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ((M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v - v)
      ≠ (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v - v) :
    ¬ commOf φ ≤ fixedSubgroupOf ψ := by
  intro h
  set a : A := f (Multiplicative.ofAdd v)
  have hfix : ψ (a⁻¹ * φ a) = a⁻¹ * φ a := h (mem_commOf φ a)
  have hMv : (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v = Multiplicative.toAdd (f.symm (φ a)) := by
    rw [← hφ, coordGL_mulVec, coordLin3_apply]
  have hw : Multiplicative.toAdd (f.symm (a⁻¹ * φ a)) =
      (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v - v := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hMv]
    simp only [a, MulEquiv.symm_apply_apply, toAdd_ofAdd]
    abel
  apply hv
  rw [← hw, ← hψ, coordGL_mulVec, coordLin3_apply]
  simp only [ofAdd_toAdd, MulEquiv.apply_symm_apply, hfix]

theorem not_inf_kOf_le_centralizer [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (h : ¬ commOf φ ≤ fixedSubgroupOf ψ) :
    ¬ A ⊓ kOf A φ ≤ Subgroup.centralizer (kOf A ψ : Set G) := by
  intro hle
  apply h
  intro b hb
  have hbK : (b : G) ∈ A ⊓ kOf A φ := ⟨b.2, map_commOf_le_kOf h222 hpair hK hφ ⟨b, hb, rfl⟩⟩
  have hbC : (b : G) ∈ A ⊓ Subgroup.centralizer (kOf A ψ : Set G) := ⟨b.2, hle hbK⟩
  rw [inf_centralizer_kOf_eq h222 hpair hK hψ] at hbC
  obtain ⟨b', hb', hb'b⟩ := hbC
  rwa [show b = b' from Subtype.ext hb'b.symm]

theorem ne_of_orderOf_mul_ne_one {A : Subgroup G} {φ ψ : MulAut A} (hψ : ψ ∈ dStar A)
    (h : orderOf (φ * ψ) ≠ 1) : φ ≠ ψ := by
  rintro rfl
  rw [mul_self_of_mem_dStar hψ, orderOf_one] at h
  exact h rfl

end CFSG.RankThree.PartTwo.Sec21
