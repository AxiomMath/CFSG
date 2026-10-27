module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmRestr
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusFour
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
public import CFSG.RankThree.PartOne.AUTSL.Rows
public import CFSG.RankThree.PartOne.AUTSL.SylowTrick
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S12.Sec1511Y1
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.StandardType

namespace RCSTOm

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup)
open CFSG.LieType.Universal.Spin (HypFrame)

section Transport

variable {U X G : Type} [Group U] [Group X] [Group G] {σ : U →* X} (hσ : Function.Injective σ)
  (φ : U →* G)

variable (σ) in
@[expose] def Φ (A : Subgroup X) : Subgroup G := (A.comap σ).map φ

include hσ in
theorem comap_sup_of_le_range {A B : Subgroup X} (hA : A ≤ σ.range) (hB : B ≤ σ.range) :
    (A ⊔ B).comap σ = A.comap σ ⊔ B.comap σ := by
  apply Subgroup.map_injective hσ
  rw [Subgroup.map_sup, Subgroup.map_comap_eq_self (sup_le hA hB), Subgroup.map_comap_eq_self hA,
    Subgroup.map_comap_eq_self hB]

include hσ in
theorem Φ_sup {A B : Subgroup X} (hA : A ≤ σ.range) (hB : B ≤ σ.range) :
    Φ σ φ (A ⊔ B) = Φ σ φ A ⊔ Φ σ φ B := by
  rw [Φ, comap_sup_of_le_range hσ hA hB, Subgroup.map_sup]
  rfl

theorem commutator_le_sup_self (A B : Subgroup X) : ⁅A, B⁆ ≤ A ⊔ B :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (mem_sup_left ha) (mem_sup_right hb))
      (inv_mem (mem_sup_left ha))) (inv_mem (mem_sup_right hb))

include hσ in
theorem Φ_commutator {A B : Subgroup X} (hA : A ≤ σ.range) (hB : B ≤ σ.range) :
    Φ σ φ ⁅A, B⁆ = ⁅Φ σ φ A, Φ σ φ B⁆ := by
  have h : ⁅A, B⁆.comap σ = ⁅A.comap σ, B.comap σ⁆ := by
    apply Subgroup.map_injective hσ
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self
      ((commutator_le_sup_self A B).trans (sup_le hA hB)), Subgroup.map_comap_eq_self hA,
      Subgroup.map_comap_eq_self hB]
  rw [Φ, h, Subgroup.map_commutator]
  rfl

theorem Φ_mono {A B : Subgroup X} (h : A ≤ B) : Φ σ φ A ≤ Φ σ φ B :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem comap_le_normalizer {A B : Subgroup X} (h : A ≤ normalizer (B : Set X)) :
    A.comap σ ≤ normalizer ((B.comap σ : Subgroup U) : Set U) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  rw [mem_comap, mem_comap, map_mul, map_mul, map_inv]
  exact mem_normalizer_iff.mp (h hg) (σ y)

theorem Φ_le_normalizer {A B : Subgroup X} (h : A ≤ normalizer (B : Set X)) :
    Φ σ φ A ≤ normalizer ((Φ σ φ B : Subgroup G) : Set G) :=
  ggRCST_map_le_normalizer φ (comap_le_normalizer h)

include hσ in
theorem Φ_le_centralizer {A B : Subgroup X} (h : A ≤ centralizer (B : Set X)) :
    Φ σ φ A ≤ centralizer ((Φ σ φ B : Subgroup G) : Set G) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  have hab : σ b * σ a = σ a * σ b := (mem_centralizer_iff.mp (h ha)) (σ b) hb
  rw [← map_mul, ← map_mul, hσ (show σ (b * a) = σ (a * b) by rw [map_mul, map_mul, hab])]

include hσ in
theorem Φ_disjoint {A B : Subgroup X} (hφ : Function.Injective φ) (h : Disjoint A B) :
    Disjoint (Φ σ φ A) (Φ σ φ B) := by
  refine RCSTSp2.disjoint_map_of_injective hφ ?_
  rw [Subgroup.disjoint_def] at h ⊢
  intro x hxA hxB
  exact hσ (by rw [h hxA hxB, map_one])

theorem Φ_isPGroup {A : Subgroup X} (hσ' : Function.Injective σ) {p : ℕ} (h : IsPGroup p A) :
    IsPGroup p (Φ σ φ A) :=
  (h.comap_of_injective σ hσ').map φ

include hσ in
@[expose] noncomputable def Φ_equiv (hφ : Function.Injective φ) {A : Subgroup X}
    (hA : A ≤ σ.range) : ↥(Φ σ φ A) ≃* ↥A :=
  ((A.comap σ).equivMapOfInjective φ hφ).symm.trans
    (((A.comap σ).equivMapOfInjective σ hσ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hA)))

end Transport

section Aux

theorem le_centralizer_bot {G : Type*} [Group G] (A : Subgroup G) :
    A ≤ centralizer ((⊥ : Subgroup G) : Set G) := by
  intro g _
  rw [mem_centralizer_iff]
  intro h hh
  rw [mem_bot.mp hh, one_mul, mul_one]

theorem card_eq_two_or_four_le (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Nat.card K = 2 ∨ 4 ≤ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hk]
  rcases Nat.lt_or_ge (k : ℕ) 2 with h | h
  · left
    have : (k : ℕ) = 1 := by have := k.ne_zero; omega
    rw [this, pow_one]
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem eq_three_of_dvd_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 6) : p = 3 := by
  have h6 : p ∣ 2 * 3 := h
  rcases (Nat.Prime.dvd_mul hp).mp h6 with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h

end Aux

section Frame

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {P₁ P₂ P₃ : HypPair Q}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polarNondegOn_wSub (hQ : (polarBilin Q).Nondegenerate) (h₁₂ : P₁.Orth P₂) :
    PolarNondegOn Q (wSub P₁ P₂) :=
  (HypPair.polarNondegOn_perp hQ P₁).inf_perp P₂ (HypPair.mem_perp.mpr ⟨h₁₂.ee, h₁₂.fe⟩)
    (HypPair.mem_perp.mpr ⟨h₁₂.ef, h₁₂.ff⟩)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem nondegenerate_restrict_wSub (hQ : (polarBilin Q).Nondegenerate) (h₁₂ : P₁.Orth P₂) :
    (polarBilin (Q.restrict (wSub P₁ P₂))).Nondegenerate :=
  nondegenerate_polarBilin_restrict (polarNondegOn_wSub hQ h₁₂)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem exists_polar_eq_one_perp (hQ : (polarBilin Q).Nondegenerate) (h₁₂ : P₁.Orth P₂)
    (h₁₃ : P₁.Orth P₃) (h₂₃ : P₂.Orth P₃) {y₀ : V} (hy₀ : y₀ ≠ 0) (hy₀W : InW P₁ P₂ y₀)
    (hy₀3 : polar Q P₃.e y₀ = 0 ∧ polar Q P₃.f y₀ = 0) :
    ∃ x', InW P₁ P₂ x' ∧ (polar Q P₃.e x' = 0 ∧ polar Q P₃.f x' = 0) ∧ polar Q y₀ x' = 1 := by
  obtain ⟨he3, hf3⟩ := inW_of_orth h₁₃.symm h₂₃.symm
  have hW' : PolarNondegOn Q (wSub P₁ P₂ ⊓ P₃.perp) :=
    (polarNondegOn_wSub hQ h₁₂).inf_perp P₃ (mem_wSub.mpr he3) (mem_wSub.mpr hf3)
  have hy : y₀ ∈ wSub P₁ P₂ ⊓ P₃.perp :=
    Submodule.mem_inf.mpr ⟨mem_wSub.mpr hy₀W, HypPair.mem_perp.mpr hy₀3⟩
  obtain ⟨y, hyW, hy0⟩ := hW'.exists_polar_ne_zero hy hy₀
  obtain ⟨hyW1, hyW2⟩ := Submodule.mem_inf.mp hyW
  obtain ⟨a, b⟩ := HypPair.mem_perp.mp hyW2
  refine ⟨(polar Q y₀ y)⁻¹ • y, inW_smul (mem_wSub.mp hyW1) _,
    ⟨by rw [polar_smul_right_eq, a, mul_zero], by rw [polar_smul_right_eq, b, mul_zero]⟩, ?_⟩
  rw [polar_smul_right_eq, inv_mul_cancel₀ hy0]

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem centralizer_eq_comap {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)}
    (hσ : Function.Injective σ) (hσE : σ.range = elementaryGroup Q) (x : U) :
    centralizer ({x} : Set U) = (centralizer {σ x} ⊓ elementaryGroup Q).comap σ := by
  ext g
  rw [mem_comap, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, ← hσE]
  constructor
  · intro h
    exact ⟨by rw [← map_mul, h, map_mul], ⟨g, rfl⟩⟩
  · rintro ⟨h, -⟩
    exact hσ (by rw [map_mul, h, map_mul])

open scoped MatrixGroups in
theorem ggRCSLayer_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hQ : (polarBilin Q).Nondegenerate) (hEΩ : elementaryGroup Q ≤ omegaGroup Q hQ)
    (hOE : orthDerived Q ≤ elementaryGroup Q) (h₁₂ : P₁.Orth P₂) (h₁₃ : P₁.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {y₀ : V} (hy₀ : y₀ ≠ 0) (hy₀W : InW P₁ P₂ y₀)
    (hy₀3 : polar Q P₃.e y₀ = 0 ∧ polar Q P₃.f y₀ = 0)
    (hΩ : omegaGroup (Q.restrict (wSub P₁ P₂)) (nondegenerate_restrict_wSub hQ h₁₂) ≤
      orthDerived (Q.restrict (wSub P₁ P₂)))
    (hWq : CFSG.IsQuasisimple (orthDerived (Q.restrict (wSub P₁ P₂))))
    (hWZ : center (orthDerived (Q.restrict (wSub P₁ P₂))) = ⊥)
    (h3 : Nat.card K = 2 → p = 3 → 3 ∣ Nat.card (omFix Q P₁ P₂))
    {U : Type} [Group U] {σ : U →* (V ≃ₗ[K] V)} (hσ : Function.Injective σ)
    (hσE : σ.range = elementaryGroup Q) {x : U} (hx : σ x = eichler Q P₁.e P₂.e)
    (hxC : centralizer {x} ≤ ggOTwoPrime (centralizer {x}))
    {G : Type} [Group G] [Finite G] (ψ : U →* G) (hψ : Function.Injective ψ) {M : Subgroup G}
    (hG₀M : ψ.range ≤ M) (hM : M ≤ normalizer (ψ.range : Set G)) (u : U) :
    GGRCSLayer p ψ.range M (ψ (u * x * u⁻¹)) := by
  have hE : ∀ a b : V, eichler Q a b ∈ elementaryGroup Q := eichler_mem_elementaryGroup Q
  set φ := ψ.comp (MulAut.conj u).toMonoidHom with hφdef
  have hφ : Function.Injective φ := RCSTSp.comp_conj_injective hψ u
  have hφr : φ.range = ψ.range := RCSTSp.range_comp_conj ψ u
  have hr : ψ (u * x * u⁻¹) = φ x := by
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [hr, ← hφr]
  rw [← hφr] at hG₀M hM
  have hRE : rootRadical Q P₁ P₂ ≤ σ.range := hσE ▸ rootRadical_le_elementaryGroup h₁₂
  have hL₁E : leviFix (elementaryGroup Q) P₁ P₂ ≤ σ.range :=
    hσE ▸ fun g hg => (mem_leviFix.mp hg).1
  have hL₂E : omFix Q P₁ P₂ ≤ σ.range := hσE ▸ fun g hg => (mem_omFix.mp hg).1
  set QG := Φ σ φ (rootRadical Q P₁ P₂) with hQGdef
  set AG := Φ σ φ (leviFix (elementaryGroup Q) P₁ P₂) with hAGdef
  set BG := Φ σ φ (omFix Q P₁ P₂) with hBGdef
  have hX : ggRCSX φ.range (φ x) = QG ⊔ AG ⊔ BG := by
    rw [RCSTSp.ggRCSX_eq_map_centralizer φ hφ hxC, centralizer_eq_comap hσ hσE x, hx,
      centralizer_inf_elementaryGroup_eq h₁₂]
    change Φ σ φ _ = _
    rw [Φ_sup hσ φ (sup_le hRE hL₁E) hL₂E, Φ_sup hσ φ hRE hL₁E]
  have hQ2 : IsPGroup 2 QG := Φ_isPGroup φ hσ isPGroup_rootRadical
  have h1Q : AG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (leviFix_le_normalizer_rootRadical h₁₂)
  have h2Q : BG ≤ normalizer (QG : Set G) :=
    Φ_le_normalizer φ (omFix_le_normalizer_rootRadical h₁₂)
  have h12 : AG ≤ centralizer (BG : Set G) :=
    Φ_le_centralizer hσ φ (leviFix_le_centralizer_omFix h₁₂)
  have eA : ↥AG ≃* SL(2, K) := (Φ_equiv hσ φ hφ hL₁E).trans (leviFixEquiv P₁ P₂ h₁₂ hE)
  have eB : ↥BG ≃* ↥(orthDerived (Q.restrict (wSub P₁ P₂))) :=
    (Φ_equiv hσ φ hφ hL₂E).trans
      (omFixEquiv h₁₂ hQ hEΩ hOE (nondegenerate_restrict_wSub hQ h₁₂) hΩ)
  have hBq : CFSG.IsQuasisimple BG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB.symm hWq
  have hBZ : center BG = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eB.symm, hWZ,
      Subgroup.map_bot]
  have hSB : GGRCSOmSummand BG := ggRCSOmSummand_of_isQuasisimple hBq hBZ
  obtain ⟨x', hx'W, hx'3, hy₀x'⟩ := exists_polar_eq_one_perp hQ h₁₂ h₁₃ h₂₃ hy₀ hy₀W hy₀3
  have hQB : QG ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := by
    have h := Φ_mono (σ := σ) φ
      (rootRadical_le_commutator_omFix h₁₂ h₁₃ h₂₃ hy₀W hx'W hy₀3 hx'3 hy₀x')
    rwa [Φ_commutator hσ φ (sup_le hRE hL₂E) (sup_le hRE hL₂E), Φ_sup hσ φ hRE hL₂E] at h
  have hX₃ : ggRCSX φ.range (φ x) = QG ⊔ (AG ⊔ BG ⊔ ⊥) := by
    rw [hX, sup_bot_eq, sup_assoc]
  rcases card_eq_two_or_four_le K with hK | hK
  ·
    obtain ⟨e3⟩ := RCSPSL.nonempty_sl2_equiv_perm (F := K) hK
    have eS : ↥AG ≃* Equiv.Perm (Fin 3) := eA.trans e3
    have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX φ.range (φ x)) = QG :=
      pCoreOf_eq_of_three_summands hX₃ hQ2 h1Q h2Q bot_le h12 (le_centralizer_bot _)
        (le_centralizer_bot _) (ggRCSOmSummand_of_perm eS) hSB ggRCSOmSummand_bot
    by_cases hp3 : p = 3
    · subst hp3
      have hdQL : Disjoint QG (AG ⊔ BG) := by
        have h := Φ_disjoint hσ φ hφ (disjoint_rootRadical_sup h₁₂)
        rwa [Φ_sup hσ φ hL₁E hL₂E] at h
      have hdST : Disjoint AG BG := Φ_disjoint hσ φ hφ (disjoint_leviFix_omFix h₁₂)
      have hBperf : ⁅BG, BG⁆ = BG := Subgroup.isPerfect_iff.mp hBq.1
      have hperf : ⁅QG ⊔ BG, QG ⊔ BG⁆ = QG ⊔ BG := by
        refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le _) (sup_le hQB ?_)
        calc BG = ⁅BG, BG⁆ := hBperf.symm
          _ ≤ ⁅QG ⊔ BG, QG ⊔ BG⁆ := Subgroup.commutator_mono le_sup_right le_sup_right
      have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
      have hSs : Group.IsSolvable ↥AG :=
        Group.isSolvable_of_isSolvable_injective (f := eS.toMonoidHom) eS.injective
      have hD : CFSG.Quasithin.perfectCore (ggRCSX φ.range (φ x)) = QG ⊔ BG :=
        perfectCore_eq_of_solvable (by rw [hX, sup_assoc])
          (le_normalizer_sup_of_centralizer h1Q h12) hSs hperf
      have h3B : 3 ∣ Nat.card BG := by
        rw [Nat.card_congr (Φ_equiv hσ φ hφ hL₂E).toEquiv]
        exact h3 hK rfl
      exact ggRCSLayer_three_of_sThree hG₀M hM (by rw [hX, sup_assoc]) hQ2 h1Q h2Q h12 hdQL hdST
        hD eS hBq hBZ h3B
    · have hpA : ¬ p ∣ Nat.card AG := by
        rw [Nat.card_congr eS.toEquiv, card_perm_three]
        exact fun h => hp3 (eq_three_of_dvd_six hp hp2 h)
      exact ggRCSLayer_of_three_summands hp hp2 hG₀M hM hQ2 hO2 (by rw [hX, sup_bot_eq]) h1Q
        h2Q bot_le h12 (le_centralizer_bot _) (le_centralizer_bot _) (fun h => absurd h hpA)
        (fun _ => ⟨hBq, hQB⟩) (ggRCSOmQuasiSummand_bot hp _)
  ·
    have hAq : CFSG.IsQuasisimple AG := CFSG.LocalCores.isQuasisimple_of_mulEquiv eA.symm
      (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl (Or.inr hK))
    have hAZ : center AG = ⊥ := by
      rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eA.symm,
        center_SL2_eq_bot_of_charTwo, Subgroup.map_bot]
    have hQA : QG ≤ ⁅QG ⊔ AG, QG ⊔ AG⁆ := by
      have h := Φ_mono (σ := σ) φ (rootRadical_le_commutator_leviFix h₁₂ h₁₃ h₂₃)
      rwa [Φ_commutator hσ φ (sup_le hRE hL₁E) (sup_le hRE hL₁E), Φ_sup hσ φ hRE hL₁E] at h
    have hO2 : CFSG.Assembly.pCoreOf 2 (ggRCSX φ.range (φ x)) = QG :=
      pCoreOf_eq_of_three_summands hX₃ hQ2 h1Q h2Q bot_le h12 (le_centralizer_bot _)
        (le_centralizer_bot _) (ggRCSOmSummand_of_isQuasisimple hAq hAZ) hSB ggRCSOmSummand_bot
    exact ggRCSLayer_of_three_summands hp hp2 hG₀M hM hQ2 hO2 (by rw [hX, sup_bot_eq]) h1Q h2Q
      bot_le h12 (le_centralizer_bot _) (le_centralizer_bot _) (fun _ => ⟨hAq, hQA⟩)
      (fun _ => ⟨hBq, hQB⟩) (ggRCSOmQuasiSummand_bot hp _)

end Frame

end RCSTOm

end CFSG.StandardType
