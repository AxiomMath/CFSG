module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU1Core
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.Untw
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcMonomial
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
import CFSG.LieType.Chevalley.SingleEdgePerfect
import CFSG.LieType.Steinberg.G2.Perfect
import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
import CFSG.HardMathSupport.Timmesfeld.LangTorus.Assembly
import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerTorus
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

private theorem ggNbrLSideRSExcU1Untw_model
    (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hcard : Nat.card K = 2 ^ n)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) (hmon : MonomialToralAt τ 3) :
    GGNbrLSideRSExcTransport τ
      (RecipeExcLang.markIDImage (IsRoot τ) K (adjointGroup τ K)) (2 ^ n) := by
  classical
  intro φ hφI ψ hψI hφ1 hφ3 hψ3 hcomm
  set Ψ₀ : LargeEvenCenterQuot (adjointGroup τ K) ≃* ↥(adjointGroup τ K) :=
    centerQuotEquivOfBot (H := adjointGroup τ K) center_adjointGroup_eq_bot with hΨ₀def
  have hmk : ∀ c : LargeEvenCenterQuot (adjointGroup τ K),
      LargeEvenCenterMk (adjointGroup τ K) (Ψ₀ c) = c := by
    intro c
    rw [← centerQuotEquivOfBot_symm center_adjointGroup_eq_bot (Ψ₀ c)]
    exact MulEquiv.symm_apply_apply Ψ₀ c
  have hΨ₀mk : ∀ x : ↥(adjointGroup τ K),
      Ψ₀ (LargeEvenCenterMk (adjointGroup τ K) x) = x := by
    intro x
    rw [hΨ₀def]
    exact centerQuotEquivOfBot_mk center_adjointGroup_eq_bot x
  have hΨ : ∀ (α : MulAut (LargeEvenCenterQuot (adjointGroup τ K)))
      (c : LargeEvenCenterQuot (adjointGroup τ K)),
      Ψ₀ (α c) = RecipeExcLang.autEquiv τ K α (Ψ₀ c) := by
    intro α c
    have h1 := RecipeExcLang.autEquiv_apply (τ := τ) (K := K) α (Ψ₀ c)
    rw [hmk] at h1
    have h2 := congrArg Ψ₀ h1
    rw [hΨ₀mk] at h2
    exact h2.symm
  obtain ⟨w, hw⟩ := RecipeExcLang.exists_inndiagConj_of_mem_markID hφI
  obtain ⟨w', hw'⟩ := RecipeExcLang.exists_inndiagConj_of_mem_markID hψI
  have hinj : Function.Injective (RecipeExcLang.inndiagConj τ K) :=
    RecipeExcLang.inndiagConj_injective_of_card_eq_two_pow hcard
  have hw3 : w ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← hw, ← map_pow, hφ3, map_one]
  have hw'3 : w' ^ 3 = 1 := by
    apply hinj
    rw [map_pow, map_one, ← hw', ← map_pow, hψ3, map_one]
  have hw1 : w ≠ 1 := by
    intro h1
    apply hφ1
    apply (RecipeExcLang.autEquiv τ K).injective
    rw [hw, h1, map_one, map_one]
  have hcommw : w * w' = w' * w := by
    apply hinj
    rw [map_mul, map_mul, ← hw, ← hw', ← map_mul, ← map_mul]
    exact congrArg (RecipeExcLang.autEquiv τ K) hcomm
  set h : ModGL τ K := (w : ModGL τ K) with hhdef
  set h' : ModGL τ K := (w' : ModGL τ K) with hh'def
  have hh3 : h ^ 3 = 1 := by rw [hhdef, ← Subgroup.coe_pow, hw3]; rfl
  have hh'3 : h' ^ 3 = 1 := by rw [hh'def, ← Subgroup.coe_pow, hw'3]; rfl
  have hh1 : h ≠ 1 := by rw [hhdef]; exact fun h1 => hw1 (Subtype.ext h1)
  have hhcomm : h * h' = h' * h := by
    rw [hhdef, hh'def, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcommw]
  have hβh : ∀ c : ↥(adjointGroup τ K),
      (RecipeExcLang.autEquiv τ K φ c : ModGL τ K) = h * c * h⁻¹ := by
    intro c
    rw [hw, hhdef]
    exact RecipeExcLang.coe_inndiagConj w c
  have hψh : ∀ c : ↥(adjointGroup τ K),
      (RecipeExcLang.autEquiv τ K ψ c : ModGL τ K) = h' * c * h'⁻¹ := by
    intro c
    rw [hw', hh'def]
    exact RecipeExcLang.coe_inndiagConj w' c
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓprime, hfcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓprime⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hqK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hfcard
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  haveI hcharL : CharP L ℓ :=
    charP_of_injective_algebraMap (algebraMap K L).injective (ringChar K)
  haveI : CharP K 2 := charP_two_of_card hcard
  have hℓ2 : ℓ = 2 := by rw [hℓdef]; exact ringChar.eq K 2
  have hℓ3 : ℓ ≠ 3 := by rw [hℓ2]; norm_num
  have hpq : Nat.Coprime 3 (ℓ ^ (f : ℕ)) := by
    rw [hℓ2]
    exact Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
  set ι₁ : K →+* L := algebraMap K L with hι₁
  have hFr : ∀ c : L, iterateFrobenius L ℓ (f : ℕ) c = c ^ Nat.card K := fun c => by
    rw [hqK]
    exact iterateFrobenius_def ℓ (f : ℕ) c
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L ℓ (f : ℕ) (baseChangeGL ι₁ y) = baseChangeGL ι₁ y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι₁ = ι₁ := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ (f : ℕ)) (ι₁ c) = ι₁ c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hfcard]
      exact FiniteField.pow_card c
    change Units.map (entrywiseHom (iterateFrobenius L ℓ (f : ℕ))) (baseChangeGL ι₁ y) =
      baseChangeGL ι₁ y
    rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  set u : ModGL τ L := baseChangeGL ι₁ h with hu
  set u' : ModGL τ L := baseChangeGL ι₁ h' with hu'
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, hh3, map_one]
  have hu'3 : u' ^ 3 = 1 := by rw [hu', ← map_pow, hh'3, map_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    exact fun h1 => hh1 (baseChangeGL_injective ι₁ (h1.trans (map_one _).symm))
  have hu'G : u' ∈ adjointGroup τ L :=
    RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag ι₁ w'.2
  have hconj : ∃ g ∈ adjointGroup τ L, g⁻¹ * u * g ∈ torusGroup τ L :=
    exists_conj_torusGroup_of_pow_eq_one Nat.prime_three hmon hℓ3
      (isAlgebraic_zmod_algebraicClosure_of_finite K ℓ)
      (RecipeExcLang.baseChangeGL_mem_adjointGroup_of_mem_inndiag ι₁ w.2) hu3
  obtain ⟨D, hΦ, hDq, hmem⟩ :=
    exists_langDatum_of_toral_untw (f : ℕ) hf1 hpq hu3 (hFix h) hconj
  have hFix' : D.Φ u' = u' := by
    rw [hΦ]
    exact hFix h'
  set ι : ↥(adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL ι₁).comp (adjointGroup τ K).subtype with hιdef
  set ι₀ : LargeEvenCenterQuot (adjointGroup τ K) →* ModGL τ L :=
    ι.comp Ψ₀.toMonoidHom with hι₀def
  have hι : Function.Injective ι :=
    (baseChangeGL_injective ι₁).comp (Subgroup.subtype_injective _)
  have hι₀ : Function.Injective ι₀ := hι.comp Ψ₀.injective
  have hι_apply : ∀ x : ↥(adjointGroup τ K), ι x = baseChangeGL ι₁ x := fun _ => rfl
  have hι₀_apply : ∀ c : LargeEvenCenterQuot (adjointGroup τ K),
      ι₀ c = ι (Ψ₀ c) := fun _ => rfl
  have hφ' : ∀ c : LargeEvenCenterQuot (adjointGroup τ K),
      ι₀ (φ c) = u * ι₀ c * u⁻¹ := by
    intro c
    rw [hι₀_apply, hι₀_apply, hι_apply, hι_apply, hu]
    rw [hΨ φ c, hw]
    rw [show (RecipeExcLang.inndiagConj τ K w (Ψ₀ c) : ModGL τ K) =
      h * (Ψ₀ c) * h⁻¹ from RecipeExcLang.coe_inndiagConj w (Ψ₀ c)]
    rw [map_mul, map_mul, map_inv]
  have hψ' : ∀ c : LargeEvenCenterQuot (adjointGroup τ K),
      ι₀ (ψ c) = u' * ι₀ c * u'⁻¹ := by
    intro c
    rw [hι₀_apply, hι₀_apply, hι_apply, hι_apply, hu']
    rw [hΨ ψ c, hw']
    rw [show (RecipeExcLang.inndiagConj τ K w' (Ψ₀ c) : ModGL τ K) =
      h' * (Ψ₀ c) * h'⁻¹ from RecipeExcLang.coe_inndiagConj w' (Ψ₀ c)]
    rw [map_mul, map_mul, map_inv]
  have hd₀ : LangDescent D 7 ι := by
    rcases hτ with h1 | h1 | h1 | h1 | h1
    · exact langDescent_exact (Or.inl h1) hFr D hΦ hperf
    · exact langDescent_exact (Or.inr h1) hFr D hΦ hperf
    · exact langDescent_untw 3 (Or.inl ⟨h1, rfl⟩) hFr D hΦ Nat.prime_seven (by norm_num) hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨h1, rfl⟩)) hFr D hΦ Nat.prime_seven (by norm_num)
        hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨h1, rfl⟩)) hFr D hΦ Nat.prime_seven (by norm_num)
        hperf
  have htopΨ : Ψ₀.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.2 (fun x => Ψ₀.surjective x)
  have hrangeι : ι₀.range = ι.range := by
    rw [hι₀def, MonoidHom.range_comp, htopΨ, Subgroup.map_top]
  have hd : LangDescent D 7 ι₀ :=
    { finite_fix := hd₀.finite_fix
      range_le := by rw [hrangeι]; exact hd₀.range_le
      pgroup_le := fun P hP hpP => by rw [hrangeι]; exact hd₀.pgroup_le P hP hpP
      derived := by rw [hrangeι]; exact hd₀.derived }
  have hqK2 : Nat.card K = 2 ^ (f : ℕ) := by rw [hqK, hℓ2]
  have hDq2 : D.q = 2 ^ n := by
    rw [hDq, hℓ2, ← hcard]
    exact hqK2.symm
  have hn1 : 1 ≤ n := by
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    rw [hcard] at h2
    cases n with
    | zero => norm_num at h2
    | succ n => omega
  have hcommu : u * u' = u' * u := by
    rw [hu, hu', ← map_mul, ← map_mul, hhcomm]
  haveI : CharP L 2 := hℓ2 ▸ hcharL
  obtain ⟨S, a, e, y, hq, hT, ha3, h1, hyM, hcent, hy3, hφe, hψe⟩ :=
    ggNbrLSideRSExc_transport_of_datum (L := L) (p₀ := 5) (f := n) hn1 D hDq2
      Nat.prime_five (by norm_num) (Or.inl le_rfl) hd.finite_model ι₀ hι₀ hd.Γ_eq φ ψ
      hφ' hψ' hmem hu3 hu1 hu'G hFix' hu'3 hcommu
  exact ⟨L, inferInstance, inferInstance, 5, S, a, e, y, CharP.cast_eq_zero L 2, hq, hT, ha3,
    h1, hyM, hcent, hy3, hφe, hψe⟩

private theorem ggNbrLSideRSExcU1Untw_recipe
    (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hcard : Nat.card K = 2 ^ n)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) (hmon : MonomialToralAt τ 3) :
    GGNbrLSideRSExcTransport τ
      (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) (2 ^ n) := by
  have hmodel := ggNbrLSideRSExcU1Untw_model τ hτ hcard hperf hmon
  have hmodel_chev : GGNbrLSideRSExcTransport τ
      (RecipeExcLang.markIDImage (IsRoot τ) K
        (MarkChev.chevH τ.cartan (IsRoot τ) K false)) (2 ^ n) :=
    (chevH_false_eq_adjointGroup K τ).symm ▸ hmodel
  have hmodel' : GGNbrLSideRSExcTransport τ
      (RecipeExcLang.markIDImage (LargeEvenIsRoot τ.cartan) K
        (MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false)) (2 ^ n) :=
    (largeEvenIsRoot_eq_isRoot τ).symm ▸ hmodel_chev
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      GGNbrLSideRSExcTransport τ (LargeEvenChevIDImage τ.cartan K H) (2 ^ n) from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [RecipeExcLang.largeEvenChevIDImage_eq]
  exact hmodel'

theorem ggNbrLSideRSExc_u1_untw :
    (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
      GGNbrLSideRSExcTransport Tag.G2
        (LargeEvenChevIDImage LargeEvenCartanG2 K (LargeEvenChevH LargeEvenCartanG2 K false))
        (2 ^ n)) ∧
    (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      GGNbrLSideRSExcTransport Tag.F4
        (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false))
        (2 ^ n)) ∧
    (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      GGNbrLSideRSExcTransport Tag.E6
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K (LargeEvenChevH (LargeEvenCartanE 6) K false))
        (2 ^ n)) ∧
    (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      GGNbrLSideRSExcTransport Tag.E7
        (LargeEvenChevIDImage (LargeEvenCartanE 7) K (LargeEvenChevH (LargeEvenCartanE 7) K false))
        (2 ^ n)) ∧
    (∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n →
      GGNbrLSideRSExcTransport Tag.E8
        (LargeEvenChevIDImage (LargeEvenCartanE 8) K (LargeEvenChevH (LargeEvenCartanE 8) K false))
        (2 ^ n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro K _ _ n hn hcard
    exact ggNbrLSideRSExcU1Untw_recipe Tag.G2 (Or.inl rfl) hcard
      (by
        have h3 : 3 ≤ Nat.card K := by
          rw [hcard]
          have h2n : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n := h2n
        exact (CFSG.LieType.Steinberg.Adjoint.isPerfect_g2_of_three_le_card K h3).commutator_eq_top)
      (by
        have hτ6 : Tag.G2 = .G2 ∨ Tag.G2 = .F4 ∨ Tag.G2 = .D4 ∨ Tag.G2 = .E6 ∨
            Tag.G2 = .E7 ∨ Tag.G2 = .E8 := by simp
        exact monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6
          Nat.prime_three (by norm_num))
  · intro K _ _ n _ hcard
    exact ggNbrLSideRSExcU1Untw_recipe Tag.F4 (Or.inr (Or.inl rfl)) hcard
      (single_edge_perfect Tag.F4 K (Or.inl rfl))
      (by
        have hτ6 : Tag.F4 = .G2 ∨ Tag.F4 = .F4 ∨ Tag.F4 = .D4 ∨ Tag.F4 = .E6 ∨
            Tag.F4 = .E7 ∨ Tag.F4 = .E8 := by simp
        exact monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6
          Nat.prime_three (by norm_num))
  · intro K _ _ n _ hcard
    exact ggNbrLSideRSExcU1Untw_recipe Tag.E6 (Or.inr (Or.inr (Or.inl rfl))) hcard
      (single_edge_perfect Tag.E6 K (Or.inr (Or.inr (Or.inl rfl))))
      (by
        have hτ6 : Tag.E6 = .G2 ∨ Tag.E6 = .F4 ∨ Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨
            Tag.E6 = .E7 ∨ Tag.E6 = .E8 := by simp
        exact monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6
          Nat.prime_three (by norm_num))
  · intro K _ _ n _ hcard
    exact ggNbrLSideRSExcU1Untw_recipe Tag.E7 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hcard
      (single_edge_perfect Tag.E7 K (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (by
        have hτ6 : Tag.E7 = .G2 ∨ Tag.E7 = .F4 ∨ Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨
            Tag.E7 = .E7 ∨ Tag.E7 = .E8 := by simp
        exact monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6
          Nat.prime_three (by norm_num))
  · intro K _ _ n _ hcard
    exact ggNbrLSideRSExcU1Untw_recipe Tag.E8 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hcard
      (single_edge_perfect Tag.E8 K (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      (by
        have hτ6 : Tag.E8 = .G2 ∨ Tag.E8 = .F4 ∨ Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨
            Tag.E8 = .E7 ∨ Tag.E8 = .E8 := by simp
        exact monomialToralAt_exc monomialToralAt_E6_five monomialToralAt_E7_five hτ6
          Nat.prime_three (by norm_num))

end CFSG.StandardType

end
