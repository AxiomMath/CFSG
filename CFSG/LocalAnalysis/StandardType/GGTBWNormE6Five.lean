module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormE6Split
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralFrobeniusFixed
public import CFSG.LocalAnalysis.StandardType.GGExcElemToralLangStep

public noncomputable section

namespace CFSG.StandardType.E6WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.C14Lattice


theorem _root_.CFSG.StandardType.ExcElemToral.exists_conj_le_torusPow_of_toralWitness
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E)
    (g : ModGL τ (AlgebraicClosure K))
    (hg : g ∈ adjointGroup τ (AlgebraicClosure K))
    (htor : ∀ x : E, g⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
        torusGroup τ (AlgebraicClosure K))
    (hfamily : ∀ a : E → Fin τ.rank → (AlgebraicClosure K)ˣ,
      Function.Injective a → (∀ x j, a x j ^ p = 1) →
      familyCentralizer τ (AlgebraicClosure K) a =
        familyGroup (K := AlgebraicClosure K) a) :
    ∃ c : adjointGroup τ K, ∀ x ∈ E,
      (c * x * c⁻¹ : adjointGroup τ K) ∈ TableBExc.torusPow τ K p := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact p.Prime := ⟨hp⟩
  let L := AlgebraicClosure K
  let : Fintype K := Fintype.ofFinite K
  let : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  let ι : K →+* L := algebraMap K L
  let φ : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype
  have hφ : Function.Injective φ := fun _ _ h =>
    Subtype.ext (baseChangeGL_injective ι h)
  choose a ha using fun x : E => exists_rootDiagUnit_eq_of_mem_torusGroup (htor x)
  have hexp : ∀ (x : E) j, a x j ^ p = 1 := by
    intro x
    have hpow : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      rw [show rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p from
        (rootDiagUnitHom τ L).map_pow (a x) p, ← ha x, rootDiagUnit_one]
      change (g⁻¹ * φ (x : adjointGroup τ K) * g) ^ p = 1
      rw [show g⁻¹ * φ (x : adjointGroup τ K) * g =
        (MulAut.conj g⁻¹) (φ (x : adjointGroup τ K)) by simp only [MulAut.conj_apply, inv_inv],
        ← map_pow, ← map_pow, hE.2 x x.2, map_one, map_one]
    exact fun j => congrFun (rootDiagUnit_injective hpow) j
  have hainj : Function.Injective a := by
    intro x y hxy
    apply Subtype.ext
    apply hφ
    apply (MulAut.conj g⁻¹).injective
    change g⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g =
      g⁻¹ * baseChangeGL (algebraMap K L) (y : ModGL τ K) * g
    rw [ha x, ha y, hxy]
  obtain ⟨f, _, hKf⟩ := FiniteField.card K 2
  have hf : 1 ≤ (f : ℕ) := f.pos
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  have haq : ∀ x j, a x j ^ 2 ^ (f : ℕ) = a x j := by
    intro x j
    rw [← hK]
    obtain ⟨k, hk⟩ := hpq
    have hKpos : 1 < Nat.card K := Finite.one_lt_card
    have hq : Nat.card K = p * k + 1 := by rw [← hk]; omega
    rw [hq, pow_succ, pow_mul, hexp, one_pow, one_mul]
  have hcent : familyCentralizer τ L a = familyGroup (K := L) a :=
    hfamily a hainj hexp
  have hFix : ∀ y : ModGL τ K, entrywiseFrobGL τ L 2 f (baseChangeGL ι y) =
      baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L 2 (f : ℕ)).comp ι = ι := by
      apply RingHom.ext
      intro t
      change iterateFrobenius L 2 f (ι t) = ι t
      rw [iterateFrobenius_def, ← map_pow, ← hKf]
      exact congrArg ι (FiniteField.pow_card t)
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hgx : ∀ x : E, g * rootDiagUnit τ (a x) * g⁻¹ = φ (x : adjointGroup τ K) := by
    intro x
    change g * rootDiagUnit τ (a x) * g⁻¹ =
      baseChangeGL (algebraMap K L) (x : ModGL τ K)
    rw [← ha x]
    group
    rfl
  obtain ⟨h, hh, hFh, hhx⟩ := ExcElemToral.exists_frobenius_fixed_conj_of_family 2 hf a
    haq hcent (inv_mem hg) (fun x => by
      rw [inv_inv, hgx]
      exact hFix (x : ModGL τ K))
  let Fr : L →+* L := iterateFrobenius L 2 f
  have hFr : ∀ t, Fr t = t ^ Nat.card K := fun t => by
    rw [show Fr t = t ^ 2 ^ (f : ℕ) from rfl, ← hK]
  obtain ⟨D, hD, j, hj, hhj⟩ :=
    ExcElemToral.exists_mem_torusGroup_mul_baseChangeGL_of_frobenius_fixed Fr hFr hh hFh
  let c : adjointGroup τ K := ⟨j, hj⟩
  refine ⟨c, ?_⟩
  intro x hx
  let hxE : E := ⟨x, hx⟩
  have heq : baseChangeGL ι (j * (x : ModGL τ K) * j⁻¹) = rootDiagUnit τ (a hxE) := by
    have hz := hhx hxE
    have hz' : h * φ x * h⁻¹ = rootDiagUnit τ (a hxE) := by
      rw [inv_inv, hgx] at hz
      change h⁻¹ * rootDiagUnit τ (a hxE) * h = φ x at hz
      rw [← hz]
      group
    rw [hhj] at hz'
    change D * baseChangeGL ι j * φ x * (D * baseChangeGL ι j)⁻¹ = rootDiagUnit τ (a hxE) at hz'
    have hDa : D * rootDiagUnit τ (a hxE) = rootDiagUnit τ (a hxE) * D :=
      CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm hD (rootDiagUnit_mem_torusGroup _)
    change (baseChangeGL ι) (j * (x : ModGL τ K) * j⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    change baseChangeGL ι j * φ x * (baseChangeGL ι j)⁻¹ = _
    calc _ = D⁻¹ * (D * baseChangeGL ι j * φ x * (D * baseChangeGL ι j)⁻¹) * D := by group
      _ = D⁻¹ * rootDiagUnit τ (a hxE) * D := by rw [hz']
      _ = rootDiagUnit τ (a hxE) := by
        calc _ = D⁻¹ * (rootDiagUnit τ (a hxE) * D) := by group
          _ = D⁻¹ * (D * rootDiagUnit τ (a hxE)) := by rw [← hDa]
          _ = rootDiagUnit τ (a hxE) := by group
  have ht : (c * x * c⁻¹ : adjointGroup τ K) ∈ TableBExc.torusPow τ K p := by
    refine ⟨?_, ?_⟩
    · exact CFSG.RankThree.Classical2.mem_torusGroup_of_baseChangeGL_mem ι
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hj x.2) (Subgroup.inv_mem _ hj))
        (heq ▸ rootDiagUnit_mem_torusGroup _)
    · rw [conj_pow, hE.2 x hx]; group
  exact ht

theorem _root_.CFSG.StandardType.ExcElemToral.exists_conj_le_torusPow_of_nonTorsion
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h3 : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 → p ≠ 3) (h5 : τ = .E8 → p ≠ 5)
    (hpq : p ∣ Nat.card K - 1) (E : Subgroup (adjointGroup τ K)) (hE : IsElemAbelian p E) :
    ∃ c : adjointGroup τ K, ∀ x ∈ E,
      (c * x * c⁻¹ : adjointGroup τ K) ∈ TableBExc.torusPow τ K p := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact p.Prime := ⟨hp⟩
  let L := AlgebraicClosure K
  let : Fintype K := Fintype.ofFinite K
  let : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  let ι : K →+* L := algebraMap K L
  let φ : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL ι).comp (adjointGroup τ K).subtype
  let A := E.map φ
  have hA : A ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup (f := ι) x.2
  have hAe : CFSG.Open.IsElemAbelian p A := TableB.isElemAbelian_map hE φ
  have hsur : Function.Surjective (fun x : E =>
      (⟨φ (x : adjointGroup τ K), Subgroup.mem_map_of_mem φ x.2⟩ : A)) := by
    rintro ⟨y, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let : Finite A := Finite.of_surjective _ hsur
  have halg := CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite K 2
  obtain ⟨g, hg, hgt⟩ := LieCore.isToralSubgroup_of_nonTorsion hp hp2 h3 h5
    (Ne.symm hp2) halg hA (inferInstance : Finite A) hAe
  exact ExcElemToral.exists_conj_le_torusPow_of_toralWitness hp hpq E hE g hg
    (fun x => hgt _ (Subgroup.mem_map_of_mem φ x.2))
    (fun a _ ha => familyCentralizer_eq_familyGroup_of_nonTorsion hp hp2 h3 h5 a ha)


theorem exists_conj_le_torus_five {K : Type} [Field K] [Finite K] [CharP K 2]
    (h5 : 5 ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .E6 K))
    (hE : IsElemAbelian 5 E) :
    ∃ c : adjointGroup .E6 K, ∀ x ∈ E,
      (c * x * c⁻¹ : adjointGroup .E6 K) ∈ TableBExc.torusPow .E6 K 5 :=
  ExcElemToral.exists_conj_le_torusPow_of_nonTorsion Nat.prime_five (by decide)
    (fun _ => by decide) (by intro h; cases h) h5 E hE

theorem card_eq_six_of_selfCent_five {K : Type} [Field K] [Finite K] [CharP K 2]
    (h5 : 5 ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .E6 K))
    (hE : IsElemAbelian 5 E)
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ 5 = 1 → g ∈ E) :
    Nat.card E = 5 ^ 6 := by
  obtain ⟨c, hct⟩ := exists_conj_le_torus_five h5 E hE
  let E' := E.map (MulAut.conj c).toMonoidHom
  have hle : E' ≤ TableBExc.torusPow .E6 K 5 := by
    rintro y ⟨x, hx, rfl⟩
    exact hct x hx
  have hback : TableBExc.torusPow .E6 K 5 ≤ E' := by
    intro t ht
    have hx : c⁻¹ * t * c ∈ E := by
      apply hsc
      · intro e he
        have hc := CFSG.LieType.Chevalley.RootTorus.torusGroup_mul_comm
          ht.1 (hct e he).1
        have hc' : t * (c * e * c⁻¹) = (c * e * c⁻¹) * t := Subtype.ext hc
        calc (c⁻¹ * t * c) * e = c⁻¹ * (t * (c * e * c⁻¹)) * c := by group
          _ = e * (c⁻¹ * t * c) := by rw [hc']; group
      · change (c⁻¹ * t * (c⁻¹)⁻¹) ^ 5 = 1
        rw [conj_pow, ht.2]; group
    exact ⟨c⁻¹ * t * c, hx, by change c * (c⁻¹ * t * c) * c⁻¹ = t; group⟩
  have hEq : E' = TableBExc.torusPow .E6 K 5 := le_antisymm hle hback
  have hc : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [← hc, hEq]
  exact TableBExc.card_torusPow_E6 Nat.prime_five (by decide) h5


theorem ggTorusWNormSC_recipe_E6_five {K : Type} [Field K] [Finite K] [CharP K 2]
    (h5 : 5 ∣ Nat.card K - 1) :
    GGTorusWNormSC 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : NeZero (5 : ℕ) := ⟨by decide⟩
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel Nat.prime_five (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (TableBExc.ggOutdiagPrime_E6 Nat.prime_five (by decide))
      (ExcSplitL.ggCenterPrime_recipe_E6 Nat.prime_five (by decide) (by decide))
      ψ hψ hker hperf hA hAI hsc
  let ε := TableBExc.recipeEquiv .E6 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian 5 E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ 5 = 1 → g ∈ E := by
    intro g hg hgp
    have hx : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hx, ε.apply_symm_apply g⟩
  have hc := card_eq_six_of_selfCent_five h5 E hEg hEgs
  have hA6 : 5 ^ 6 ≤ Nat.card A := by
    rw [Subgroup.card_map_of_injective ε.injective, hEc] at hc
    exact hc.ge
  obtain ⟨ψa, hψa, hka, Λ, hΛ, hΛn, -, hFA⟩ :=
    TBE6Ind.exists_aligned_adjoint Nat.prime_five (by decide) (by decide) h5 ψ A
      ⟨hψ, hker, hperf, hA, hAI, hA6, h3, hsc⟩
  obtain ⟨κ, hW⟩ := exists_coordinates_aligned_of_ge_five Nat.prime_five (by decide) h5
    ψa hψa hka A Λ hΛ hΛn hFA
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact wNormConcl_of_full_frame (by decide) A κ hW ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E6_five {lab : LargeEvenLabel}
    (htag : lab.tag = .E6) (h5 : 5 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC 5 R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag h5 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E6_five (by rw [hK]; exact h5)

end CFSG.StandardType.E6WNorm
