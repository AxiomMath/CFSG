module

public import CFSG.LieType.SeitzGeneration.ExcTorusPowerMap
public import CFSG.LieType.SeitzGeneration.ExcTorusE8Six
public import CFSG.LocalAnalysis.StandardType.GGTBWNorm
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDet
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public noncomputable section

namespace CFSG.StandardType.E8PowerWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice
  CFSG.StandardType.TableBExc

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem orderOf_eq_six_of_dvd {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (h : p ∣ q ^ 2 - q + 1) : orderOf (q : ZMod p) = 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  set x : ZMod p := (q : ZMod p) with hxq
  have hx : x ^ 2 - x + 1 = 0 := by
    have h0 := (ZMod.natCast_eq_zero_iff (q ^ 2 - q + 1) p).2 h
    rw [Nat.cast_add, Nat.cast_sub hq, Nat.cast_pow, Nat.cast_one] at h0
    exact h0
  have h3 : x ^ 3 = -1 := by linear_combination (x + 1) * hx
  have h6 : x ^ 6 = 1 := by linear_combination (x ^ 3 - 1) * h3
  have hne : ∀ n : ℕ, n.Prime → n ≠ p → (n : ZMod p) ≠ 0 := by
    intro n hn hnp h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact hnp ((Nat.prime_dvd_prime_iff_eq hp hn).1 h0).symm
  have h2ne : (2 : ZMod p) ≠ 0 := by exact_mod_cast hne 2 Nat.prime_two (Ne.symm hp2)
  have h3ne : (3 : ZMod p) ≠ 0 := by exact_mod_cast hne 3 Nat.prime_three (Ne.symm hp3)
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨h6, fun m hm hm0 => ?_⟩
  intro hxm
  interval_cases m
  · exact one_ne_zero (by linear_combination hx - x * hxm)
  · exact h3ne (by linear_combination hxm + (x + 2) * (hx - hxm))
  · exact h2ne (by linear_combination h3 - hxm)
  · exact h3ne (by linear_combination hx - (x - 2) * (x * h3 - hxm))
  · exact one_ne_zero (by linear_combination x ^ 4 * (x ^ 2 * h3 - hxm - hx) - hxm)


theorem exists_powerMap_mem_automizer_E8 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : SylowTorus (adjointGroup .E8 K) p 4) {k : ℕ}
    (hV : ∃ V : Subgroup (adjointGroup .E8 K), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      ∃ y : adjointGroup .E8 K, ∀ x ∈ V, y * x * y⁻¹ = x ^ k)
    {L : Type} [Group L] [Finite L] (ψ : L →* RecipeGroup .E8 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤)
    {A : Subgroup (MulAut L)} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ θ ∈ RecipeID .E8 K, ∀ l : L, θ (ψ l) = ψ (a l))
    (hsc : GGTorusSelfCent p A) :
    Nat.card A = p ^ 4 ∧ ∃ u ∈ ggAutomizer (MulAut.conj : L →* MulAut L).range A,
      ∀ b : A, u b = b ^ k := by
  classical
  have hIp : GGOutdiagPrime p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
    intro θ hθ _
    obtain ⟨x, rfl⟩ := idImage_subset_inn_E8 K hθ
    exact ⟨x, rfl⟩
  obtain ⟨Λ₀, hΛeq, hΛinj, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E8 K) hIp
      (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E8 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  obtain ⟨V, hVab, hVcard, y, hy⟩ := hV
  obtain ⟨hEcard, z, hz⟩ := hS.exists_powerMap_of_selfCent hp hVab hVcard hy hEg hEgs
  have hAcard : Nat.card A = p ^ 4 := by
    rw [← hEc, ← Subgroup.card_map_of_injective (f := ε.toMonoidHom) ε.injective]
    exact hEcard
  have hAfin : Finite A :=
    Nat.finite_of_card_ne_zero (by rw [hAcard]; exact (pow_pos hp.pos 4).ne')
  obtain ⟨l, hl⟩ := hψ (ε.symm z)
  have hγ : Λ₀ (ε.symm z) = MulAut.conj l := hΛeq hl
  let γ : MulAut L := MulAut.conj l
  have hpowA : ∀ a ∈ A, γ * a * γ⁻¹ = a ^ k := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    have heA : e ∈ A.comap Λ₀ := by rw [Subgroup.mem_comap, he]; exact ha
    have h1 : z * ε e * z⁻¹ = (ε e) ^ k := hz (ε e) ⟨e, heA, rfl⟩
    have h2 : ε.symm z * e * (ε.symm z)⁻¹ = e ^ k := by
      apply ε.injective
      rw [map_mul, map_mul, map_inv, ε.apply_symm_apply, map_pow]
      exact h1
    change MulAut.conj l * a * (MulAut.conj l)⁻¹ = a ^ k
    rw [← hγ, ← he, ← map_inv, ← map_mul, ← map_mul, h2, map_pow]
  have hAmap : A.map (MulAut.conj γ).toMonoidHom = A := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      change γ * a * γ⁻¹ ∈ A
      rw [hpowA a ha]
      exact pow_mem ha k
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj γ).toMonoidHom)
        (MulAut.conj γ).injective]
  have hγN : γ ∈ Subgroup.normalizer (A : Set (MulAut L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hAmap]
      exact ⟨x, hx, rfl⟩
    · rw [← hAmap] at hx
      obtain ⟨a, ha, hax⟩ := hx
      have hax' : γ * a * γ⁻¹ = γ * x * γ⁻¹ := hax
      rw [← mul_left_cancel (mul_right_cancel hax')]
      exact ha
  let φ₀ : MulAut ↥A := A.normalizerMonoidHom ⟨γ, hγN⟩
  have hφ₀ : φ₀ ∈ ggAutomizer (MulAut.conj : L →* MulAut L).range A :=
    Subgroup.subset_closure ⟨γ, ⟨l, rfl⟩, hγN, fun b => rfl⟩
  have hφ₀k : ∀ b : A, φ₀ b = b ^ k := by
    intro b
    apply Subtype.ext
    change γ * (b : MulAut L) * γ⁻¹ = ((b ^ k : A) : MulAut L)
    rw [hpowA b b.2, Subgroup.coe_pow]
  exact ⟨hAcard, φ₀, hφ₀, hφ₀k⟩

theorem ggTorusWNormSC_recipe_E8_of_powerMap {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : SylowTorus (adjointGroup .E8 K) p 4) {k : ℕ}
    (hV : ∃ V : Subgroup (adjointGroup .E8 K), IsElemAbelian p V ∧ Nat.card V = p ^ 4 ∧
      ∃ y : adjointGroup .E8 K, ∀ x ∈ V, y * x * y⁻¹ = x ^ k)
    (hk : ((k : ZMod p)) ^ 8 ≠ 1) :
    GGTorusWNormSC p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
  classical
  intro L _ _ ψ hψ hker hperf A hA hAI _ hsc _ Γ _ _ M C W _ _ ι φ h α _ hC hα hφ hgen φ' _
  exfalso
  obtain ⟨hAcard, φ₀, hφ₀, hφ₀k⟩ :=
    exists_powerMap_mem_automizer_E8 hp hp2 hS hV ψ hψ hker hperf hA hAI hsc
  have hAfin : Finite A :=
    Nat.finite_of_card_ne_zero (by rw [hAcard]; exact (pow_pos hp.pos 4).ne')
  rw [hgen] at hφ₀
  have hsq := ggLin_det_sq_eq_one_of_mem_closure_refl ι φ h α
    (fun i => by rw [hα i i, hC.1 i]; norm_num) hφ hφ₀
  have hdet := ggLin_det_of_pow (p := p) ι hφ₀k
  have hWfin : Finite W := Finite.of_equiv _ ι.toEquiv
  have hrank : Module.finrank (ZMod p) W = 4 := by
    have h1 := FiniteField.pow_finrank_eq_natCard p W
    rw [← Nat.card_congr ι.toEquiv, Nat.card_congr Additive.toMul, hAcard] at h1
    exact Nat.pow_right_injective hp.two_le h1
  apply hk
  have h2 := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hsq
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
  rw [hdet, hrank, ← pow_mul] at h2
  exact h2

theorem ggTorusWNormSC_recipe_E8_six {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (h6 : p ∣ Nat.card K ^ 2 - Nat.card K + 1) :
    GGTorusWNormSC p (RecipeGroup .E8 K) (RecipeID .E8 K) := by
  have he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6 := orderOf_eq_six_of_dvd hp hp2 hp3 h6
  have hpq : ¬ p ∣ Nat.card K := not_dvd_of_orderOf_pos hp he (by norm_num)
  have hlt : 6 < p := orderOf_lt_prime hp hpq he
  have hdeg : ∀ d ∈ degreesE .E8, 6 ∣ d → ¬ p ∣ d / 6 := by
    intro d hd h6d hpd
    simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | omega
        | (have := Nat.le_of_dvd (by norm_num) hpd; omega)
  obtain ⟨hS, hV⟩ := sylowTorus_powerMap_of_blocks 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp
    (by omega) (IsWeylMatrix.of_word Tag.E8 e8SixWord) [6, 6, 6, 6] e8Six_charpoly e8Six_pow he
    (by norm_num) (by simp) hdeg (by decide)
  have h4 : [6, 6, 6, 6].count 6 = 4 := by decide
  rw [h4] at hS hV
  simp only [pow_one] at hV
  refine ggTorusWNormSC_recipe_E8_of_powerMap hp hp2 hS hV ?_
  intro h8
  have h68 := orderOf_dvd_of_pow_eq_one h8
  rw [he] at h68
  norm_num at h68

theorem largeEvenLabelAll_wnorm_E8_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (htag : lab.tag = .E8)
    (h6 : p ∣ (2 ^ lab.n) ^ 2 - 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  have hf : 1 ≤ f := hlab.1
  dsimp only at htag h6 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E8_six hp hp2 hp3 (by rw [hK]; exact h6)

end CFSG.StandardType.E8PowerWNorm
