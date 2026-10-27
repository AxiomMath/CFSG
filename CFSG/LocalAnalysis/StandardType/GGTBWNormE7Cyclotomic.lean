module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormCartanScalar
public import CFSG.LocalAnalysis.StandardType.GGTBWNormE7Split
public import CFSG.LieType.SeitzGeneration.ExcTorusPowerMap
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Three
public import CFSG.LieType.SeitzGeneration.ExcTorusE7Six
public import CFSG.LieType.SeitzGeneration.ExcTorusArith

public noncomputable section

namespace CFSG.StandardType.E7Cyclotomic
open CFSG.LieType.SeitzGeneration

theorem seven_le_of_orderOf_three_or_six {p q : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : orderOf (q : ZMod p) = 3 ∨ orderOf (q : ZMod p) = 6) : 7 ≤ p := by
  by_contra hn
  have hp6 : p ≤ 6 := by omega
  have hcases : p = 5 ∨ p = 6 := by omega
  rcases hcases with rfl | rfl
  · have h6 : (q : ZMod 5) ^ 6 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by
      rcases he with h | h <;> norm_num [h])
    have hq : (q : ZMod 5) ≠ 0 := by
      intro hz
      exact (show (0 : ZMod 5) ^ 6 ≠ 1 from by decide +kernel) (hz ▸ h6)
    have h4 : (q : ZMod 5) ^ 4 = 1 :=
      (show ∀ a : ZMod 5, a ≠ 0 → a ^ 4 = 1 from by decide +kernel) _ hq
    have hd := orderOf_dvd_of_pow_eq_one h4
    rcases he with h | h <;> rw [h] at hd <;> norm_num at hd
  · exact (show ¬ Nat.Prime 6 from by decide +kernel) hp

theorem fourth_power_ne_one_of_orderOf_three_or_six {p q : ℕ}
    (he : orderOf (q : ZMod p) = 3 ∨ orderOf (q : ZMod p) = 6) :
    (q : ZMod p) ^ 4 ≠ 1 := by
  intro hz
  have hd := orderOf_dvd_of_pow_eq_one hz
  rcases he with h | h <;> rw [h] at hd <;> norm_num at hd

theorem orderOf_three_or_six_of_dvd_six_not_two {p q : ℕ}
    (hq : 1 ≤ q) (h6 : p ∣ q ^ 6 - 1) (h2 : ¬ p ∣ q ^ 2 - 1) :
    orderOf (q : ZMod p) = 3 ∨ orderOf (q : ZMod p) = 6 := by
  have hd6 : orderOf (q : ZMod p) ∣ 6 :=
    (dvd_pow_sub_one_iff_orderOf hq rfl).mp h6
  have hn2 : ¬ orderOf (q : ZMod p) ∣ 2 :=
    fun hd => h2 ((dvd_pow_sub_one_iff_orderOf hq rfl).mpr hd)
  generalize orderOf (q : ZMod p) = e at hd6 hn2 ⊢
  have he6 : e ≤ 6 := Nat.le_of_dvd (by decide) hd6
  interval_cases e <;> norm_num at *

end CFSG.StandardType.E7Cyclotomic


namespace CFSG.LieType.SeitzGeneration
open CFSG.Open CFSG.Blueprint.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Chevalley Polynomial

theorem e7_three_sylow_powerMap
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3) :
    SylowTorus (adjointGroup .E7 K) p 3 ∧
      ∃ E : Subgroup (adjointGroup .E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        ∃ y : adjointGroup .E7 K, ∀ x ∈ E, y * x * y⁻¹ = x ^ (Nat.card K ^ 2) := by
  have hother : ∀ d ∈ [1, 3, 3, 3], d ≠ 3 → ¬ p ∣ d := by
    intro d hd hne hpd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · have hb := Nat.le_of_dvd (by decide : 0 < 1) hpd
      omega
    all_goals exact hne rfl
  have hdeg : ∀ d ∈ degreesE .E7, 3 ∣ d → ¬ p ∣ d / 3 := by
    intro d hd hdiv hpd
    change d ∈ [2, 6, 8, 10, 12, 14, 18] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hdiv
    all_goals
      have hb := Nat.le_of_dvd (by norm_num) hpd
      norm_num at hb
      omega
  have hh := sylowTorus_powerMap_of_blocks 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E7 e7ThreeWord) [1, 3, 3, 3] e7Three_charpoly e7Three_pow
    he (by decide) hother hdeg (by decide)
  simpa using hh

theorem e7_six_sylow_powerMap
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    SylowTorus (adjointGroup .E7 K) p 3 ∧
      ∃ E : Subgroup (adjointGroup .E7 K), IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
        ∃ y : adjointGroup .E7 K, ∀ x ∈ E, y * x * y⁻¹ = x ^ (Nat.card K ^ 2) := by
  have hother : ∀ d ∈ [2, 6, 6, 6], d ≠ 6 → ¬ p ∣ d := by
    intro d hd hne hpd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · have hb := Nat.le_of_dvd (by decide : 0 < 2) hpd
      omega
    all_goals exact hne rfl
  have hdeg : ∀ d ∈ degreesE .E7, 6 ∣ d → ¬ p ∣ d / 6 := by
    intro d hd hdiv hpd
    change d ∈ [2, 6, 8, 10, 12, 14, 18] at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hdiv
    all_goals
      have hb := Nat.le_of_dvd (by norm_num) hpd
      norm_num at hb
      omega
  have hh := sylowTorus_powerMap_of_blocks 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) K hp (by omega)
    (IsWeylMatrix.of_word Tag.E7 e7SixWord) [2, 6, 6, 6] e7Six_charpoly e7Six_pow
    he (by decide) hother hdeg (by decide)
  simpa using hh

end CFSG.LieType.SeitzGeneration

namespace CFSG.StandardType.E7Cyclotomic
open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.CentralCover CFSG.StandardType.TableBExc
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTorusWNormSC_recipe_E7_of_powerMap
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hT : SylowTorus (adjointGroup .E7 K) p 3) {k : ℕ}
    (hPow : ∃ E0 : Subgroup (adjointGroup .E7 K), IsElemAbelian p E0 ∧
      Nat.card E0 = p ^ 3 ∧ ∃ y : adjointGroup .E7 K,
        ∀ x ∈ E0, y * x * y⁻¹ = x ^ k)
    (hk : (k : ZMod p) ^ 2 ≠ 1) :
    GGTorusWNormSC p (RecipeGroup .E7 K) (RecipeID .E7 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI _h3 hsc
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Λ0, hΛeq, hΛinj, hΛmap, hAΛ, hE, hCard, hEsc⟩ :=
    TwE6TB.exists_innerModel hp (center_recipeGroup_eq_bot .E7 K)
      (fun _ hφ _ => idImage_subset_inn_E7 K hφ) (ExcSplitL.ggCenterPrime_recipe_E7 hf hK hp hp2)
      ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E7 K
  let E := (A.comap Λ0).map ε.toMonoidHom
  have hEg : IsElemAbelian p E := TableB.isElemAbelian_map hE _
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E :=
    CFSG.GroupTheory.selfCentralizing_map_mulEquiv ε hEsc
  obtain ⟨E0, hE0, hEc0, y0, hy0⟩ := hPow
  obtain ⟨hEc, y, hy⟩ := hT.exists_powerMap_of_selfCent hp hE0 hEc0 hy0 hEg hEgs
  let t : MulAut L := Λ0 (ε.symm y)
  have hAct : ∀ a ∈ A, t * a * t⁻¹ = a ^ k := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    have heA : e ∈ A.comap Λ0 := by change Λ0 e ∈ A; rwa [he]
    have heE : ε e ∈ E := ⟨e, heA, rfl⟩
    have hePow : ε.symm y * e * (ε.symm y)⁻¹ = e ^ k := by
      apply ε.injective
      simpa only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply] using hy (ε e) heE
    have hh := congrArg Λ0 hePow
    simpa only [map_mul, map_inv, map_pow, he] using hh
  have htN : t ∈ Subgroup.normalizer (A : Set (MulAut L)) :=
    Subgroup.mem_normalizer_fintype (fun a ha => (hAct a ha).symm ▸ A.pow_mem ha k)
  let s0 : MulAut A := ggConjAut A htN
  have hsPow : ∀ a : A, s0 a = a ^ k := by
    intro a
    apply Subtype.ext
    exact (ggConjAut_apply A htN a).trans (hAct a a.2)
  have htInner : t ∈ (MulAut.conj : L →* MulAut L).range := by
    obtain ⟨l, hl⟩ := hψ (ε.symm y)
    exact ⟨l, (hΛeq hl).symm⟩
  have hsInner : s0 ∈ ggAutomizer (MulAut.conj : L →* MulAut L).range A :=
    Subgroup.subset_closure ⟨t, htInner, htN, ggConjAut_apply A htN⟩
  intro _ ιM _ _ M C V _ _ ι φ h α hM hC hpair hlin hgen φ' hφ'
  have hlin0 : ∀ v, ggLin (p := p) ι s0 v = (k : ZMod p) • v := by
    intro v
    obtain ⟨a, rfl⟩ : ∃ a : A, ι (Additive.ofMul a) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [ggLin_apply_ofMul, hsPow, ofMul_pow, map_nsmul, Nat.cast_smul_eq_nsmul (ZMod p)]
  have hsCl : ggLin (p := p) ι s0 ∈
      Subgroup.closure (Set.range (fun i => ggLin (p := p) ι (φ i))) := by
    have hh := Subgroup.mem_map_of_mem (ggLin (p := p) ι) (hgen ▸ hsInner)
    rw [MonoidHom.map_closure, ← Set.range_comp] at hh
    change ggLin (p := p) ι s0 ∈ Subgroup.closure
      (Set.range (fun i => ggLin (p := p) ι (φ i))) at hh
    exact hh
  exact (hk (scalar_sq_eq_one_of_cartan_reflection_datum hp5 M hM C hC h α hpair
    (fun i => ggLin (p := p) ι (φ i)) hlin (ggLin (p := p) ι s0) hsCl (k : ZMod p) hlin0)).elim

theorem ggTorusWNormSC_recipe_E7_cyclotomic
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = 3 ∨
      orderOf ((Nat.card K : ℕ) : ZMod p) = 6) :
    GGTorusWNormSC p (RecipeGroup .E7 K) (RecipeID .E7 K) := by
  have hp7 := seven_le_of_orderOf_three_or_six hp hp5 he
  have hh : SylowTorus (adjointGroup .E7 K) p 3 ∧
      ∃ E0 : Subgroup (adjointGroup .E7 K), IsElemAbelian p E0 ∧ Nat.card E0 = p ^ 3 ∧
        ∃ y : adjointGroup .E7 K, ∀ x ∈ E0, y * x * y⁻¹ = x ^ (Nat.card K ^ 2) := by
    rcases he with he | he
    · exact e7_three_sylow_powerMap K hp hp7 he
    · exact e7_six_sylow_powerMap K hp hp7 he
  apply ggTorusWNormSC_recipe_E7_of_powerMap hf hK hp hp5 hh.1 hh.2
  simpa only [Nat.cast_pow, ← pow_mul] using fourth_power_ne_one_of_orderOf_three_or_six he

theorem largeEvenLabelAll_wnorm_E7_cyclotomic
    {lab : LargeEvenLabel} (htag : lab.tag = .E7) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h6 : p ∣ (2 ^ lab.n) ^ 6 - 1) (h2 : ¬ p ∣ (2 ^ lab.n) ^ 2 - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag h6 h2 ⊢
  subst htag
  have hf : 1 ≤ f := by
    by_contra hn
    have hz : f = 0 := by omega
    subst f
    norm_num at h2
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  apply ggTorusWNormSC_recipe_E7_cyclotomic hf hK hp hp5
  rw [hK]
  exact orderOf_three_or_six_of_dvd_six_not_two
    (Nat.one_le_pow _ _ (by decide : 1 ≤ (2 : ℕ))) h6 h2

end CFSG.StandardType.E7Cyclotomic
