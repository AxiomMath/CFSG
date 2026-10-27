module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmall
public import CFSG.LocalAnalysis.StandardType.GGPGLTorality

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.ComponentClassification CFSG.Assembly
open scoped commutatorElement

variable {d p : ℕ} {K : Type} [Field K]

section Blocks

theorem coordBlockSL_inf_scalars_of_not_mem {S : Finset (Fin d)} {k₀ : Fin d} (hk₀ : k₀ ∉ S)
    {s : SpecialLinearGroup (Fin d) K} (hs : s ∈ coordBlockSL K S) (hz : s ∈ scalars d K) :
    s = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  have h1 := mem_coordBlockSL_iff.mp hs k₀ k₀ (Or.inl hk₀)
  rw [ite_eq_left rfl, hc, scalar_apply, diagonal_apply_eq] at h1
  ext i j
  rw [hc, h1, map_one]
  rfl

variable {D : GL (Fin d) K} {t : Fin d → K}

theorem coordBlockSL_le_fix_of_const (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    {S : Finset (Fin d)} (hS : ∀ k ∈ S, ∀ l ∈ S, t k = t l) :
    coordBlockSL K S ≤ ggFix (CatalogueBHigherLinearAction.slConjugation d K D) := by
  intro s hs
  rw [mem_ggFix_slConjugation_iff hD]
  intro k l hkl
  have hne : k ≠ l := fun h => hkl (h ▸ rfl)
  have hout : k ∉ S ∨ l ∉ S := by
    by_contra h
    simp only [not_or, not_not] at h
    exact hkl (hS k h.1 l h.2)
  rw [mem_coordBlockSL_iff.mp hs k l hout, ite_eq_right hne]

theorem conj_mem_coordBlockSL_of_level (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    {S : Finset (Fin d)} {i : Fin d} (hS : ∀ k, k ∈ S ↔ t k = t i)
    {c g : SpecialLinearGroup (Fin d) K}
    (hc : c ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D))
    (hg : g ∈ coordBlockSL K S) : c * g * c⁻¹ ∈ coordBlockSL K S := by
  apply conj_mem_coordBlockSL _ hg
  have h := (mem_ggFix_slConjugation_iff hD).mp hc
  ext k l
  rw [compIndicator_mul_apply, mul_compIndicator_apply]
  by_cases hk : k ∈ S <;> by_cases hl : l ∈ S
  · rw [ite_eq_left hk, ite_eq_left hl]
  · rw [ite_eq_left hk, ite_eq_right hl,
      h k l fun hkl => hl ((hS l).mpr (hkl.symm.trans ((hS k).mp hk)))]
  · rw [ite_eq_right hk, ite_eq_left hl,
      h k l fun hkl => hk ((hS k).mpr (hkl.trans ((hS l).mp hl)))]
  · rw [ite_eq_right hk, ite_eq_right hl]

theorem commutator_fix_eq_bot_of_injective (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (ht : Function.Injective t) :
    ⁅ggFix (CatalogueBHigherLinearAction.slConjugation d K D),
      ggFix (CatalogueBHigherLinearAction.slConjugation d K D)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hdiag : ∀ u ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D),
      (u : Matrix (Fin d) (Fin d) K) = diagonal fun k => (u : Matrix (Fin d) (Fin d) K) k k := by
    intro u hu
    apply eq_diagonal_of_offDiag
    intro k l hkl
    exact (mem_ggFix_slConjugation_iff hD).mp hu k l (fun h => hkl (ht h))
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro s' hs'
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hdiag s hs,
    hdiag s' hs', diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext k
  ring

end Blocks

section Main

variable [Finite K]

theorem layer_coordBlockSL_map_le (h4 : 4 ≤ Nat.card K) {L' : Type} [Group L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {a : MulAut L'} {D : GL (Fin d) K}
    {t : Fin d → K} (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (haD : ∀ s, a (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K D s))
    (ha1 : a ≠ 1) {i j : Fin d} (hij : i ≠ j) (htij : t i = t j) :
    ∃ S : Finset (Fin d), (∀ k, k ∈ S ↔ t k = t i) ∧ 2 ≤ S.card ∧
      IsComponentOf ((coordBlockSL K S).map φ) (ggFix a) ∧
      (coordBlockSL K S).map φ ≤ LargeEvenLayer (ggFix a) ∧
      (∀ g ∈ coordBlockSL K S, ∀ h ∈ coordBlockSL K S, φ g = φ h → g = h) := by
  classical
  set C := ggFix (CatalogueBHigherLinearAction.slConjugation d K D) with hC
  set F := ggFix a with hFdef
  have hCF : C.map φ ≤ F := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_ggFix, haD, mem_ggFix.mp hc]
  have hFdesc : ∀ f ∈ F, ∃ s z, φ s = f ∧ z ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) ∧
      CatalogueBHigherLinearAction.slConjugation d K D s = s * z := by
    intro f hf
    obtain ⟨s, rfl⟩ := hφs f
    refine ⟨s, s⁻¹ * CatalogueBHigherLinearAction.slConjugation d K D s, rfl, ?_, by group⟩
    apply scalars_le_center d K
    apply hφker
    rw [map_mul, map_inv, ← haD s, mem_ggFix.mp hf, inv_mul_cancel]
  have hCn : ((C.map φ).subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCF]
    rintro _ f ⟨c, hc, rfl⟩ hf
    obtain ⟨s, z, rfl, hz, hsz⟩ := hFdesc f hf
    refine ⟨s * c * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change CatalogueBHigherLinearAction.slConjugation d K D (s * c * s⁻¹) = s * c * s⁻¹
    rw [map_mul, map_mul, map_inv, hsz, mem_ggFix.mp hc]
    have hzc := (Subgroup.mem_center_iff.mp hz) c
    calc s * z * c * (s * z)⁻¹ = s * (z * c) * z⁻¹ * s⁻¹ := by group
      _ = s * (c * z) * z⁻¹ * s⁻¹ := by rw [hzc]
      _ = s * c * s⁻¹ := by group
  set S : Finset (Fin d) := Finset.univ.filter fun k => t k = t i with hSdef
  have hS : ∀ k, k ∈ S ↔ t k = t i := fun k => by simp [hSdef]
  have hiS : i ∈ S := (hS i).mpr rfl
  have hjS : j ∈ S := (hS j).mpr htij.symm
  have hS2 : 2 ≤ S.card := by
    have h1 : ({i, j} : Finset (Fin d)) ⊆ S := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hiS
      · rw [Finset.mem_singleton.mp hk]
        exact hjS
    have h2 := Finset.card_le_card h1
    rwa [Finset.card_pair hij] at h2
  have hSconst : ∀ k ∈ S, ∀ l ∈ S, t k = t l := fun k hk l hl =>
    ((hS k).mp hk).trans ((hS l).mp hl).symm
  obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ ∉ S := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply ha1
    ext l
    obtain ⟨s, rfl⟩ := hφs l
    rw [haD, slConjugation_eq_self_of_const hD (fun k => (hS k).mp (hcon k)) (diag_ne_zero hD i)]
    rfl
  set J₀ := coordBlockSL K S with hJ₀
  set J₁ := J₀.map φ with hJ₁
  have hJ₀C : J₀ ≤ C := coordBlockSL_le_fix_of_const hD hSconst
  have hJ₁C : J₁ ≤ C.map φ := Subgroup.map_mono hJ₀C
  have hJF : J₁ ≤ F := hJ₁C.trans hCF
  have hinj : ∀ g ∈ J₀, ∀ h ∈ J₀, φ g = φ h → g = h := by
    intro g hg h hh hgh
    have h1 : φ (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, hgh, inv_mul_cancel]
    exact inv_mul_eq_one.mp (coordBlockSL_inf_scalars_of_not_mem hk₀
      (J₀.mul_mem (J₀.inv_mem hg) hh) (hφker _ h1))
  have hinj' : Function.Injective (φ.comp J₀.subtype) := fun x y hxy =>
    Subtype.ext (hinj x x.2 y y.2 hxy)
  have hrange : (φ.comp J₀.subtype).range = J₁ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple J₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange))
      (isQuasisimple_coordBlockSL hS2 h4)
  have hJn : (J₁.subgroupOf (C.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJ₁C]
    rintro _ _ ⟨g, hg, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * g * c⁻¹, conj_mem_coordBlockSL_of_level hD hS hc hg,
      by rw [map_mul, map_mul, map_inv]⟩
  have hJcomp : IsComponentOf J₁ F :=
    ⟨hJF, IsSubnormal.step hJ₁C hJn (IsSubnormal.step hCF hCn (IsSubnormal.refl F)),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J₁).mpr hJq⟩
  have hJE : J₁ ≤ LargeEvenLayer F := le_sSup hJcomp
  exact ⟨S, hS, hS2, hJcomp, hJE, hinj⟩

theorem ggStdSubTwoTorus_of_model [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (h4 : 4 ≤ Nat.card K) {L' : Type} [Group L'] [Finite L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hmodel : ∀ a ∈ A, ∃ D : GL (Fin d) K,
      (∃ t : Fin d → K, (D : Matrix (Fin d) (Fin d) K) = diagonal t) ∧
      ∀ s, a (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K D s))
    {a : MulAut L'} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hEcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ U ≤ LargeEvenLayer (ggFix a) ∧
      (∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) ∧
      ∃ t ∈ LargeEvenLayer (ggFix a), t ^ p = 1 ∧ (∀ a' ∈ A, a' t = t) ∧
        t ∈ Subgroup.normalizer (U : Set L') ∧
        ∃ j ∈ LargeEvenLayer (ggFix a), t * j ≠ j * t := by
  classical
  obtain ⟨D, ⟨t, hD⟩, haD⟩ := hmodel a haA
  set C := ggFix (CatalogueBHigherLinearAction.slConjugation d K D) with hC
  set F := ggFix a with hFdef
  have hCF : C.map φ ≤ F := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_ggFix, haD, mem_ggFix.mp hc]
  have hFdesc : ∀ f ∈ F, ∃ s z, φ s = f ∧ z ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) ∧
      CatalogueBHigherLinearAction.slConjugation d K D s = s * z := by
    intro f hf
    obtain ⟨s, rfl⟩ := hφs f
    refine ⟨s, s⁻¹ * CatalogueBHigherLinearAction.slConjugation d K D s, rfl, ?_, by group⟩
    apply scalars_le_center d K
    apply hφker
    rw [map_mul, map_inv, ← haD s, mem_ggFix.mp hf, inv_mul_cancel]
  have hCn : ((C.map φ).subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCF]
    rintro _ f ⟨c, hc, rfl⟩ hf
    obtain ⟨s, z, rfl, hz, hsz⟩ := hFdesc f hf
    refine ⟨s * c * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    change CatalogueBHigherLinearAction.slConjugation d K D (s * c * s⁻¹) = s * c * s⁻¹
    rw [map_mul, map_mul, map_inv, hsz, mem_ggFix.mp hc]
    have hzc := (Subgroup.mem_center_iff.mp hz) c
    calc s * z * c * (s * z)⁻¹ = s * (z * c) * z⁻¹ * s⁻¹ := by group
      _ = s * (c * z) * z⁻¹ * s⁻¹ := by rw [hzc]
      _ = s * c * s⁻¹ := by group
  have hFF : ⁅F, F⁆ ≤ C.map φ := by
    rw [Subgroup.commutator_le]
    intro f₁ hf₁ f₂ hf₂
    obtain ⟨s₁, z₁, rfl, hz₁, hs₁⟩ := hFdesc f₁ hf₁
    obtain ⟨s₂, z₂, rfl, hz₂, hs₂⟩ := hFdesc f₂ hf₂
    refine ⟨⁅s₁, s₂⁆, ?_, by rw [map_commutatorElement]⟩
    change CatalogueBHigherLinearAction.slConjugation d K D ⁅s₁, s₂⁆ = ⁅s₁, s₂⁆
    rw [map_commutatorElement, hs₁, hs₂, commutatorElement_mul_central hz₁ hz₂]
  obtain ⟨i, j, hij, htij⟩ : ∃ i j, i ≠ j ∧ t i = t j := by
    by_contra hcon
    have ht : Function.Injective t := by
      intro k l hkl
      by_contra hne
      exact hcon ⟨k, l, hne, hkl⟩
    have hC2 : ⁅C.map φ, C.map φ⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, commutator_fix_eq_bot_of_injective hD ht, Subgroup.map_bot]
    have hq' := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native
      _).mp hEcomp.2.2
    have hperfE : ⁅LargeEvenLayer F, LargeEvenLayer F⁆ = LargeEvenLayer F :=
      Subgroup.isPerfect_iff.mp hq'.1
    have hbot : LargeEvenLayer F = ⊥ := by
      have h1 : ⁅LargeEvenLayer F, LargeEvenLayer F⁆ ≤ C.map φ :=
        (Subgroup.commutator_mono hEcomp.1 hEcomp.1).trans hFF
      rw [hperfE] at h1
      rw [← hperfE, eq_bot_iff, ← hC2]
      exact Subgroup.commutator_mono h1 h1
    have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq'
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(LargeEvenLayer F))
    apply hy
    apply Subtype.ext
    have hy' : (y : L') ∈ (⊥ : Subgroup L') := hbot ▸ y.2
    exact Subgroup.mem_bot.mp hy'
  obtain ⟨S, hS, hS2, hJcomp, hJElayer, hinj⟩ :=
    layer_coordBlockSL_map_le h4 hφs hφker hD haD ha1 hij htij
  have hiS : i ∈ S := (hS i).mpr rfl
  have hjS : j ∈ S := (hS j).mpr htij.symm
  set J₀ := coordBlockSL K S with hJ₀
  set J₁ := J₀.map φ with hJ₁
  have hJE : J₁ ≤ LargeEvenLayer F := hJElayer
  have htrJ : ∀ c : K, SpecialLinearGroup.transvection hij c ∈ J₀ := by
    intro c
    rw [hJ₀, mem_coordBlockSL_iff]
    intro k l hkl
    rw [CFSG.LinearGroups.coe_transvection]
    rcases hkl with hk | hl
    · have hki : i ≠ k := fun h => hk (h ▸ hiS)
      simp [Matrix.add_apply, Matrix.one_apply, hki]
    · have hlj : j ≠ l := fun h => hl (h ▸ hjS)
      simp [Matrix.add_apply, Matrix.one_apply, hlj]
  set U₀ := (SpecialLinearGroup.transvectionHom hij : Multiplicative K →* _).range with hU₀
  set U := U₀.map φ with hU
  have hU₀J : U₀ ≤ J₀ := by
    rintro _ ⟨c, rfl⟩
    rw [SpecialLinearGroup.transvectionHom_apply]
    exact htrJ _
  have hUE : U ≤ LargeEvenLayer F := (Subgroup.map_mono hU₀J).trans hJE
  have hU1 : U ≠ ⊥ := by
    intro hbot
    have hmem : φ (SpecialLinearGroup.transvection hij 1) ∈ U :=
      ⟨_, ⟨Multiplicative.ofAdd 1, by rw [SpecialLinearGroup.transvectionHom_apply, toAdd_ofAdd]⟩,
        rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (hφker _ hmem)
    have h1 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i j) hc
    simp [CFSG.LinearGroups.coe_transvection, hij] at h1
  have hU2 : IsPGroup 2 U := by
    refine IsPGroup.map (fun y => ⟨1, ?_⟩) φ
    obtain ⟨y, c, hc⟩ := y
    have h2 : y ^ 2 = 1 := by
      rw [← hc, SpecialLinearGroup.transvectionHom_apply,
        CFSG.RankThree.CALinearPlane.transvection_pow, Nat.cast_ofNat, CharTwo.two_eq_zero,
        zero_mul]
      exact Matrix.SpecialLinearGroup.transvection_coeff_zero hij
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact h2
  have hAU : ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U := by
    intro a' ha' u hu
    obtain ⟨D', ⟨t', hD'⟩, ha'D⟩ := hmodel a' ha'
    obtain ⟨_, ⟨c, rfl⟩, rfl⟩ := hu
    rw [ha'D, SpecialLinearGroup.transvectionHom_apply,
      slConjugation_transvection_of_diagonal hD' hij]
    exact ⟨_, ⟨Multiplicative.ofAdd _, by rw [SpecialLinearGroup.transvectionHom_apply,
      toAdd_ofAdd]⟩, rfl⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpK
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  set τ : Fin d → K := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹ with hτ
  have hτi : τ i = ζ := by simp [hτ, hij]
  have hτj : τ j = ζ⁻¹ := by simp [hτ, hij.symm]
  have hτk : ∀ k, k ≠ i → k ≠ j → τ k = 1 := fun k hki hkj => by
    simp [hτ, hki, hkj]
  have hτdet : (diagonal τ).det = 1 := by
    rw [det_diagonal, hτ]
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, Finset.prod_pi_mulSingle', Finset.prod_pi_mulSingle',
      ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), mul_inv_cancel₀ hζ0]
  set D₀ : SpecialLinearGroup (Fin d) K := ⟨diagonal τ, hτdet⟩ with hD₀
  have hD₀mat : (D₀ : Matrix (Fin d) (Fin d) K) = diagonal τ := rfl
  have hD₀J : D₀ ∈ J₀ := by
    rw [hJ₀, mem_coordBlockSL_iff]
    intro k l hkl
    rw [hD₀mat, diagonal_apply]
    split_ifs with hkl'
    · subst hkl'
      have hki : k ≠ i := fun h => by rcases hkl with h' | h' <;> exact h' (h ▸ hiS)
      have hkj : k ≠ j := fun h => by rcases hkl with h' | h' <;> exact h' (h ▸ hjS)
      exact hτk k hki hkj
    · rfl
  have hD₀p : D₀ ^ p = 1 := by
    have h1 : τ ^ p = fun _ => (1 : K) := by
      funext k
      rw [Pi.pow_apply]
      by_cases hki : k = i
      · rw [hki, hτi, hζp]
      · by_cases hkj : k = j
        · rw [hkj, hτj, inv_pow, hζp, inv_one]
        · rw [hτk k hki hkj, one_pow]
    ext k l
    rw [Matrix.SpecialLinearGroup.coe_pow, hD₀mat, diagonal_pow, h1, diagonal_one]
    rfl
  have hA0 : ∀ a' ∈ A, a' (φ D₀) = φ D₀ := by
    intro a' ha'
    obtain ⟨D', ⟨t', hD'⟩, ha'D⟩ := hmodel a' ha'
    rw [ha'D]
    congr 1
    apply mem_ggFix.mp
    rw [mem_ggFix_slConjugation_iff hD']
    intro k l hkl
    rw [hD₀mat, diagonal_apply_ne _ (fun h => hkl (by rw [h]))]
  have hfin : IsOfFinOrder D₀ := isOfFinOrder_iff_pow_eq_one.mpr ⟨p, hp.pos, hD₀p⟩
  have hD₀diag : ∀ g ∈ Subgroup.zpowers D₀,
      ∃ s : Fin d → K, (g : Matrix (Fin d) (Fin d) K) = diagonal s := by
    intro g hg
    obtain ⟨n, rfl⟩ := hfin.mem_powers_iff_mem_zpowers.mpr hg
    exact ⟨τ ^ n, by rw [Matrix.SpecialLinearGroup.coe_pow, hD₀mat, diagonal_pow]⟩
  have hD₀N : D₀ ∈ Subgroup.normalizer (U₀ : Set (SpecialLinearGroup (Fin d) K)) :=
    le_normalizer_rootGroup hD₀diag hij (Subgroup.mem_zpowers D₀)
  have ht₀N : φ D₀ ∈ Subgroup.normalizer (U : Set L') :=
    Subgroup.le_normalizer_map φ ⟨D₀, hD₀N, rfl⟩
  refine ⟨U, hU1, hU2, hUE, hAU, φ D₀, hJE ⟨D₀, hD₀J, rfl⟩, ?_, hA0, ht₀N,
    φ (SpecialLinearGroup.transvection hij 1), hJE ⟨_, htrJ 1, rfl⟩, ?_⟩
  · rw [← map_pow, hD₀p, map_one]
  · intro hcomm
    have h1 : φ (D₀ * SpecialLinearGroup.transvection hij 1) =
        φ (SpecialLinearGroup.transvection hij 1 * D₀) := by
      rw [map_mul, map_mul]
      exact hcomm
    have h2 := hinj _ (J₀.mul_mem hD₀J (htrJ 1)) _ (J₀.mul_mem (htrJ 1) hD₀J) h1
    have h3 : D₀ * SpecialLinearGroup.transvection hij 1 * D₀⁻¹ =
        SpecialLinearGroup.transvection hij 1 := by
      rw [h2, mul_inv_cancel_right]
    rw [conj_transvection_of_diagonal hD₀mat hij, hτi, hτj] at h3
    have h4 := congrArg (fun g : SpecialLinearGroup (Fin d) K => (g : Matrix (Fin d) (Fin d) K) i j)
      h3
    simp [CFSG.LinearGroups.coe_transvection, hij] at h4
    have hζ2 : ζ ^ 2 = 1 := by
      rw [sq]
      exact h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hζ.dvd_of_pow_eq_one 2 hζ2))

theorem ggStdSubTwoTorus_coprime [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 4 ≤ d) (hpd : Nat.Coprime p d) (h4 : 4 ≤ Nat.card K)
    (hsec : SLHasSections d K) (r : ℕ) :
    GGStdSubTwoTorus p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ _ a haA ha1 hEcomp _
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  obtain ⟨φ', hφ's, hφ'ker, hdiag, -, -⟩ :=
    exists_diagonal_model hp hpK (by omega) hpd hperfSL hψ hker hperf hφs hφ hA hAI
  refine ggStdSubTwoTorus_of_model hp hp2 hpK h4 hφ's hφ'ker (fun a' ha' => ?_) haA ha1 hEcomp
  obtain ⟨D, ⟨t, hD⟩, -, haD⟩ := hdiag a' ha'
  refine ⟨SpecialLinearGroup.toGL D, ⟨t, hD⟩, fun s => ?_⟩
  rw [haD]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation, map_mul, map_mul, map_inv]


theorem ggStdSubTwoTorus_small (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) (r : ℕ) :
    GGStdSubTwoTorus p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hle := card_le_of_subset_conjAut hp hpK hd hpd hX hXI
  rw [hcard] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans hle)
  omega

theorem ggStdSubTwoTorus_of_torality [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d) (h4 : 4 ≤ Nat.card K) (hsec : SLHasSections d K)
    (htor : GGPGLTorality p d K) :
    GGStdSubTwoTorus p (d - 2) (projectiveSL d K) (Set.range (conjAut d K)) := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 a haA ha1 hEcomp _
  have hperfSL : commutator (SpecialLinearGroup (Fin d) K) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (K := K) (n := d) (by omega)
      (Or.inl (by omega))).commutator_eq_top
  obtain ⟨φ, hφs, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  set X := inducedSub ψ A with hX
  have hXA : IsElemAbelian p X := isElemAbelian_inducedSub hψ hA
  have hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have hcardX : Nat.card X = Nat.card A := card_inducedSub hψ hker hperf (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  obtain ⟨A₀, hA₀⟩ := htor X hXA hXI (hcardX ▸ hr) (hcardX ▸ h3)
  set c₀ := CatalogueBHigherLinearAction.slConjugation d K A₀⁻¹ with hc₀
  set φ' := φ.comp c₀.toMonoidHom with hφ'
  have hφ's : Function.Surjective φ' := hφs.comp c₀.surjective
  have hφ'ker : ∀ g, φ' g = 1 → g ∈ scalars d K := by
    intro g hg
    have h1 : proj d K (c₀ g) = 1 := by
      rw [← hφ]
      change ψ (φ' g) = 1
      rw [hg, map_one]
    exact mem_scalars_of_slConjugation_mem A₀⁻¹ (proj_eq_one_iff.mp h1)
  refine ggStdSubTwoTorus_of_model hp hp2 hpK h4 hφ's hφ'ker (fun a' ha' => ?_) haA ha1 hEcomp
  obtain ⟨φa, ⟨B, rfl⟩, hφa⟩ := hAI a' ha'
  have hBX : conjAut d K B ∈ X := ⟨a', ha', hφa⟩
  set D := A₀ * B * A₀⁻¹ with hD
  refine ⟨D, ⟨fun i => (D : Matrix (Fin d) (Fin d) K) i i,
    CFSG.RankThree.CALinearPlane.eq_diagonal_of_offDiag fun i j hij => by
      rw [hD, Units.val_mul, Units.val_mul]
      exact hA₀ B hBX i j hij⟩, fun s => ?_⟩
  have h1 := act_of_lift_GL hperfSL hker hφ hφa (c₀ s)
  change a' (φ (c₀ s)) = φ (c₀ (CatalogueBHigherLinearAction.slConjugation d K D s))
  rw [h1, hc₀, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hD]
  congr 2
  group

theorem ggStdSubTwoTorus_small_of_torality (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    (hd : 0 < d) (hd3 : d ≤ 3) (htor : GGPGLTorality p d K) (r : ℕ) :
    GGStdSubTwoTorus p r (projectiveSL d K) (Set.range (conjAut d K)) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _ h3
  exfalso
  have hX := isElemAbelian_inducedSub hψ hA
  have hcard := card_inducedSub hψ hker hperf (A := A) (fun a ha => by
    obtain ⟨φa, -, hφa⟩ := hAI a ha
    exact ⟨φa, hφa⟩)
  have hXI : ((inducedSub ψ A : Subgroup (MulAut (projectiveSL d K))) :
      Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K) := by
    rintro x ⟨a, ha, hxa⟩
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    exact induced_unique ψ hψ hφa hxa ▸ hφaI
  have := card_lt_of_torality hp hpK hd hd3 htor hX hXI
  rw [hcard] at this
  omega

end Main

section Transport

variable {r : ℕ} {R R' : Type} [Group R] [Group R'] {I : Set (MulAut R)} {I' : Set (MulAut R')}

theorem ggStdSubTwoTorus_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGStdSubTwoTorus p r R' I') : GGStdSubTwoTorus p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ)
    ((ker_comp_mulEquiv e ψ).symm ▸ hker) hperf A hA (fun a ha => ?_) hr h3
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
  change e (φ (e.symm (e (ψ l)))) = e (ψ (a l))
  rw [MulEquiv.symm_apply_apply, hφa]

end Transport

theorem recipeLinear_stdSubTwoTorus {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggStdSubTwoTorus_of_mulEquiv (recipeEquiv d K) hI
        (ggStdSubTwoTorus_small hp hpK (by omega) hd3 hpd' 0)⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggStdSubTwoTorus_of_mulEquiv (recipeEquiv d K) hI
        (ggStdSubTwoTorus_coprime hp hp2 hpK hd4 hpd' h4 hsec _)⟩

theorem recipeLinear_stdSubTwoTorus_dvd (htor : GGPGLToralityInput) {d N p : ℕ} (hp : p.Prime)
    (hpN : p ∣ N - 1) (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hd3 : 3 ≤ d := hp3.trans (Nat.le_of_dvd (by omega) hpd)
  have htor' := htor p d K hp hp2 hpK hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  rcases (show d = 3 ∨ d = 4 ∨ 5 ≤ d by omega) with h3 | h4' | h5
  · subst h3
    exact ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv 3 K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL (by norm_num))),
      ggStdSubTwoTorus_of_mulEquiv (recipeEquiv 3 K) hI
        (ggStdSubTwoTorus_small_of_torality hp hpK (by norm_num) le_rfl htor' 0)⟩
  · subst h4'
    exfalso
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1))
  · have hsec : SLHasSections d K := slHasSections_of_five_le h5
    exact ⟨d - 2, ggTorusLift_of_mulEquiv (recipeEquiv d K) (ggTorusLift_sub_two hp hpK hd hsec),
      ggStdSubTwoTorus_of_mulEquiv (recipeEquiv d K) hI
        (ggStdSubTwoTorus_of_torality hp hp2 hpK h5 h4 hsec htor')⟩

end CFSG.StandardType.TypeA

namespace CFSG.StandardType

open CFSG.Assembly TypeA

@[expose] def GGStdSubFixedJOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J →
    LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ LargeEvenSplit p lab ∧
      B ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
    Bs ⊓ Subgroup.centralizer (J : Set G) = D ∧
      ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)

section FixedJ

variable {G : Type} [Group G] [Finite G]

theorem GGStdSubFixedJ_eq_of_le {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hle : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D) :
    Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
  obtain ⟨hDB, -, -, -, -, -, hDC⟩ := hcfg.2.2.1
  exact le_antisymm hle (le_inf (hDB.trans hcfg.2.1.1) ((le_of_eq hDC).trans inf_le_right))

end FixedJ

theorem GGStdSubFixedJOn_of_labels {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I) :
    GGStdSubFixedJOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hM' := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨hle, hI2⟩ := ggStdSubInputs_of_twoTorus hcfg
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨⟨hP.1.2.2.1, hP.1.2.2.2⟩, hP.2⟩) hM')
  exact ⟨GGStdSubFixedJ_eq_of_le hcfg hle, hI2⟩

theorem GGStdSubFixedJOn.or {S T : ℕ → LargeEvenLabel → Prop} (hS : GGStdSubFixedJOn S)
    (hT : GGStdSubFixedJOn T) : GGStdSubFixedJOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hcfg hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact hS G p B Bs x L D J hcfg ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hQ⟩ => ⟨hs, hna, θ', h, hQ⟩) hraw⟩
  · exact hT G p B Bs x L D J hcfg ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hQ⟩ => ⟨hs, hna, θ', h, hQ⟩) hraw⟩

theorem GGStdSubSmallInputOn_of_fixedJ {S : ℕ → LargeEvenLabel → Prop}
    (h : GGStdSubFixedJOn S) : GGStdSubSmallInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM _
  obtain ⟨heq, hI2⟩ := h G p B Bs x L D J hcfg hM
  exact ⟨heq.le, hI2⟩

theorem largeEvenLabelAll_stdSubTwoTorus_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_stdSubTwoTorus hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_stdSubTwoTorus hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_stdSubTwoTorus hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

theorem GGStdSubFixedJOn_typeA : GGStdSubFixedJOn GGTypeALabel :=
  GGStdSubFixedJOn_of_labels fun _ _ hp hlab h =>
    largeEvenLabelAll_stdSubTwoTorus_typeA hp hlab h

theorem ggStdSubSmallInputOn_typeA : GGStdSubSmallInputOn GGTypeALabel :=
  GGStdSubSmallInputOn_of_fixedJ GGStdSubFixedJOn_typeA


theorem largeEvenLabelAll_stdSubTwoTorus_typeA_dvd (htor : GGPGLToralityInput) {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTypeALabelDvd p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGStdSubTwoTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨h, hpn, hpl⟩ := h
  dsimp only at h hpn hpl
  subst h
  intro Q hQ
  have hl1 : 1 ≤ l := hlab.2.1
  exact recipeLinear_stdSubTwoTorus_dvd htor hp hpn ⟨n, rfl⟩ (by omega) hpl hQ

theorem GGStdSubFixedJOn_typeA_split_of_torality (htor : GGPGLToralityInput) :
    GGStdSubFixedJOn GGTypeASplitLabel :=
  GGStdSubFixedJOn_of_labels fun _ _ hp hlab h => h.elim
    (fun h' => largeEvenLabelAll_stdSubTwoTorus_typeA hp hlab h')
    (fun h' => largeEvenLabelAll_stdSubTwoTorus_typeA_dvd htor hp hlab h')

theorem GGStdSubFixedJOn_typeA_split : GGStdSubFixedJOn GGTypeASplitLabel :=
  GGStdSubFixedJOn_typeA_split_of_torality ggPGLToralityInput_holds

theorem ggStdSubSmallInputOn_typeA_split (htor : GGPGLToralityInput) :
    GGStdSubSmallInputOn GGTypeASplitLabel :=
  GGStdSubSmallInputOn_of_fixedJ (GGStdSubFixedJOn_typeA_split_of_torality htor)

theorem ggStdSubSmallInputOn_typeA_split_holds : GGStdSubSmallInputOn GGTypeASplitLabel :=
  ggStdSubSmallInputOn_typeA_split ggPGLToralityInput_holds


theorem ggStdSubSmallInput_of_rest
    (h : GGStdSubSmallInputOn fun p lab => ¬ GGTypeASplitLabel p lab) : GGStdSubSmallInput :=
  ggStdSubSmallInput_of_cover (ggStdSubSmallInputOn_typeA_split_holds.or h)
    fun p lab _ _ => Classical.em (GGTypeASplitLabel p lab)

end CFSG.StandardType

end
