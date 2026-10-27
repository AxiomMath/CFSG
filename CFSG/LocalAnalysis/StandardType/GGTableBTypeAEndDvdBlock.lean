module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeABstarDvd

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.ComponentClassification CFSG.Assembly

theorem layer_eq_of_block {G L' : Type} [Group G] [Group L'] [Finite L'] {φ : G →* L'}
    {C J₀ : Subgroup G} (hJ₀C : J₀ ≤ C) (hJn : ∀ c ∈ C, ∀ j ∈ J₀, c * j * c⁻¹ ∈ J₀)
    (hcomm : ⁅C, C⁆ ≤ J₀) (hinj : ∀ j ∈ J₀, φ j = 1 → j = 1) (hq : CFSG.IsQuasisimple J₀) :
    LargeEvenLayer (C.map φ) = J₀.map φ ∧ IsComponentOf (J₀.map φ) (C.map φ) := by
  set F := C.map φ with hF
  set J := J₀.map φ with hJ
  have hJF : J ≤ F := Subgroup.map_mono hJ₀C
  have hinj' : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hinj x x.2 hx)
  have hrange : (φ.comp J₀.subtype).range = J := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange)) hq
  have hJn' : (J.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ f ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
    exact ⟨c * j * c⁻¹, hJn c hc j hj, by rw [map_mul, map_mul, map_inv]⟩
  have hcommF : ⁅F, F⁆ ≤ J := by
    rw [hF, ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm
  have hJqA : CFSG.Assembly.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mpr hJq
  have hJcomp : IsComponentOf J F :=
    ⟨hJF, IsSubnormal.step hJF hJn' (IsSubnormal.refl F), hJqA⟩
  have huniq : ∀ K' : Subgroup L', IsComponentOf K' F → K' = J := by
    rintro K' ⟨hKF, hKs, hKq⟩
    have hKq' : CFSG.IsQuasisimple K' :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K').mp hKq
    have hKperf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp hKq'.1
    have hKJ : K' ≤ J := hKperf ▸ (Subgroup.commutator_mono hKF hKF).trans hcommF
    have hK'c : CFSG.IsComponent (K'.subgroupOf F) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKF).symm hKq',
        isSubnormal_subgroupOf_of hKs⟩
    have hJ'c : CFSG.IsComponent (J.subgroupOf F) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJF).symm hJq,
        isSubnormal_subgroupOf_of hJcomp.2.1⟩
    rcases CFSG.LocalCores.distinct_components_commute hK'c hJ'c with h | h
    · have h1 := Subgroup.subgroupOf_inj.mp h
      rwa [inf_eq_left.mpr hKF, inf_eq_left.mpr hJF] at h1
    · exfalso
      have hle : K'.subgroupOf F ≤ J.subgroupOf F := Subgroup.subgroupOf_mono F hKJ
      have h1 : ⁅K'.subgroupOf F, K'.subgroupOf F⁆ = ⊥ :=
        le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hle)
      have h2 : ⁅K'.subgroupOf F, K'.subgroupOf F⁆ = K'.subgroupOf F :=
        Subgroup.isPerfect_iff.mp hK'c.1.1
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hK'c.1
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥(K'.subgroupOf F))
      have hx' : (x : F) ∈ ⁅K'.subgroupOf F, K'.subgroupOf F⁆ := h2.symm ▸ x.2
      rw [h1, Subgroup.mem_bot] at hx'
      exact hx (Subtype.ext hx')
  exact ⟨le_antisymm (sSup_le fun K' hK' => (huniq K' hK').le) (le_sSup hJcomp), hJcomp⟩

variable {d : ℕ} {K : Type} [Field K]

theorem det_eq_zero_of_block_zero {M : Matrix (Fin d) (Fin d) K} {S : Finset (Fin d)}
    (hS : Sᶜ.card < S.card) (h : ∀ k ∈ S, ∀ l ∈ S, M k l = 0) : M.det = 0 := by
  rw [det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  have hex : ∃ k ∈ S, σ k ∈ S := by
    by_contra hne
    have hne' : ∀ k ∈ S, σ k ∉ S := fun k hk hσ => hne ⟨k, hk, hσ⟩
    have := Finset.card_le_card_of_injOn σ (fun k hk => Finset.mem_compl.mpr (hne' k hk))
      (σ.injective.injOn)
    omega
  obtain ⟨k, hk, hσk⟩ := hex
  have h0 : ∏ i, M (σ i) i = 0 :=
    Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ k) (h _ hσk _ hk)
  rw [h0, smul_zero]

section SetBlock

theorem diagonal_conj_apply {t : Fin d → K} (M : Matrix (Fin d) (Fin d) K) (i j : Fin d) :
    (diagonal t * M * diagonal (fun k => (t k)⁻¹)) i j = t i * M i j * (t j)⁻¹ := by
  rw [mul_diagonal, diagonal_mul]

variable {D : GL (Fin d) K} {t : Fin d → K}

theorem mem_ggFix_slConjugation_iff (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    {s : SpecialLinearGroup (Fin d) K} :
    s ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D) ↔
      ∀ i j, t i ≠ t j → (s : Matrix (Fin d) (Fin d) K) i j = 0 := by
  have ht0 : ∀ k, t k ≠ 0 := by
    intro k hk
    have h1 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := K))
    rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
      Finset.prod_eq_zero (Finset.mem_univ k) hk] at h1
    exact not_isUnit_zero h1
  rw [mem_ggFix]
  constructor
  · intro h i j hij
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin d) K =>
      (g : Matrix (Fin d) (Fin d) K) i j) h
    simp only [coe_slConjugation', hD, coe_inv_of_diagonal hD, diagonal_conj_apply] at h1
    have h2 : (s : Matrix (Fin d) (Fin d) K) i j * (t i - t j) = 0 := by
      have h3 : t i * (s : Matrix (Fin d) (Fin d) K) i j =
          (s : Matrix (Fin d) (Fin d) K) i j * t j := by
        calc t i * (s : Matrix (Fin d) (Fin d) K) i j =
            t i * (s : Matrix (Fin d) (Fin d) K) i j * (t j)⁻¹ * t j := by
              rw [mul_assoc _ (t j)⁻¹, inv_mul_cancel₀ (ht0 j), mul_one]
          _ = _ := by rw [h1]
      rw [mul_sub, ← h3]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hij
  · intro h
    ext i j
    rw [coe_slConjugation', hD, coe_inv_of_diagonal hD, diagonal_conj_apply]
    by_cases hij : t i = t j
    · rw [hij, mul_comm, ← mul_assoc, inv_mul_cancel₀ (ht0 j), one_mul]
    · rw [h i j hij, mul_zero, zero_mul]

variable {T : Finset (Fin d)}

theorem entry_eq_zero_of_mem_fix (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i) {s : SpecialLinearGroup (Fin d) K}
    (hs : s ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D)) {i : Fin d} (hi : i ∈ T)
    {j : Fin d} (hj : j ≠ i) :
    (s : Matrix (Fin d) (Fin d) K) i j = 0 ∧ (s : Matrix (Fin d) (Fin d) K) j i = 0 := by
  have h := (mem_ggFix_slConjugation_iff hD).mp hs
  exact ⟨h i j (htT i hi j hj).symm, h j i (htT i hi j hj)⟩

theorem coordBlockSL_le_fix (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htc : ∀ i j, i ∉ T → j ∉ T → t i = t j) :
    coordBlockSL K Tᶜ ≤ ggFix (CatalogueBHigherLinearAction.slConjugation d K D) := by
  intro s hs
  rw [mem_ggFix_slConjugation_iff hD]
  intro i j hij
  have hs' := mem_coordBlockSL_iff.mp hs
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  by_cases hi : i ∈ T
  · rw [hs' i j (Or.inl (by simpa using hi)), ite_eq_right hne]
  · by_cases hj : j ∈ T
    · rw [hs' i j (Or.inr (by simpa using hj)), ite_eq_right hne]
    · exact absurd (htc i j hi hj) hij

theorem entry_mul_of_mem_fix (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i) {s : SpecialLinearGroup (Fin d) K}
    (hs : s ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D)) {i : Fin d} (hi : i ∈ T)
    (s' : SpecialLinearGroup (Fin d) K) :
    ((s * s' : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) i i =
      (s : Matrix (Fin d) (Fin d) K) i i * (s' : Matrix (Fin d) (Fin d) K) i i := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Finset.sum_eq_single i
      (fun j _ hj => by rw [(entry_eq_zero_of_mem_fix hD htT hs hi hj).1, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h)]


@[expose] def blockEntT (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i) {i : Fin d} (hi : i ∈ T) :
    ggFix (CatalogueBHigherLinearAction.slConjugation d K D) →* K where
  toFun s := ((s : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) i i
  map_one' := by simp
  map_mul' s s' := entry_mul_of_mem_fix hD htT s.2 hi s'

theorem mem_coordBlockSL_of_mem_fix (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i) {s : SpecialLinearGroup (Fin d) K}
    (hs : s ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D))
    (h1 : ∀ i ∈ T, (s : Matrix (Fin d) (Fin d) K) i i = 1) : s ∈ coordBlockSL K Tᶜ := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  simp only [Finset.mem_compl, not_not] at hij
  rcases hij with hi | hj
  · by_cases hji : j = i
    · subst hji
      rw [h1 j hi, ite_eq_left rfl]
    · rw [(entry_eq_zero_of_mem_fix hD htT hs hi hji).1, ite_eq_right (Ne.symm hji)]
  · by_cases hij : i = j
    · subst hij
      rw [h1 i hj, ite_eq_left rfl]
    · rw [(entry_eq_zero_of_mem_fix hD htT hs hj hij).2, ite_eq_right hij]

theorem commutator_fix_le (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i) :
    ⁅ggFix (CatalogueBHigherLinearAction.slConjugation d K D),
        ggFix (CatalogueBHigherLinearAction.slConjugation d K D)⁆ ≤ coordBlockSL K Tᶜ := by
  set C := ggFix (CatalogueBHigherLinearAction.slConjugation d K D) with hC
  have h1 : ⁅C, C⁆ = (commutator C).map C.subtype := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [h1]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_coordBlockSL_of_mem_fix hD htT x.2 fun i hi => ?_
  have h2 := Abelianization.commutator_subset_ker (blockEntT hD htT hi).toHomUnits hx
  rw [MonoidHom.mem_ker] at h2
  have := congrArg Units.val h2
  simpa [blockEntT] using this

theorem conj_mem_coordBlockSL_of_mem_fix (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i) (htc : ∀ i j, i ∉ T → j ∉ T → t i = t j)
    {c j : SpecialLinearGroup (Fin d) K}
    (hc : c ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D))
    (hj : j ∈ coordBlockSL K Tᶜ) : c * j * c⁻¹ ∈ coordBlockSL K Tᶜ := by
  set C := ggFix (CatalogueBHigherLinearAction.slConjugation d K D) with hC
  have hjC := coordBlockSL_le_fix hD htc hj
  have hcj : c * j ∈ C := C.mul_mem hc hjC
  refine mem_coordBlockSL_of_mem_fix hD htT (C.mul_mem hcj (C.inv_mem hc)) fun i hi => ?_
  have e1 := entry_mul_of_mem_fix hD htT hcj hi c⁻¹
  have e2 := entry_mul_of_mem_fix hD htT hc hi j
  have e3 := entry_mul_of_mem_fix hD htT hc hi c⁻¹
  have hj1 : (j : Matrix (Fin d) (Fin d) K) i i = 1 := by
    have := mem_coordBlockSL_iff.mp hj i i (Or.inl (by simpa using hi))
    rwa [ite_eq_left rfl] at this
  rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at e3
  rw [e1, e2, hj1, mul_one, ← e3]

theorem coordBlockSL_compl_inf_scalars {i₀ : Fin d} (hi₀ : i₀ ∈ T)
    {s : SpecialLinearGroup (Fin d) K} (hs : s ∈ coordBlockSL K Tᶜ) (hz : s ∈ scalars d K) :
    s = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  have h1 := mem_coordBlockSL_iff.mp hs i₀ i₀ (Or.inl (by simpa using hi₀))
  rw [ite_eq_left rfl, hc, scalar_apply, diagonal_apply_eq] at h1
  ext i j
  rw [hc, h1, map_one]
  rfl

theorem mem_fix_of_apply_eq {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (htc : ∀ i j, i ∉ T → j ∉ T → t i = t j) (hT : T.card < Tᶜ.card)
    {s : SpecialLinearGroup (Fin d) K}
    (h1 : φ (CatalogueBHigherLinearAction.slConjugation d K D s) = φ s) :
    s ∈ ggFix (CatalogueBHigherLinearAction.slConjugation d K D) := by
  set u := CatalogueBHigherLinearAction.slConjugation d K D s with hu
  have hz : φ (s⁻¹ * u) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨c, -, hc⟩ := mem_scalars.mp (hφker _ hz)
  have hus : (u : Matrix (Fin d) (Fin d) K) =
      (s : Matrix (Fin d) (Fin d) K) * scalar (Fin d) (c : K) := by
    have h2 : u = s * (s⁻¹ * u) := by group
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, hc]
  by_cases hc1 : (c : K) = 1
  · rw [mem_ggFix]
    ext i j
    rw [← hu, hus, hc1, map_one, Matrix.mul_one]
  · exfalso
    have hblock : ∀ k ∈ Tᶜ, ∀ l ∈ Tᶜ, (s : Matrix (Fin d) (Fin d) K) k l = 0 := by
      intro k hk l hl
      have ht0 : t l ≠ 0 := by
        intro h0
        have h3 := D.isUnit.map (Matrix.detMonoidHom (n := Fin d) (R := K))
        rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
          Finset.prod_eq_zero (Finset.mem_univ l) h0] at h3
        exact not_isUnit_zero h3
      have h2 := congrArg (fun M : Matrix (Fin d) (Fin d) K => M k l) hus
      simp only [hu, coe_slConjugation', hD, coe_inv_of_diagonal hD, mul_diagonal, diagonal_mul,
        scalar_apply] at h2
      rw [htc k l (by simpa using hk) (by simpa using hl), mul_comm (t l), mul_assoc,
        mul_inv_cancel₀ ht0, mul_one] at h2
      have h3 : (s : Matrix (Fin d) (Fin d) K) k l * (1 - (c : K)) = 0 := by
        rw [mul_sub, mul_one, ← h2, sub_self]
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact h4
      · exact absurd (sub_eq_zero.mp h4).symm hc1
    have hdet := det_eq_zero_of_block_zero (S := Tᶜ) (by rwa [compl_compl]) hblock
    rw [s.2] at hdet
    exact one_ne_zero hdet

theorem layer_ggFix_eq_of_set [Finite K] {L' : Type} [Group L'] [Finite L']
    {φ : SpecialLinearGroup (Fin d) K →* L'} (h4 : 4 ≤ Nat.card K)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) (hφs : Function.Surjective φ)
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (htT : ∀ i ∈ T, ∀ j, j ≠ i → t j ≠ t i)
    (htc : ∀ i j, i ∉ T → j ∉ T → t i = t j) (hT : T.card < Tᶜ.card) {i₀ : Fin d}
    (hi₀ : i₀ ∈ T) (hS : 2 ≤ Tᶜ.card) {a : MulAut L'}
    (ha : ∀ s, a (φ s) = φ (CatalogueBHigherLinearAction.slConjugation d K D s)) :
    LargeEvenLayer (ggFix a) = (coordBlockSL K Tᶜ).map φ ∧
      IsComponentOf ((coordBlockSL K Tᶜ).map φ) (ggFix a) := by
  have hF : ggFix a = (ggFix (CatalogueBHigherLinearAction.slConjugation d K D)).map φ := by
    ext l
    constructor
    · intro hl
      obtain ⟨s, rfl⟩ := hφs l
      exact ⟨s, mem_fix_of_apply_eq hφker hD htc hT ((ha s).symm.trans hl), rfl⟩
    · rintro ⟨s, hs, rfl⟩
      rw [mem_ggFix, ha, mem_ggFix.mp hs]
  rw [hF]
  exact layer_eq_of_block (coordBlockSL_le_fix hD htc)
    (fun c hc j hj => conj_mem_coordBlockSL_of_mem_fix hD htT htc hc hj)
    (commutator_fix_le hD htT)
    (fun j hj h1 => coordBlockSL_compl_inf_scalars hi₀ hj (hφker j h1))
    (isQuasisimple_coordBlockSL hS h4)

end SetBlock

end CFSG.StandardType.TypeA
