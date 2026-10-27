module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly

variable {d : ℕ} {K : Type} [Field K]

section Centralizer

theorem commute_diagonal_iff {s D : SpecialLinearGroup (Fin d) K} {t : Fin d → K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    s * D = D * s ↔ ∀ i j, t i ≠ t j → (s : Matrix (Fin d) (Fin d) K) i j = 0 := by
  constructor
  · intro h i j hij
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin d) K =>
      (g : Matrix (Fin d) (Fin d) K) i j) h
    simp only [Matrix.SpecialLinearGroup.coe_mul, hD, mul_diagonal, diagonal_mul] at h1
    have h2 : (s : Matrix (Fin d) (Fin d) K) i j * (t j - t i) = 0 := by
      rw [mul_sub, h1, mul_comm]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3).symm hij
  · intro h
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, hD, mul_diagonal, diagonal_mul]
    by_cases hij : t i = t j
    · rw [hij, mul_comm]
    · rw [h i j hij, zero_mul, mul_zero]

variable {i₀ : Fin d} {t : Fin d → K} (ht0 : ∀ j, j ≠ i₀ → t j ≠ t i₀)
  (ht1 : ∀ i j, i ≠ i₀ → j ≠ i₀ → t i = t j)

include ht0 in
theorem entry_eq_zero_of_mem {D s : SpecialLinearGroup (Fin d) K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (hs : s ∈ Subgroup.centralizer {D})
    {j : Fin d}
    (hj : j ≠ i₀) :
    (s : Matrix (Fin d) (Fin d) K) i₀ j = 0 ∧ (s : Matrix (Fin d) (Fin d) K) j i₀ = 0 := by
  have h := (commute_diagonal_iff hD).mp (Subgroup.mem_centralizer_singleton_iff.mp hs)
  exact ⟨h i₀ j (ht0 j hj).symm, h j i₀ (ht0 j hj)⟩

include ht1 in
theorem coordBlockSL_le_centralizer {D : SpecialLinearGroup (Fin d) K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) :
    coordBlockSL K ({i₀}ᶜ : Finset (Fin d)) ≤ Subgroup.centralizer {D} := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff, commute_diagonal_iff hD]
  intro i j hij
  have hs' := mem_coordBlockSL_iff.mp hs
  by_cases hi : i = i₀
  · have hji : j ≠ i := fun h => hij (h ▸ rfl)
    rw [hs' i j (Or.inl (by simp [hi])), ite_eq_right hji.symm]
  · by_cases hj : j = i₀
    · have hji : i ≠ j := fun h => hij (h ▸ rfl)
      rw [hs' i j (Or.inr (by simp [hj])), ite_eq_right hji]
    · exact absurd (ht1 i j hi hj) hij

variable (D : SpecialLinearGroup (Fin d) K) (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t)

include ht0 hD in
theorem entry_mul_of_mem {s : SpecialLinearGroup (Fin d) K} (hs : s ∈ Subgroup.centralizer {D})
    (s' : SpecialLinearGroup (Fin d) K) :
    ((s * s' : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) i₀ i₀ =
      (s : Matrix (Fin d) (Fin d) K) i₀ i₀ * (s' : Matrix (Fin d) (Fin d) K) i₀ i₀ := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Finset.sum_eq_single i₀ (fun j _ hj => by rw [(entry_eq_zero_of_mem ht0 hD hs hj).1, zero_mul])
      (fun h => absurd (Finset.mem_univ i₀) h)]

include ht0 hD in
@[expose] def blockEnt : Subgroup.centralizer {D} →* K where
  toFun s := ((s : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) i₀ i₀
  map_one' := by simp
  map_mul' s s' := entry_mul_of_mem ht0 D hD s.2 s'

theorem blockEnt_apply (s : Subgroup.centralizer {D}) :
    blockEnt ht0 D hD s = ((s : SpecialLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) i₀ i₀ :=
  rfl

include ht0 hD in
theorem mem_coordBlockSL_of_mem {s : SpecialLinearGroup (Fin d) K}
    (hs : s ∈ Subgroup.centralizer {D}) (h1 : (s : Matrix (Fin d) (Fin d) K) i₀ i₀ = 1) :
    s ∈ coordBlockSL K ({i₀}ᶜ : Finset (Fin d)) := by
  rw [mem_coordBlockSL_iff]
  intro i j hij
  simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at hij
  rcases hij with rfl | rfl
  · by_cases hj : j = i
    · subst hj
      rw [h1, ite_eq_left rfl]
    · rw [(entry_eq_zero_of_mem ht0 hD hs hj).1, ite_eq_right (Ne.symm hj)]
  · by_cases hi : i = j
    · subst hi
      rw [h1, ite_eq_left rfl]
    · rw [(entry_eq_zero_of_mem ht0 hD hs hi).2, ite_eq_right hi]

include ht0 hD in
theorem commutator_centralizer_le :
    ⁅Subgroup.centralizer {D}, Subgroup.centralizer {D}⁆ ≤
      coordBlockSL K ({i₀}ᶜ : Finset (Fin d)) := by
  set C := Subgroup.centralizer {D} with hC
  have hχ := Abelianization.commutator_subset_ker (blockEnt ht0 D hD).toHomUnits
  have h1 : ⁅C, C⁆ = (commutator C).map C.subtype := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [h1]
  rintro _ ⟨x, hx, rfl⟩
  have h2 := hχ hx
  rw [MonoidHom.mem_ker] at h2
  have h3 : blockEnt ht0 D hD x = 1 := by
    have := congrArg Units.val h2
    simpa using this
  exact mem_coordBlockSL_of_mem ht0 D hD x.2 h3

theorem coordBlockSL_inf_scalars {s : SpecialLinearGroup (Fin d) K}
    (hs : s ∈ coordBlockSL K ({i₀}ᶜ : Finset (Fin d))) (hz : s ∈ scalars d K) : s = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hz
  have h1 := mem_coordBlockSL_iff.mp hs i₀ i₀ (Or.inl (by simp))
  rw [ite_eq_left rfl, hc, scalar_apply, diagonal_apply_eq] at h1
  ext i j
  rw [hc, h1, map_one]
  rfl

end Centralizer

section General

variable {G : Type*} [Group G]

theorem isSubnormal_subgroupOf_of {A B : Subgroup G} (h : IsSubnormal A B) :
    (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

end General

section Layer

variable {p : ℕ} {L' : Type} [Group L'] {φ : SpecialLinearGroup (Fin d) K →* L'}

theorem conj_pow_eq_mul_pow {G : Type*} [Group G] {D s z : G} (hz : z ∈ Subgroup.center G)
    (h : D * s * D⁻¹ = s * z) (k : ℕ) : D ^ k * s * (D ^ k)⁻¹ = s * z ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hzk : z ^ k ∈ Subgroup.center G := Subgroup.pow_mem _ hz k
    calc D ^ (k + 1) * s * (D ^ (k + 1))⁻¹ = D * (D ^ k * s * (D ^ k)⁻¹) * D⁻¹ := by group
      _ = D * s * (z ^ k * D⁻¹) := by rw [ih]; group
      _ = (D * s * D⁻¹) * z ^ k := by rw [← (Subgroup.mem_center_iff.mp hzk) D⁻¹]; group
      _ = s * z ^ (k + 1) := by rw [h, mul_assoc, ← pow_succ']

theorem mem_centralizer_of_apply_eq (hφker : ∀ g, φ g = 1 → g ∈ scalars d K)
    (hpd : Nat.Coprime p d) {D : SpecialLinearGroup (Fin d) K} (hDp : D ^ p = 1)
    {s : SpecialLinearGroup (Fin d) K} (h1 : φ (D * s * D⁻¹) = φ s) :
    s ∈ Subgroup.centralizer {D} := by
  set z := s⁻¹ * (D * s * D⁻¹) with hz
  have hzk : φ z = 1 := by rw [hz, map_mul, map_inv, h1, inv_mul_cancel]
  have hzs := hφker z hzk
  have hzc := scalars_le_center d K hzs
  have h2 : D * s * D⁻¹ = s * z := by rw [hz]; group
  have h3 := conj_pow_eq_mul_pow hzc h2 p
  rw [hDp, one_mul, inv_one, mul_one] at h3
  have hzp : z ^ p = 1 := by
    have h4 : s * z ^ p = s * 1 := by rw [← h3, mul_one]
    exact mul_left_cancel h4
  have hz1 := eq_one_of_scalar_of_pow hpd hzs hzp
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [hz1, mul_one] at h2
  calc s * D = D * s * D⁻¹ * D := by rw [h2]
    _ = D * s := by group

theorem ggFix_eq_map (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) (hpd : Nat.Coprime p d)
    (hφs : Function.Surjective φ) {D : SpecialLinearGroup (Fin d) K} (hDp : D ^ p = 1)
    {a : MulAut L'} (ha : ∀ s, a (φ s) = φ (D * s * D⁻¹)) :
    ggFix a = (Subgroup.centralizer {D}).map φ := by
  ext l
  constructor
  · intro hl
    obtain ⟨s, rfl⟩ := hφs l
    exact ⟨s, mem_centralizer_of_apply_eq hφker hpd hDp ((ha s).symm.trans hl), rfl⟩
  · rintro ⟨s, hs, rfl⟩
    rw [mem_ggFix, ha]
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hs
    congr 1
    calc D * s * D⁻¹ = s * D * D⁻¹ := by rw [hs]
      _ = s := by group

end Layer

section LayerMain

variable {p : ℕ} {L' : Type} [Group L'] [Finite L'] {φ : SpecialLinearGroup (Fin d) K →* L'}
  {i₀ : Fin d} {t : Fin d → K}

theorem layer_ggFix_eq [Finite K] (h4 : 4 ≤ Nat.card K) (hS : 2 ≤ ({i₀}ᶜ : Finset (Fin d)).card)
    (ht0 : ∀ j, j ≠ i₀ → t j ≠ t i₀) (ht1 : ∀ i j, i ≠ i₀ → j ≠ i₀ → t i = t j)
    (hφker : ∀ g, φ g = 1 → g ∈ scalars d K) (hpd : Nat.Coprime p d)
    (hφs : Function.Surjective φ) {D : SpecialLinearGroup (Fin d) K}
    (hD : (D : Matrix (Fin d) (Fin d) K) = diagonal t) (hDp : D ^ p = 1) {a : MulAut L'}
    (ha : ∀ s, a (φ s) = φ (D * s * D⁻¹)) :
    LargeEvenLayer (ggFix a) = (coordBlockSL K ({i₀}ᶜ : Finset (Fin d))).map φ ∧
      IsComponentOf ((coordBlockSL K ({i₀}ᶜ : Finset (Fin d))).map φ) (ggFix a) := by
  set J₀ := coordBlockSL K ({i₀}ᶜ : Finset (Fin d)) with hJ₀
  set C := Subgroup.centralizer {D} with hC
  set F := ggFix a with hFdef
  set J := J₀.map φ with hJ
  have hF : F = C.map φ := ggFix_eq_map hφker hpd hφs hDp ha
  have hJ₀C : J₀ ≤ C := coordBlockSL_le_centralizer ht1 hD
  have hJF : J ≤ F := hF ▸ Subgroup.map_mono hJ₀C
  have hinj : Function.Injective (φ.comp J₀.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (coordBlockSL_inf_scalars x.2 (hφker _ hx))
  have hrange : (φ.comp J₀.subtype).range = J := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hJq : CFSG.IsQuasisimple J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
      (isQuasisimple_coordBlockSL hS h4)
  have hJn : (J.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJF]
    rintro _ f ⟨j, hj, rfl⟩ hf
    rw [hF] at hf
    obtain ⟨c, hc, rfl⟩ := hf
    refine ⟨c * j * c⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hcj : c * j ∈ C := C.mul_mem hc (hJ₀C hj)
    apply mem_coordBlockSL_of_mem ht0 D hD (C.mul_mem hcj (C.inv_mem hc))
    have e1 := entry_mul_of_mem ht0 D hD hcj c⁻¹
    have e2 := entry_mul_of_mem ht0 D hD hc j
    have e3 := entry_mul_of_mem ht0 D hD hc c⁻¹
    have hj1 : (j : Matrix (Fin d) (Fin d) K) i₀ i₀ = 1 := by
      have := mem_coordBlockSL_iff.mp hj i₀ i₀ (Or.inl (by simp))
      rwa [ite_eq_left rfl] at this
    rw [mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at e3
    rw [e1, e2, hj1, mul_one, ← e3]
  have hcomm : ⁅F, F⁆ ≤ J := by
    rw [hF, ← Subgroup.map_commutator]
    exact Subgroup.map_mono (commutator_centralizer_le ht0 D hD)
  have hJqA : CFSG.Assembly.IsQuasisimple J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).mpr hJq
  have hJcomp : IsComponentOf J F :=
    ⟨hJF, IsSubnormal.step hJF hJn (IsSubnormal.refl F), hJqA⟩
  have huniq : ∀ K' : Subgroup L', IsComponentOf K' F → K' = J := by
    rintro K' ⟨hKF, hKs, hKq⟩
    have hKq' : CFSG.IsQuasisimple K' :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K').mp hKq
    have hKperf : ⁅K', K'⁆ = K' := Subgroup.isPerfect_iff.mp hKq'.1
    have hKJ : K' ≤ J := hKperf ▸ (Subgroup.commutator_mono hKF hKF).trans hcomm
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
  have hL : LargeEvenLayer F = J :=
    le_antisymm (sSup_le fun K' hK' => (huniq K' hK').le) (le_sSup hJcomp)
  exact ⟨hL, hJcomp⟩

end LayerMain

end CFSG.StandardType.TypeA
