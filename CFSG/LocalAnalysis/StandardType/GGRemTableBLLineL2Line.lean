module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Frame
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitary
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeACover
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGNbrLangNorm

public section

namespace CFSG.StandardType

namespace LineL2

open Matrix CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def MoveStmt (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∀ Λ : Subgroup R, Λ ≤ E → Nat.card Λ = p →
      ∃ w ∈ Subgroup.normalizer (E : Set R), ∃ e ∈ Λ, w * e * w⁻¹ ∉ Λ

theorem moveStmt_of_mulEquiv {p : ℕ} {R S : Type} [Group R] [Group S] (e : R ≃* S)
    (h : MoveStmt p S) : MoveStmt p R := by
  intro E hE h3 hsc Λ hΛ hΛc
  set E' : Subgroup S := E.map e.toMonoidHom with hE'
  set Λ' : Subgroup S := Λ.map e.toMonoidHom with hΛ'
  have hcardE : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective e.injective
  have hcardΛ : Nat.card Λ' = Nat.card Λ := Subgroup.card_map_of_injective e.injective
  have hmemE : ∀ y : R, e y ∈ E' ↔ y ∈ E := fun y => by
    rw [hE', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hmemΛ : ∀ y : R, e y ∈ Λ' ↔ y ∈ Λ := fun y => by
    rw [hΛ', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hsc' : ∀ g : S, (∀ x ∈ E', g * x = x * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have h1 : e.symm g ∈ E := by
      apply hsc
      · intro x hx
        apply e.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hg _ ((hmemE x).mpr hx)
      · apply e.injective
        rw [map_pow, MulEquiv.apply_symm_apply, hgp, map_one]
    have := (hmemE (e.symm g)).mpr h1
    rwa [MulEquiv.apply_symm_apply] at this
  obtain ⟨w, hwN, x, hx, hne⟩ := h E' (TableB.isElemAbelian_map hE e.toMonoidHom)
    (hcardE ▸ h3) hsc' Λ' (Subgroup.map_mono hΛ) (hcardΛ ▸ hΛc)
  refine ⟨e.symm w, ?_, e.symm x, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp hwN (e y)
    rw [hmemE] at h1
    rw [h1, ← hmemE, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  · have := (hmemΛ (e.symm x)).mp
    rw [MulEquiv.apply_symm_apply] at this
    exact this hx
  · intro hmem
    apply hne
    have := (hmemΛ _).mpr hmem
    rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this

theorem ggNoInvariantLineSC_of_moveStmt {p : ℕ} {R : Type} [Group R] [Finite R]
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : MoveStmt p R) :
    CorFourTwoOpen.GGNoInvariantLineSC p R I := by
  intro Eh hEhI hEhA h3 hscR Λ hΛ hΛp
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := OrthRest.conj_injective hZ
  set E := Eh.comap (MulAut.conj : R →* MulAut R) with hE
  have hmap : E.map (MulAut.conj : R →* MulAut R) = Eh := by
    rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI hφ)
  have hcardE : Nat.card E = Nat.card Eh := by
    rw [Nat.card_congr (E.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hEe : IsElemAbelian p E := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEhA a.2 b.2
    · rw [map_pow, map_one]
      exact hEhA.2 _ hx
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    show MulAut.conj g ∈ Eh
    refine hscR g (fun a ha => ?_) hgp
    obtain ⟨y, rfl⟩ := hI (hEhI ha)
    have hy : y ∈ E := ha
    rw [MulAut.conj_apply, ← hg y hy, mul_inv_cancel_right]
  set Λ' := Λ.comap (MulAut.conj : R →* MulAut R) with hΛ'
  have hΛmap : Λ'.map (MulAut.conj : R →* MulAut R) = Λ := by
    rw [hΛ', Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEhI (hΛ hφ))
  have hΛ'card : Nat.card Λ' = p := by
    rw [Nat.card_congr (Λ'.equivMapOfInjective _ hinj).toEquiv, hΛmap, hΛp]
  have hΛ'E : Λ' ≤ E := fun e he => hΛ he
  obtain ⟨w, hwN, e, he, hne⟩ := h E hEe (hcardE ▸ h3) hscE Λ' hΛ'E hΛ'card
  refine ⟨w, ?_, MulAut.conj e, he, fun hmem => hne ?_⟩
  · refine NbrLang.mem_normalizer_of_conj_mem fun b hb => ?_
    obtain ⟨y, rfl⟩ := hI (hEhI hb)
    have hy : y ∈ E := hb
    have h1 : w * y * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hwN y).mp hy
    rw [← map_inv, ← map_mul, ← map_mul]
    exact h1
  · show MulAut.conj (w * e * w⁻¹) ∈ Λ
    rw [map_mul, map_mul, map_inv]
    exact hmem

section Two

variable {K : Type} [Field K] [Finite K] {d : ℕ}

theorem center_eq_bot_two (hK : Nat.card K = 2) :
    Subgroup.center (SpecialLinearGroup (Fin d) K) = ⊥ := by
  rw [← scalars_eq_center, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  exact TwoThree.eq_one_of_mem_scalars hK hg

@[expose] noncomputable def projEquivTwo (hK : Nat.card K = 2) :
    SpecialLinearGroup (Fin d) K ≃* projectiveSL d K :=
  MulEquiv.ofBijective (proj d K) ⟨by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact TwoThree.eq_one_of_mem_scalars hK (proj_eq_one_iff.mp hg), proj_surjective d K⟩

theorem moveStmt_sl_two (hK : Nat.card K = 2) : MoveStmt 3 (SpecialLinearGroup (Fin d) K) :=
  fun _ hE h3 hsc _ hΛ hΛc => exists_normalizer_move hK hE h3 hsc hΛ hΛc

@[expose] noncomputable def recipeEquivTwo (hK : Nat.card K = 2) :
    LargeEvenProj (LargeEvenSLGroup (Fin d) K) ≃* SpecialLinearGroup (Fin d) K :=
  (TypeA.recipeEquiv d K).trans (projEquivTwo hK).symm

theorem moveStmt_recipe_two (hK : Nat.card K = 2) :
    MoveStmt 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
  moveStmt_of_mulEquiv (recipeEquivTwo hK) (moveStmt_sl_two hK)

theorem eq_conj_of_congr_eq_conj {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {φ : MulAut R} {x : R'} (h : MulAut.congr e φ = MulAut.conj x) :
    φ = MulAut.conj (e.symm x) := by
  ext y
  have h1 := congrArg (fun ψ : MulAut R' => ψ (e y)) h
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    MulAut.conj_apply] at h1
  apply e.injective
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem matConjImage_subset_conj (hK : Nat.card K = 2) :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ ⊆
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin d) K) →*
        MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) := by
  intro φ hφ
  obtain ⟨B, hB⟩ := TypeA.congr_recipeEquiv_mem hφ
  refine ⟨(TypeA.recipeEquiv d K).symm (proj d K (TwoThree.toSLHom hK B)), ?_⟩
  symm
  apply eq_conj_of_congr_eq_conj (TypeA.recipeEquiv d K)
  rw [← hB, ← TwoThree.toGL_toSLHom hK B, conjAut_toGL, TwoThree.toGL_toSLHom]

theorem ggNoInvariantLineSC_recipe_two (hK : Nat.card K = 2) :
    CorFourTwoOpen.GGNoInvariantLineSC 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have hfin : Finite (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
    Finite.of_equiv _ (recipeEquivTwo hK).symm.toEquiv
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h1 : recipeEquivTwo hK x ∈ Subgroup.center (SpecialLinearGroup (Fin d) K) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨y, rfl⟩ := (recipeEquivTwo hK).surjective s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    rw [center_eq_bot_two hK, Subgroup.mem_bot] at h1
    exact (recipeEquivTwo hK).injective (h1.trans (map_one _).symm)
  exact ggNoInvariantLineSC_of_moveStmt (matConjImage_subset_conj hK) hZ (moveStmt_recipe_two hK)

theorem ggCenterCoprime_psl_two (hK : Nat.card K = 2) (hd : 5 ≤ d) :
    GGCenterCoprime 3 (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf hdvd
  obtain ⟨φ, hφs, hφ⟩ := TypeA.exists_sl_cover (TypeA.slHasSections_of_five_le hd) ψ hψ hker
    hperf
  have hbot : ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_bot]
    obtain ⟨s, rfl⟩ := hφs l
    have h1 : proj d K s = 1 := by
      rw [← hφ, ← MonoidHom.mem_ker.mp hl]
    rw [TwoThree.eq_one_of_mem_scalars hK (proj_eq_one_iff.mp h1), map_one]
  rw [hbot, Subgroup.card_bot] at hdvd
  exact absurd (Nat.le_of_dvd one_pos hdvd) (by norm_num)

theorem ggCenterCoprime_recipe_two (hK : Nat.card K = 2) (hd : 5 ≤ d) :
    GGCenterCoprime 3 (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :=
  ggCenterCoprime_of_mulEquiv (TypeA.recipeEquiv d K) (ggCenterCoprime_psl_two hK hd)

end Two

end LineL2

end CFSG.StandardType

end
