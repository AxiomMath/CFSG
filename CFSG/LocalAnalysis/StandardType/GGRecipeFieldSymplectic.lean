module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSp
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldSymplectic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

section MatConj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] def matConjSubgroup (H S : Subgroup (GL ι K))
    (hSH : ∀ A ∈ S, ∀ h ∈ H, A * h * A⁻¹ ∈ H) : Subgroup (MulAut (LargeEvenProj H)) where
  carrier := LargeEvenMatConjImage (LargeEvenProjMk H) (S : Set (GL ι K))
  mul_mem' := by
    rintro φ ψ ⟨A, hA, hφ⟩ ⟨B, hB, hψ⟩
    refine ⟨A * B, S.mul_mem hA hB, fun h h' hh' => ?_⟩
    have hh'₀ : (h' : GL ι K) = A * B * h * (A * B)⁻¹ := hh'
    set h'' : H := ⟨B * h * B⁻¹, hSH B hB h h.2⟩ with hh''
    have hcoe : (h'' : GL ι K) = B * h * B⁻¹ := rfl
    have e1 : ψ (LargeEvenProjMk H h) = LargeEvenProjMk H h'' := hψ h h'' rfl
    have e2 : φ (LargeEvenProjMk H h'') = LargeEvenProjMk H h' := hφ h'' h' (by
      show (h' : GL ι K) = A * (h'' : GL ι K) * A⁻¹
      rw [hh'₀, hcoe]
      group)
    rw [MulAut.mul_apply, e1, e2]
  one_mem' := ⟨1, S.one_mem, fun h h' hh' => by
    have hh'₀ : (h' : GL ι K) = 1 * h * 1⁻¹ := hh'
    rw [MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [hh'₀]
    group⟩
  inv_mem' := by
    rintro φ ⟨A, hA, hφ⟩
    refine ⟨A⁻¹, S.inv_mem hA, fun h h' hh' => ?_⟩
    have hh'₀ : (h' : GL ι K) = A⁻¹ * h * A⁻¹⁻¹ := hh'
    have e : φ (LargeEvenProjMk H h') = LargeEvenProjMk H h := hφ h' h (by
      show (h : GL ι K) = A * (h' : GL ι K) * A⁻¹
      rw [hh'₀]
      group)
    rw [← e, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem coe_matConjSubgroup (H S : Subgroup (GL ι K))
    (hSH : ∀ A ∈ S, ∀ h ∈ H, A * h * A⁻¹ ∈ H) :
    (matConjSubgroup H S hSH : Set (MulAut (LargeEvenProj H))) =
      LargeEvenMatConjImage (LargeEvenProjMk H) (S : Set (GL ι K)) :=
  rfl

theorem conj_mem_matConjSubgroup (H S : Subgroup (GL ι K)) (hHS : H ≤ S)
    (hSH : ∀ A ∈ S, ∀ h ∈ H, A * h * A⁻¹ ∈ H) (x : LargeEvenProj H) :
    MulAut.conj x ∈ matConjSubgroup H S hSH := by
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective x
  refine ⟨h₀, hHS h₀.2, fun h h' hh' => ?_⟩
  change h₀ * (h : LargeEvenProj H) * (h₀ : LargeEvenProj H)⁻¹ = (h' : LargeEvenProj H)
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext hh'.symm

theorem matFieldImage_eq_one_of_card_two (hK : Nat.card K = 2) (H : Subgroup (GL ι K))
    {φ : MulAut (LargeEvenProj H)} (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk H)) :
    φ = 1 := by
  obtain ⟨σ, hσ⟩ := hφ
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  have hmap : ((h : GL ι K) : Matrix ι ι K) = ((h : GL ι K) : Matrix ι ι K).map σ := by
    ext i j
    rw [Matrix.map_apply, ringEquiv_apply_eq_of_card_two hK]
  simpa using hσ h h hmap

end MatConj

namespace RecipeFieldSp

variable {m : ℕ} {K : Type} [Field K]

theorem exists_conjAut_of_mem {φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m))
      (LargeEvenGSpSet K m)) :
    ∃ A : gsp m K, φ = (conjAut m K A : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
  obtain ⟨A, ⟨μ, hμ0, hA⟩, hφA⟩ := hφ
  have hAg : A ∈ gsp m K := ⟨Units.mk0 μ hμ0, by rw [Units.val_mk0]; exact hA⟩
  refine ⟨⟨A, hAg⟩, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  exact hφA g (conjSp m K ⟨A, hAg⟩ g) (coe_conjSp _ g)

theorem exists_fieldAut_of_mem {φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))}
    (hφ : φ ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) :
    ∃ σ : K ≃+* K, φ = (fieldAut m K σ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
  obtain ⟨σ, hσ⟩ := hφ
  refine ⟨σ, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  exact hσ g (fieldSp m K σ g) (coe_fieldSp σ g)

variable [Finite K] [CharP K 2]

theorem mem_conjImage_iff_inn {φ : MulAut (LargeEvenProj (LargeEvenSpGroup K m))} :
    φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) ↔
      φ ∈ (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut _).range := by
  constructor
  · intro hφ
    obtain ⟨A, rfl⟩ := exists_conjAut_of_mem hφ
    exact AutPSp.conjAut_mem_inn A
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := proj_surjective x
    have e := conjAut_statedSp (r := m) (K := K) g
    change MulAut.conj (proj m K g) ∈ _
    rw [← e]
    exact NbrGraphSymplectic.conjAut_mem _

theorem ggRawInnField_symplectic [NeZero m] {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) := by
  refine ggRawInnField_of_subgroup hp (MulAut.conj : _ →* MulAut _).range ?_ (fun r => ⟨r, rfl⟩) ?_
  · ext φ
    exact mem_conjImage_iff_inn.symm
  · intro f hf hfI
    obtain ⟨σ, rfl⟩ := exists_fieldAut_of_mem hf
    have hmem : (fieldAut m K σ : MulAut (StatedProj (StatedSp m K))) ∈
        (MulAut.conj : StatedProj (StatedSp m K) →* MulAut _).range ⊓
          (AutPSp.compl : Subgroup (MulAut (StatedProj (StatedSp m K)))) :=
      ⟨mem_conjImage_iff_inn.mp hfI, σ, rfl⟩
    rw [AutPSp.inn_inf_compl] at hmem
    exact Subgroup.mem_bot.mp hmem

theorem commutator_mem_inn_symplectic (hm : 3 ≤ m) (α β : MulAut (StatedProj (StatedSp m K))) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : StatedProj (StatedSp m K) →* MulAut _).range := by
  refine commutator_mem_of_eq_mul _ (Set.range (fieldAut m K)) ?_ ?_ ?_ α β
  · rintro _ ⟨σ, rfl⟩ _ ⟨τ, rfl⟩
    rw [← map_mul, ← map_mul, ringEquiv_mul_comm_of_finite]
  · rintro _ ⟨σ, rfl⟩ d hd
    exact Subgroup.Normal.conj_mem inferInstance d hd _
  · intro a
    obtain ⟨i, hi, c, ⟨σ, rfl⟩, rfl⟩ := AutPSp.exists_mul_compl hm a
    exact ⟨i, hi, _, ⟨σ, rfl⟩, rfl⟩

theorem ggRawFieldCentral_symplectic (hm : 3 ≤ m) :
    GGRawFieldCentral (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) :=
  ggRawFieldCentral_of_commutator_mem fun α β =>
    mem_conjImage_iff_inn.mpr (commutator_mem_inn_symplectic hm α β)

end RecipeFieldSp

namespace RecipeFieldSp

variable {K : Type} [Field K]

theorem largeEvenGSpSet_eq (m : ℕ) :
    LargeEvenGSpSet K m = (gsp m K : Set (GL (Fin m ⊕ Fin m) K)) := by
  ext A
  constructor
  · rintro ⟨μ, hμ0, hA⟩
    exact ⟨Units.mk0 μ hμ0, by rw [Units.val_mk0]; exact hA⟩
  · rintro ⟨μ, hA⟩
    exact ⟨μ, μ.ne_zero, hA⟩

theorem conj_mem_commutator_statedSp {m : ℕ} (A : GL (Fin m ⊕ Fin m) K) (hA : A ∈ gsp m K)
    {h : GL (Fin m ⊕ Fin m) K} (hh : h ∈ ⁅StatedSp m K, StatedSp m K⁆) :
    A * h * A⁻¹ ∈ ⁅StatedSp m K, StatedSp m K⁆ := by
  have hle : (StatedSp m K).map (MulAut.conj A).toMonoidHom ≤ StatedSp m K := by
    rintro _ ⟨g, hg, rfl⟩
    exact (conjSp m K ⟨A, hA⟩ ⟨g, hg⟩).2
  have hmap : (⁅StatedSp m K, StatedSp m K⁆ : Subgroup (GL (Fin m ⊕ Fin m) K)).map
      (MulAut.conj A).toMonoidHom ≤ ⁅StatedSp m K, StatedSp m K⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono hle hle
  exact hmap ⟨h, hh, rfl⟩

theorem commutator_statedSp_le_gsp (m : ℕ) : ⁅StatedSp m K, StatedSp m K⁆ ≤ gsp m K :=
  Subgroup.commutator_le.mpr fun _ h₁ _ h₂ => statedSp_le_gsp
    ((StatedSp m K).mul_mem ((StatedSp m K).mul_mem ((StatedSp m K).mul_mem h₁ h₂)
      ((StatedSp m K).inv_mem h₁)) ((StatedSp m K).inv_mem h₂))

open scoped commutatorElement in
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner) in
theorem commutator_mem_inn_of_mulEquiv_alternatingSix {R : Type} [Group R]
    (e : R ≃* alternatingGroup (Fin 6)) (α β : MulAut R) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : R →* MulAut R).range := by
  have h : ∀ x y : Outer R, x * y = y * x := fun x y => by
    apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective
    rw [map_mul, map_mul]
    exact (CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_commutative
      ).is_comm.comm _ _
  change ⁅α, β⁆ ∈ inner R
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
    commutatorElement_eq_one_iff_mul_comm]
  exact h _ _

theorem ggRawAll_b2der [Finite K] (hK : Nat.card K = 2) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
          (LargeEvenGSpSet K 2))
        (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) ∧
      GGRawFieldCentral (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
          (LargeEvenGSpSet K 2))
        (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) ∧
      GGRawFieldConj p (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
          (LargeEvenGSpSet K 2))
        (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) := by
  have hSH : ∀ A ∈ gsp 2 K, ∀ h ∈ (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :
      Subgroup (GL (Fin 2 ⊕ Fin 2) K)), A * h * A⁻¹ ∈ ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
    fun A hA h hh => conj_mem_commutator_statedSp A hA hh
  set J := matConjSubgroup ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ (gsp 2 K) hSH with hJdef
  have hJ : (J : Set (MulAut (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆))) =
      LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2) := by
    rw [hJdef, coe_matConjSubgroup, largeEvenGSpSet_eq]
  have hinn := conj_mem_matConjSubgroup _ _ (commutator_statedSp_le_gsp 2) hSH
  have hF := fun f hf => matFieldImage_eq_one_of_card_two hK
    ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ (φ := f) hf
  obtain ⟨e⟩ := nonempty_b2der_equiv_alternatingGroup hK
  refine ⟨ggRawInnField_of_forall_eq_one hp J hJ hinn hF, ?_, ggRawFieldConj_of_forall_eq_one hF⟩
  rw [← hJ]
  refine ggRawFieldCentral_of_commutator_mem fun α β => ?_
  obtain ⟨r, hr⟩ := commutator_mem_inn_of_mulEquiv_alternatingSix e α β
  rw [← hr]
  exact hinn r

end RecipeFieldSp

open RecipeFieldSp

@[expose] def GGSymplecticHighLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank

theorem ggRawInnFieldOn_symplectic : GGRawInnFieldOn GGSymplecticRecipeLabel := by
  intro p hp _ lab hlab hS Q₀ h
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · have hl2 : 2 ≤ l := hlab.2.1
    have : NeZero l := ⟨by omega⟩
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawInnField_symplectic hp1
  · have hl2 : 2 ≤ l := hlab.2.1
    have : NeZero l := ⟨by omega⟩
    dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawInnField_symplectic hp1

theorem ggRawFieldCentralOn_symplecticHigh : GGRawFieldCentralOn GGSymplecticHighLabel := by
  intro lab _ hS Q₀ h
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hS, hl3⟩ := hS
  dsimp only at hl3
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawFieldCentral_symplectic hl3
  · dsimp only [LargeEvenRawDatum] at h ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) h
    have : CharP K 2 := charP_two_of_card hK
    exact ggRawFieldCentral_symplectic hl3

@[expose] def GGB2derLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B2der

theorem largeEvenLabelAll_b2der {lab : LargeEvenLabel} (hS : GGB2derLabel lab) {P : LargeEvenRawCont}
    (hP : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
      P (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
          (LargeEvenGSpSet K 2))
        (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆))) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only [GGB2derLabel] at hS
  subst hS
  intro Q hQ
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQK, hP K hK⟩

theorem ggRawInnFieldOn_b2der : GGRawInnFieldOn GGB2derLabel :=
  fun _ hp _ _ _ hS => largeEvenLabelAll_b2der hS fun _ _ _ hK => (ggRawAll_b2der hK hp.one_lt.ne').1

theorem ggRawFieldCentralOn_b2der : GGRawFieldCentralOn GGB2derLabel :=
  fun _ _ hS => largeEvenLabelAll_b2der hS fun _ _ _ hK =>
    (ggRawAll_b2der hK (p := 2) (by norm_num)).2.1

theorem ggRawFieldConjOn_b2der : GGRawFieldConjOn fun _ => GGB2derLabel :=
  fun _ hp _ _ _ hS => largeEvenLabelAll_b2der hS fun _ _ _ hK =>
    (ggRawAll_b2der hK hp.one_lt.ne').2.2

end CFSG.StandardType

end
