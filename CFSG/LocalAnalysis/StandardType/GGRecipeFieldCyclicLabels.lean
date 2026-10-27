module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSymplectic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphFieldB2der

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

section Generic

variable {R : Type} [Group R] {I F : Set (MulAut R)}

theorem ggRawPCyclic_of_mem {p : ℕ} (J : Subgroup (MulAut R)) (hJ : (J : Set (MulAut R)) = I)
    (hpJ : ∀ α : MulAut R, (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ J) : GGRawPCyclic p R I F := by
  intro _ _
  refine ⟨J, J, hJ, le_rfl, ?_, ⟨1, J.one_mem, fun s hs => ⟨0, by simpa using hs⟩⟩, hpJ⟩
  rw [Subgroup.subgroupOf_self]
  infer_instance

theorem ggRawPCyclic_of_outCyclic {p : ℕ} (J : Subgroup (MulAut R))
    (hJ : (J : Set (MulAut R)) = I) (hinn : ∀ r : R, MulAut.conj r ∈ J) (h : GGOutCyclic R) :
    GGRawPCyclic p R I F := by
  intro _ _
  have hInnJ : (MulAut.conj : R →* MulAut R).range ≤ J := by
    rintro _ ⟨r, rfl⟩
    exact hinn r
  have hJn : J.Normal := ⟨fun j hj α => by
    have hc := commutator_mem_inn_of_outCyclic h α j
    have e : α * j * α⁻¹ = (α * j * α⁻¹ * j⁻¹) * j := by group
    rw [e]
    exact J.mul_mem (hInnJ hc) hj⟩
  obtain ⟨φ₀, hφ₀⟩ := h
  refine ⟨J, ⊤, hJ, le_top, inferInstance, ⟨φ₀, Subgroup.mem_top _, fun s _ => ?_⟩,
    fun α _ => Subgroup.mem_top α⟩
  have hs := hφ₀ s
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hs
  obtain ⟨i, hi, z, hz, rfl⟩ := hs
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨-m, ?_⟩
  have e : φ₀ ^ (-m) * (i * φ₀ ^ m) = φ₀ ^ (-m) * i * (φ₀ ^ (-m))⁻¹ := by group
  rw [e]
  exact hInnJ (Subgroup.Normal.conj_mem inferInstance i hi _)

end Generic

section OutCyclic

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem isCyclic_ringEquiv_of_card {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : IsCyclic (K ≃+* K) :=
  (card_ringAut_and_isCyclic Nat.prime_two K hK).2


theorem ggOutCyclic_chev {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (τ : Tag)
    (hτ : (τ = .G2 ∧ 2 ≤ f) ∨ τ = .F4 ∨ τ = .E7 ∨ τ = .E8) :
    GGOutCyclic (adjointGroup τ K) := by
  have := isCyclic_ringEquiv_of_card hK
  rcases hτ with ⟨rfl, hf2⟩ | rfl | rfl | rfl
  · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf2 K hK
    exact ggOutCyclic_of_hom Θ hsurj hker
  · have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
    obtain ⟨-, -, ⟨Θ, -, hsurj, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
    exact ggOutCyclic_of_hom Θ hsurj hker
  · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
    exact ggOutCyclic_of_hom Θ hsurj hker
  · obtain ⟨-, Θ, -, hsurj, hker, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E8 (Or.inr rfl)
    exact ggOutCyclic_of_hom Θ hsurj hker

@[expose] def GGRecipeExcCyclicLabel (lab : LargeEvenLabel) : Prop :=
  GGRecipeExcOutLabel lab ∨ GGRecipeOutCyclicLabel lab

theorem ggRawPCyclicOn_excCyclic :
    GGRawPCyclicOn fun _ => GGRecipeExcCyclicLabel := by
  intro p _ _ lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with (ht | ht | ht | ht) | (ht | ht) <;> dsimp only at ht <;> subst ht
  · obtain ⟨-, hn2⟩ := hl
    exact recipeChevalley_and (fun K _ _ hK => ggRawPCyclic_of_outCyclic _ rfl
      (conj_mem_chevIDImage _) ((ggOutCyclic_chev hn K hK .G2 (Or.inl ⟨rfl, hn2⟩)).of_mulEquiv
        (recipeChevEquiv .G2 K))) hQ
  · exact recipeChevalley_and (fun K _ _ hK => ggRawPCyclic_of_outCyclic _ rfl
      (conj_mem_chevIDImage _) ((ggOutCyclic_chev hn K hK .F4 (Or.inr (Or.inl rfl))).of_mulEquiv
        (recipeChevEquiv .F4 K))) hQ
  · exact recipeChevalley_and (fun K _ _ hK => ggRawPCyclic_of_outCyclic _ rfl
      (conj_mem_chevIDImage _)
      ((ggOutCyclic_chev hn K hK .E7 (Or.inr (Or.inr (Or.inl rfl)))).of_mulEquiv
        (recipeChevEquiv .E7 K))) hQ
  · exact recipeChevalley_and (fun K _ _ hK => ggRawPCyclic_of_outCyclic _ rfl
      (conj_mem_chevIDImage _)
      ((ggOutCyclic_chev hn K hK .E8 (Or.inr (Or.inr (Or.inr rfl)))).of_mulEquiv
        (recipeChevEquiv .E8 K))) hQ
  · exact recipeTwisted_and (fun K _ _ hK => ggRawPCyclic_of_outCyclic _ rfl
      (conj_mem_chevIDImage _) (ggOutCyclic_triD4 hn K hK)) hQ
  · obtain ⟨-, -, h3⟩ := hl
    exact recipeTwF4_and (fun K _ _ hK => ggRawPCyclic_of_outCyclic _ rfl
      (conj_mem_chevIDImage _) (ggOutCyclic_twF4 (by omega) K hK)) hQ

end OutCyclic

namespace RecipeFieldLinear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d : ℕ} {K : Type} [Field K]

theorem conj_mem_linearAutGroup_of_mem_semilinear {e x : MulAut (projectiveSL d K)}
    (he : e ∈ semilinearAutGroup d K) (hx : x ∈ linearAutGroup d K) :
    e * x * e⁻¹ ∈ linearAutGroup d K := by
  obtain ⟨-, -, hfc, -⟩ := standard_automorphism_transport (n := d) (K := K)
  obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp he
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.mp hx
  have e1 : conjAut d K A * fieldAut d K σ * conjAut d K B * (conjAut d K A * fieldAut d K σ)⁻¹ =
      conjAut d K A * (fieldAut d K σ * conjAut d K B * (fieldAut d K σ)⁻¹) * (conjAut d K A)⁻¹ := by
    group
  rw [e1, hfc σ B, ← map_inv, ← map_mul, ← map_mul]
  exact conjAut_mem_linearAutGroup _

theorem ggRawPCyclic_linear [Finite K] (hd : 2 ≤ d) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  intro _ _
  set E := MulAut.congr (TypeA.recipeEquiv d K) with hE
  set S : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) :=
    (semilinearAutGroup d K).comap E.toMonoidHom with hS
  have hJS : recI d K ≤ S := fun φ hφ => linearAutGroup_le_semilinearAutGroup hφ
  have hFS : LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) ⊆ S := by
    intro f hf
    obtain ⟨σ, hσ⟩ := congr_field_eq hf
    change E f ∈ semilinearAutGroup d K
    rw [hσ]
    exact fieldAut_mem_semilinearAutGroup σ
  obtain ⟨-, -, -, -, -, ⟨g, hgE, hgk⟩, -⟩ := standard_outer_quotients (n := d) (K := K)
  refine ⟨recI d K, S, coe_recI, hJS, ⟨fun n hn s => ?_⟩, ⟨E.symm g, ?_, fun s hs => ?_⟩,
    fun α ⟨k, hk⟩ => ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [mem_recI_iff, map_mul, map_mul, map_inv]
    exact conj_mem_linearAutGroup_of_mem_semilinear s.2 hn
  · change E (E.symm g) ∈ semilinearAutGroup d K
    rw [MulEquiv.apply_symm_apply]
    exact hgE
  · obtain ⟨k, hk⟩ := hgk (E s) hs
    refine ⟨k, ?_⟩
    rw [mem_recI_iff, map_mul, map_zpow, MulEquiv.apply_symm_apply]
    exact hk
  · obtain ⟨u, hu, f, hf, rfl⟩ := NbrGraphLinear.ggOddAutInnField_linear (K := K) hd hp.pow α hk
    rw [← coe_recI] at hu
    exact S.mul_mem (hJS hu) ((Subgroup.closure_le S).mpr hFS hf)

end RecipeFieldLinear

namespace RecipeFieldSp

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {m : ℕ} {K : Type} [Field K]

theorem exists_pCyclic_symplectic [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hm : 2 ≤ m) {p : ℕ} (hp : Odd p) :
    ∃ J S : Subgroup (MulAut (StatedProj (StatedSp m K))),
      (J : Set (MulAut (StatedProj (StatedSp m K)))) =
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) ∧
      J ≤ S ∧ (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut (StatedProj (StatedSp m K)), (∃ k : ℕ, α ^ p ^ k = 1) → α ∈ S := by
  have : CharP K 2 := charP_two_of_card hK
  have : NeZero m := ⟨by omega⟩
  obtain ⟨Fr, -, -, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_two hf hK
  have hJ : (((MulAut.conj : StatedProj (StatedSp m K) →* MulAut _).range :
      Subgroup (MulAut (StatedProj (StatedSp m K)))) : Set (MulAut (StatedProj (StatedSp m K)))) =
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) := by
    ext φ
    exact mem_conjImage_iff_inn.symm
  have hJS : (MulAut.conj : StatedProj (StatedSp m K) →* MulAut _).range ≤
      spSemilinearAutGroup m K :=
    (standard_outer_quotient (K := K) (by omega : 1 ≤ m)).1.trans
      spLinearAutGroup_le_spSemilinearAutGroup
  refine ⟨_, spSemilinearAutGroup m K, hJ, hJS, Subgroup.normal_subgroupOf,
    ⟨fieldAut m K Fr, fieldAut_mem_spSemilinearAutGroup Fr, fun s hs => ?_⟩, fun α ⟨k, hk⟩ => ?_⟩
  · obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hs
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hzp ▸ Subgroup.mem_top σ)
    refine ⟨-j, ?_⟩
    have e : fieldAut m K Fr ^ (-j) * (conjAut m K A * fieldAut m K (Fr ^ j)) =
        fieldAut m K Fr ^ (-j) * conjAut m K A * (fieldAut m K Fr ^ (-j))⁻¹ := by
      rw [map_zpow]
      group
    rw [e]
    exact Subgroup.Normal.conj_mem inferInstance _ (AutPSp.conjAut_mem_inn A) _
  · rcases Nat.lt_or_ge m 3 with h | h
    · obtain rfl : m = 2 := by omega
      obtain ⟨A, σ, rfl⟩ := RootDetectSp.sp_two_form_of_pow_eq_one hp.pow α hk
      exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
        (fieldAut_mem_spSemilinearAutGroup σ)
    · obtain ⟨A, σ, rfl⟩ := (automorphism_generation (K := K) h).2 α
      exact mul_mem (spLinearAutGroup_le_spSemilinearAutGroup (conjAut_mem_spLinearAutGroup A))
        (fieldAut_mem_spSemilinearAutGroup σ)

theorem ggRawPCyclic_symplectic [Finite K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hm : 2 ≤ m) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K m))) :=
  fun _ _ => exists_pCyclic_symplectic hf hK hm hp

theorem ggRawPCyclic_b2der [Finite K] (hK : Nat.card K = 2) {p : ℕ} (hp : Odd p) :
    GGRawPCyclic p (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
      (LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2))
      (LargeEvenMatFieldImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)) := by
  have hSH : ∀ A ∈ gsp 2 K, ∀ h ∈ (⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :
      Subgroup (GL (Fin 2 ⊕ Fin 2) K)), A * h * A⁻¹ ∈ ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ :=
    fun A hA h hh => conj_mem_commutator_statedSp A hA hh
  have hJ : (matConjSubgroup ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆ (gsp 2 K) hSH :
      Set (MulAut (LargeEvenProj ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆))) =
      LargeEvenMatConjImage (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆)
        (LargeEvenGSpSet K 2) := by
    rw [coe_matConjSubgroup, largeEvenGSpSet_eq]
  refine ggRawPCyclic_of_mem _ hJ fun α ⟨k, hk⟩ => ?_
  obtain ⟨u, hu, f, hf, rfl⟩ := NbrGraphB2der.ggOddAutInnField_b2der hK hp.pow α hk
  rw [eq_one_of_mem_closure_of_forall
    (fun f hf => matFieldImage_eq_one_of_card_two hK _ (φ := f) hf) hf, mul_one]
  rw [← SetLike.mem_coe, hJ]
  exact hu

end RecipeFieldSp

open RecipeFieldLinear RecipeFieldSp

theorem ggRawPCyclicOn_linear : GGRawPCyclicOn fun _ => GGLinearRecipeLabel := by
  intro p hp hp2 lab hlab hS Q₀ h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht <;> subst ht
  · have hl1 : 1 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ggRawPCyclic_linear (by omega) hodd) h
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ggRawPCyclic_linear (by omega) hodd) h
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at h ⊢
    exact NbrGraphLinear.recipeLinear_all (fun K _ _ _ => ggRawPCyclic_linear le_rfl hodd) h

theorem ggRawPCyclicOn_symplectic : GGRawPCyclicOn fun _ => GGSymplecticRecipeLabel := by
  intro p hp hp2 lab hlab hS Q₀ h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨t, l, n⟩ := lab
  rcases hS with ht | ht <;> dsimp only at ht <;> subst ht
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK =>
      ggRawPCyclic_symplectic hlab.1 hK hl2 hodd) h
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK =>
      ggRawPCyclic_symplectic hlab.1 hK hl2 hodd) h

theorem ggRawPCyclicOn_b2der : GGRawPCyclicOn fun _ => GGB2derLabel :=
  fun _ hp hp2 _ _ hS => largeEvenLabelAll_b2der hS fun _ _ _ hK =>
    ggRawPCyclic_b2der hK (hp.odd_of_ne_two hp2)

end CFSG.StandardType

end
