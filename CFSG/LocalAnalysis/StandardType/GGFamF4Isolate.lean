module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart1
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.JointShapesPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddShapesPart2
public import CFSG.Mathlib.Decide.Bounded

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.LieCore Matrix
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Dickson.Sec6.I1431.ExcKacNodes CFSG.SeitzReduction.F4Pilot

open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.StandardType.F4ExplicitPos.JointIsolator
open CFSG.StandardType.F4ExplicitPos.JointShapes
open scoped MatrixGroups Matrix
open Classical

theorem l10lH1_kernelRoots_isolated
    {Ω : Type} [Field Ω] [IsAlgClosed Ω]
    {p ℓ : ℕ} (hℓ : 11 < ℓ) (hcop : p.Coprime ℓ)
    {M M₁ : Type*} [CommGroup M] [CommGroup M₁]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (χ₁ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M₁)
    (d : Fin Tag.F4.rank → Ωˣ)
    (hinter : kernelRoots χ = kernelRoots χ₁ ∩ kernelRoots (rootCharHom d))
    (hd : ∀ i, d i ^ p = 1)
    {lam : Ωˣ} (hlam : IsPrimitiveRoot lam ℓ)
    {v : WeylGroup Tag.F4} {J : Set (Fin Tag.F4.rank)}
    {j : KernelComponent χ₁}
    (hH : componentRoots χ₁ j = (fun α => v • α) '' parabolicRoots Tag.F4 J) :
    kernelRoots (rootCharHom (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d))) =
      kernelRoots χ ∩ componentRoots χ₁ j := by
  have hd' : ∀ i, (weylTuple v⁻¹ d) i ^ p = 1 := fun i => weylTuple_coord_pow hd v⁻¹ i
  have hkerd' : kernelRoots (rootCharHom (weylTuple v⁻¹ d)) =
      (fun α => v⁻¹ • α) '' kernelRoots (rootCharHom d) := kernelRoots_weylTuple v⁻¹ d
  have hb0 : kernelRoots (rootCharHom (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d)) =
      parabolicRoots Tag.F4 J ∩ kernelRoots (rootCharHom (weylTuple v⁻¹ d)) :=
    kernelRoots_lamDiag_mul_eq_inter hcop hlam hd'
      (kernelRoots_lamDiag_eq_parabolicRoots (Ω := Ω) hℓ hlam)
  rw [kernelRoots_weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d), hb0]
  have hinj : Function.Injective (fun α : Fin Tag.F4.rank → ℤ => v • α) :=
    fun x y h => by simpa using congrArg (fun z => v⁻¹ • z) h
  rw [Set.image_inter hinj]
  have himg : (fun α => v • α) '' kernelRoots (rootCharHom (weylTuple v⁻¹ d)) =
      kernelRoots (rootCharHom d) := by
    rw [hkerd', Set.image_image]
    have hfun : (fun α : Fin Tag.F4.rank → ℤ => v • (v⁻¹ • α)) = (fun α => α) := by
      funext α
      rw [← mul_smul, mul_inv_cancel, one_smul]
    rw [hfun, Set.image_id']
  rw [← hH, himg, hinter]
  ext x
  constructor
  · rintro ⟨hxj, hxd⟩
    exact ⟨⟨hxj.1, hxd⟩, hxj⟩
  · rintro ⟨⟨-, hxd⟩, hxj⟩
    exact ⟨hxj, hxd⟩

theorem l10lH1_proper_levi_case
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1)
    {M M₁ : Type*} [CommGroup M] [CommGroup M₁]
    (χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M)
    (χ₁ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M₁)
    (d : Fin Tag.F4.rank → Ωˣ)
    (hinter : kernelRoots χ = kernelRoots χ₁ ∩ kernelRoots (rootCharHom d))
    (hd : ∀ i, d i ^ p = 1)
    (v : WeylGroup Tag.F4) (J : Set (Fin Tag.F4.rank))
    (hJ : ∃ i, i ∉ J)
    {j : KernelComponent χ₁}
    (hH : componentRoots χ₁ j = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : γ ∈ kernelRoots χ)
    (hγj : γ ∈ componentRoots χ₁ j)
    {i : KernelComponent χ} (hi : i = (⟦⟨γ, hγ⟩⟧ : KernelComponent χ)) :
    ∃ w : WeylGroup Tag.F4,
      (∃ j, componentRoots χ i =
        (fun α => w • α) ''
          ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
      componentRoots χ i = (fun α => w • α) '' b2LeviRoots ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3 ∨
      componentRoots χ i =
        (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3 := by
  classical
  let ℓ : ℕ := 12 * p + 1
  have hℓ_gt : 11 < ℓ := by dsimp [ℓ]; omega
  have hℓ_pos : 0 < ℓ := by omega
  have hℓ_odd : ℓ % 2 = 1 := by dsimp [ℓ]; exact twelve_mul_add_one_odd p
  have hcop : p.Coprime ℓ := by dsimp [ℓ]; exact coprime_twelve_mul_add_one p
  have hℓΩ : (ℓ : Ω) ≠ 0 := natCast_ne_zero_of_odd hℓ_odd
  have : NeZero ℓ := ⟨Nat.pos_iff_ne_zero.1 hℓ_pos⟩
  obtain ⟨lam, hlam⟩ := exists_primitiveRoot_unit Ω ℓ hℓΩ
  have hd' : ∀ i, (weylTuple v⁻¹ d) i ^ p = 1 := fun i => weylTuple_coord_pow hd v⁻¹ i
  have hbker : kernelRoots
      (rootCharHom (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d))) =
      kernelRoots χ ∩ componentRoots χ₁ j :=
    l10lH1_kernelRoots_isolated hℓ_gt hcop χ χ₁ d hinter hd hlam hH
  have hb0N : ∀ i, (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d) i ^ (p * ℓ) = 1 :=
    fun i => lamDiag_mul_pow hlam hd' i
  have hbN : ∀ i, (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d)) i ^ (p * ℓ) = 1 :=
    fun i => weylTuple_coord_pow hb0N v i
  obtain ⟨i₀, hi₀⟩ := hJ
  have hb₀ne : (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d) i₀ ≠ 1 :=
    exists_off_ne_one hcop hlam (IsPrimitiveRoot.ne_one hlam (by omega)) hd' hi₀
  have hb1 : rootDiagUnit Tag.F4 (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d)) ≠ 1 :=
    weylTuple_rootDiagUnit_ne_one v (rootDiagUnit_ne_one_of_exists_ne_one ⟨i₀, hb₀ne⟩)
  have hN_pos : 0 < p * ℓ := Nat.mul_pos hp hℓ_pos
  have hN_odd : (p * ℓ) % 2 = 1 := mul_odd_mod_two hpodd hℓ_odd
  have hNΩ : ((p * ℓ : ℕ) : Ω) ≠ 0 := natCast_ne_zero_of_odd hN_odd
  have hsub : kernelRoots χ ⊆ kernelRoots χ₁ := by
    intro x hx
    rw [hinter] at hx
    exact hx.1
  obtain ⟨k, hk⟩ := exists_componentRoots_eq_of_kernelRoots_inter_component
    (τ := Tag.F4) hsub hbker hγ hγj
  have hki : componentRoots (rootCharHom
      (weylTuple v (lamDiag (K := Ω) J lam * weylTuple v⁻¹ d))) k = componentRoots χ i := by
    rw [hi]
    exact hk
  exact six_shape_of_isolated_component hN_pos hN_odd hNΩ hbN hb1 χ hki

abbrev l10lH1_SixShape (Ψ : Set (Fin Tag.F4.rank → ℤ)) : Prop :=
  ∃ w : WeylGroup Tag.F4,
    (∃ j : Fin Tag.F4.rank,
      Ψ = (fun α => w • α) '' ({Pi.single j 1, -Pi.single j 1} : Set (Fin Tag.F4.rank → ℤ))) ∨
    Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4LongSupport ∨
    Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4ShortSupport ∨
    Ψ = (fun α => w • α) '' b2LeviRoots ∨
    Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviB3 ∨
    Ψ = (fun α => w • α) '' parabolicRoots Tag.F4 f4LeviC3

theorem l10lH1_shape_finset
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {p : ℕ} (hp : 0 < p) (hpodd : p % 2 = 1) (F : Finset (Fin Tag.F4.rank → Ωˣ)) :
    (∀ b ∈ F, ∀ i, b i ^ p = 1) →
    (∃ b ∈ F, rootDiagUnit Tag.F4 b ≠ 1) →
    ∀ i : KernelComponent (famCharHom (fun b : ↥F => (b : Fin Tag.F4.rank → Ωˣ))),
      l10lH1_SixShape
        (componentRoots (famCharHom (fun b : ↥F => (b : Fin Tag.F4.rank → Ωˣ))) i) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _ hne
    exact absurd hne (by rintro ⟨b, hb, -⟩; exact Finset.notMem_empty b hb)
  | insert d F' hdnot ih =>
    intro hF hne
    set χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* (↥(insert d F') → Ωˣ) :=
      famCharHom (fun b : ↥(insert d F') => (b : Fin Tag.F4.rank → Ωˣ)) with hχ
    set χ₁ : Multiplicative (Fin Tag.F4.rank → ℤ) →* (↥F' → Ωˣ) :=
      famCharHom (fun b : ↥F' => (b : Fin Tag.F4.rank → Ωˣ)) with hχ₁
    have hF' : ∀ b ∈ F', ∀ i, b i ^ p = 1 := fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have hinter : kernelRoots χ = kernelRoots χ₁ ∩ kernelRoots (rootCharHom d) := by
      rw [hχ, hχ₁]
      ext γ'
      simp only [mem_kernelRoots_famChar, kernelRoots_rootCharHom, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · rintro ⟨hroot, hall⟩
        exact ⟨⟨hroot, fun u => hall ⟨u.1, Finset.mem_insert_of_mem u.2⟩⟩, hroot,
          hall ⟨d, Finset.mem_insert_self d F'⟩⟩
      · rintro ⟨⟨hroot, hall⟩, -, hd1⟩
        refine ⟨hroot, fun u => ?_⟩
        rcases Finset.mem_insert.1 u.2 with h | h
        · rw [h]; exact hd1
        · exact hall ⟨u.1, h⟩
    intro i
    obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
    by_cases hF'ne : ∃ b ∈ F', rootDiagUnit Tag.F4 b ≠ 1
    · have hγ₁ : γ ∈ kernelRoots χ₁ := (hinter.le hγ).1
      let j : KernelComponent χ₁ := ⟦⟨γ, hγ₁⟩⟧
      have hγj : γ ∈ componentRoots χ₁ j := ⟨hγ₁, rfl⟩
      rcases ih hF' hF'ne j with ⟨w, hA | hlong | hshort | hb2 | hb3 | hc3⟩
      · rcases hA with ⟨jj, hshape⟩
        refine ⟨w, Or.inl ⟨jj, ?_⟩⟩
        refine eq_pair_of_subset_wely_pair ?_ ⟨γ, hγ, rfl⟩
          (fun α hα => (isRootComponent_componentRoots (χ := χ) _).neg_mem α hα)
        exact hshape ▸ componentRoots_subset_of_kernel_subset
          (fun x hx => (hinter.le hx).1) ⟨hγ, rfl⟩ hγj
      · exact l10lH1_proper_levi_case hp hpodd χ χ₁ d hinter
          (hF d (Finset.mem_insert_self d F')) w f4LongSupport
          ⟨f4Index 3, by rw [mem_f4LongSupport]; decide⟩ hlong hγ hγj rfl
      · exact l10lH1_proper_levi_case hp hpodd χ χ₁ d hinter
          (hF d (Finset.mem_insert_self d F')) w f4ShortSupport
          ⟨f4Index 0, by rw [mem_f4ShortSupport]; decide⟩ hshort hγ hγj rfl
      · exact l10lH1_proper_levi_case hp hpodd χ χ₁ d hinter
          (hF d (Finset.mem_insert_self d F')) w nodesTU
          ⟨f4Index 0, by rw [mem_nodesTU]; decide⟩ hb2 hγ hγj rfl
      · exact l10lH1_proper_levi_case hp hpodd χ χ₁ d hinter
          (hF d (Finset.mem_insert_self d F')) w f4LeviB3
          ⟨f4Index 3, by rw [mem_f4LeviB3_narrow]; decide⟩ hb3 hγ hγj rfl
      · exact l10lH1_proper_levi_case hp hpodd χ χ₁ d hinter
          (hF d (Finset.mem_insert_self d F')) w f4LeviC3
          ⟨f4Index 0, by rw [mem_f4LeviC3_narrow]; decide⟩ hc3 hγ hγj rfl
    · push Not at hF'ne
      have hF'triv : ∀ b ∈ F', rootDiagUnit Tag.F4 b = 1 := fun b hb => hF'ne b hb
      have hd1 : rootDiagUnit Tag.F4 d ≠ 1 := by
        obtain ⟨b, hb, hbne⟩ := hne
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hbF'
        · exact hbne
        · exact absurd (hF'triv b hbF') hbne
      have hker : kernelRoots χ = kernelRoots (rootCharHom d) := by
        ext γ'
        rw [mem_kernelRoots_famChar, kernelRoots_rootCharHom, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hroot, hall⟩
          exact ⟨hroot, hall ⟨d, Finset.mem_insert_self d F'⟩⟩
        · rintro ⟨hroot, hdk⟩
          refine ⟨hroot, fun u => ?_⟩
          rcases Finset.mem_insert.1 u.2 with h | h
          · rw [h]; exact hdk
          · have hb1 : (u.1 : Fin Tag.F4.rank → Ωˣ) = 1 := by
              have hru : rootDiagUnit Tag.F4 u.1 =
                  rootDiagUnit Tag.F4 (1 : Fin Tag.F4.rank → Ωˣ) := by
                rw [hF'triv u.1 h, rootDiagUnit_one]
              exact CFSG.LieType.Chevalley.rootDiagUnit_injective hru
            rw [hb1]
            simp [rootChar]
      have hγd : γ ∈ kernelRoots (rootCharHom d) := hker.le hγ
      have heq : componentRoots (rootCharHom d) (⟦⟨γ, hγd⟩⟧ : KernelComponent (rootCharHom d)) =
          componentRoots χ (⟦⟨γ, hγ⟩⟧ : KernelComponent χ) :=
        (OddToralOrdinary.componentRoots_eq_of_kernelRoots_eq hker hγ hγd).symm
      exact six_shape_of_isolated_component hp hpodd (natCast_ne_zero_of_odd hpodd)
        (hF d (Finset.mem_insert_self d F')) hd1 χ heq

end CFSG.StandardType.TableCRes

end

end
