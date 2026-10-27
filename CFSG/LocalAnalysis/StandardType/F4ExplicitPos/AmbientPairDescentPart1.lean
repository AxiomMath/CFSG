module

public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedImage
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PairStabilizerNativePart2

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

open CFSG.LieType.Steinberg.Adjoint

open CFSG.LieType.Universal

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

open CFSG.StandardType.F4ExplicitPos.PairStabilizerNative

open CFSG.StandardType.F4ExplicitPos.FixedImage

open CFSG.StandardType.F4ExplicitPos.AmbientAction

open CFSG.StandardType

open CFSG.SeitzReduction

open scoped CFSG.ConvolutionPoints

namespace CFSG.StandardType.F4ExplicitPos.AmbientPairDescent

variable {τ : Tag} {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]

section No117Roots

open CFSG.LieType.RootSystem

theorem roots_eq_setOf_isRoot_no117 {τ : Tag} (hA : TauCeti.IsFiniteType τ.cartan) :
    CFSG.LieType.RootSystem.roots hA ∅ = {γ | IsRoot τ γ} := by
  ext γ
  constructor
  · rintro (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix hA).toCoxeterSystem.wordProd_surjective w
      induction ω with
      | nil => simpa using IsRoot.basis i
      | cons j ω ih =>
        rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
          reflection_apply]
        exact IsRoot.reflect j ih
    · exact absurd hi (Set.notMem_empty i)
  · intro h
    induction h with
    | basis j => exact Or.inl ⟨1, j, by simp⟩
    | @reflect i v _ ih =>
      rcases ih with ⟨w, j, hw⟩ | ⟨w, j, hj, -⟩
      · refine Or.inl ⟨(coxeterMatrix hA).toCoxeterSystem.simple i * w, j, ?_⟩
        rw [weylAction_mul_apply, ← hw, weylAction_simple, reflection_apply]
        rfl
      · exact absurd hj (Set.notMem_empty j)

theorem adjDatum_roots_no117
    (F : RootOperatorFamily τ) (K : Type) [Field K] :
    (adjDatum F K).roots = {γ | IsRoot τ γ} :=
  roots_eq_setOf_isRoot_no117 (τ := τ) (isFiniteType_cartan τ)

theorem mem_adjDatum_roots_no117
    (F : RootOperatorFamily τ) (K : Type) [Field K]
    {γ : Fin τ.rank → ℤ} :
    γ ∈ (adjDatum F K).roots ↔ IsRoot τ γ := by
  rw [adjDatum_roots_no117 F K]
  rfl

theorem eq_one_of_isRoot_nsmul_no117 {γ : Fin τ.rank → ℤ} {n : ℕ}
    (h : IsRoot τ (n • γ)) : n = 1 := by
  have e : (n • γ : Fin τ.rank → ℤ) = (n : ℤ) • γ := (Nat.cast_smul_eq_nsmul ℤ n γ).symm
  rcases h.eq_one_or_neg_one_of_eq_smul e with h1 | h1 <;> omega

end No117Roots

theorem rootSubgroup_map_bcGL_eq_fixed
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K) (β : Fin τ.rank → ℤ) :
    (rootSubgroup τ K β).map (bcGL (τ := τ) (algebraMap K Ω)) =
      rootSubgroup τ Ω β ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id (ModGL τ Ω)) := by
  have hFbc : (Units.map (entrywiseHom Fr) : ModGL τ Ω →* ModGL τ Ω) =
      bcGL (τ := τ) Fr := by
    rw [bcGL, ← bcEndHom_eq_entrywiseHom]
  refine le_antisymm ?_ ?_
  · rintro x ⟨g, hg, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hg
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact Subgroup.subset_closure
        ⟨algebraMap K Ω c, (bcGL_pinnedX (τ := τ) (algebraMap K Ω) β c).symm⟩
    · change Units.map (entrywiseHom Fr)
          (bcGL (τ := τ) (algebraMap K Ω) (pinnedX τ K β c)) =
        bcGL (τ := τ) (algebraMap K Ω) (pinnedX τ K β c)
      rw [hFbc, bcGL_comp (algebraMap K Ω) Fr, frobenius_comp_algebraMap Fr hFr]
  · intro x hx
    obtain ⟨hxU, hxfix⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hxU
    have hfix : bcGL (τ := τ) Fr (pinnedX τ Ω β c) = pinnedX τ Ω β c := by
      rw [← hFbc]; exact hxfix
    rw [bcGL_pinnedX (τ := τ) Fr β c] at hfix
    have hc : Fr c = c := pinnedX_injective τ Ω β hfix
    obtain ⟨a, ha⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (L := Ω)
      (c := c) (by rw [← hFr]; exact hc)
    refine Subgroup.mem_map.2
      ⟨pinnedX τ K β a, Subgroup.subset_closure ⟨a, rfl⟩, ?_⟩
    rw [bcGL_pinnedX (τ := τ) (algebraMap K Ω) β a, ha]

theorem card_map_bcGL_rootSubgroup
    (Fr : Ω →+* Ω) (_hFr : ∀ c, Fr c = c ^ Nat.card K) (β : Fin τ.rank → ℤ) :
    Nat.card ((rootSubgroup τ K β).map (bcGL (τ := τ) (algebraMap K Ω))) = Nat.card K := by
  rw [Subgroup.card_map_of_injective (bcGL_injective (τ := τ) (algebraMap K Ω)
    (FaithfulSMul.algebraMap_injective K Ω)), card_rootSubgroup]

section GenericPair

variable {G : Type*} [Group G]

theorem mem_normalizer_inv_mul_of_map_conj_eq
    (F : G →* G) {U : Subgroup G} {g : G}
    (h : U.map (MulAut.conj (F g)).toMonoidHom = U.map (MulAut.conj g).toMonoidHom) :
    g⁻¹ * F g ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  have hcomp : (MulAut.conj (g⁻¹ * F g)).toMonoidHom =
      ((MulAut.conj g⁻¹).toMonoidHom).comp ((MulAut.conj (F g)).toMonoidHom) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [hcomp, ← Subgroup.map_map, h, Subgroup.map_map]
  have hid : ((MulAut.conj g⁻¹).toMonoidHom).comp ((MulAut.conj g).toMonoidHom) =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    group
  rw [hid, Subgroup.map_id]

theorem exists_fixed_conj_eq_of_lang_pair
    (F : G →* G) (A Uplus Uminus : Subgroup G)
    (hFA : ∀ x ∈ A, F x ∈ A)
    (hLang : ∀ c ∈ A ⊓ Subgroup.normalizer (Uplus : Set G) ⊓
        Subgroup.normalizer (Uminus : Set G), ∃ z ∈
        A ⊓ Subgroup.normalizer (Uplus : Set G) ⊓ Subgroup.normalizer (Uminus : Set G),
        z⁻¹ * F z = c)
    {g : G} (hgA : g ∈ A)
    (hstabplus : Uplus.map (MulAut.conj (F g)).toMonoidHom =
      Uplus.map (MulAut.conj g).toMonoidHom)
    (hstabminus : Uminus.map (MulAut.conj (F g)).toMonoidHom =
      Uminus.map (MulAut.conj g).toMonoidHom) :
    ∃ u ∈ A, F u = u ∧
      Uplus.map (MulAut.conj u).toMonoidHom = Uplus.map (MulAut.conj g).toMonoidHom ∧
      Uminus.map (MulAut.conj u).toMonoidHom = Uminus.map (MulAut.conj g).toMonoidHom := by
  have hcA : g⁻¹ * F g ∈ A := Subgroup.mul_mem _ (Subgroup.inv_mem _ hgA) (hFA g hgA)
  have hcNplus := mem_normalizer_inv_mul_of_map_conj_eq F hstabplus
  have hcNminus := mem_normalizer_inv_mul_of_map_conj_eq F hstabminus
  have hcZ : g⁻¹ * F g ∈ A ⊓ Subgroup.normalizer (Uplus : Set G) ⊓
      Subgroup.normalizer (Uminus : Set G) :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hcA, hcNplus⟩, hcNminus⟩
  obtain ⟨z, hzZ, hz⟩ := hLang _ hcZ
  obtain ⟨⟨hzA, hzNplus⟩, hzNminus⟩ := Subgroup.mem_inf.1 hzZ
  have hzinvmapPlus : Uplus.map (MulAut.conj z⁻¹).toMonoidHom = Uplus := by
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ hzNplus)
    rwa [← MulEquiv.toMonoidHom_eq_coe] at h1
  have hzinvmapMinus : Uminus.map (MulAut.conj z⁻¹).toMonoidHom = Uminus := by
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.inv_mem _ hzNminus)
    rwa [← MulEquiv.toMonoidHom_eq_coe] at h1
  refine ⟨g * z⁻¹, Subgroup.mul_mem _ hgA (Subgroup.inv_mem _ hzA), ?_, ?_, ?_⟩
  · have hFz : F z = z * (g⁻¹ * F g) := by rw [← hz]; group
    rw [map_mul, map_inv, hFz]; group
  · have hcomp : (MulAut.conj (g * z⁻¹)).toMonoidHom =
        ((MulAut.conj g).toMonoidHom).comp ((MulAut.conj z⁻¹).toMonoidHom) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map, hzinvmapPlus]
  · have hcomp : (MulAut.conj (g * z⁻¹)).toMonoidHom =
        ((MulAut.conj g).toMonoidHom).comp ((MulAut.conj z⁻¹).toMonoidHom) := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hcomp, ← Subgroup.map_map, hzinvmapMinus]

theorem map_conj_fixed_eq
    (F : G →* G) {u : G} (hu : F u = u) (U : Subgroup G) :
    U.map (MulAut.conj u).toMonoidHom ⊓ F.eqLocus (MonoidHom.id G) =
      (U ⊓ F.eqLocus (MonoidHom.id G)).map (MulAut.conj u).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxmap, hxfix⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hy, rfl⟩ := hxmap
    refine Subgroup.mem_map.2 ⟨y, ⟨hy, ?_⟩, rfl⟩
    have h2 : F y = y := by
      have h : F (u * y * u⁻¹) = u * y * u⁻¹ := hxfix
      rw [map_mul, map_mul, map_inv, hu] at h
      calc F y = u⁻¹ * (u * F y * u⁻¹) * u := by group
        _ = u⁻¹ * (u * y * u⁻¹) * u := by rw [h]
        _ = y := by group
    exact h2
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨hyU, hyfix⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem _ hyU, ?_⟩
    have h : F y = y := hyfix
    change F (u * y * u⁻¹) = u * y * u⁻¹
    rw [map_mul, map_mul, map_inv, hu, h]

end GenericPair

section FrobeniusPair

variable [IsAlgClosed Ω]

variable (p : ℕ) [Fact p.Prime] [CharP Ω p]

theorem exists_fixed_conj_eq_of_frobTwist_pair
    (e : ℕ) (he : 1 ≤ e)
    (A Uplus Uminus : Subgroup (ModGL τ Ω))
    (hFA : ∀ x ∈ A, frobTwistGL τ Ω p e 1 x ∈ A)
    (hFZ : ∀ x ∈ A ⊓ Subgroup.normalizer (Uplus : Set (ModGL τ Ω)) ⊓
        Subgroup.normalizer (Uminus : Set (ModGL τ Ω)), frobTwistGL τ Ω p e 1 x ∈
        A ⊓ Subgroup.normalizer (Uplus : Set (ModGL τ Ω)) ⊓
          Subgroup.normalizer (Uminus : Set (ModGL τ Ω)))
    (hZ : IsConnectedAlgebraicSubgroup Ω
      ((A ⊓ Subgroup.normalizer (Uplus : Set (ModGL τ Ω)) ⊓
        Subgroup.normalizer (Uminus : Set (ModGL τ Ω))).map (modGLPoint τ Ω).toMonoidHom))
    {g : ModGL τ Ω} (hgA : g ∈ A)
    (hstabplus : Uplus.map (MulAut.conj (frobTwistGL τ Ω p e 1 g)).toMonoidHom =
      Uplus.map (MulAut.conj g).toMonoidHom)
    (hstabminus : Uminus.map (MulAut.conj (frobTwistGL τ Ω p e 1 g)).toMonoidHom =
      Uminus.map (MulAut.conj g).toMonoidHom) :
    ∃ u ∈ A, frobTwistGL τ Ω p e 1 u = u ∧
      Uplus.map (MulAut.conj u).toMonoidHom = Uplus.map (MulAut.conj g).toMonoidHom ∧
      Uminus.map (MulAut.conj u).toMonoidHom = Uminus.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_, _, _, hLang⟩ := exists_frobTwist_restriction (τ := τ) p hZ he (1 : ModGL τ Ω) hFZ
  exact exists_fixed_conj_eq_of_lang_pair (frobTwistGL τ Ω p e 1) A Uplus Uminus hFA hLang hgA
    hstabplus hstabminus

end FrobeniusPair

section F4Native

variable [IsAlgClosed Ω] [CharP Ω 2]

theorem f4_long_pair_descent
    (f : ℕ) (hf : 1 ≤ f)
    {g : ModGL Tag.F4 Ω} (hgA : g ∈ adjointGroup Tag.F4 Ω)
    (hstabplus : (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom)
    (hstabminus : (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map
        (MulAut.conj (entrywiseFrobGL Tag.F4 Ω 2 f g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom) :
    ∃ u ∈ adjointGroup Tag.F4 Ω, entrywiseFrobGL Tag.F4 Ω 2 f u = u ∧
      (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map (MulAut.conj u).toMonoidHom =
        (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom ∧
      (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map (MulAut.conj u).toMonoidHom =
        (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom := by
  have hFZ : ∀ x ∈ adjointGroup Tag.F4 Ω ⊓
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω (highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)) ⊓
      Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)),
      frobTwistGL Tag.F4 Ω 2 f 1 x ∈
      adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)) :=
    fun x hx => f4_frobTwistGL_one_mem_pairStabilizer (K := Ω) 2 f hx
  have hZ : IsConnectedAlgebraicSubgroup Ω
      ((adjointGroup Tag.F4 Ω ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (highRoot Tag.F4) : Set (ModGL Tag.F4 Ω)) ⊓
        Subgroup.normalizer (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4) : Set (ModGL Tag.F4 Ω))).map
          (modGLPoint Tag.F4 Ω).toMonoidHom) :=
    f4_isConnectedAlgebraicSubgroup_pairStabilizer (K := Ω)
  have hFA : ∀ x ∈ adjointGroup Tag.F4 Ω,
      frobTwistGL Tag.F4 Ω 2 f 1 x ∈ adjointGroup Tag.F4 Ω := by
    intro x hx
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    have hm : (entrywiseFrobGL Tag.F4 Ω 2 f : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) =
        bcGL (τ := Tag.F4) (iterateFrobenius Ω 2 f) := by
      rw [entrywiseFrobGL, bcGL, bcEndHom_eq_entrywiseHom]
    rw [hm]
    exact bcGL_mem_adjointGroup _ hx
  have hstabplus' : (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map
      (MulAut.conj (frobTwistGL Tag.F4 Ω 2 f 1 g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom := by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]; exact hstabplus
  have hstabminus' : (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map
      (MulAut.conj (frobTwistGL Tag.F4 Ω 2 f 1 g)).toMonoidHom =
      (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)).map (MulAut.conj g).toMonoidHom := by
    rw [frobTwistGL_apply, one_mul, inv_one, mul_one]; exact hstabminus
  obtain ⟨u, huA, hFu, hplus, hminus⟩ :=
    exists_fixed_conj_eq_of_frobTwist_pair (τ := Tag.F4) 2 f hf
      (adjointGroup Tag.F4 Ω) (rootSubgroup Tag.F4 Ω (highRoot Tag.F4))
      (rootSubgroup Tag.F4 Ω (-highRoot Tag.F4)) hFA hFZ hZ hgA hstabplus' hstabminus'
  refine ⟨u, huA, ?_, hplus, hminus⟩
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one] at hFu
  exact hFu

end F4Native
end CFSG.StandardType.F4ExplicitPos.AmbientPairDescent
end

end
