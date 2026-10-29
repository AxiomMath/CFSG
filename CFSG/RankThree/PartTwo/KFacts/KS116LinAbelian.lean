module

public import CFSG.RepresentationTheory.PerfectWeightStabilizerModule
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import CFSG.RankThree.PartTwo.KFacts.KS116LinRep

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

section CyclicNormalizer

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

private theorem ndc_C_exists_zpow_of_mem_normalizer {H : Type*} [Group H] {C : Subgroup H}
    [IsCyclic C] {k : H} (hk : k ∈ Subgroup.normalizer (C : Set H)) :
    ∃ m : ℤ, ∀ c ∈ C, k * c * k⁻¹ = c ^ m := by
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic (C.normalizerMonoidHom ⟨k, hk⟩).toMonoidHom
  exact ⟨m, fun c hc => by simpa using congrArg Subtype.val (hm ⟨c, hc⟩)⟩

theorem commutator_le_centralizer_of_isCyclic' {H : Type*} [Group H] {C K : Subgroup H}
    [IsCyclic C] (hK : K ≤ Subgroup.normalizer (C : Set H)) :
    ⁅K, K⁆ ≤ Subgroup.centralizer (C : Set H) := by
  rw [Subgroup.commutator_le]
  intro k₁ hk₁ k₂ hk₂
  obtain ⟨m₁, h₁⟩ := ndc_C_exists_zpow_of_mem_normalizer (hK hk₁)
  obtain ⟨m₂, h₂⟩ := ndc_C_exists_zpow_of_mem_normalizer (hK hk₂)
  obtain ⟨n₁, h₁'⟩ := ndc_C_exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ (hK hk₁))
  obtain ⟨n₂, h₂'⟩ := ndc_C_exists_zpow_of_mem_normalizer (Subgroup.inv_mem _ (hK hk₂))
  have e₁ : ∀ c ∈ C, (c ^ n₁) ^ m₁ = c := fun c hc => by
    rw [← h₁ _ (C.zpow_mem hc n₁), ← h₁' c hc]
    group
  have e₂ : ∀ c ∈ C, (c ^ n₂) ^ m₂ = c := fun c hc => by
    rw [← h₂ _ (C.zpow_mem hc n₂), ← h₂' c hc]
    group
  refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
  have hc₂ := C.zpow_mem hc n₂
  have hc₂₁ := C.zpow_mem hc₂ n₁
  have hc₂₁₂ := C.zpow_mem hc₂₁ m₂
  have key : ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹ = c := by
    calc ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹
        = k₁ * (k₂ * (k₁⁻¹ * (k₂⁻¹ * c * k₂⁻¹⁻¹) * k₁⁻¹⁻¹) * k₂⁻¹) * k₁⁻¹ := by
          rw [commutatorElement_def]; group
      _ = (((c ^ n₂) ^ n₁) ^ m₂) ^ m₁ := by rw [h₂' c hc, h₁' _ hc₂, h₂ _ hc₂₁, h₁ _ hc₂₁₂]
      _ = c := by
          rw [← zpow_mul (c ^ n₂) n₁ m₂, mul_comm n₁ m₂, zpow_mul (c ^ n₂) m₂ n₁, e₂ c hc,
            e₁ c hc]
  calc c * ⁅k₁, k₂⁆ = ⁅k₁, k₂⁆ * c * ⁅k₁, k₂⁆⁻¹ * ⁅k₁, k₂⁆ := by rw [key]
    _ = ⁅k₁, k₂⁆ * c := by group

private theorem ndc_C_isCyclic_units_of_irred [Finite F] [Module.Finite F V] [Nontrivial V]
    (𝒮 : Set (V →ₗ[F] V))
    (hirr : ∀ U : Submodule F V, (∀ s ∈ 𝒮, ∀ u ∈ U, s u ∈ U) → U = ⊥ ∨ U = ⊤)
    (P : Subgroup (V →ₗ[F] V)ˣ)
    (hP : ∀ u ∈ P, ∀ s ∈ 𝒮, (u : V →ₗ[F] V) ∘ₗ s = s ∘ₗ (u : V →ₗ[F] V)) :
    IsCyclic P := by
  classical
  have hVfin : Finite V := Module.finite_of_finite F
  set R : Subalgebra F (V →ₗ[F] V) := Algebra.adjoin F 𝒮 with hR
  haveI : IsSimpleModule R V := by
    rw [isSimpleModule_iff_toSpanSingleton_surjective]
    refine ⟨‹Nontrivial V›, fun x hx => ?_⟩
    set Ux : Submodule F V :=
      (LinearMap.range (LinearMap.toSpanSingleton R V x)).restrictScalars F with hUx
    have hx_mem : x ∈ Ux := ⟨1, by simp⟩
    have hinv : ∀ s ∈ 𝒮, ∀ u ∈ Ux, s u ∈ Ux := by
      rintro s hs u ⟨r, rfl⟩
      refine ⟨⟨s, Algebra.subset_adjoin hs⟩ * r, ?_⟩
      simp [LinearMap.toSpanSingleton_apply, mul_smul]
      rfl
    have hne : Ux ≠ ⊥ := fun hb => hx (by simpa [hb] using hx_mem)
    have htop : Ux = ⊤ := (hirr Ux hinv).resolve_left hne
    intro w
    have : w ∈ Ux := by rw [htop]; trivial
    exact this
  haveI : Finite (V →ₗ[F] V) :=
    Finite.of_injective (fun h : V →ₗ[F] V => (h : V → V)) DFunLike.coe_injective
  haveI : Finite (Module.End R V) :=
    Finite.of_injective (fun f : Module.End R V => (f : V → V)) DFunLike.coe_injective
  have hcentr : ∀ χ : V →ₗ[F] V, (∀ s ∈ 𝒮, χ ∘ₗ s = s ∘ₗ χ) →
      ∀ r ∈ R, χ ∘ₗ r = r ∘ₗ χ := by
    intro χ hχ
    have hle : R ≤ Subalgebra.centralizer F {χ} := by
      refine Algebra.adjoin_le fun s hs => ?_
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact hχ s hs
    intro r hr
    have hr' := hle hr
    rw [Subalgebra.mem_centralizer_iff] at hr'
    exact hr' χ (Set.mem_singleton χ)
  let toEnd : ∀ χ : V →ₗ[F] V, (∀ s ∈ 𝒮, χ ∘ₗ s = s ∘ₗ χ) → Module.End R V := fun χ hχ =>
    { toFun := χ
      map_add' := χ.map_add
      map_smul' := fun r v => by
        have := hcentr χ hχ r.1 r.2
        exact LinearMap.congr_fun this v }
  let g : P → Module.End R V := fun u => toEnd (u.1 : V →ₗ[F] V) (hP u.1 u.2)
  let f : P →* Module.End R V :=
    { toFun := g
      map_one' := by
        apply LinearMap.ext
        intro v
        rfl
      map_mul' := fun u v => by
        apply LinearMap.ext
        intro x
        rfl }
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun e : Module.End R V => (e x : V)) huv
  haveI : Finite P :=
    Finite.of_injective (fun u : P => ((u.1 : (V →ₗ[F] V)ˣ) : V →ₗ[F] V))
      (fun u v h => Subtype.ext (Units.ext h))
  letI : DivisionRing (Module.End R V) := Module.End.instDivisionRing
  letI : Field (Module.End R V) := littleWedderburn _
  exact isCyclic_of_injective_ringHom f hf

theorem isCyclic_image_of_simple_abelian [Finite F] [Module.Finite F V] [Nontrivial V]
    (ρ : Representation F G V) (B : Subgroup G)
    (hab : ∀ b ∈ B, ∀ b' ∈ B, ρ b * ρ b' = ρ b' * ρ b)
    (hsimple : ∀ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) → U = ⊥ ∨ U = ⊤) :
    IsCyclic (B.map ρ.toHomUnits) := by
  have hirr : ∀ U : Submodule F V,
      (∀ s ∈ (⇑ρ) '' (B : Set G), ∀ u ∈ U, s u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    refine hsimple U fun b hb u hu => ?_
    exact Submodule.mem_comap.mpr (hU (ρ b) ⟨b, hb, rfl⟩ u hu)
  have hP : ∀ u ∈ B.map ρ.toHomUnits, ∀ s ∈ (⇑ρ) '' (B : Set G),
      (u : V →ₗ[F] V) ∘ₗ s = s ∘ₗ (u : V →ₗ[F] V) := by
    intro u hu s hs
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨b', hb', rfl⟩ := hs
    have h := hab b hb b' hb'
    simp only [MonoidHom.coe_toHomUnits, Module.End.mul_eq_comp] at h ⊢
    exact h
  exact ndc_C_isCyclic_units_of_irred _ hirr _ hP

theorem commute_of_simple_abelian [Finite F] [Module.Finite F V] [Nontrivial V]
    (ρ : Representation F G V) (B K : Subgroup G)
    (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B) (hK : ⁅K, K⁆ = K)
    (hab : ∀ b ∈ B, ∀ b' ∈ B, ρ b * ρ b' = ρ b' * ρ b)
    (hsimple : ∀ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) → U = ⊥ ∨ U = ⊤) :
    ∀ k ∈ K, ∀ b ∈ B, ρ k * ρ b = ρ b * ρ k := by
  intro k hk b hb
  haveI : IsCyclic (B.map ρ.toHomUnits) := isCyclic_image_of_simple_abelian ρ B hab hsimple
  have hKN : K.map ρ.toHomUnits ≤
      Subgroup.normalizer ((B.map ρ.toHomUnits : Subgroup (V →ₗ[F] V)ˣ) : Set (V →ₗ[F] V)ˣ) := by
    rintro x hx
    obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hh
      have e : ρ.toHomUnits k' * ρ.toHomUnits b' * (ρ.toHomUnits k')⁻¹
          = ρ.toHomUnits (k' * b' * k'⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem ρ.toHomUnits (hKB k' hk' b' hb')
    · intro hh
      obtain ⟨b', hb', hb'eq⟩ := Subgroup.mem_map.mp hh
      refine Subgroup.mem_map.mpr ⟨k'⁻¹ * b' * k'⁻¹⁻¹, hKB k'⁻¹ (K.inv_mem hk') b' hb', ?_⟩
      simp only [map_mul, map_inv, inv_inv]
      rw [hb'eq]
      group
  have hK' : ⁅K.map ρ.toHomUnits, K.map ρ.toHomUnits⁆ = K.map ρ.toHomUnits := by
    rw [← Subgroup.map_commutator, hK]
  have hmemK : ρ.toHomUnits k ∈ ⁅K.map ρ.toHomUnits, K.map ρ.toHomUnits⁆ := by
    rw [hK']
    exact Subgroup.mem_map_of_mem ρ.toHomUnits hk
  have hcent := commutator_le_centralizer_of_isCyclic' hKN hmemK
  have key := Subgroup.mem_centralizer_iff.mp hcent (ρ.toHomUnits b)
    (Subgroup.mem_map_of_mem ρ.toHomUnits hb)
  have key' := congrArg Units.val key
  simp only [Units.val_mul, MonoidHom.coe_toHomUnits] at key'
  exact key'.symm

end Rep

end CyclicNormalizer

section WeightCount

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

private lemma weightSpace_iSupIndep_E (E : Subgroup G) (ρ : Representation F G V)
    (hab : ∀ e ∈ E, ∀ e' ∈ E, ρ e * ρ e' = ρ e' * ρ e) :
    iSupIndep fun χ : E →* Fˣ => CFSG.RepresentationTheory.weightSpace E ρ χ := by
  let f : E → Module.End F V := fun e => ρ (e : G)
  have hcomm : ∀ i j : E, Commute (f j) (f i) := fun i j => hab (j : G) j.2 (i : G) i.2
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm i j) φ)
  let g : (E →* Fˣ) → (E → F) := fun χ e => ((χ e : Fˣ) : F)
  have hg : Function.Injective g := fun χ₁ χ₂ h =>
    MonoidHom.ext fun e => Units.ext (congrFun h e)
  have hle : (fun χ : E →* Fˣ => CFSG.RepresentationTheory.weightSpace E ρ χ) ≤
      (fun μ : E → F => ⨅ i, (f i).maxGenEigenspace (μ i)) ∘ g := by
    intro χ v hv
    show v ∈ ⨅ i : E, (f i).maxGenEigenspace (g χ i)
    refine (Submodule.mem_iInf _).mpr fun i => ?_
    have hvi : v ∈ (f i).eigenspace (g χ i) :=
      Module.End.mem_eigenspace_iff.mpr ((CFSG.RepresentationTheory.mem_weightSpace.mp hv) i)
    exact Module.End.eigenspace_le_maxGenEigenspace hvi
  exact (hind.comp hg).mono hle

theorem card_weightSpaces_le [Module.Finite F V] (E : Subgroup G) (ρ : Representation F G V)
    (hab : ∀ e ∈ E, ∀ e' ∈ E, ρ e * ρ e' = ρ e' * ρ e) :
    {W : Submodule F V | W ≠ ⊥ ∧ ∃ χ : E →* Fˣ,
        W = CFSG.RepresentationTheory.weightSpace E ρ χ}.Finite ∧
      Nat.card {W : Submodule F V | W ≠ ⊥ ∧ ∃ χ : E →* Fˣ,
        W = CFSG.RepresentationTheory.weightSpace E ρ χ} ≤ Module.finrank F V := by
  have hind := weightSpace_iSupIndep_E E ρ hab
  letI : Fintype {χ : E →* Fˣ // CFSG.RepresentationTheory.weightSpace E ρ χ ≠ ⊥} :=
    hind.fintypeNeBotOfFiniteDimensional
  have hset : {W : Submodule F V | W ≠ ⊥ ∧ ∃ χ : E →* Fˣ,
        W = CFSG.RepresentationTheory.weightSpace E ρ χ} =
      Set.range (fun χ : {χ : E →* Fˣ // CFSG.RepresentationTheory.weightSpace E ρ χ ≠ ⊥} =>
        CFSG.RepresentationTheory.weightSpace E ρ χ.1) := by
    ext W
    constructor
    · rintro ⟨hW, χ, rfl⟩
      exact ⟨⟨χ, hW⟩, rfl⟩
    · rintro ⟨χ, rfl⟩
      exact ⟨χ.2, χ.1, rfl⟩
  have hinj : Function.Injective (fun χ : {χ : E →* Fˣ //
        CFSG.RepresentationTheory.weightSpace E ρ χ ≠ ⊥} =>
      CFSG.RepresentationTheory.weightSpace E ρ χ.1) := by
    intro a b hab'
    exact Subtype.ext (hind.injOn a.2 b.2 hab')
  rw [hset]
  refine ⟨Set.finite_range _, ?_⟩
  rw [Nat.card_range_of_injective hinj, Nat.card_eq_fintype_card]
  exact hind.subtype_ne_bot_le_finrank

end Rep

end WeightCount

section WeightLines

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem exists_weight_of_nonsimple [Module.Finite F V] (ρ : Representation F G V)
    (hirr : ∀ U : Submodule F V, (∀ g, U ≤ U.comap (ρ g)) → U = ⊥ ∨ U = ⊤)
    (hd2 : 2 ≤ Module.finrank F V) (hd3 : Module.finrank F V ≤ 3) (B : Subgroup G) [B.Normal]
    (hnsimple : ∃ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) ∧ U ≠ ⊥ ∧ U ≠ ⊤) :
    ∃ χ : B →* Fˣ, CFSG.RepresentationTheory.weightSpace B ρ χ ≠ ⊥ := by
  obtain ⟨U, hU, hU0, hUt⟩ := hnsimple
  have hline : ∃ L : Submodule F V, (∀ b ∈ B, L ≤ L.comap (ρ b)) ∧ Module.finrank F L = 1 := by
    have hpos : 1 ≤ Module.finrank F U := Submodule.one_le_finrank_iff.mpr hU0
    have hlt : Module.finrank F U < Module.finrank F V := Submodule.finrank_lt hUt
    rcases (show Module.finrank F U = 1 ∨ Module.finrank F U = 2 by omega) with h1 | h2
    · exact ⟨U, hU, h1⟩
    · have hG : ∃ g : G, ¬ U ≤ U.comap (ρ g) := by
        by_contra hcon
        push Not at hcon
        rcases hirr U hcon with h | h
        · exact hU0 h
        · exact hUt h
      obtain ⟨g, hg⟩ := hG
      have hinj : Function.Injective (ρ g) :=
        CFSG.RepresentationTheory.representation_injective ρ g
      have hfU' : Module.finrank F (U.map (ρ g)) = 2 := by
        rw [← h2]
        exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ρ g) hinj U)).symm
      have hUU' : U.map (ρ g) ≠ U := by
        intro h
        apply hg
        intro u hu
        rw [Submodule.mem_comap]
        have hmem : ρ g u ∈ U.map (ρ g) := Submodule.mem_map_of_mem hu
        rw [h] at hmem
        exact hmem
      have hkey : ∀ b : G, ∀ u : V, ρ b (ρ g u) = ρ g (ρ (g⁻¹ * b * g) u) := by
        intro b u
        have hgg : b * g = g * (g⁻¹ * b * g) := by group
        calc ρ b (ρ g u) = ρ (b * g) u := by rw [map_mul ρ b g, Module.End.mul_apply]
          _ = ρ (g * (g⁻¹ * b * g)) u := by rw [← hgg]
          _ = ρ g (ρ (g⁻¹ * b * g) u) := by
            rw [map_mul ρ g (g⁻¹ * b * g), Module.End.mul_apply]
      have hU'B : ∀ b ∈ B, U.map (ρ g) ≤ (U.map (ρ g)).comap (ρ b) := by
        intro b hb x hx
        obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
        have hc : ρ (g⁻¹ * b * g) u ∈ U :=
          Submodule.mem_comap.mp (hU _ (Subgroup.Normal.conj_mem' ‹B.Normal› b hb g) hu)
        rw [Submodule.mem_comap, hkey b u]
        exact Submodule.mem_map_of_mem hc
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq U (U.map (ρ g))
      have hsle : Module.finrank F ↥(U ⊔ U.map (ρ g)) ≤ Module.finrank F V :=
        Submodule.finrank_le _
      have hinfpos : 1 ≤ Module.finrank F ↥(U ⊓ U.map (ρ g)) := by omega
      have hne : U ⊓ U.map (ρ g) ≠ U := by
        intro h
        have hle : U ≤ U.map (ρ g) := inf_eq_left.mp h
        exact hUU' (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
      have hlt1 : Module.finrank F ↥(U ⊓ U.map (ρ g)) < Module.finrank F ↥U :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
      refine ⟨U ⊓ U.map (ρ g), ?_, by omega⟩
      intro b hb x hx
      rw [Submodule.mem_inf] at hx
      rw [Submodule.mem_comap, Submodule.mem_inf]
      exact ⟨Submodule.mem_comap.mp (hU b hb hx.1), Submodule.mem_comap.mp (hU'B b hb hx.2)⟩
  obtain ⟨L, hL, hL1⟩ := hline
  have hL0 : L ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨v, hvL, hv0⟩ := (Submodule.ne_bot_iff L).mp hL0
  have hspan : Submodule.span F {v} = L := by
    apply Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem v L).mpr hvL)
    rw [finrank_span_singleton hv0, hL1]
  have hscal : ∀ b : B, ∃ c : F, ρ (b : G) v = c • v := by
    intro b
    have hmem : ρ (b : G) v ∈ L := Submodule.mem_comap.mp (hL (b : G) b.2 hvL)
    rw [← hspan] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  choose c hc using hscal
  have hmul : ∀ b b' : B, c (b * b') = c b * c b' := by
    intro b b'
    have h1 : ρ ((b * b' : B) : G) v = c (b * b') • v := hc (b * b')
    have h2 : ρ ((b * b' : B) : G) v = (c b * c b') • v := by
      rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hc b', map_smul, hc b, smul_smul,
        mul_comm (c b') (c b)]
    exact smul_left_injective F hv0 (h1.symm.trans h2)
  have hone : c 1 = 1 := by
    have h1 : ρ ((1 : B) : G) v = c 1 • v := hc 1
    rw [Subgroup.coe_one, map_one, Module.End.one_apply] at h1
    have h2 : c 1 • v = (1 : F) • v := by
      rw [one_smul]
      exact h1.symm
    exact smul_left_injective F hv0 h2
  obtain ⟨χ, hχ⟩ : ∃ χ : B →* Fˣ, ∀ b : B, ((χ b : Fˣ) : F) = c b :=
    ⟨({ toFun := c, map_one' := hone, map_mul' := hmul } : B →* F).toHomUnits, fun b => rfl⟩
  refine ⟨χ, ?_⟩
  rw [Submodule.ne_bot_iff]
  refine ⟨v, ?_, hv0⟩
  rw [CFSG.RepresentationTheory.mem_weightSpace]
  intro e
  rw [hχ e]
  exact hc e

theorem weightSpace_finrank_eq_one [Module.Finite F V] (ρ : Representation F G V)
    (hirr : ∀ U : Submodule F V, (∀ g, U ≤ U.comap (ρ g)) → U = ⊥ ∨ U = ⊤)
    (hd2 : 2 ≤ Module.finrank F V) (hd3 : Module.finrank F V ≤ 3) (B : Subgroup G) [B.Normal]
    (hns : ∃ b ∈ B, ∀ c : F, ρ b ≠ c • (1 : V →ₗ[F] V)) (χ : B →* Fˣ)
    (hχ : CFSG.RepresentationTheory.weightSpace B ρ χ ≠ ⊥) :
    Module.finrank F (CFSG.RepresentationTheory.weightSpace B ρ χ) = 1 := by
  obtain ⟨W, hWdef⟩ : ∃ W, W = CFSG.RepresentationTheory.weightSpace B ρ χ := ⟨_, rfl⟩
  rw [← hWdef] at hχ ⊢
  have hWtop : W ≠ ⊤ := by
    intro htop
    obtain ⟨b, hbB, hbns⟩ := hns
    apply hbns ((χ ⟨b, hbB⟩ : Fˣ) : F)
    apply LinearMap.ext
    intro v
    have hvW : v ∈ W := by
      rw [htop]
      exact Submodule.mem_top
    rw [hWdef, CFSG.RepresentationTheory.mem_weightSpace] at hvW
    have hv := hvW ⟨b, hbB⟩
    simpa using hv
  have hfW1 : 1 ≤ Module.finrank F W := Submodule.one_le_finrank_iff.mpr hχ
  have hfWlt : Module.finrank F W < Module.finrank F V := Submodule.finrank_lt hWtop
  have hne2 : Module.finrank F W ≠ 2 := by
    intro h2
    have hG : ∃ g : G, ¬ W ≤ W.comap (ρ g) := by
      by_contra hcon
      push Not at hcon
      rcases hirr W hcon with h | h
      · exact hχ h
      · exact hWtop h
    obtain ⟨g, hg⟩ := hG
    have hinj : Function.Injective (ρ g) :=
      CFSG.RepresentationTheory.representation_injective ρ g
    have hfW' : Module.finrank F (W.map (ρ g)) = 2 := by
      rw [← h2]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (ρ g) hinj W)).symm
    have hW'le : W.map (ρ g) ≤
        CFSG.RepresentationTheory.weightSpace B ρ (CFSG.RepresentationTheory.charConj B χ g) := by
      rintro x ⟨w, hw, rfl⟩
      rw [hWdef] at hw
      exact CFSG.RepresentationTheory.apply_mem_weightSpace_charConj B ρ χ g hw
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (W.map (ρ g))
    have hsle : Module.finrank F ↥(W ⊔ W.map (ρ g)) ≤ Module.finrank F V :=
      Submodule.finrank_le _
    have hinfpos : 1 ≤ Module.finrank F ↥(W ⊓ W.map (ρ g)) := by omega
    have hinfne : W ⊓ W.map (ρ g) ≠ ⊥ := Submodule.one_le_finrank_iff.mp hinfpos
    obtain ⟨v, hvinf, hv0⟩ := (Submodule.ne_bot_iff _).mp hinfne
    have hvW : v ∈ W := (Submodule.mem_inf.mp hvinf).1
    have hvW' : v ∈ W.map (ρ g) := (Submodule.mem_inf.mp hvinf).2
    have hvWg : v ∈ CFSG.RepresentationTheory.weightSpace B ρ
        (CFSG.RepresentationTheory.charConj B χ g) := hW'le hvW'
    have hvWχ : v ∈ CFSG.RepresentationTheory.weightSpace B ρ χ := by
      rw [← hWdef]
      exact hvW
    have hcc : CFSG.RepresentationTheory.charConj B χ g = χ := by
      apply MonoidHom.ext
      intro e
      have h1 := CFSG.RepresentationTheory.mem_weightSpace.mp hvWχ e
      have h2' := CFSG.RepresentationTheory.mem_weightSpace.mp hvWg e
      have h3 : ((χ e : Fˣ) : F) • v = ((CFSG.RepresentationTheory.charConj B χ g e : Fˣ) : F) • v :=
        h1.symm.trans h2'
      exact Units.ext (smul_left_injective F hv0 h3).symm
    have hw : ∃ w ∈ W, ρ g w ∉ W := by
      by_contra hcon
      push Not at hcon
      apply hg
      intro x hx
      exact Submodule.mem_comap.mpr (hcon x hx)
    obtain ⟨w, hwW, hgw⟩ := hw
    apply hgw
    have hwWχ : w ∈ CFSG.RepresentationTheory.weightSpace B ρ χ := by
      rw [← hWdef]
      exact hwW
    have hgmem := CFSG.RepresentationTheory.apply_mem_weightSpace_charConj B ρ χ g hwWχ
    rw [hcc, ← hWdef] at hgmem
    exact hgmem
  omega

end Rep

end WeightLines

section EigenCase

open Representation
open scoped commutatorElement

section Rep

variable {F : Type*} [Field F] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]

theorem map_weightSpace_eq (ρ : Representation F G V) (B : Subgroup G) [B.Normal]
    (χ : B →* Fˣ) (g : G) :
    (CFSG.RepresentationTheory.weightSpace B ρ χ).map (ρ g) =
      CFSG.RepresentationTheory.weightSpace B ρ (CFSG.RepresentationTheory.charConj B χ g) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact CFSG.RepresentationTheory.apply_mem_weightSpace_charConj B ρ χ g hv
  · intro w hw
    have h1 : CFSG.RepresentationTheory.charConj B
        (CFSG.RepresentationTheory.charConj B χ g) g⁻¹ = χ := by
      rw [← CFSG.RepresentationTheory.charConj_mul, inv_mul_cancel,
        CFSG.RepresentationTheory.charConj_one]
    have hv := CFSG.RepresentationTheory.apply_mem_weightSpace_charConj B ρ
      (CFSG.RepresentationTheory.charConj B χ g) g⁻¹ hw
    rw [h1] at hv
    exact Submodule.mem_map.mpr ⟨ρ g⁻¹ w, hv, Representation.self_inv_apply ρ g w⟩

private lemma ndcB2_map_ne_bot (ρ : Representation F G V) (g : G) {W : Submodule F V}
    (hW : W ≠ ⊥) : W.map (ρ g) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hW ⊢
  obtain ⟨v, hv, hv0⟩ := hW
  refine ⟨ρ g v, Submodule.mem_map_of_mem hv, fun h => hv0 ?_⟩
  rw [← Representation.inv_self_apply ρ g v, h, map_zero]

private lemma ndcB2_map_mem_family (ρ : Representation F G V) (B : Subgroup G) [B.Normal]
    (g : G) {W : Submodule F V}
    (hW : W ≠ ⊥ ∧ ∃ χ : B →* Fˣ, W = CFSG.RepresentationTheory.weightSpace B ρ χ) :
    W.map (ρ g) ≠ ⊥ ∧ ∃ χ : B →* Fˣ,
      W.map (ρ g) = CFSG.RepresentationTheory.weightSpace B ρ χ := by
  obtain ⟨hne, χ, rfl⟩ := hW
  exact ⟨ndcB2_map_ne_bot ρ g hne, CFSG.RepresentationTheory.charConj B χ g,
    map_weightSpace_eq ρ B χ g⟩

theorem sSup_weightSpaces_eq_top (ρ : Representation F G V)
    (hirr : ∀ U : Submodule F V, (∀ g, U ≤ U.comap (ρ g)) → U = ⊥ ∨ U = ⊤)
    (B : Subgroup G) [B.Normal]
    (hex : ∃ χ : B →* Fˣ, CFSG.RepresentationTheory.weightSpace B ρ χ ≠ ⊥) :
    sSup {W : Submodule F V | W ≠ ⊥ ∧ ∃ χ : B →* Fˣ,
      W = CFSG.RepresentationTheory.weightSpace B ρ χ} = ⊤ := by
  set 𝒱 : Set (Submodule F V) := {W : Submodule F V | W ≠ ⊥ ∧ ∃ χ : B →* Fˣ,
    W = CFSG.RepresentationTheory.weightSpace B ρ χ} with h𝒱
  obtain ⟨χ0, hχ0⟩ := hex
  have hmem0 : CFSG.RepresentationTheory.weightSpace B ρ χ0 ∈ 𝒱 := ⟨hχ0, χ0, rfl⟩
  have hS : sSup 𝒱 ≠ ⊥ := by
    intro h
    have h1 := le_sSup hmem0
    rw [h, le_bot_iff] at h1
    exact hχ0 h1
  have hinv : ∀ g : G, sSup 𝒱 ≤ (sSup 𝒱).comap (ρ g) := by
    intro g
    apply sSup_le
    intro W hW
    rw [← Submodule.map_le_iff_le_comap]
    apply le_sSup
    exact ndcB2_map_mem_family ρ B g hW
  rcases hirr (sSup 𝒱) hinv with h | h
  · exact absurd h hS
  · exact h

theorem eigen_case [Module.Finite F V] (ρ : Representation F G V)
    (hirr : ∀ U : Submodule F V, (∀ g, U ≤ U.comap (ρ g)) → U = ⊥ ∨ U = ⊤)
    (hd2 : 2 ≤ Module.finrank F V) (hd3 : Module.finrank F V ≤ 3) (B K : Subgroup G) [B.Normal]
    (hab : ∀ b ∈ B, ∀ b' ∈ B, ρ b * ρ b' = ρ b' * ρ b)
    (hns : ∃ b ∈ B, ∀ c : F, ρ b ≠ c • (1 : V →ₗ[F] V))
    (hK : ⁅K, K⁆ = K)
    (hnsimple : ∃ U : Submodule F V, (∀ b ∈ B, U ≤ U.comap (ρ b)) ∧ U ≠ ⊥ ∧ U ≠ ⊤) :
    ∀ k ∈ K, ρ k = 1 := by
  have hex : ∃ χ : B →* Fˣ, CFSG.RepresentationTheory.weightSpace B ρ χ ≠ ⊥ :=
    exists_weight_of_nonsimple ρ hirr hd2 hd3 B hnsimple
  obtain ⟨hfin, hcard0⟩ := card_weightSpaces_le B ρ hab
  have hcard : Nat.card {W : Submodule F V | W ≠ ⊥ ∧ ∃ χ : B →* Fˣ,
      W = CFSG.RepresentationTheory.weightSpace B ρ χ} ≤ 4 :=
    le_trans hcard0 (le_trans hd3 (by norm_num))
  refine trivial_of_line_family ρ hK _ hfin hcard ?_ ?_ ?_
  · intro g W hW
    exact ndcB2_map_mem_family ρ B g hW
  · intro W hW
    obtain ⟨hne, χ, rfl⟩ := hW
    exact weightSpace_finrank_eq_one ρ hirr hd2 hd3 B hns χ hne
  · exact sSup_weightSpaces_eq_top ρ hirr B hex

end Rep

end EigenCase

end CFSG.RankThree.PartTwo.KFacts.NDC

end
