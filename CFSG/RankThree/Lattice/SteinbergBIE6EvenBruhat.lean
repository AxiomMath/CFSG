module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBridge
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.RankThree.Lattice.SteinbergBIGenBruhat

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups
open scoped Pointwise

theorem parabolicRoots_inter_inversionSet_eq {τ : Tag} {J : Set (Fin τ.rank)} {v : WeylGroup τ}
    (hv : v ∈ parabolicWeylGroup τ J) :
    parabolicRoots τ J ∩ inversionSet v =
      {α | α ∈ parabolicPosRoots τ J ∧ -(v • α) ∈ parabolicPosRoots τ J} := by
  ext α
  constructor
  · rintro ⟨hαJ, hαr, hαpos, hvr, hvneg⟩
    have hvJ := smul_mem_parabolicRoots hv hαJ
    refine ⟨⟨hαJ, hαr, hαpos⟩, ⟨⟨IsRoot.neg hvr, fun i hi => ?_⟩, IsRoot.neg hvr, ?_⟩⟩
    · rw [Pi.neg_apply, hvJ.2 i hi, neg_zero]
    · rw [height_neg]
      omega
  · rintro ⟨⟨hαJ, hαr, hαpos⟩, ⟨-, hvr, hvpos⟩⟩
    refine ⟨hαJ, hαr, hαpos, ?_, ?_⟩
    · simpa using IsRoot.neg hvr
    · rw [height_neg] at hvpos
      omega

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

theorem orbitMap_mul {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (A B : SL2 (D.orbitField O)) : D.orbitMap O (A * B) = D.orbitMap O A * D.orbitMap O B := by
  obtain ⟨σ, -, h⟩ := D.exists_orbitMap_eq_gen hO
  rw [h, h, h, map_mul]
  exact D.gen.orbitMap_mul (D.mem_gen_orbits.2 hO) _ _

theorem neg_eq_self_orbitField (O : Set (Fin Tag.E6.rank → ℤ)) (c : D.orbitField O) : -c = c :=
  Subtype.ext (by rw [Subfield.coe_neg]; exact CharTwo.neg_eq _)

theorem neg_one_eq_one_SL2 (O : Set (Fin Tag.E6.rank → ℤ)) : (-1 : SL2 (D.orbitField O)) = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, Matrix.neg_apply]
  exact D.neg_eq_self_orbitField O _

theorem orbitMap_injective {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    Function.Injective (D.orbitMap O) := by
  obtain ⟨σ, hσ, h⟩ := D.exists_orbitMap_eq_gen hO
  have hO' := D.mem_gen_orbits.2 hO
  have hmap : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) σ) :=
    fun X Y hXY => Subtype.ext (Matrix.ext fun a b => hσ.1 (congrFun (congrFun
      (congrArg Subtype.val hXY) a) b))
  intro A B hAB
  rw [h, h] at hAB
  have h1 := D.gen.orbitMap_eq_one_of_eq hO' (B := Matrix.SpecialLinearGroup.map σ A *
    (Matrix.SpecialLinearGroup.map σ B)⁻¹) (inv_mul_cancel_right _ _).symm hAB
  have h2 : Matrix.SpecialLinearGroup.map σ A * (Matrix.SpecialLinearGroup.map σ B)⁻¹ = 1 := by
    rcases D.gen.eq_one_or_neg_one_of_orbitMap_eq_one hO' h1 with e | e
    · exact e
    · exact e.trans (D.neg_one_eq_one_SL2 O)
  exact hmap (mul_inv_eq_one.1 h2)

theorem orbitMap_mem_fixedGroup {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitMap O A ∈ D.fixedGroup := by
  obtain ⟨σ, -, h⟩ := D.exists_orbitMap_eq_gen hO
  rw [h, ← D.gen_fixedGroup]
  exact ⟨_, D.gen.orbitMap_mem_fixedGroup (D.mem_gen_orbits.2 hO) _, rfl⟩

theorem orbitMap_mem_orbitGroup {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitMap O A ∈ D.orbitGroup := by
  obtain ⟨σ, -, h⟩ := D.exists_orbitMap_eq_gen hO
  rw [h, ← D.gen_orbitGroup]
  exact D.gen.orbitMap_mem_orbitGroup (D.mem_gen_orbits.2 hO) _

theorem range_orbitX {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.range (D.orbitX O) = D.fixedRootGroup O := by
  obtain ⟨σ, hσ, -, hX, -, -⟩ := D.exists_orbitX_eq_gen hO
  rw [← D.coe_gen_fixedRootSpan, ← D.gen.range_orbitX (D.mem_gen_orbits.2 hO)]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨σ c, (hX c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨c', rfl⟩ := hσ.2 c
    exact ⟨c', hX c'⟩

theorem range_orbitY {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits) :
    Set.range (D.orbitY O) = D.fixedRootGroup ((fun γ => -γ) '' O) := by
  obtain ⟨σ, hσ, -, -, hY, -⟩ := D.exists_orbitX_eq_gen hO
  rw [← D.coe_gen_fixedRootSpan, ← D.gen.range_orbitY (D.mem_gen_orbits.2 hO)]
  ext g
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨σ c, (hY c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨c', rfl⟩ := hσ.2 c
    exact ⟨c', hY c'⟩

theorem exists_conj_fixedRootGroup_rootOrbit {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) :
    ∃ O ∈ D.orbits, ∃ g ∈ D.orbitGroup,
      (D.fixedRootGroup (D.rootOrbit α) : Set (ModGL Tag.E6 Ω)) =
        (fun x => g * x * g⁻¹) '' Set.range (D.orbitX O) := by
  have hαG : α ∈ D.gen.roots := by
    rw [D.gen_roots]
    exact hα
  obtain ⟨w, hw, O, hO, hwO⟩ := D.gen.exists_fixedWeyl_image_eq hαG
  obtain ⟨n, hn⟩ := D.gen.exists_isOrbitLift hw
  obtain ⟨hnC, ⟨hnN, hnw⟩, x, rfl, hxF⟩ := D.gen.isOrbitLift_spec hn
  have hmap := D.gen.map_conj_fixedRootSpan hnN hnw hxF (S := O)
    (fun γ hγ => D.gen.isRoot_of_mem_orbits hO hγ)
  rw [hwO] at hmap
  have hO' := D.mem_gen_orbits.1 hO
  refine ⟨O, hO', x, by rw [← D.gen_orbitGroup]; exact hnC, ?_⟩
  rw [D.rootOrbit_eq_thetaOrbit, ← D.coe_gen_fixedRootSpan, ← hmap, D.range_orbitX hO',
    ← D.coe_gen_fixedRootSpan, Subgroup.coe_map, Set.image_image, Set.image_image]
  rfl

theorem finite_fixedGroup : Finite D.fixedGroup := by
  have := D.gen.finite_fixedGroup
  rw [← D.gen_fixedGroup]
  exact Finite.of_equiv _ (D.gen.fixedGroup.equivMapOfInjective _
    (adjointGroup Tag.E6 Ω).subtype_injective).toEquiv

theorem orbitGroup_le_fixedGroup : D.orbitGroup ≤ D.fixedGroup := by
  rw [← D.gen_orbitGroup, ← D.gen_fixedGroup]
  intro g hg
  exact ⟨⟨g, D.gen.orbitGroup_le_adjointGroup hg⟩,
    D.gen.orbitGroupC_le_fixedGroup (D.gen.mk_mem_orbitGroupC hg), rfl⟩

theorem exists_mem_gen_fixedGroup {g : ModGL Tag.E6 Ω} (hg : g ∈ D.fixedGroup) :
    ∃ x : adjointGroup Tag.E6 Ω, x ∈ D.gen.fixedGroup ∧ (x : ModGL Tag.E6 Ω) = g := by
  rw [← D.gen_fixedGroup] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact ⟨x, hx, rfl⟩

theorem orbitGroup_normal : (D.orbitGroup.subgroupOf D.fixedGroup).Normal := by
  have hN := D.gen.orbitGroupC_normal
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨x, hx, hxg⟩ := D.exists_mem_gen_fixedGroup g.2
  obtain ⟨y, hy, hyn⟩ := D.exists_mem_gen_fixedGroup n.2
  have hyC : (⟨y, hy⟩ : D.gen.fixedGroup) ∈ D.gen.orbitGroupC.subgroupOf D.gen.fixedGroup := by
    rw [Subgroup.mem_subgroupOf, GenFixedRootDatum.orbitGroupC, Subgroup.mem_subgroupOf,
      D.gen_orbitGroup]
    change (y : ModGL Tag.E6 Ω) ∈ D.orbitGroup
    rw [hyn]
    exact hn
  have h := hN.conj_mem _ hyC ⟨x, hx⟩
  rw [Subgroup.mem_subgroupOf, GenFixedRootDatum.orbitGroupC, Subgroup.mem_subgroupOf,
    D.gen_orbitGroup] at h
  have e : ((g * n * g⁻¹ : D.fixedGroup) : ModGL Tag.E6 Ω) =
      (((⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ : D.gen.fixedGroup) : adjointGroup Tag.E6 Ω) :
        ModGL Tag.E6 Ω) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxg, hyn]
  rw [e]
  exact h

theorem coe_fixedGroup_eq_mul :
    (D.fixedGroup : Set (ModGL Tag.E6 Ω)) =
      (D.fixedTorus : Set (ModGL Tag.E6 Ω)) * (D.orbitGroup : Set (ModGL Tag.E6 Ω)) := by
  have h := congrArg (fun s => (adjointGroup Tag.E6 Ω).subtype '' s) D.gen.coe_fixedGroup_eq_mul
  simp only [Set.image_mul] at h
  rw [← D.gen_fixedGroup, ← D.gen_fixedTorus, Subgroup.coe_map, Subgroup.coe_map, h]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← D.gen_orbitGroup]
    exact Subgroup.mem_subgroupOf.1 hx
  · intro hg
    rw [SetLike.mem_coe, ← D.gen_orbitGroup] at hg
    exact ⟨⟨g, D.gen.orbitGroup_le_adjointGroup hg⟩, D.gen.mk_mem_orbitGroupC hg, rfl⟩

theorem commutator_fixedGroup_le : ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroup := by
  rw [← D.gen_fixedGroup, ← Subgroup.map_commutator]
  refine (Subgroup.map_mono D.gen.commutator_fixedGroup_le).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← D.gen_orbitGroup]
  exact Subgroup.mem_subgroupOf.1 hx

theorem fixedUnipotent_le_orbitGroup : D.fixedUnipotent ≤ D.orbitGroup := by
  rw [← D.gen_fixedUnipotentM, ← D.gen_orbitGroup]
  rintro _ ⟨u, hu, rfl⟩
  exact Subgroup.mem_subgroupOf.1 (D.gen.fixedUnipotent_le_orbitGroupC hu)

theorem isNilpotent_fixedUnipotent : Group.IsNilpotent D.fixedUnipotent := by
  rw [← D.gen_fixedUnipotentM]
  exact D.gen.isNilpotent_fixedUnipotentM

theorem eq_and_eq_of_orbitBorel {t t' u u' : ModGL Tag.E6 Ω} (ht : t ∈ D.orbitTorus)
    (ht' : t' ∈ D.orbitTorus) (hu : u ∈ D.fixedUnipotent) (hu' : u' ∈ D.fixedUnipotent)
    (h : t * u = t' * u') : t = t' ∧ u = u' := by
  rw [← D.gen_orbitTorus] at ht ht'
  rw [← D.gen_fixedUnipotentM] at hu hu'
  exact D.gen.eq_and_eq_of_orbitBorel ht ht' hu hu' h

theorem orbitBorel_inter_orbitNegBorel : D.orbitBorel ∩ D.orbitNegBorel = D.orbitTorus := by
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element Tag.E6
  have hBB := (opposite_Borel_intersection Tag.E6 Ω w₀ hw₀).2.2.1
  ext g
  constructor
  · rintro ⟨⟨t, ht, u, hu, rfl⟩, ⟨t', ht', u', hu', e⟩⟩
    have hu₁ : u ∈ posUnipotent Tag.E6 Ω := rootSpan_le_posUnipotent
      (fun α hα => ⟨D.isRoot_of_mem_Ξ hα.1, hα.2⟩) hu.1
    have hu₂ : u' ∈ negUnipotent Tag.E6 Ω := rootSpan_le_negUnipotent (fun α hα => by
      have hα' : -α ∈ D.Ξ := hα.1
      have hαΞ : α ∈ D.Ξ := by simpa using D.neg_mem_Ξ hα'
      refine ⟨D.isRoot_of_mem_Ξ hαΞ, ?_⟩
      have h2 := hα.2
      rw [Set.mem_ofPred_eq, height_neg] at h2
      omega) hu'.1
    have h1 : t * u ∈ borelGroup Tag.E6 Ω :=
      mul_mem (Subgroup.mem_sup_left ht.2.2) (Subgroup.mem_sup_right hu₁)
    have h2 : t * u ∈ torusGroup Tag.E6 Ω ⊔ negUnipotent Tag.E6 Ω := by
      rw [e]
      exact mul_mem (Subgroup.mem_sup_left ht'.2.2) (Subgroup.mem_sup_right hu₂)
    have hH : t * u ∈ torusGroup Tag.E6 Ω := by
      rw [← hBB]
      exact ⟨h1, h2⟩
    have hP : t * u ∈ D.orbitGroup := mul_mem ht.1 (D.fixedUnipotent_le_orbitGroup hu)
    exact ⟨hP, D.orbitGroup_le_rootGroup hP, hH⟩
  · intro hg
    exact ⟨⟨g, hg, 1, one_mem _, (mul_one g).symm⟩, ⟨g, hg, 1, one_mem _, (mul_one g).symm⟩⟩

theorem exists_isOrbitLift {w : WeylGroup Tag.E6} (hw : w ∈ D.relWeyl) :
    ∃ n, D.IsOrbitLift n w := by
  rw [← D.gen_fixedWeyl] at hw
  obtain ⟨n, hn⟩ := D.gen.exists_isOrbitLift hw
  exact ⟨n, D.isOrbitLift_iff.2 hn⟩

theorem isOrbitLift_spec {n : ModGL Tag.E6 Ω} {w : WeylGroup Tag.E6} (h : D.IsOrbitLift n w) :
    n ∈ D.orbitGroup ∧ D.psi n = n ∧
      ∃ hn : n ∈ monomialSubgroup Tag.E6 Ω, weylQuotientHom Tag.E6 Ω ⟨n, hn⟩ = w := by
  obtain ⟨h1, h2, x, rfl, hxF⟩ := D.gen.isOrbitLift_spec (D.isOrbitLift_iff.1 h)
  exact ⟨D.gen_orbitGroup ▸ h1, congrArg Subtype.val hxF, h2⟩

end E6EvenFixedRootDatum

theorem E6_even_supported_fixed_root_Bruhat_and_full_torus_kernel :
    (∀ (K : Type) [Field K] [CharP K 2] (J : Set (Fin Tag.E6.rank)),
      subsystemGroup Tag.E6 K J = rootSpan Tag.E6 K (parabolicRoots Tag.E6 J) ∧
      subsystemGroup Tag.E6 K J ⊓ torusGroup Tag.E6 K = supportedTorus Tag.E6 K J ∧
      supportedTorus Tag.E6 K J = subsystemTorus Tag.E6 K J ∧
      (∀ v ∈ parabolicWeylGroup Tag.E6 J, parabolicRoots Tag.E6 J ∩ inversionSet v =
        {α | α ∈ parabolicPosRoots Tag.E6 J ∧ -(v • α) ∈ parabolicPosRoots Tag.E6 J}) ∧
      (subsystemGroup Tag.E6 K J : Set (ModGL Tag.E6 K)) =
        ⋃ v ∈ parabolicWeylGroup Tag.E6 J, supportedCell Tag.E6 K J v ∧
      (∀ v v' : WeylGroup Tag.E6, v ≠ v' →
        Disjoint (supportedCell Tag.E6 K J v) (supportedCell Tag.E6 K J v')) ∧
      (∀ v : WeylGroup Tag.E6,
        Set.BijOn (fun p : ModGL Tag.E6 K × ModGL Tag.E6 K × ModGL Tag.E6 K =>
            p.1 * p.2.1 * canonicalRep (coxeterSystem Tag.E6) K v * p.2.2)
          ((supportedTorus Tag.E6 K J : Set (ModGL Tag.E6 K)) ×ˢ
            (parabolicLeviUnipotent Tag.E6 K J : Set (ModGL Tag.E6 K)) ×ˢ
              (rootSpan Tag.E6 K (parabolicRoots Tag.E6 J ∩ inversionSet v) :
                Set (ModGL Tag.E6 K)))
          (supportedCell Tag.E6 K J v)) ∧
      (∀ g ∈ subsystemGroup Tag.E6 K J,
        ∃! p : WeylGroup Tag.E6 × ModGL Tag.E6 K × ModGL Tag.E6 K × ModGL Tag.E6 K,
          p.1 ∈ parabolicWeylGroup Tag.E6 J ∧ p.2.1 ∈ supportedTorus Tag.E6 K J ∧
          p.2.2.1 ∈ parabolicLeviUnipotent Tag.E6 K J ∧
          p.2.2.2 ∈ rootSpan Tag.E6 K (parabolicRoots Tag.E6 J ∩ inversionSet p.1) ∧
          p.2.1 * p.2.2.1 * canonicalRep (coxeterSystem Tag.E6) K p.1 * p.2.2.2 = g) ∧
      (∀ {m : ℕ} (α : Fin m → Fin Tag.E6.rank → ℤ), Function.Injective α →
        Set.range α = parabolicPosRoots Tag.E6 J →
        Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX Tag.E6 K (α k) (c k)).prod)
          Set.univ (parabolicLeviUnipotent Tag.E6 K J)) ∧
      (∀ (v : WeylGroup Tag.E6) {m : ℕ} (α : Fin m → Fin Tag.E6.rank → ℤ),
        Function.Injective α → Set.range α = parabolicRoots Tag.E6 J ∩ inversionSet v →
        Set.BijOn (fun c : Fin m → K => (List.ofFn fun k => pinnedX Tag.E6 K (α k) (c k)).prod)
          Set.univ (rootSpan Tag.E6 K (parabolicRoots Tag.E6 J ∩ inversionSet v))) ∧
      (∀ [Fintype J] (a : J → Kˣ), a ∈ (supportedTorusHom Tag.E6 K J).ker ↔
        ∀ i : Fin Tag.E6.rank, ∏ j : J, a j ^ Tag.E6.cartan j i = 1) ∧
      (∀ h ∈ torusGroup Tag.E6 K, ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
        (h : Module.End K (RootModule Tag.E6 K)) (rootVec Tag.E6 K α) =
          torusRootChar h α • rootVec Tag.E6 K α ∧
        (∀ c : K, h * pinnedX Tag.E6 K α c * h⁻¹ =
          pinnedX Tag.E6 K α (torusRootChar h α * c)) ∧
        ∀ s : K, (∀ c : K, h * pinnedX Tag.E6 K α c * h⁻¹ = pinnedX Tag.E6 K α (s * c)) →
          s = torusRootChar h α) ∧
      ∀ g : subsystemGroup Tag.E6 K J, g ∈ Subgroup.center (subsystemGroup Tag.E6 K J) ↔
        (g : ModGL Tag.E6 K) ∈ supportedTorus Tag.E6 K J ∧
          ∀ α ∈ parabolicRoots Tag.E6 J, torusRootChar (g : ModGL Tag.E6 K) α = 1) ∧
    ∀ (Ω : Type) [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω),
      (∀ O ∈ D.orbits, (∀ A B, D.orbitMap O (A * B) = D.orbitMap O A * D.orbitMap O B) ∧
        Function.Injective (D.orbitMap O) ∧ (∀ A, D.orbitMap O A ∈ D.fixedGroup) ∧
        (∀ A, D.orbitMap O A ∈ D.orbitGroup) ∧ D.orbitN O ∈ D.orbitGroup ∧
        Set.range (D.orbitX O) = D.fixedRootGroup O ∧
        Set.range (D.orbitY O) = D.fixedRootGroup ((fun γ => -γ) '' O)) ∧
      (∀ α ∈ D.Ξ, ∃ O ∈ D.orbits, ∃ g ∈ D.orbitGroup,
        (D.fixedRootGroup (D.rootOrbit α) : Set (ModGL Tag.E6 Ω)) =
          (fun x => g * x * g⁻¹) '' Set.range (D.orbitX O)) ∧
      Finite D.fixedGroup ∧ D.orbitGroup ≤ D.fixedGroup ∧
      (D.orbitGroup.subgroupOf D.fixedGroup).Normal ∧
      (D.fixedGroup : Set (ModGL Tag.E6 Ω)) =
        (D.fixedTorus : Set (ModGL Tag.E6 Ω)) * (D.orbitGroup : Set (ModGL Tag.E6 Ω)) ∧
      ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroup ∧
      D.fixedUnipotent ≤ D.orbitGroup ∧ Group.IsNilpotent D.fixedUnipotent ∧
      (∃ B : Subgroup (ModGL Tag.E6 Ω), (B : Set (ModGL Tag.E6 Ω)) = D.orbitBorel) ∧
      (∀ t ∈ D.orbitTorus, ∀ t' ∈ D.orbitTorus, ∀ u ∈ D.fixedUnipotent,
        ∀ u' ∈ D.fixedUnipotent, t * u = t' * u' → t = t' ∧ u = u') ∧
      (∀ w ∈ D.relWeyl, ∃ n, D.IsOrbitLift n w) ∧
      (∀ n w, D.IsOrbitLift n w → n ∈ D.orbitGroup ∧ D.psi n = n ∧
        ∃ hn : n ∈ monomialSubgroup Tag.E6 Ω, weylQuotientHom Tag.E6 Ω ⟨n, hn⟩ = w) ∧
      (∀ nw : WeylGroup Tag.E6 → ModGL Tag.E6 Ω, (∀ w ∈ D.relWeyl, D.IsOrbitLift (nw w) w) →
        (∀ w ∈ D.relWeyl, Set.BijOn (fun p : ModGL Tag.E6 Ω × ModGL Tag.E6 Ω => p.1 * nw w * p.2)
          (D.orbitBorel ×ˢ (D.fixedRootGroup (D.inversionRoots w) : Set (ModGL Tag.E6 Ω)))
          (D.cell (nw w))) ∧
        (D.orbitGroup : Set (ModGL Tag.E6 Ω)) = ⋃ w ∈ D.relWeyl, D.cell (nw w) ∧
        (∀ w ∈ D.relWeyl, ∀ w' ∈ D.relWeyl, w ≠ w' → Disjoint (D.cell (nw w)) (D.cell (nw w'))) ∧
        ∀ O ∈ D.orbits, ∀ w ∈ D.relWeyl,
          (D.relLength (E6EvenFixedRootDatum.orbitReflection O * w) = D.relLength w + 1 →
            D.cell (nw (E6EvenFixedRootDatum.orbitReflection O)) * D.cell (nw w) =
              D.cell (nw (E6EvenFixedRootDatum.orbitReflection O * w))) ∧
          (D.relLength (E6EvenFixedRootDatum.orbitReflection O * w) ≠ D.relLength w + 1 →
            D.cell (nw (E6EvenFixedRootDatum.orbitReflection O)) * D.cell (nw w) =
              D.cell (nw (E6EvenFixedRootDatum.orbitReflection O * w)) ∪ D.cell (nw w))) ∧
      D.orbitBorel ∩ D.orbitNegBorel = D.orbitTorus := by
  refine ⟨fun K _ _ J => ?_, fun Ω _ _ _ D => ?_⟩
  · obtain ⟨h1, h2, h3, -, h5⟩ := supported_Bruhat_and_exact_native_torus_kernel Tag.E6 K J
    exact ⟨h1, h2, h3, fun v hv => parabolicRoots_inter_inversionSet_eq hv, h5⟩
  refine ⟨fun O hO => ⟨D.orbitMap_mul hO, D.orbitMap_injective hO, D.orbitMap_mem_fixedGroup hO,
      D.orbitMap_mem_orbitGroup hO, D.orbitMap_mem_orbitGroup hO _, D.range_orbitX hO,
      D.range_orbitY hO⟩,
    fun α hα => D.exists_conj_fixedRootGroup_rootOrbit hα, D.finite_fixedGroup,
    D.orbitGroup_le_fixedGroup, D.orbitGroup_normal, D.coe_fixedGroup_eq_mul,
    D.commutator_fixedGroup_le, D.fixedUnipotent_le_orbitGroup, D.isNilpotent_fixedUnipotent,
    ⟨D.gen.orbitBorel, D.gen_orbitBorel⟩,
    fun t ht t' ht' u hu u' hu' h => D.eq_and_eq_of_orbitBorel ht ht' hu hu' h,
    fun w hw => D.exists_isOrbitLift hw, fun n w h => D.isOrbitLift_spec h, fun nw hnw => ?_,
    D.orbitBorel_inter_orbitNegBorel⟩
  have hnwG : ∀ w ∈ D.gen.fixedWeyl, D.gen.IsOrbitLift (nw w) w := fun w hw =>
    D.isOrbitLift_iff.1 (hnw w (D.gen_fixedWeyl ▸ hw))
  have hlift : ∀ w ∈ D.gen.fixedWeyl, ∃ x : adjointGroup Tag.E6 Ω,
      (x : ModGL Tag.E6 Ω) = nw w ∧ D.gen.F x = x :=
    fun w hw => (D.gen.isOrbitLift_spec (hnwG w hw)).2.2
  choose! x hx hxF using hlift
  have hnw' : ∀ w ∈ D.gen.fixedWeyl, D.gen.IsOrbitLift (x w : ModGL Tag.E6 Ω) w ∧
      D.gen.F (x w) = x w := fun w hw => ⟨(hx w hw).symm ▸ hnwG w hw, hxF w hw⟩
  refine ⟨fun w hw => ?_, ?_, fun w hw w' hw' hne => ?_, fun O hO w hw => ?_⟩
  · have hwG : w ∈ D.gen.fixedWeyl := D.gen_fixedWeyl ▸ hw
    have h := D.gen.bijOn_mul_fixedCell hwG (hnw' w hwG).1 (hxF w hwG)
    rw [D.gen_orbitBorel, D.gen_inversionRootsJ, D.coe_gen_fixedRootSpan, D.gen_fixedCell,
      hx w hwG] at h
    exact h
  · have h := D.gen.coe_orbitGroup_eq_iUnion (nw := x) hnw'
    rw [D.gen_orbitGroup, D.gen_fixedWeyl] at h
    rw [h]
    refine Set.iUnion₂_congr fun w hw => ?_
    rw [D.gen_fixedCell, hx w (D.gen_fixedWeyl ▸ hw)]
  · have hwG : w ∈ D.gen.fixedWeyl := D.gen_fixedWeyl ▸ hw
    have hw'G : w' ∈ D.gen.fixedWeyl := D.gen_fixedWeyl ▸ hw'
    rw [← D.gen_fixedCell, ← D.gen_fixedCell, ← hx w hwG, ← hx w' hw'G]
    exact D.gen.disjoint_fixedCell (fun w hw => (hnw' w hw).1) hwG hw'G hne
  · have hO' := D.mem_gen_orbits.2 hO
    have hwG : w ∈ D.gen.fixedWeyl := D.gen_fixedWeyl ▸ hw
    have hrO := D.gen.setReflection_mem_fixedWeyl hO'
    have hrOw := mul_mem hrO hwG
    have e₁ : D.gen.fixedCell (nw (setReflection O)) = D.gen.fixedCell (D.gen.orbitN O) :=
      D.gen.fixedCell_eq_of_isOrbitLift (hnwG _ hrO) (D.gen.isOrbitLift_orbitN hO')
    have e₂ : D.gen.fixedCell (nw (setReflection O * w)) =
        D.gen.fixedCell (D.gen.orbitN O * nw w) :=
      D.gen.fixedCell_eq_of_isOrbitLift (hnwG _ hrOw) (D.gen.isOrbitLift_orbitN_mul hO'
        (hnwG w hwG))
    have h := D.gen.fixedCell_orbitN_mul_fixedCell hO' hwG (hnwG w hwG)
    rw [← e₁, ← e₂, D.gen_foldedLength, D.gen_foldedLength, D.gen_fixedCell, D.gen_fixedCell,
      D.gen_fixedCell] at h
    exact h
