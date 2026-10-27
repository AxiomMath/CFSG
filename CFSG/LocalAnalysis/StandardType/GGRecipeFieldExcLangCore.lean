module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.LangAdjointDiagonalLift
public import CFSG.LieType.AlgebraicGroups.AllCharacteristicLang
public import CFSG.RankThree.PartOne.KE.LangDescent
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


section Group

variable (τ : Tag) (K : Type) [Field K]

@[expose] def inndiagGroup : Subgroup (ModGL τ K) where
  carrier := {w | ∃ b : Fin τ.rank → Kˣ, ∃ j ∈ adjointGroup τ K, w = rootDiagUnit τ b * j}
  mul_mem' := by
    rintro _ _ ⟨b, j, hj, rfl⟩ ⟨b', j', hj', rfl⟩
    have h1 := conj_rootDiagUnit_mem_adjointGroup (τ := τ) b'⁻¹ hj
    rw [← rootDiagUnit_inv, inv_inv] at h1
    refine ⟨b * b', (rootDiagUnit τ b')⁻¹ * j * rootDiagUnit τ b' * j', mul_mem h1 hj', ?_⟩
    rw [rootDiagUnit_mul]
    group
  one_mem' := ⟨1, 1, one_mem _, by rw [rootDiagUnit_one, one_mul]⟩
  inv_mem' := by
    rintro _ ⟨b, j, hj, rfl⟩
    refine ⟨b⁻¹, rootDiagUnit τ b * j⁻¹ * (rootDiagUnit τ b)⁻¹,
      conj_rootDiagUnit_mem_adjointGroup b (inv_mem hj), ?_⟩
    rw [← rootDiagUnit_inv]
    group

variable {τ K}

theorem mem_inndiagGroup {w : ModGL τ K} :
    w ∈ inndiagGroup τ K ↔ ∃ b : Fin τ.rank → Kˣ, ∃ j ∈ adjointGroup τ K,
      w = rootDiagUnit τ b * j :=
  Iff.rfl

theorem adjointGroup_le_inndiagGroup : adjointGroup τ K ≤ inndiagGroup τ K :=
  fun j hj => ⟨1, j, hj, by rw [rootDiagUnit_one, one_mul]⟩

theorem rootDiagUnit_mem_inndiagGroup (b : Fin τ.rank → Kˣ) :
    rootDiagUnit τ b ∈ inndiagGroup τ K :=
  ⟨b, 1, one_mem _, by rw [mul_one]⟩

theorem conj_mem_adjointGroup_of_mem_inndiag {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K)
    {h : ModGL τ K} (hh : h ∈ adjointGroup τ K) : w * h * w⁻¹ ∈ adjointGroup τ K := by
  obtain ⟨b, j, hj, rfl⟩ := hw
  have e : rootDiagUnit τ b * j * h * (rootDiagUnit τ b * j)⁻¹ =
      rootDiagUnit τ b * (j * h * j⁻¹) * (rootDiagUnit τ b)⁻¹ := by group
  rw [e]
  exact conj_rootDiagUnit_mem_adjointGroup b (mul_mem (mul_mem hj hh) (inv_mem hj))

theorem entrywise_mem_adjointGroup (σ : K ≃+* K) {j : ModGL τ K} (hj : j ∈ adjointGroup τ K) :
    Units.map (entrywiseHom σ.toRingHom) j ∈ adjointGroup τ K := by
  rw [← map_exactEntrywiseAut σ (Or.inl rfl)]
  exact Subgroup.mem_map_of_mem _ hj

theorem entrywise_mem_inndiagGroup (σ : K ≃+* K) {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K) :
    Units.map (entrywiseHom σ.toRingHom) w ∈ inndiagGroup τ K := by
  obtain ⟨b, j, hj, rfl⟩ := hw
  refine ⟨fun i => Units.map σ.toRingHom.toMonoidHom (b i), _,
    entrywise_mem_adjointGroup σ hj, ?_⟩
  rw [map_mul, units_map_entrywiseHom_rootDiagUnit_ringEquiv]

theorem map_exactEntrywiseAut_inndiagGroup (σ : K ≃+* K) :
    (inndiagGroup τ K).map (exactEntrywiseAut τ σ).toMonoidHom = inndiagGroup τ K := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact entrywise_mem_inndiagGroup σ hw
  · refine ⟨exactEntrywiseAut τ σ.symm w, entrywise_mem_inndiagGroup σ.symm hw, ?_⟩
    exact (exactEntrywiseAut τ σ).apply_symm_apply w

variable (τ K) in
@[expose] noncomputable def inndiagFieldAut : (K ≃+* K) →* MulAut (inndiagGroup τ K) where
  toFun σ := mulAutRestrict (inndiagGroup τ K) (exactEntrywiseAut τ σ)
    (map_exactEntrywiseAut_inndiagGroup σ)
  map_one' := by
    have h1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    refine MulEquiv.ext fun w => Subtype.ext (Units.ext ?_)
    rw [coe_mulAutRestrict, exactEntrywiseAut_apply, MulAut.one_apply, Units.coe_map, h1]
    exact entrywise_id (R := K) _
  map_mul' σ σ' := MulEquiv.ext fun w => Subtype.ext
    (units_map_entrywiseHom_mul_ringEquiv σ σ' (w : ModGL τ K))

theorem coe_inndiagFieldAut (σ : K ≃+* K) (w : inndiagGroup τ K) :
    ((inndiagFieldAut τ K σ w : inndiagGroup τ K) : ModGL τ K) =
      Units.map (entrywiseHom σ.toRingHom) (w : ModGL τ K) :=
  rfl

end Group

section Embed

variable {τ : Tag} {K : Type} [Field K]

theorem baseChangeGL_mem_adjointGroup_of_mem_inndiag {L : Type} [Field L] [IsAlgClosed L]
    (ι : K →+* L) {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K) :
    baseChangeGL ι w ∈ adjointGroup τ L := by
  obtain ⟨b, j, hj, rfl⟩ := hw
  rw [map_mul, baseChangeGL_rootDiagUnit]
  exact mul_mem (exceptional_Lang_adjoint_diagonal_lift τ L _).1
    (baseChangeGL_mem_adjointGroup ι hj)

variable (τ K) in
@[expose] noncomputable def inndiagEmbed (L : Type) [Field L] [IsAlgClosed L] (ι : K →+* L) :
    inndiagGroup τ K →* adjointGroup τ L :=
  ((baseChangeGL ι).comp (inndiagGroup τ K).subtype).codRestrict (adjointGroup τ L)
    fun w => baseChangeGL_mem_adjointGroup_of_mem_inndiag ι w.2

theorem coe_inndiagEmbed {L : Type} [Field L] [IsAlgClosed L] (ι : K →+* L)
    (w : inndiagGroup τ K) : (inndiagEmbed τ K L ι w : ModGL τ L) = baseChangeGL ι w :=
  rfl

theorem inndiagEmbed_injective {L : Type} [Field L] [IsAlgClosed L] (ι : K →+* L) :
    Function.Injective (inndiagEmbed τ K L ι) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))

theorem eq_one_of_commute_adjointGroup [Finite K] (hK4 : 4 ≤ Nat.card K) {z : ModGL τ K}
    (hz : z ∈ inndiagGroup τ K) (hc : ∀ h ∈ adjointGroup τ K, z * h = h * z) : z = 1 := by
  set L := AlgebraicClosure K
  obtain ⟨hinj, -, hC, -⟩ :=
    Chevalley_large_finite_root_centralizer_faithfulness_of_four_le τ K hK4 L (algebraMap K L)
  apply hinj
  rw [map_one]
  refine hC _ (baseChangeGL_mem_adjointGroup_of_mem_inndiag _ hz) fun h hh => ?_
  obtain ⟨h₀, hh₀, rfl⟩ := hh
  rw [← map_mul, ← map_mul, hc h₀ hh₀]

theorem center_inndiagGroup_eq_bot [Finite K] (hK4 : 4 ≤ Nat.card K) :
    Subgroup.center (inndiagGroup τ K) = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  rw [Subgroup.mem_bot]
  refine Subtype.ext (eq_one_of_commute_adjointGroup hK4 z.2 fun h hh => ?_)
  have := (Subgroup.mem_center_iff.1 hz) ⟨h, adjointGroup_le_inndiagGroup hh⟩
  exact (congrArg Subtype.val this).symm

end Embed

section Lang

variable {τ : Tag} {K : Type} [Field K]

theorem exists_conj_eq_inndiagFieldAut_frob {ℓ f e p : ℕ} [Fact ℓ.Prime] [Finite K] [CharP K ℓ]
    (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hp : 1 ≤ p)
    (hep : e * p = f) (T : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (x : inndiagGroup τ K)
    (hx : (MulAut.conj x * inndiagFieldAut τ K T) ^ p = 1) :
    ∃ g : inndiagGroup τ K, MulAut.conj g * (MulAut.conj x * inndiagFieldAut τ K T) *
      (MulAut.conj g)⁻¹ = inndiagFieldAut τ K T := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have hTp : T ^ p = 1 := by
    refine RingEquiv.ext fun c => ?_
    rw [ringEquiv_pow_apply, RingAut.one_apply]
    have hit : ∀ n : ℕ, (⇑T)^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Function.iterate_succ_apply', ih, hT, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  obtain ⟨S, hS, hLang⟩ :=
    (CFSG.LieType.AlgebraicGroups.exceptional_all_characteristic_field_Lang_surjectivity ℓ L e
      he).1 τ
  set ι := inndiagEmbed τ K L (algebraMap K L) with hι
  have hFrc : (iterateFrobenius L ℓ e).comp (algebraMap K L) =
      (algebraMap K L).comp T.toRingHom := by
    ext c
    simp [iterateFrobenius_def, hT, map_pow]
  have heF₀ : ∀ w, ι (inndiagFieldAut τ K T w) = S (ι w) := by
    intro w
    apply Subtype.ext
    rw [hS, coe_inndiagEmbed, coe_inndiagEmbed, coe_inndiagFieldAut,
      units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFrc]
  have hiterS : ∀ (n : ℕ) (g : adjointGroup τ L), (((S ^ n) g : adjointGroup τ L) :
      ModGL τ L) = Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ n)) g := by
    intro n
    induction n with
    | zero =>
      intro g
      refine Units.ext ?_
      rw [pow_zero, MulAut.one_apply, Units.coe_map, pow_zero, RingHom.one_def]
      exact (entrywise_id (R := L) _).symm
    | succ n ih =>
      intro g
      rw [pow_succ', MulAut.mul_apply, hS, ih]
      refine Units.ext ?_
      rw [Units.coe_map, Units.coe_map, Units.coe_map, pow_succ', RingHom.mul_def]
      exact entrywise_entrywise (R := L) _ _ _
  have hFrK : ∀ c : L, ((iterateFrobenius L ℓ e) ^ p) c = c ^ Nat.card K := by
    intro c
    rw [RingHom.coe_pow]
    have hit : ∀ n : ℕ, (⇑(iterateFrobenius L ℓ e))^[n] c = c ^ ((ℓ ^ e) ^ n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, iterateFrobenius_def, pow_succ, pow_mul]
    rw [hit, ← pow_mul, hep, hK]
  have hmem : ∀ h : adjointGroup τ L, (S ^ p) h = h → h ∈ ι.range := by
    intro h hh
    have hfix : Units.map (entrywiseHom ((iterateFrobenius L ℓ e) ^ p)) (h : ModGL τ L) = h := by
      rw [← hiterS, hh]
    obtain ⟨a, u, ⟨j, hj, rfl⟩, hu⟩ :=
      exists_rootDiagUnit_mul_of_frobenius_fixed τ _ hFrK h.2 hfix
    refine ⟨⟨rootDiagUnit τ a * j, ⟨a, j, hj, rfl⟩⟩, Subtype.ext ?_⟩
    rw [coe_inndiagEmbed, map_mul, hu]
  exact CFSG.RankThree.PartOne.KE.exists_inner_conj_eq_of_lang (center_inndiagGroup_eq_bot hK4)
    (inndiagFieldAut τ K T) hp (by rw [← map_pow, hTp, map_one]) S hLang ι
    (inndiagEmbed_injective _) heF₀ hmem x hx

end Lang

end RecipeExcLang

end CFSG.StandardType
