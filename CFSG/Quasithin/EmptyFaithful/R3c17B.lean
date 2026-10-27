module

public import CFSG.Quasithin.EmptyFaithful.R3c17A
public import CFSG.Quasithin.EmptyFaithful.R3c16TriA

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
  CFSG.Quasithin.R3c16 CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.ExceptionalCat
open scoped commutatorElement Pointwise

section Shape

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem triality_overgroup_shape
    (σ : K ≃+* K)
    (h4 : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a))
    {M : Subgroup (ModGL TwistTag.D4.tag K)}
    (hMC : M ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hUM : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ M)
    (hMne : M ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    M ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ∨
      ∃ (a : Fin TwistTag.D4.foldedTag.rank) (L : Subgroup (ModGL TwistTag.D4.tag K)),
        Group.IsPerfect ↥L ∧ L ≤ M ∧
        fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a =
          graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊔ L ∧
        fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a ≤ M ∧
        M ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
          fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a ∧
        canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈ L := by
  classical
  obtain ⟨hle, hiff, -⟩ :=
    fixed_positive_root_overgroup_parabolic_containment TwistTag.D4 K σ hMC hUM
  set J : Set (Fin TwistTag.D4.foldedTag.rank) :=
    {a | canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) ∈ M}
    with hJ
  by_cases hJe : J = ∅
  · left
    rw [hJe, graphFixedParabolic_empty, CFSG.LieType.Chevalley.graphFixedRootBorel_eq_sup σ.surjective] at hle
    exact hle
  · right
    obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.2 hJe
    have hJsub : J ⊆ {a₀} := by
      intro a ha
      by_contra hne
      apply hMne
      apply hiff.1
      refine Set.eq_univ_of_forall fun i => ?_
      have h2 : ∀ x y z : Fin TwistTag.D4.foldedTag.rank, x ≠ y → z = x ∨ z = y := by decide
      rcases h2 a a₀ i (fun h => hne (by rw [h]; exact Set.mem_singleton _)) with rfl | rfl
      · exact ha
      · exact ha₀
    have hMP : M ≤ graphFixedParabolic TwistTag.D4 K σ.toRingHom {a₀} :=
      hle.trans (sup_le_sup_left (Subgroup.closure_mono (Set.image_mono hJsub)) _)
    have hyP : M ≤ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔
        fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ := by
      rw [← graphFixedParabolic_singleton_eq_sup σ.surjective]
      exact hMP
    obtain ⟨R, hRu, hRv, hRH, hRW, hn, hrange, -, -, -⟩ :=
      exceptional_fixed_rank_one_central_image TwistTag.D4 K σ.toRingHom a₀
    have hnL : canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection a₀) ∈ R.range := ⟨WSL, by rw [hRW, hn]⟩
    have hperf : Group.IsPerfect ↥R.range := by
      have := isPerfect_SL2_of_four_le (h4 a₀)
      exact Group.IsPerfect.range R
    have hNle : fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ ≤
        graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ⊔ R.range :=
      sup_le_sup_left ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnL)) _
    have hLN : R.range ≤ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ := by
      rw [hrange]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact graphFixedPosUnipotent_le_fixedPosWeylGroup a₀
          (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom a₀ c)
      · exact orbitY_mem_fixedPosWeylGroup a₀ c
    have hNM : fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a₀ ≤ M :=
      sup_le hUM ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ha₀))
    exact ⟨a₀, R.range, hperf, hLN.trans hNM,
      le_antisymm hNle (sup_le (graphFixedPosUnipotent_le_fixedPosWeylGroup a₀) hLN), hNM, hyP, hnL⟩

end Shape

section Param

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem triality_x6_central
    (c : trialityFixedField K σ.toRingHom) {u : ModGL TwistTag.D4.tag K}
    (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :
    u * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨-, -, -, -, -, ⟨f₆, hf₆i, hf₆⟩, hbij, -, -⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  obtain ⟨-, -, -, -, c16, -, -, c26, -, c36, -, c46, c56, -, -⟩ :=
    even_triality_trace_commutators K σ.toRingHom hσ3
  have a₆ := add_of_hom f₆ (trialityX₆ K τ₀) hf₆
  obtain ⟨⟨a, b, d, e, f, g⟩, -, hzN⟩ := hbij.2.2 hu
  have hc : Commute (trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ d *
      trialityX₄ K τ₀ e * trialityX₅ K τ₀ f * trialityX₆ K τ₀ g) (trialityX₆ K τ₀ c) :=
    Commute.mul_left (Commute.mul_left (Commute.mul_left (Commute.mul_left (Commute.mul_left
      (c16 a c) (c26 b c)) (c36 d c)) (c46 e c)) (c56 f c)) (comm_self_of_add _ a₆ g c)
  have hzz : ((trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ d *
      trialityX₄ K τ₀ e * trialityX₅ K τ₀ f * trialityX₆ K τ₀ g : adjointGroup TwistTag.D4.tag K) :
        ModGL TwistTag.D4.tag K) = u := hzN
  have h1 := congrArg Subtype.val hc.eq
  have e1 : (((trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ d *
      trialityX₄ K τ₀ e * trialityX₅ K τ₀ f * trialityX₆ K τ₀ g) * trialityX₆ K τ₀ c :
        adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
      u * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) := by
    rw [Subgroup.coe_mul, hzz]
    rfl
  have e2 : ((trialityX₆ K τ₀ c * (trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ d *
      trialityX₄ K τ₀ e * trialityX₅ K τ₀ f * trialityX₆ K τ₀ g) :
        adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * u := by
    rw [Subgroup.coe_mul, hzz]
    rfl
  rw [e1, e2] at h1
  exact h1

include hσ3 in
theorem triality_center_x6'
    {z : ModGL TwistTag.D4.tag K}
    (hz : z ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
    (hzc : ∀ q ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, q * z = z * q) :
    ∃ c : trialityFixedField K σ.toRingHom,
      z = pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) := by
  have hzC : z ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ hz
  obtain ⟨c, hc⟩ := triality_center_x6 σ hσ3
    (z := (⟨z, hzC⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) hz
    (fun q hq => Subtype.ext (hzc q.1 hq))
  exact ⟨c, hc⟩

include hσ3 in
theorem triality_x5_ne_x6
    {d : trialityFixedField K σ.toRingHom}
    (h : pinnedX TwistTag.D4.tag K (trialityRoot 4) (d : K) =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (d : K)) : d = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := TwistTag.D4.tag) (K := K)
  obtain ⟨⟨f₁, hf₁i, hf₁⟩, ⟨f₂, hf₂i, hf₂⟩, ⟨f₃, hf₃i, hf₃⟩, ⟨f₄, hf₄i, hf₄⟩,
    ⟨f₅, hf₅i, hf₅⟩, ⟨f₆, hf₆i, hf₆⟩, hbij, -, -⟩ :=
    even_triality_positive_orbit_parametrization K σ hσ3
  have a₁ := add_of_hom f₁ (trialityX₁ K τ₀) hf₁
  have a₂ := add_of_hom f₂ (trialityX₂ K τ₀) hf₂
  have a₃ := add_of_hom f₃ (trialityX₃ K τ₀) hf₃
  have a₄ := add_of_hom f₄ (trialityX₄ K τ₀) hf₄
  have a₅ := add_of_hom f₅ (trialityX₅ K τ₀) hf₅
  have a₆ := add_of_hom f₆ (trialityX₆ K τ₀) hf₆
  have z1 := zero_of_add (trialityX₁ K τ₀) a₁
  have z2 := zero_of_add (trialityX₂ K τ₀) a₂
  have z3 := zero_of_add (trialityX₃ K τ₀) a₃
  have z4 := zero_of_add (trialityX₄ K τ₀) a₄
  have z5 := zero_of_add (trialityX₅ K τ₀) a₅
  have z6 := zero_of_add (trialityX₆ K τ₀) a₆
  have inj : ∀ (a a' : K) (b b' : trialityFixedField K τ₀) (c c' d d' : K)
      (e e' f f' : trialityFixedField K τ₀),
      trialityX₁ K τ₀ a * trialityX₂ K τ₀ b * trialityX₃ K τ₀ c * trialityX₄ K τ₀ d *
        trialityX₅ K τ₀ e * trialityX₆ K τ₀ f =
      trialityX₁ K τ₀ a' * trialityX₂ K τ₀ b' * trialityX₃ K τ₀ c' * trialityX₄ K τ₀ d' *
        trialityX₅ K τ₀ e' * trialityX₆ K τ₀ f' →
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ f = f' := by
    intro a a' b b' c c' d d' e e' f f' h
    have := hbij.2.1 (Set.mem_univ (a, b, c, d, e, f)) (Set.mem_univ (a', b', c', d', e', f'))
      (congrArg Subtype.val h)
    simp only [Prod.mk.injEq] at this
    exact this
  have h' : trialityX₅ K τ₀ d = trialityX₆ K τ₀ d := Subtype.ext h
  have := inj 0 0 0 0 0 0 0 0 d 0 0 d (by
    rw [z1, z2, z3, z4, z5, z6]
    simp only [one_mul, mul_one]
    exact h')
  exact this.2.2.2.2.1

end Param

section Weyl

variable {K : Type} [Field K] [CharP K 2]

theorem triality_n_outer_conj
    (c : K) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) *
      pinnedX TwistTag.D4.tag K (trialityRoot 5) c *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)))⁻¹ =
    pinnedX TwistTag.D4.tag K (trialityRoot 5) c := by
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  have hr0 : TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) •
      trialityRoot 5 = trialityRoot 5 := by
    have hw : TwistTag.D4.orbitWord (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) =
        [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  rw [canonicalRep_conj_charTwo _ hroot6, hr0]

theorem triality_n_central_conj
    (c : K) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) *
      pinnedX TwistTag.D4.tag K (trialityRoot 5) c *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K
        (TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)))⁻¹ =
    pinnedX TwistTag.D4.tag K (trialityRoot 4) c := by
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  have hr1 : TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) •
      trialityRoot 5 = trialityRoot 4 := by
    have hw : TwistTag.D4.orbitWord (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) =
        [⟨2, by decide⟩] := by decide
    unfold TwistTag.orbitReflection
    rw [hw, CoxeterSystem.wordProd_singleton, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  rw [canonicalRep_conj_charTwo _ hroot6, hr1]

end Weyl

theorem torus_conj_scalar {K : Type} [Field K]
    {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    ∃ l : K, ∀ c : K, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (l * c) := by
  rw [torusGroup] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hx
    exact ⟨_, fun c => root_torus_conjugation i hα t c⟩
  | one => exact ⟨1, fun c => by rw [one_mul, inv_one, mul_one, one_mul]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨lx, hlx⟩ := ihx
    obtain ⟨ly, hly⟩ := ihy
    refine ⟨lx * ly, fun c => ?_⟩
    have e : x * y * pinnedX τ K α c * (x * y)⁻¹ =
        x * (y * pinnedX τ K α c * y⁻¹) * x⁻¹ := by group
    rw [e, hly, hlx, mul_assoc]
  | inv x hx ihx =>
    obtain ⟨lx, hlx⟩ := ihx
    have hl0 : lx ≠ 0 := by
      intro h0
      have h1 := hlx 1
      rw [h0, zero_mul, pinnedX_zero] at h1
      have h2 : pinnedX τ K α 1 = 1 := by
        have := congrArg (fun g => x⁻¹ * g * x) h1
        simpa [mul_assoc] using this
      have := pinnedX_injective (τ := τ) (R := K) α (h2.trans (pinnedX_zero τ K α).symm)
      exact one_ne_zero this
    refine ⟨lx⁻¹, fun c => ?_⟩
    have h1 := hlx (lx⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hl0, one_mul] at h1
    have h2 : x⁻¹ * pinnedX τ K α c * x = pinnedX τ K α (lx⁻¹ * c) := by
      rw [← h1]
      group
    exact h2

section Scalar

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)

omit [Finite K] [CharP K 2] in
theorem triality_scalar_of_sup
    {W : Subgroup (ModGL TwistTag.D4.tag K)}
    (hHW : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤ Subgroup.normalizer (W : Set _))
    (hWc : ∀ w ∈ W, ∀ c : trialityFixedField K σ.toRingHom,
      w * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * w)
    {g : ModGL TwistTag.D4.tag K}
    (hg : g ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom ⊔ W) :
    ∃ l : K, ∀ c : trialityFixedField K σ.toRingHom,
      g * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * g⁻¹ =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) (l * (c : K)) := by
  have hg' : g ∈ (graphFixedRootTorus TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) *
      (W : Set (ModGL TwistTag.D4.tag K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHW]
    exact hg
  obtain ⟨h, hh, w, hw, rfl⟩ := hg'
  have hhT : h ∈ torusGroup TwistTag.D4.tag K := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hh).1).1
  have hroot6 : IsRoot TwistTag.D4.tag (trialityRoot 5) := (isRoot_trialityRoot 5 0).1
  obtain ⟨l, hl⟩ := torus_conj_scalar hroot6 hhT
  refine ⟨l, fun c => ?_⟩
  have hwc : w * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * w⁻¹ =
      pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) := by
    rw [hWc w hw c]
    group
  have e : h * w * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * (h * w)⁻¹ =
      h * (w * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * w⁻¹) * h⁻¹ := by group
  rw [e, hwc]
  exact hl (c : K)

end Scalar

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom

include hσ3 in
theorem triality_core
    (h4 : ∀ a : Fin TwistTag.D4.foldedTag.rank,
      4 ≤ Nat.card (orbitField TwistTag.D4 K σ.toRingHom a))
    {V M : Subgroup (ModGL TwistTag.D4.tag K)}
    (hVU : V ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) (hV4 : Nat.card V = 4)
    (hMC : M ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hUM : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ M)
    (hMne : M ≠ graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hMV : M ≤ Subgroup.normalizer (V : Set (ModGL TwistTag.D4.tag K)))
    {y : ModGL TwistTag.D4.tag K} (hyM : y ∈ M) {k : ℕ} (hk : y ^ (3 ^ k) = 1)
    (hyn : ¬ ∀ v ∈ V, y * v = v * y) :
    (∀ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, ∀ v ∈ V, u * v = v * u) ∧
    ∀ g ∈ M, ∃ l : K, ∀ c : trialityFixedField K σ.toRingHom,
      g * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * g⁻¹ =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) (l * (c : K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 ↥(graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :=
    (isPGroup_posUnipotent (K := K) 2 TwistTag.D4.tag).to_le
      (inf_le_left : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ _)
  have hHU : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
      Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
        Set (ModGL TwistTag.D4.tag K)) :=
    graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent
  have hUc : ∀ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      ∀ c : trialityFixedField K σ.toRingHom,
        u * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) =
          pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * u :=
    fun u hu c => triality_x6_central σ hσ3 c hu
  rcases triality_overgroup_shape σ h4 hMC hUM hMne with
    hB | ⟨a, L, hLperf, hLM, hNL, hNM, hMP, hnL⟩
  ·
    have hWn : ∀ m ∈ M, ∀ w ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
        m * w * m⁻¹ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
      intro m hm w hw
      have hm' : m ∈ Subgroup.normalizer (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :
          Set (ModGL TwistTag.D4.tag K)) := (sup_le hHU Subgroup.le_normalizer) (hB hm)
      exact (Subgroup.mem_normalizer_iff.1 hm' w).1 hw
    have ha := two_group_trivial_action hMV hV4 hU2 le_rfl hUM hWn
      (fun w hw => ⟨w, hw, fun v _ => rfl⟩) hyM hk hyn
    exact ⟨ha, fun g hg => triality_scalar_of_sup σ hHU hUc (hB hg)⟩
  ·
    have hHN : graphFixedRootTorus TwistTag.D4 K σ.toRingHom ≤
        Subgroup.normalizer (fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a :
          Set (ModGL TwistTag.D4.tag K)) :=
      graphFixedRootTorus_le_normalizer_fixedPosWeylGroup a
    have hWn : ∀ m ∈ M, ∀ w ∈ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a,
        m * w * m⁻¹ ∈ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a := by
      intro m hm w hw
      have hm' : m ∈ Subgroup.normalizer (fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a :
          Set (ModGL TwistTag.D4.tag K)) := (sup_le hHN Subgroup.le_normalizer) (hMP hm)
      exact (Subgroup.mem_normalizer_iff.1 hm' w).1 hw
    have hW : ∀ w ∈ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom a,
        ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom, ∀ v ∈ V,
          w * v * w⁻¹ = u * v * u⁻¹ := fun w hw =>
      act_eq_of_mem_sup_perfect hMV hV4 hUM hLM hLperf (hNL ▸ hw)
    have ha := two_group_trivial_action hMV hV4 hU2
      (graphFixedPosUnipotent_le_fixedPosWeylGroup a) hNM hWn hW hyM hk hyn
    refine ⟨ha, ?_⟩
    have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank,
        a = ⟨0, by decide⟩ ∨ a = ⟨1, by decide⟩ := by decide
    rcases hcases a with rfl | rfl
    ·
      have hWc : ∀ w ∈ fixedPosWeylGroup TwistTag.D4 K σ.toRingHom
          (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank),
          ∀ c : trialityFixedField K σ.toRingHom,
            w * pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) =
              pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) * w := by
        intro w hw c
        have hle : fixedPosWeylGroup TwistTag.D4 K σ.toRingHom
            (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank) ≤
            Subgroup.centralizer {pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K)} := by
          refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hUc u hu c)
          · rintro _ rfl
            refine Subgroup.mem_centralizer_singleton_iff.2 ?_
            have h1 := triality_n_outer_conj (K := K) (c : K)
            have h2 : canonicalRep (coxeterSystem TwistTag.D4.tag) K
                (TwistTag.D4.orbitReflection (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) *
                pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) =
                pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) *
                canonicalRep (coxeterSystem TwistTag.D4.tag) K
                  (TwistTag.D4.orbitReflection
                    (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) := by
              calc _ = (canonicalRep (coxeterSystem TwistTag.D4.tag) K
                    (TwistTag.D4.orbitReflection
                      (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) *
                    pinnedX TwistTag.D4.tag K (trialityRoot 5) (c : K) *
                    (canonicalRep (coxeterSystem TwistTag.D4.tag) K
                      (TwistTag.D4.orbitReflection
                        (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)))⁻¹) *
                    canonicalRep (coxeterSystem TwistTag.D4.tag) K
                      (TwistTag.D4.orbitReflection
                        (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) := by group
                _ = _ := by rw [h1]
            exact h2
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
      exact fun g hg => triality_scalar_of_sup σ hHN hWc (hMP hg)
    ·
      exfalso
      obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : V = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
        rw [this, Subgroup.card_bot] at hV4
        omega
      obtain ⟨c, hc⟩ := triality_center_x6' σ hσ3 (hVU hv) (fun q hq => ha q hq v hv)
      have hc0 : c ≠ 0 := by
        intro h0
        apply hv1
        rw [hc, h0]
        exact pinnedX_zero _ _ _
      have hnv : canonicalRep (coxeterSystem TwistTag.D4.tag) K
          (TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)) * v *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) K
            (TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)))⁻¹ =
          v := by
        obtain ⟨u, hu, hu'⟩ := act_eq_of_mem_sup_perfect (U := ⊥) hMV hV4 bot_le hLM hLperf
          (w := canonicalRep (coxeterSystem TwistTag.D4.tag) K
            (TwistTag.D4.orbitReflection (⟨1, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)))
          (by rw [bot_sup_eq]; exact hnL)
        rw [hu' v hv, Subgroup.mem_bot.1 hu]
        group
      rw [hc, triality_n_central_conj (K := K) (c : K)] at hnv
      exact hc0 (triality_x5_ne_x6 σ hσ3 hnv)

end Core

end CFSG.Quasithin.R3c17
