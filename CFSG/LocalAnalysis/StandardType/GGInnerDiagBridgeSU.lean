module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace InnerDiagSU

section General

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

@[expose] def IsJUnitary (A : GL (Fin n) F) : Prop :=
  conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F) =
    antidiag n

variable {σ}

theorem val_mul_val_inv (A : GL (Fin n) F) :
    (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem IsJUnitary.inv {A : GL (Fin n) F} (hA : IsJUnitary σ A) : IsJUnitary σ A⁻¹ := by
  unfold IsJUnitary at hA ⊢
  calc conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F)) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [hA]
    _ = conjTr σ ((A : Matrix (Fin n) (Fin n) F) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * antidiag n *
          ((A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = antidiag n := by rw [val_mul_val_inv, conjTr_one, Matrix.one_mul, Matrix.mul_one]

theorem conj_mem_SU {A : GL (Fin n) F} (hA : IsJUnitary σ A) {u : GL (Fin n) F}
    (hu : u ∈ SU σ n) : A * u * A⁻¹ ∈ SU σ n := by
  obtain ⟨hdet, hiso⟩ := hu
  have hAi := hA.inv
  unfold IsJUnitary at hA hAi
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
      val_mul_val_inv, det_one]
  · rw [Units.val_mul, Units.val_mul]
    calc conjTr σ ((A : Matrix (Fin n) (Fin n) F) * (u : Matrix (Fin n) (Fin n) F) *
          ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * antidiag n *
          ((A : Matrix (Fin n) (Fin n) F) * (u : Matrix (Fin n) (Fin n) F) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        = conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (u : Matrix (Fin n) (Fin n) F) *
              (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
                (A : Matrix (Fin n) (Fin n) F)) * (u : Matrix (Fin n) (Fin n) F)) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = antidiag n := by rw [hA, hiso, hAi]

@[expose] noncomputable def conjSU (A : GL (Fin n) F) (hA : IsJUnitary σ A) :
    SU σ n →* SU σ n where
  toFun u := ⟨A * u * A⁻¹, conj_mem_SU hA u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by
    show A * ((u : GL (Fin n) F) * v) * A⁻¹ = A * u * A⁻¹ * (A * v * A⁻¹)
    group)

theorem coe_conjSU (A : GL (Fin n) F) (hA : IsJUnitary σ A) (u : SU σ n) :
    ((conjSU A hA u : SU σ n) : GL (Fin n) F) = A * u * A⁻¹ :=
  rfl

end General

section Finite

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

@[expose] def SUInnerDiagConj (hF : Nat.card F = (2 ^ f) ^ 2) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] (ψ : SU (unitaryInvolution F 2 f) n →* G),
    ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) n) → ∀ c : G,
      GGPsiInnerDiag (rootDatum hF n) ψ c →
        ∃ (A : GL (Fin n) F) (hA : IsJUnitary (unitaryInvolution F 2 f) A),
          ∀ u, c⁻¹ * ψ u * c = ψ (conjSU A hA u)

end Finite

section Identity

variable {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def IsIdUnitary (σ : F ≃+* F) (B : GL (Fin n) F) : Prop :=
  conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F) = 1

theorem IsIdUnitary.inv {B : GL (Fin n) F} (hB : IsIdUnitary σ B) : IsIdUnitary σ B⁻¹ := by
  unfold IsIdUnitary at hB ⊢
  calc conjTr σ ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = conjTr σ ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
            ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        rw [hB, Matrix.mul_one]
    _ = conjTr σ ((B : Matrix (Fin n) (Fin n) F) *
          ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          ((B : Matrix (Fin n) (Fin n) F) * ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = 1 := by rw [val_mul_val_inv, conjTr_one, Matrix.one_mul]

theorem conj_mem_SUid {B : GL (Fin n) F} (hB : IsIdUnitary σ B) {h : GL (Fin n) F}
    (hh : h ∈ SUid σ n) : B * h * B⁻¹ ∈ SUid σ n := by
  obtain ⟨hdet, hiso⟩ := hh
  have hBi := hB.inv
  unfold IsIdUnitary at hB hBi
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hdet, mul_one, ← det_mul,
      val_mul_val_inv, det_one]
  · rw [Units.val_mul, Units.val_mul]
    calc conjTr σ ((B : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
          ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          ((B : Matrix (Fin n) (Fin n) F) * (h : Matrix (Fin n) (Fin n) F) *
            ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
        = conjTr σ ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (h : Matrix (Fin n) (Fin n) F) *
              (conjTr σ (B : Matrix (Fin n) (Fin n) F) * (B : Matrix (Fin n) (Fin n) F)) *
                (h : Matrix (Fin n) (Fin n) F)) *
            ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [conjTr_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hB, Matrix.mul_one, hiso, Matrix.mul_one, hBi]

theorem mem_normalizer_SUid {B : GL (Fin n) F} (hB : IsIdUnitary σ B) :
    B ∈ Subgroup.normalizer (SUid σ n : Set (GL (Fin n) F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_SUid hB, fun hh => ?_⟩
  have := conj_mem_SUid hB.inv hh
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

theorem isIdUnitary_conj {P A : GL (Fin n) F}
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hA : IsJUnitary σ A) : IsIdUnitary σ (P * A * P⁻¹) := by
  unfold IsIdUnitary
  unfold IsJUnitary at hA
  rw [Units.val_mul, Units.val_mul]
  calc conjTr σ ((P : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) *
        ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
        ((P : Matrix (Fin n) (Fin n) F) * (A : Matrix (Fin n) (Fin n) F) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      = conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (A : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F)) *
              (A : Matrix (Fin n) (Fin n) F)) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F)) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [hP, hA, ← hP]
    _ = conjTr σ ((P : Matrix (Fin n) (Fin n) F) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          ((P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = 1 := by rw [val_mul_val_inv, conjTr_one, Matrix.one_mul]

end Identity

section Marking

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem mem_center_iff_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X} :
    e x ∈ Subgroup.center Y ↔ x ∈ Subgroup.center X := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply e.injective
    rw [map_mul, map_mul, h (e y)]
  · intro h y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h z]

theorem largeEvenMarking_unitary (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {m : ℕ}
    (hm : 3 ≤ m) {G : Type} [Group G] (ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    (hconj : SUInnerDiagConj hF (m + 1)) :
    LargeEvenMarking ↥ψ.range (fun _ _ _ I _ θ => ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (rootDatum hF (m + 1)) ψ c →
        ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ) := by
  have hn3 : 3 ≤ m + 1 := by omega
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h => by
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hperfS : Group.IsPerfect (StatedSU (m + 1) (2 ^ f) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF hn3 hnq
  let H := LargeEvenSUGroup (Fin (m + 1)) F (2 ^ f)
  have hZ : Subgroup.center ↥H = (LargeEvenScalars (Fin (m + 1)) F).subgroupOf H :=
    (isQuasisimple_statedSU_of_card hF hn3 hnq).2
  have hperfH : Group.IsPerfect ↥H := hperfS
  have hSU : SUid (unitaryInvolution F 2 f) (m + 1) = H := SUid_eq_statedSU hF (m + 1)
  set P := (exists_wittMatrix hF (m + 1)).choose with hPdef
  have hP := (exists_wittMatrix hF (m + 1)).choose_spec
  let E : SU (unitaryInvolution F 2 f) (m + 1) ≃* ↥H :=
    (conjEquiv P hP).trans (MulEquiv.subgroupCongr hSU)
  have hEu : ∀ u, ((E u : ↥H) : GL (Fin (m + 1)) F) = P * u * P⁻¹ := fun _ => rfl
  have hperfU : Group.IsPerfect (SU (unitaryInvolution F 2 f) (m + 1)) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hperf : commutator (SU (unitaryInvolution F 2 f) (m + 1)) = ⊤ :=
    Group.isPerfect_def.mp hperfU
  let q₁ : SU (unitaryInvolution F 2 f) (m + 1) →* ↥ψ.range ⧸ Subgroup.center ↥ψ.range :=
    (QuotientGroup.mk' _).comp ψ.rangeRestrict
  let q₂ : SU (unitaryInvolution F 2 f) (m + 1) →* LargeEvenProj H :=
    (LargeEvenProjMk H).comp E.toMonoidHom
  have hq₁ : Function.Surjective q₁ :=
    (QuotientGroup.mk'_surjective _).comp ψ.rangeRestrict_surjective
  have hq₂ : Function.Surjective q₂ :=
    (QuotientGroup.mk'_surjective _).comp E.surjective
  have hk₁ : q₁.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (ψ.rangeRestrict u) : ↥ψ.range ⧸ Subgroup.center ↥ψ.range) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    refine ⟨InnerDiagA.mem_center_of_rangeRestrict_mem_center hperf ψ hker, fun hu => ?_⟩
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨s, rfl⟩ := ψ.rangeRestrict_surjective l
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hu s]
  have hk₂ : q₂.ker = Subgroup.center _ := by
    ext u
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (s := (LargeEvenScalars (Fin (m + 1)) F).subgroupOf H) (E u) :
      LargeEvenProj H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, ← mem_center_iff_of_mulEquiv E, hZ]
  let θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* LargeEvenProj H :=
    (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (hk₁.trans hk₂.symm)).trans
        (QuotientGroup.quotientKerEquivOfSurjective q₂ hq₂))
  have hθ : ∀ u, θ (q₁ u) = q₂ u := fun u => by
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective q₁ hq₁).symm (q₁ u) =
        (u : SU (unitaryInvolution F 2 f) (m + 1) ⧸ q₁.ker) :=
      (MulEquiv.symm_apply_eq _).mpr rfl
    simp only [θ, MulEquiv.trans_apply, h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hsimple : IsSimpleGroup (LargeEvenProj H) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 2 f hF (m + 1) hn3 hnq
  have hnonab : ∃ a b : LargeEvenProj H, a * b ≠ b * a := by
    have : Group.IsPerfect (LargeEvenProj H) :=
      Group.IsPerfect.ofSurjective (f := LargeEvenProjMk H) (QuotientGroup.mk'_surjective _)
    have := hsimple.toNontrivial
    by_contra h
    push Not at h
    exact Group.IsPerfect.not_isMulCommutative (LargeEvenProj H) ⟨⟨h⟩⟩
  have hcomm : commutator ↥ψ.range = ⊤ := by
    have h1 := congrArg (Subgroup.map ψ.rangeRestrict) hperf
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ ψ.rangeRestrict_surjective] at h1
    rw [commutator_def]
    exact h1
  have key : ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      GGPsiInnerDiag (rootDatum hF (m + 1)) ψ c →
        ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin (m + 1)) F (2 ^ f)),
          LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
    intro c _ hdiag
    obtain ⟨A, hA, hAc⟩ := hconj G ψ hker c hdiag
    have hB : IsIdUnitary (unitaryInvolution F 2 f) (P * A * P⁻¹) := isIdUnitary_conj hP hA
    have hBN : P * A * P⁻¹ ∈ Subgroup.normalizer (H : Set (GL (Fin (m + 1)) F)) := by
      have h1 := mem_normalizer_SUid hB
      rw [hSU] at h1
      exact h1
    refine ⟨TableB.projConj H ⟨P * A * P⁻¹, hBN⟩, ⟨P * A * P⁻¹, ?_, fun h h' hh' => ?_⟩, ?_⟩
    · refine ⟨1, one_ne_zero, one_pow _, ?_⟩
      rw [one_smul]
      have hmap : ((P * A * P⁻¹ : GL (Fin (m + 1)) F) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (· ^ 2 ^ f) =
          ((P * A * P⁻¹ : GL (Fin (m + 1)) F) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) F).map (unitaryInvolution F 2 f) := by
        ext i j
        simp only [Matrix.map_apply, unitaryInvolution_apply]
      rw [hmap]
      exact hB
    · show TableB.projConj H ⟨P * A * P⁻¹, hBN⟩ (h : LargeEvenProj H) = (h' : LargeEvenProj H)
      rw [TableB.projConj_mk]
      congr 1
      exact Subtype.ext hh'.symm
    · intro l l' hl
      obtain ⟨u, rfl⟩ := ψ.rangeRestrict_surjective l
      have hl' : l' = ψ.rangeRestrict (conjSU A hA u) := by
        apply Subtype.ext
        rw [hl, MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict]
        exact hAc u
      rw [hl']
      change TableB.projConj H _ (θ (q₁ u)) = θ (q₁ (conjSU A hA u))
      rw [hθ, hθ]
      change TableB.projConj H _ ((E u : ↥H) : LargeEvenProj H) =
        ((E (conjSU A hA u) : ↥H) : LargeEvenProj H)
      rw [TableB.projConj_mk]
      congr 1
      apply Subtype.ext
      show P * A * P⁻¹ * (E u : GL (Fin (m + 1)) F) * (P * A * P⁻¹)⁻¹ =
        (E (conjSU A hA u) : GL (Fin (m + 1)) F)
      rw [hEu, hEu, coe_conjSU]
      group
  have hm1 : m = 2 → 2 ≤ f := fun h => by omega
  have hraw : LargeEvenRecipeUnitary (m + 1) (2 ^ f) fun R _ I _ => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : ↥ψ.range ⧸ Subgroup.center ↥ψ.range ≃* R,
        ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
          GGPsiInnerDiag (rootDatum hF (m + 1)) ψ c →
            ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ :=
    ⟨F, inferInstance, inferInstance, hF, hsimple, hnonab, θ, key⟩
  exact ⟨hcomm, ⟨.twA, m, f⟩, ⟨hf, (by omega : 2 ≤ m), hm1⟩, hraw⟩

end Marking

end InnerDiagSU

section Genuine

theorem ggInnerDiagMarkingAt_PSU_of
    (h : ∀ (f : ℕ) (hf : 1 ≤ f) (n : ℕ), 4 ≤ n →
      InnerDiagSU.SUInnerDiagConj (card_galoisField_two_mul 2 f hf) n) :
    GGInnerDiagMarkingAt .PSU := by
  intro G _ _ n f
  by_cases hf : 1 ≤ f
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have e : ggU .PSU n f =
        ⟨Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
          Unitary.rootDatum (card_galoisField_two_mul 2 f hf) n⟩ := by
      simp only [ggU, lieUniversal, hf, ↓reduceDIte]
    rw [e]
    intro ψ G₀ hpres
    obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hn : 4 ≤ n := by
      change 2 ≤ n / 2 at hrk
      omega
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact InnerDiagSU.largeEvenMarking_unitary (card_galoisField_two_mul 2 f hf) hf (by omega) ψ
      hker (h f hf (m + 1) hn)
  · intro ψ G₀ hpres
    exact absurd hpres.1.1.2.1 hf

end Genuine

end CFSG.StandardType
