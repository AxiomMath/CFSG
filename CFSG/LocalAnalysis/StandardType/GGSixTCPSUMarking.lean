module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.StandardType CFSG.StandardType.InnerDiagSU

section Marking

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}

theorem tcMarkingUnitary_of_conj (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) {m : ℕ}
    (hm : 3 ≤ m) {G : Type} [Group G] (ψ : SU (unitaryInvolution F 2 f) (m + 1) →* G)
    (hker : ψ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) (m + 1)))
    (Bs : Subgroup G) (hBN : Bs ≤ Subgroup.normalizer (ψ.range : Set G))
    (hact : ∀ b ∈ Bs, ∃ (A : GL (Fin (m + 1)) F) (hA : IsJUnitary (unitaryInvolution F 2 f) A),
      ∀ u, b⁻¹ * ψ u * b = ψ (conjSU A hA u)) :
    GGInnerDiagOn Bs ψ.range := by
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
  have key : ∀ c ∈ Bs,
        ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk H) (LargeEvenGUSet (Fin (m + 1)) F (2 ^ f)),
          LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ := by
    intro c hc
    obtain ⟨A, hA, hAc⟩ := hact c hc
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
        Bs ≤ Subgroup.normalizer (ψ.range : Set G) ∧ ∀ c ∈ Bs,
          ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = c⁻¹ * l * c) φ :=
    ⟨F, inferInstance, inferInstance, hF, hsimple, hnonab, θ, hBN, key⟩
  exact ⟨hcomm, ⟨.twA, m, f⟩, ⟨hf, (by omega : 2 ≤ m), hm1⟩, hraw⟩

end Marking

end CFSG.StandardType.TableCRes
