module

public import CFSG.RankThree.PartOne.KLAY.SL2
public import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools

public section

namespace CFSG.RankThree.PartOne.KLAY

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {k K : Type} [Field k] [Field K]

@[expose] noncomputable def rootSL2Map (τ : Tag) (θ : Fin τ.rank → ℤ) (ι : k →+* K) :
    SL2 k →* ModGL τ K :=
  (rootSL2 τ K θ).comp (Matrix.SpecialLinearGroup.map ι)

theorem rootSL2Map_apply (θ : Fin τ.rank → ℤ) (ι : k →+* K) (A : SL2 k) :
    rootSL2Map τ θ ι A = rootSL2 τ K θ (Matrix.SpecialLinearGroup.map ι A) := rfl

theorem map_injective_SL2 (ι : k →+* K) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) ι) := by
  intro A B h
  apply Subtype.ext
  ext i j
  have := congrArg (fun X : SL2 K => (X : Matrix (Fin 2) (Fin 2) K) i j) h
  exact ι.injective (by simpa using this)

theorem rootSL2Map_injective (θ : Fin τ.rank → ℤ) (ι : k →+* K) :
    Function.Injective (rootSL2Map τ θ ι) :=
  (rootSL2_injective_of_field θ).comp (map_injective_SL2 ι)

theorem rootSL2Map_mem_adjointGroup (θ : Fin τ.rank → ℤ) (ι : k →+* K) (A : SL2 k) :
    rootSL2Map τ θ ι A ∈ adjointGroup τ K :=
  (exceptional_Lang_root_rank_one_data τ K θ).2.2.2.2.1 _

theorem map_conjSL_diagUnitOne (ι : k →+* K) (χ : kˣ) (A : SL2 k) :
    conjSL (diagUnitOne (Units.map (ι : k →* K) χ)) (Matrix.SpecialLinearGroup.map ι A) =
      Matrix.SpecialLinearGroup.map ι (conjSL (diagUnitOne χ) A) := by
  apply Subtype.ext
  ext i j
  simp only [coe_conjSL, coe_diagUnitOne, coe_diagUnitOne_inv,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

theorem rootDiagUnit_conj_rootSL2Map {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ) (ι : k →+* K)
    (a : Fin τ.rank → Kˣ) (χ : kˣ) (hχ : rootChar a θ = Units.map (ι : k →* K) χ) (A : SL2 k) :
    rootDiagUnit τ a * rootSL2Map τ θ ι A * (rootDiagUnit τ a)⁻¹ =
      rootSL2Map τ θ ι (conjSL (diagUnitOne χ) A) := by
  rw [rootSL2Map_apply, rootSL2Map_apply, rootDiagUnit_conj_rootSL2 a hθ, hχ,
    map_conjSL_diagUnitOne]

theorem rootChar_single (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  classical
  unfold rootChar
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem rootSL2_single (i : Fin τ.rank) :
    rootSL2 τ K (Pi.single i 1) = simpleRootSL2 τ K i := by
  ext A : 1
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]

theorem map_HSL (ι : k →+* K) (s : kˣ) :
    Matrix.SpecialLinearGroup.map ι (HSL s) = HSL (Units.map (ι : k →* K) s) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_HSL]

theorem rootSL2Map_single_HSL (i : Fin τ.rank) (ι : k →+* K) (s : kˣ) :
    rootSL2Map τ (Pi.single i 1) ι (HSL s) =
      rootDiagUnit τ (fun j => (Units.map (ι : k →* K) s) ^ τ.cartan i j) := by
  rw [rootSL2Map_apply, rootSL2_single, map_HSL, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit]

theorem SL2Torus.of_rootDiag {p : ℕ} {M₀ : Subgroup (ModGL τ K)} {θ : Fin τ.rank → ℤ}
    (hθ : IsRoot τ θ) (ι : k →+* K) (φ : SL2 k →* ↥M₀)
    (hφ : ∀ A, ((φ A : ↥M₀) : ModGL τ K) = rootSL2Map τ θ ι A) {T₀ : Subgroup ↥M₀}
    (hexp : ∀ t ∈ T₀, t ^ p = 1)
    (hT : ∀ t ∈ T₀, ∃ (a : Fin τ.rank → Kˣ) (χ : kˣ),
      ((t : ↥M₀) : ModGL τ K) = rootDiagUnit τ a ∧ rootChar a θ = Units.map (ι : k →* K) χ)
    (hdiag : ∀ s : kˣ, s ^ p = 1 → φ (HSL s) ∈ T₀)
    (hmove : ∃ t ∈ T₀, ∃ (a : Fin τ.rank → Kˣ) (χ : kˣ),
      ((t : ↥M₀) : ModGL τ K) = rootDiagUnit τ a ∧ rootChar a θ = Units.map (ι : k →* K) χ ∧
        χ ≠ 1) :
    SL2Torus p φ T₀ := by
  have hinj : Function.Injective φ := fun A B h =>
    rootSL2Map_injective θ ι (by rw [← hφ, ← hφ, h])
  refine ⟨hinj, hexp, ?_, hdiag, ?_⟩
  · intro t ht
    obtain ⟨a, χ, hta, hχ⟩ := hT t ht
    refine ⟨χ, fun A => ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφ, hφ, hta]
    exact rootDiagUnit_conj_rootSL2Map hθ ι a χ hχ A
  · obtain ⟨t, ht, a, χ, hta, hχ, hχ1⟩ := hmove
    refine ⟨t, ht, fun h => ?_⟩
    have h1 : t * φ (uSL 1) * t⁻¹ = φ (conjSL (diagUnitOne χ) (uSL 1)) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hφ, hφ, hta]
      exact rootDiagUnit_conj_rootSL2Map hθ ι a χ hχ _
    rw [h1, conjSL_diagUnitOne_uSL] at h
    have hu : (uSL ((χ : k) * 1) : SL2 k) = uSL 1 := hinj h
    have := congrArg (fun X : SL2 k => (X : Matrix (Fin 2) (Fin 2) k) 0 1) hu
    simp only [coe_uSL, mul_one] at this
    exact hχ1 (Units.ext (by simpa using this))

theorem rootSpan_le_centralizer_of_char_one {A : Fin τ.rank → Kˣ}
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α ∧ rootChar A α = 1) :
    rootSpan τ K S ≤ Subgroup.centralizer ({rootDiagUnit τ A} : Set (ModGL τ K)) := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h := rootDiagUnit_conj_pinnedX A (hS α hα).1 c
  rw [(hS α hα).2, Units.val_one, one_mul] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

end CFSG.RankThree.PartOne.KLAY
