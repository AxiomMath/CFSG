module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.HallHigman

public section

open Module Module.End Polynomial CFSG.SignalizerFunctorTheorem.CatalogBridge

namespace CFSG.SignalizerFunctorTheorem.NonLocal

variable {F W G : Type*} [Field F] [AddCommGroup W] [Module F W] [Group G]

theorem linearIndependent_of_distinct_weights {ι : Type*} (ρ : G →* End F W) (A : Subgroup G)
    (hA : IsMulCommutative A) (w : ι → W) (χ : ι → A → F) (hw : ∀ i, w i ≠ 0)
    (hev : ∀ i (a : A), ρ a (w i) = χ i a • w i) (hχ : Function.Injective χ) :
    LinearIndependent F w := by
  let f : A → End F W := fun a => ρ a
  have hcomm : ∀ a b : A, Commute (f a) (f b) := by
    intro a b
    show ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (mul_comm' a b)
  have hind := independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun i j φ => mapsTo_maxGenEigenspace_of_comm (hcomm j i) φ)
  have hind' : iSupIndep fun i : ι => ⨅ a : A, (f a).maxGenEigenspace (χ i a) :=
    hind.comp hχ
  refine hind'.linearIndependent _ (fun i => ?_) hw
  rw [Submodule.mem_iInf]
  intro a
  exact (f a).eigenspace_le_maxGenEigenspace (mem_eigenspace_iff.mpr (hev i a))

theorem isSemisimple_of_mem_finite (ρ : G →* End F W) (A : Subgroup G) [Finite A]
    (hinv : (Nat.card A : F) ≠ 0) (a : A) : (ρ a).IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ Nat.card A - 1) ?_ ?_
  · simpa using (Polynomial.separable_X_pow_sub_C (1 : F) hinv one_ne_zero).squarefree
  · have h1 : (a : G) ^ Nat.card A = 1 := by
      rw [← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one]
    have h2 : (ρ (a : G)) ^ Nat.card A = 1 := by rw [← map_pow, h1, map_one]
    simp [aeval_X_pow, h2]

theorem exists_jointEigenvector_apply_ne_zero [IsAlgClosed F] [FiniteDimensional F W]
    (ρ : G →* End F W) (A : Subgroup G) (hA : IsMulCommutative A) [Finite A]
    (hinv : (Nat.card A : F) ≠ 0) (T : End F W) (hT : T ≠ 0) :
    ∃ (χ : A → F) (w : W), (∀ a : A, ρ a w = χ a • w) ∧ T w ≠ 0 := by
  let f : A → End F W := fun a => ρ a
  have hss : ∀ a, (f a).IsSemisimple := isSemisimple_of_mem_finite ρ A hinv
  have hcomm : ∀ a b : A, Commute (f a) (f b) := by
    intro a b
    show ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (mul_comm' a b)
  have hspan := iSup_iInf_eigenspace_eq_top_of_commute f hss hcomm
  obtain ⟨χ, w, hw, hTw⟩ :
      ∃ (χ : A → F) (w : W), w ∈ (⨅ a, (f a).eigenspace (χ a)) ∧ T w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hT
    rw [← LinearMap.ker_eq_top, eq_top_iff, ← hspan]
    exact iSup_le fun χ w hw => LinearMap.mem_ker.mpr (hcon χ w hw)
  refine ⟨χ, w, fun a => ?_, hTw⟩
  exact mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hw a)

end CFSG.SignalizerFunctorTheorem.NonLocal
