module

public import CFSG.ClassicalGroups.Orthogonal.Models
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus)

@[expose] def stdP0 (F : Type) [Field F] (b c : F) : HypPair (quadMinus 3 F b c) :=
  minusPair F b c (⟨0, by norm_num⟩ : Fin (3 - 1))

@[expose] def stdP1 (F : Type) [Field F] (b c : F) : HypPair (quadMinus 3 F b c) :=
  minusPair F b c (⟨1, by norm_num⟩ : Fin (3 - 1))

theorem stdP0_orth_stdP1 (F : Type) [Field F] (b c : F) :
    (stdP0 F b c).Orth (stdP1 F b c) :=
  minusPair_orth (by simp)

@[expose] def PerpIsMinusTwo {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} (P : HypPair Q) (b c : F) : Prop :=
  ∃ φ : ↥P.perp ≃ₗ[F] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F),
    ∀ x, quadMinus 2 F b c (φ x) = Q.restrict P.perp x

private theorem mem_perp_stdP0_T2J2 (F : Type) [Field F] (b c : F)
    {x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F} :
    x ∈ (stdP0 F b c).perp ↔ x (Sum.inr (Sum.inl 0)) = 0 ∧ x (Sum.inl 0) = 0 := by
  rw [HypPair.mem_perp]
  constructor
  · rintro ⟨h1, h2⟩
    rw [stdP0, minusPair_e, polar_single_inl_quadMinus] at h1
    rw [stdP0, minusPair_f, polar_single_inr_quadMinus] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [stdP0, minusPair_e, polar_single_inl_quadMinus]; exact h1,
      by rw [stdP0, minusPair_f, polar_single_inr_quadMinus]; exact h2⟩

private noncomputable def projMinusTwo_T2J2 (F : Type) [Field F] :
    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) →ₗ[F]
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) :=
  LinearMap.pi (fun j =>
    match j with
    | Sum.inl _ => LinearMap.proj (Sum.inl (⟨1, by norm_num⟩ : Fin (3 - 1)))
    | Sum.inr (Sum.inl _) =>
        LinearMap.proj (Sum.inr (Sum.inl (⟨1, by norm_num⟩ : Fin (3 - 1))))
    | Sum.inr (Sum.inr k) => LinearMap.proj (Sum.inr (Sum.inr k)))

private noncomputable def insMinusTwo_T2J2 (F : Type) [Field F] :
    (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) →
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) :=
  fun y j =>
    match j with
    | Sum.inl i => if i = 0 then 0 else y (Sum.inl (0 : Fin (2 - 1)))
    | Sum.inr (Sum.inl i) => if i = 0 then 0 else y (Sum.inr (Sum.inl (0 : Fin (2 - 1))))
    | Sum.inr (Sum.inr k) => y (Sum.inr (Sum.inr k))

private theorem insMinusTwo_mem_T2J2 (F : Type) [Field F] (b c : F)
    (y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) :
    insMinusTwo_T2J2 F y ∈ (stdP0 F b c).perp := by
  rw [mem_perp_stdP0_T2J2]
  exact ⟨by simp [insMinusTwo_T2J2], by simp [insMinusTwo_T2J2]⟩

private noncomputable def perpEquivMinusTwo_T2J2 (F : Type) [Field F] (b c : F) :
    ↥(stdP0 F b c).perp ≃ₗ[F] (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → F) := by
  refine ⟨(projMinusTwo_T2J2 F).comp (stdP0 F b c).perp.subtype,
    fun y => ⟨insMinusTwo_T2J2 F y, insMinusTwo_mem_T2J2 F b c y⟩, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext j
    rcases j with i | i
    · fin_cases i
      · have hx := (mem_perp_stdP0_T2J2 F b c).mp x.2
        simp [insMinusTwo_T2J2, hx.2]
      · simp [projMinusTwo_T2J2, insMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]
    · rcases i with i | k
      · fin_cases i
        · have hx := (mem_perp_stdP0_T2J2 F b c).mp x.2
          simp [insMinusTwo_T2J2, hx.1]
        · simp [projMinusTwo_T2J2, insMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]
      · simp [projMinusTwo_T2J2, insMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]
  · intro y
    funext j
    rcases j with i | i
    · fin_cases i <;>
        simp [projMinusTwo_T2J2, insMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]
    · rcases i with i | k
      · fin_cases i <;>
          simp [projMinusTwo_T2J2, insMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]
      · simp [projMinusTwo_T2J2, insMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]

private theorem quadMinus_proj_T2J2 (F : Type) [Field F] (b c : F)
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) (hx : x ∈ (stdP0 F b c).perp) :
    quadMinus 2 F b c (projMinusTwo_T2J2 F x) = quadMinus 3 F b c x := by
  obtain ⟨h0, h1⟩ := (mem_perp_stdP0_T2J2 F b c).mp hx
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply, CFSG.LieType.Universal.Spin.quadMinus_apply,
    Fin.sum_univ_one (fun i : Fin 1 => (projMinusTwo_T2J2 F x) (Sum.inl i) *
      (projMinusTwo_T2J2 F x) (Sum.inr (Sum.inl i))),
    Fin.sum_univ_two (fun i : Fin 2 => x (Sum.inl i) * x (Sum.inr (Sum.inl i)))]
  simp only [projMinusTwo_T2J2, LinearMap.pi_apply, LinearMap.proj_apply]
  rw [h0, h1]
  have hidx : (⟨1, projMinusTwo_T2J2._proof_1⟩ : Fin (3 - 1)) = 1 := Fin.ext rfl
  rw [hidx]
  ring

theorem perpIsMinusTwo_stdP0 (F : Type) [Field F] (b c : F) :
    PerpIsMinusTwo (stdP0 F b c) b c := by
  refine ⟨perpEquivMinusTwo_T2J2 F b c, fun x => ?_⟩
  exact quadMinus_proj_T2J2 F b c x.1 x.2

instance instFiniteGomQuadMinusThree (F : Type) [Field F] [Finite F] (b c : F) :
    Finite (Gom (quadMinus 3 F b c)) :=
  haveI : Finite (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := inferInstance
  haveI : Finite ((Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) ≃ₗ[F]
      (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F)) := DFunLike.finite _
  inferInstance

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
