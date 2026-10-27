module

public import CFSG.RankThree.GF2n.Smith81.S81UElem
public import CFSG.LinearAlgebra.S81JSchurEq
import TauCeti.RepresentationTheory.Unipotent.Solvable

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG CFSG.Open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary Module
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.U6Cube

variable {F : Type} [Field F]

private theorem s81v_sub_one_mem_flag {V : Type*} [AddCommGroup V] [Module F V] {n : ℕ}
    (b : Basis (Fin n) F V) {T : V →ₗ[F] V}
    (hT : (LinearMap.toMatrixAlgEquiv b T).IsUpperUnitriangular) (i : ℕ) {v : V}
    (hv : v ∈ Submodule.span F (b '' {j | (j : ℕ) < i + 1})) :
    (T - 1) v ∈ Submodule.span F (b '' {j | (j : ℕ) < i}) := by
  obtain ⟨hTu, hTd⟩ := (Matrix.isUpperUnitriangular_def _).mp hT
  have hle : Submodule.span F (b '' {j | (j : ℕ) < i + 1}) ≤
      (Submodule.span F (b '' {j | (j : ℕ) < i})).comap (T - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, Basis.mem_span_image]
    intro k hk
    rw [Finset.mem_coe, Finsupp.mem_support_iff] at hk
    simp only [Set.mem_setOf_eq] at hj ⊢
    by_contra hki
    apply hk
    have hjk : j ≤ k := by
      rw [Fin.le_iff_val_le_val]
      omega
    rcases hjk.lt_or_eq with hlt | heq
    · have h0 : LinearMap.toMatrixAlgEquiv b T k j = 0 := hTu (show id j < id k from hlt)
      rw [LinearMap.toMatrixAlgEquiv_apply] at h0
      rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, h0, Module.End.one_apply,
        Basis.repr_self, Finsupp.single_apply, if_neg hlt.ne, sub_zero]
    · subst heq
      have h1 : LinearMap.toMatrixAlgEquiv b T j j = 1 := hTd j
      rw [LinearMap.toMatrixAlgEquiv_apply] at h1
      rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, h1, Module.End.one_apply,
        Basis.repr_self, Finsupp.single_eq_same, sub_self]
  exact hle hv

private theorem s81v_commute_of_mem_span {V : Type*} [AddCommGroup V] [Module F V]
    {S : Set (V →ₗ[F] V)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, Commute x y) {y z : V →ₗ[F] V} (hy : y ∈ Submodule.span F S)
    (hz : z ∈ Submodule.span F S) : Commute y z := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    induction hz using Submodule.span_induction with
    | mem w hw => exact hS x hx w hw
    | zero => exact Commute.zero_right _
    | add a c _ _ ha hc => exact ha.add_right hc
    | smul r a _ ha => exact ha.smul_right r
  | zero => exact Commute.zero_left _
  | add a c _ _ ha hc => exact ha.add_left hc
  | smul r a _ ha => exact ha.smul_left r

private theorem s81v_finrank_eq_three {N : Submodule F ((Fin 6 → F) →ₗ[F] (Fin 6 → F))}
    {W : Submodule F (Fin 6 → F)} (hW1 : ∀ y ∈ N, ∀ w ∈ W, y w = 0)
    (hW2 : ∀ y ∈ N, ∀ v, y v ∈ W) (h9 : 9 ≤ finrank F N) (hle : finrank F W ≤ 3) :
    finrank F W = 3 := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hdim : finrank F W + finrank F C = 6 := by
    have h := Submodule.finrank_add_eq_of_isCompl hC
    rwa [Module.finrank_fin_fun] at h
  let Φ : N →ₗ[F] (C →ₗ[F] W) :=
    { toFun := fun y =>
        { toFun := fun c => ⟨(y : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) c, hW2 y y.2 c⟩
          map_add' := fun c c' =>
            Subtype.ext (map_add (y : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) (c : Fin 6 → F) (c' : Fin 6 → F))
          map_smul' := fun r c =>
            Subtype.ext (map_smul (y : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) r (c : Fin 6 → F)) }
      map_add' := fun y z => LinearMap.ext fun c => Subtype.ext rfl
      map_smul' := fun r y => LinearMap.ext fun c => Subtype.ext rfl }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hyC : ∀ c ∈ C, (y : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) c = 0 := by
      intro c hc
      exact congrArg Subtype.val (LinearMap.congr_fun hy ⟨c, hc⟩)
    refine Subtype.ext (LinearMap.ext fun v => ?_)
    have hv : v ∈ W ⊔ C := by
      rw [hC.sup_eq_top]
      trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
    simp [map_add, hyC c hc, hW1 _ y.2 w hw]
  have hle2 : finrank F N ≤ finrank F (C →ₗ[F] W) :=
    LinearMap.finrank_le_finrank_of_injective hΦ
  rw [Module.finrank_linearMap] at hle2
  have hprod : 9 ≤ finrank F C * finrank F W := h9.trans hle2
  generalize finrank F W = a at hdim hprod hle ⊢
  generalize finrank F C = c at hdim hprod
  interval_cases a <;> omega

theorem exists_schur_space [Finite F] [CharP F 2] {E : Subgroup (GL (Fin 6) F)}
    (hE : IsElemAbelian 2 E) (h9 : 9 ≤ finrank F (nilpSpan E)) :
    ∃ W : Submodule F (Fin 6 → F), finrank F W = 3 ∧
      (∀ e ∈ E, ∀ v, ((e : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v - v ∈ W) ∧
      (∀ e ∈ E, ∀ w ∈ W, ((e : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec w = w) ∧
      W ≤ Submodule.span F {u | ∃ e ∈ E, ∃ v,
        u = ((e : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v - v} := by
  let ρ : Representation F E (Fin 6 → F) :=
    (MonoidHomClass.toMonoidHom (Matrix.toLinAlgEquiv' (R := F) (n := Fin 6))).comp
      ((Units.coeHom (Matrix (Fin 6) (Fin 6) F)).comp E.subtype)
  have hact : ∀ (a : E) (v : Fin 6 → F),
      ρ a v = ((a : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v :=
    fun a v => Matrix.toLinAlgEquiv'_apply _ v
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have h2 : ∀ a : E, a * a = 1 := by
    intro a
    apply Subtype.ext
    have := hE.2 a a.2
    rw [pow_two] at this
    simpa using this
  have hsq : ∀ a : E, (ρ a - 1) * (ρ a - 1) = 0 := by
    intro a
    have h' : ρ a * ρ a = 1 := by rw [← map_mul, h2, map_one]
    have htwo : (2 : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) = 0 := by
      rw [← map_ofNat (algebraMap F ((Fin 6 → F) →ₗ[F] (Fin 6 → F))) 2, CharTwo.two_eq_zero,
        map_zero]
    have hone : (1 : (Fin 6 → F) →ₗ[F] (Fin 6 → F)) + 1 = 0 := by
      rw [one_add_one_eq_two, htwo]
    have hX : ρ a + ρ a = 0 := by
      rw [← two_mul, htwo, zero_mul]
    calc (ρ a - 1) * (ρ a - 1) = ρ a * ρ a - ρ a - ρ a + 1 := by
          simp only [sub_mul, mul_sub, mul_one, one_mul]
          abel
      _ = 1 - ρ a - ρ a + 1 := by rw [h']
      _ = (1 + 1) - (ρ a + ρ a) := by abel
      _ = 0 := by rw [hone, hX, sub_zero]
  obtain ⟨m, b, hb⟩ := ρ.exists_basis_isUpperUnitriangular_of_isUnipotent
    (fun a => ⟨2, by rw [pow_two]; exact hsq a⟩)
  set S : Set ((Fin 6 → F) →ₗ[F] (Fin 6 → F)) := Set.range fun a : E => ρ a - 1 with hS
  set N : Submodule F ((Fin 6 → F) →ₗ[F] (Fin 6 → F)) := Submodule.span F S with hN
  set Fl : ℕ → Submodule F (Fin 6 → F) :=
    fun i => Submodule.span F (b '' {j | (j : ℕ) < i}) with hFl
  have hFl0 : Fl 0 = ⊥ := by
    simp only [hFl, Nat.not_lt_zero, Set.setOf_false, Set.image_empty, Submodule.span_empty]
  have hFl6 : Fl m = ⊤ := by
    have : {j : Fin m | (j : ℕ) < m} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    simp only [hFl, this, Set.image_univ, b.span_eq]
  have hFlN : ∀ y ∈ N, ∀ i, ∀ v ∈ Fl (i + 1), y v ∈ Fl i := by
    intro y hy i v hv
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact s81v_sub_one_mem_flag b (hb a) i hv
    | zero => simp
    | add x z _ _ hx hz => exact Submodule.add_mem _ hx hz
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    have hρc : Commute (ρ a) (ρ a') := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hcomm]
    exact (hρc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hcommN : ∀ y ∈ N, ∀ z ∈ N, Commute y z := fun y hy z hz =>
    s81v_commute_of_mem_span hcommS hy hz
  have hfun : ∀ a : E, Matrix.toLin' (nilpOf ((a : GL (Fin 6) F))) = ρ a - 1 := by
    intro a
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, LinearMap.sub_apply, Module.End.one_apply, hact]
    simp only [nilpOf, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hNeq : N = Submodule.map
      (Matrix.toLin' : Matrix (Fin 6) (Fin 6) F ≃ₗ[F] ((Fin 6 → F) →ₗ[F] (Fin 6 → F))).toLinearMap
      (nilpSpan E) := by
    show Submodule.span F S = _
    rw [nilpSpan, Submodule.map_span, ← Set.range_comp, hS]
    congr 1
    congr 1
    funext a
    exact (hfun a).symm
  have hfinN : finrank F N = finrank F (nilpSpan E) := by
    rw [hNeq]
    exact LinearEquiv.finrank_map_eq _ _
  have h9N : 9 ≤ finrank F N := by
    rw [hfinN]
    exact h9
  obtain ⟨-, W₁, hW₁3, hW₁N, hW₁N0⟩ :=
    CFSG.LinearAlgebra.S81JSchur.schur_eq_case (V := Fin 6 → F) (Module.finrank_fin_fun F)
      hcommN hFl0 hFl6 hFlN h9N
  set W : Submodule F (Fin 6 → F) := Submodule.span F {u | ∃ e ∈ E, ∃ v,
    u = ((e : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v - v} with hW
  have hgen : ∀ e ∈ E, ∀ v, ((e : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec v - v ∈ W :=
    fun e he v => Submodule.subset_span ⟨e, he, v, rfl⟩
  have hWW₁ : W ≤ W₁ := by
    rw [hW, Submodule.span_le]
    rintro u ⟨e, he, v, rfl⟩
    have hy : ρ ⟨e, he⟩ - 1 ∈ N := Submodule.subset_span ⟨⟨e, he⟩, rfl⟩
    have h := hW₁N _ hy v
    rw [LinearMap.sub_apply, Module.End.one_apply, hact] at h
    exact h
  have hW2 : ∀ y ∈ N, ∀ v, y v ∈ W := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro v
      show (ρ a - 1) v ∈ W
      rw [LinearMap.sub_apply, Module.End.one_apply, hact]
      exact hgen a.1 a.2 v
    | zero => intro v; simp
    | add x z _ _ hx hz =>
      intro v
      rw [LinearMap.add_apply]
      exact Submodule.add_mem _ (hx v) (hz v)
    | smul r x _ hx =>
      intro v
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem _ r (hx v)
  have hW1 : ∀ y ∈ N, ∀ w ∈ W, y w = 0 := fun y hy w hw => hW₁N0 y hy w (hWW₁ hw)
  have hWle : finrank F W ≤ 3 := (Submodule.finrank_mono hWW₁).trans_eq hW₁3
  have hW3 : finrank F W = 3 := s81v_finrank_eq_three hW1 hW2 h9N hWle
  refine ⟨W, hW3, fun e he v => hgen e he v, fun e he w hw => ?_, le_rfl⟩
  have hy : ρ ⟨e, he⟩ - 1 ∈ N := Submodule.subset_span ⟨⟨e, he⟩, rfl⟩
  have h := hW₁N0 _ hy w (hWW₁ hw)
  rw [LinearMap.sub_apply, Module.End.one_apply, hact, sub_eq_zero] at h
  exact h

end CFSG.RankThree.GF2n.Smith81.S81V
