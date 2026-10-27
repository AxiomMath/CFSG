module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Planes
public import CFSG.LinearAlgebra.S81JSchurEq
import TauCeti.RepresentationTheory.Unipotent.Solvable

public section

namespace CFSG.LinearAlgebra.S81JSchur

open Module Submodule

variable {K : Type} [Field K]

private theorem sub_one_mem_flag {V : Type*} [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) {T : V →ₗ[K] V}
    (hT : (LinearMap.toMatrixAlgEquiv b T).IsUpperUnitriangular) (i : ℕ) {v : V}
    (hv : v ∈ span K (b '' {j | (j : ℕ) < i + 1})) :
    (T - 1) v ∈ span K (b '' {j | (j : ℕ) < i}) := by
  obtain ⟨hTu, hTd⟩ := (Matrix.isUpperUnitriangular_def _).mp hT
  have hle : span K (b '' {j | (j : ℕ) < i + 1}) ≤
      (span K (b '' {j | (j : ℕ) < i})).comap (T - 1) := by
    rw [span_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, mem_comap, Basis.mem_span_image]
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

private theorem commute_of_mem_span {V : Type*} [AddCommGroup V] [Module K V]
    {S : Set (V →ₗ[K] V)}
    (hS : ∀ x ∈ S, ∀ y ∈ S, Commute x y) {y z : V →ₗ[K] V} (hy : y ∈ span K S)
    (hz : z ∈ span K S) : Commute y z := by
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

open CFSG.RankThree.GF2n.Smith81.A5Cube in
private theorem mem_UnipGL_iff' {S : Submodule K (Fin 6 → K)} {g : GL (Fin 6) K} :
    g ∈ UnipGL K S ↔ ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 ∧
      (∀ v, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v - v ∈ S) ∧
      ∀ s ∈ S, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec s = s :=
  Iff.rfl

open CFSG.RankThree.GF2n.Smith81.A5Cube in
theorem card_unipGL_le [Finite K] {W : Submodule K (Fin 6 → K)} (hW : finrank K W = 3) :
    Nat.card ↥(UnipGL K W) ≤ Nat.card K ^ 9 := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have hCfin : finrank K C = 3 := by
    have h2 : finrank K W + finrank K C = finrank K (Fin 6 → K) :=
      Submodule.finrank_add_eq_of_isCompl hC
    rw [Module.finrank_fin_fun K, hW] at h2
    omega
  let T : ↥(UnipGL K W) → ((Fin 6 → K) →ₗ[K] (Fin 6 → K)) := fun g =>
    Matrix.mulVecLin ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) - LinearMap.id
  have hT : ∀ g v, T g v = ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v - v :=
    fun g v => rfl
  let f : ↥(UnipGL K W) → (C →ₗ[K] W) := fun g =>
    LinearMap.codRestrict W ((T g).comp C.subtype) (fun c => by
      rw [LinearMap.comp_apply, hT]
      exact (mem_UnipGL_iff'.1 g.2).2.1 (c : Fin 6 → K))
  have hinj : Function.Injective f := by
    intro g g' hgg'
    have hc : ∀ c ∈ C, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec c =
        ((g' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec c := by
      intro c hc0
      have h1 := congrArg Subtype.val (LinearMap.congr_fun hgg' ⟨c, hc0⟩)
      have h : ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec c - c =
          ((g' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec c - c := h1
      exact sub_left_inj.mp h
    have hw : ∀ w ∈ W, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec w =
        ((g' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec w := by
      intro w hw0
      rw [(mem_UnipGL_iff'.1 g.2).2.2 w hw0, (mem_UnipGL_iff'.1 g'.2).2.2 w hw0]
    have hall : ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        ((g' : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      have hv : v ∈ W ⊔ C := by
        rw [hC.sup_eq_top]
        trivial
      obtain ⟨w, hw0, c, hc0, rfl⟩ := mem_sup.mp hv
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_add, Matrix.mulVec_add,
        hw w hw0, hc c hc0]
    exact Subtype.ext (Units.ext hall)
  haveI : Finite (C →ₗ[K] W) := Module.finite_of_finite K
  calc Nat.card ↥(UnipGL K W) ≤ Nat.card (C →ₗ[K] W) := Nat.card_le_card_of_injective f hinj
    _ = Nat.card K ^ finrank K (C →ₗ[K] W) :=
      Module.natCard_eq_pow_finrank (K := K) (V := C →ₗ[K] W)
    _ = Nat.card K ^ 9 := by simp only [Module.finrank_linearMap, hCfin, hW]

open CFSG.RankThree.GF2n.Smith81.A5Cube in
theorem lemmaJ [Finite K] [CharP K 2] {E : Subgroup (GL (Fin 6) K)}
    (hE : CFSG.Open.IsElemAbelian 2 E) (h : Nat.card K ^ 9 ≤ Nat.card E) :
    ∃ W : Submodule K (Fin 6 → K), finrank K W = 3 ∧ E = UnipGL K W := by
  classical
  let ρ : Representation K E (Fin 6 → K) :=
    (MonoidHomClass.toMonoidHom (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6))).comp
      ((Units.coeHom (Matrix (Fin 6) (Fin 6) K)).comp E.subtype)
  have hρ : Function.Injective ρ := by
    intro a a' ha
    apply Subtype.ext
    apply Units.ext
    exact (Matrix.toLinAlgEquiv' (R := K) (n := Fin 6)).injective ha
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  have h2 : ∀ a : E, a * a = 1 := by
    intro a
    apply Subtype.ext
    have := hE.2 a a.2
    rw [pow_two] at this
    simpa using this
  have hsq : ∀ a, (ρ a - 1) * (ρ a - 1) = 0 := by
    intro a
    have h' : ρ a * ρ a = 1 := by rw [← map_mul, h2, map_one]
    have htwo : (2 : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) = 0 := by
      rw [← map_ofNat (algebraMap K ((Fin 6 → K) →ₗ[K] (Fin 6 → K))) 2, CharTwo.two_eq_zero,
        map_zero]
    have hone : (1 : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) + 1 = 0 := by
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
  set S : Set ((Fin 6 → K) →ₗ[K] (Fin 6 → K)) := Set.range fun a => ρ a - 1 with hS
  set N : Submodule K ((Fin 6 → K) →ₗ[K] (Fin 6 → K)) := span K S with hN
  set F : ℕ → Submodule K (Fin 6 → K) := fun i => span K (b '' {j | (j : ℕ) < i}) with hFdef
  have hF0 : F 0 = ⊥ := by
    simp only [hFdef, Nat.not_lt_zero, Set.setOf_false, Set.image_empty, span_empty]
  have hFm : F m = ⊤ := by
    have : {j : Fin m | (j : ℕ) < m} = Set.univ := Set.eq_univ_of_forall fun j => j.isLt
    simp only [hFdef, this, Set.image_univ, b.span_eq]
  have hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i := by
    intro y hy i v hv
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact sub_one_mem_flag b (hb a) i hv
    | zero => simp
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, Commute x y := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    have hρc : Commute (ρ a) (ρ a') := by
      rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hcomm]
    exact (hρc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  have hcommN : ∀ y ∈ N, ∀ z ∈ N, Commute y z := fun y hy z hz =>
    commute_of_mem_span hcommS hy hz
  have hinjA : Function.Injective fun a : E => (⟨ρ a - 1, subset_span ⟨a, rfl⟩⟩ : N) := by
    intro a a' ha
    apply hρ
    have := congrArg Subtype.val ha
    simpa using this
  haveI : Finite ((Fin 6 → K) →ₗ[K] (Fin 6 → K)) := Module.finite_of_finite K
  have hcardE : Nat.card E ≤ Nat.card K ^ finrank K N :=
    calc Nat.card E ≤ Nat.card N := Nat.card_le_card_of_injective _ hinjA
      _ = Nat.card K ^ finrank K N := Module.natCard_eq_pow_finrank (K := K) (V := N)
  have h9 : 9 ≤ finrank K N := by
    have h1 : Nat.card K ^ 9 ≤ Nat.card K ^ finrank K N := h.trans hcardE
    exact (pow_le_pow_iff_right₀ (Finite.one_lt_card : 1 < Nat.card K)).mp h1
  obtain ⟨-, W, hW3, hWN, hWN0⟩ :=
    schur_eq_case (V := Fin 6 → K) (Module.finrank_fin_fun K) hcommN hF0 hFm hF h9
  refine ⟨W, hW3, ?_⟩
  have hle : E ≤ UnipGL K W := by
    intro e he
    have hy : ρ ⟨e, he⟩ - 1 ∈ N := subset_span ⟨⟨e, he⟩, rfl⟩
    have he2 : e ^ 2 = 1 := hE.2 e he
    have hMM : ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
        ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Units.val_mul, ← pow_two, he2, Units.val_one]
    have hdd : ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det *
        ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      rw [← Matrix.det_mul, hMM, Matrix.det_one]
    have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
    have hdet : ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det = 1 := by
      have hsq1 : (((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det - 1) *
          (((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det - 1) = 0 := by
        linear_combination hdd +
          (1 - ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).det) * h2K
      exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq1)
    have hact : ∀ v, ρ ⟨e, he⟩ v = ((e : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).mulVec v :=
      fun v => Matrix.toLinAlgEquiv'_apply _ v
    refine mem_UnipGL_iff'.2 ⟨hdet, fun v => ?_, fun s hs => ?_⟩
    · have h1 := hWN _ hy v
      rw [LinearMap.sub_apply, Module.End.one_apply, hact] at h1
      exact h1
    · have h1 := hWN0 _ hy s hs
      rw [LinearMap.sub_apply, Module.End.one_apply, hact, sub_eq_zero] at h1
      exact h1
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K))
      (fun a b h => Units.ext h)
  exact Subgroup.eq_of_le_of_card_ge hle ((card_unipGL_le hW3).trans h)

end CFSG.LinearAlgebra.S81JSchur
