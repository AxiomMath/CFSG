module

public import CFSG.Quasithin.Background.G13Perm
public import CFSG.Quasithin.Background.G1Half

public section

open Matrix CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace CFSG.Quasithin.G1

variable {F : Type*} [Field F] {n : ℕ} {i j k : Fin n}

section Local

variable [CharP F 2] {U : Type*} [AddCommGroup U]
  [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]
  {φ : Submodule F (Fin n → F) → AddSubgroup U}

omit [CharP F 2] in
theorem Vi_ne_Vi (hij : i ≠ j) : Vi F n i ≠ Vi F n j := by
  intro h
  have h1 : (Pi.single i 1 : Fin n → F) ∈ Vi F n j := by
    rw [← h]
    exact Submodule.mem_span_singleton_self _
  have h2 := mem_Vi.1 h1 i hij
  simp at h2

theorem actSub_wS_Vi (hij : i ≠ j) : actSub (wS F hij) (Vi F n i) = Vi F n j := by
  have hle : actSub (wS F hij) (Vi F n i) ≤ Vi F n j := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_actSub.1 hv
    rw [mem_Vi] at hw ⊢
    intro l hl
    rw [wS_smul]
    refine hw _ fun h => hl ?_
    have := congrArg (Equiv.swap i j) h
    simpa using this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := isPoint_actSub (wS F hij) (isPoint_Vi (F := F) (n := n) i)
  have h2 := isPoint_Vi (F := F) (n := n) j
  unfold IsPoint at h1 h2
  omega

theorem phi_Vi_eq (hφ : G13Hyp F n U φ) (hij : i ≠ j) :
    φ (Vi F n j) = (φ (Vi F n i)).map (actU (wS F hij)) := by
  have h := hφ.equivariant (wS F hij) (Vi F n i) (isPoint_Vi i)
  rwa [actSub_wS_Vi] at h

@[expose] def fixSubgroup (Y : AddSubgroup U) : Subgroup (Matrix.SpecialLinearGroup (Fin n) F) where
  carrier := {g | ∀ y ∈ Y, g • y = y}
  one_mem' := fun y _ => one_smul _ y
  mul_mem' := fun {g h} hg hh y hy => by rw [mul_smul, hh y hy, hg y hy]
  inv_mem' := fun {g} hg y hy => by
    rw [inv_smul_eq_iff]
    exact (hg y hy).symm

omit [CharP F 2] in
theorem root_smul_of_ne (hφ : G13Hyp F n U φ) {a b : Fin n} (hab : a ≠ b) (hkb : k ≠ b)
    {t : Matrix.SpecialLinearGroup (Fin n) F} (ht : t ∈ rootGroup (Vi F n a) (Vhat F n b))
    {y : U} (hy : y ∈ φ (Vi F n k)) : t • y = y :=
  hφ.le_fixU (Vi F n a) (Vhat F n b) (isFlag_Vi_Vhat hab) (Vi F n k) (isPoint_Vi k)
    (isFlag_Vi_Vhat hkb).2.2 hy t ht

omit [CharP F 2] in
theorem Lij_smul_of_ne (hφ : G13Hyp F n U φ) {a b : Fin n} (hab : a ≠ b) (hka : k ≠ a)
    (hkb : k ≠ b) {g : Matrix.SpecialLinearGroup (Fin n) F} (hg : g ∈ Lij F a b) {y : U}
    (hy : y ∈ φ (Vi F n k)) : g • y = y := by
  have hle : Lij F a b ≤ fixSubgroup (φ (Vi F n k)) :=
    sup_le (fun t ht y hy => root_smul_of_ne hφ hab hkb ht hy)
      (fun t ht y hy => root_smul_of_ne hφ hab.symm hka ht hy)
  exact hle hg y hy

theorem wS_smul_of_ne (hφ : G13Hyp F n U φ) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {y : U}
    (hy : y ∈ φ (Vi F n k)) : wS F hij • y = y :=
  Lij_smul_of_ne hφ hij hki hkj (wS_mem_Lij hij) hy

end Local

section Pair

variable {U : Type*} [AddCommGroup U]
  [DistribMulAction (Matrix.SpecialLinearGroup (Fin n) F) U]

theorem embSL_e12 (hij : i ≠ j) (c : F) :
    embSL hij (e12 c) = Matrix.SpecialLinearGroup.transvection hij c := by
  apply Subtype.ext
  rw [embSL_coe, Matrix.SpecialLinearGroup.transvection_coe]
  have h := emb_transvection hij 0 1 zero_ne_one c
  have he : (e12 c : Matrix (Fin 2) (Fin 2) F) = Matrix.transvection 0 1 c := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.transvection]
  rw [he, h]
  simp [Matrix.transvection]

theorem actSub_embSL_of_lower_left_zero (hij : i ≠ j) {B : Matrix.SpecialLinearGroup (Fin 2) F}
    (hB : B.1 1 0 = 0) : actSub (embSL hij B) (Vi F n i) = Vi F n i := by
  have hle : actSub (embSL hij B) (Vi F n i) ≤ Vi F n i := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := mem_actSub.1 hv
    rw [mem_Vi] at hw ⊢
    intro l hl
    show ((embSL hij B : Matrix (Fin n) (Fin n) F) *ᵥ w) l = 0
    rw [embSL_coe, emb_mulVec, blockMap_apply]
    have hj := hw j hij.symm
    by_cases hlj : l = j
    · subst hlj
      simp [hl, hB, hj]
    · simp [hl, hlj, hw l hl]
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have h1 := isPoint_actSub (embSL hij B) (isPoint_Vi (F := F) (n := n) i)
  have h2 := isPoint_Vi (F := F) (n := n) i
  unfold IsPoint at h1 h2
  omega

variable (F) in
@[expose, instance_reducible] noncomputable def pairAct (hij : i ≠ j) :
    DistribMulAction (Matrix.SpecialLinearGroup (Fin 2) F) U :=
  DistribMulAction.compHom U (embSL hij)

variable [CharP F 2] {φ : Submodule F (Fin n → F) → AddSubgroup U}

theorem G13Hyp.pre (hφ : G13Hyp F n U φ) (hij : i ≠ j) :
    @G13Pre F _ _ U _ (pairAct F hij) (φ (Vi F n i)) := by
  let _ := pairAct F (U := U) hij
  refine ⟨fun d y hy => ?_, fun c y hy => ?_, fun c u => ?_, fun z hz hwz => ?_⟩
  · have hg := hφ.equivariant (embSL hij (dgm d)) (Vi F n i) (isPoint_Vi i)
    rw [actSub_embSL_of_lower_left_zero hij (by simp)] at hg
    show embSL hij (dgm d) • y ∈ φ (Vi F n i)
    rw [hg]
    exact ⟨y, hy, rfl⟩
  · show embSL hij (e12 c) • y = y
    rw [embSL_e12]
    exact root_smul_of_ne hφ hij hij (T_mem_Rij hij c) hy
  · show embSL hij (e12 c) • u - u ∈ φ (Vi F n i)
    rw [embSL_e12]
    exact hφ.commU_le _ _ (isFlag_Vi_Vhat hij)
      (AddSubgroup.subset_closure ⟨_, T_mem_Rij hij c, u, rfl⟩)
  · have h1 := phi_Vi_eq hφ hij
    have h2 : wS F hij • z ∈ φ (Vi F n j) := by
      rw [h1]
      exact ⟨z, hz, rfl⟩
    have h3 := hφ.disjoint (Vi F n i) (Vi F n j) (isPoint_Vi i) (isPoint_Vi j) (Vi_ne_Vi hij)
    have h4 : wS F hij • z ∈ φ (Vi F n i) ⊓ φ (Vi F n j) := ⟨hwz, h2⟩
    rw [h3] at h4
    have h5 : wS F hij • z = 0 := AddSubgroup.mem_bot.1 h4
    have h6 : wS F hij • wS F hij • z = wS F hij • (0 : U) := by rw [h5]
    rwa [wS_smul_smul, smul_zero] at h6

theorem exists_module (hφ : G13Hyp F n U φ) (hsq : ∀ u : U, u + u = 0) (hij : i ≠ j) :
    ∃ _ : Module F ↥(φ (Vi F n i)), ∀ (c : F) (y : ↥(φ (Vi F n i))),
      ((c • y : ↥(φ (Vi F n i))) : U) =
        Matrix.SpecialLinearGroup.transvection hij c • wS F hij • (y : U) - wS F hij • (y : U) := by
  let _ := pairAct F (U := U) hij
  have hpre : G13Pre F (φ (Vi F n i)) := hφ.pre hij
  refine ⟨hpre.module hsq, fun c y => ?_⟩
  show th c (y : U) = _
  show embSL hij (e12 c) • embSL hij (wmat F) • (y : U) - embSL hij (wmat F) • (y : U) = _
  rw [embSL_e12]
  rfl

end Pair

end CFSG.Quasithin.G1
