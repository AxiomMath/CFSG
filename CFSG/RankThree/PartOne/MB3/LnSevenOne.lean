module

public import CFSG.RankThree.PartOne.MB3.LnSevenMat
public import CFSG.RankThree.PartOne.MB3.CompSimple

public section

namespace CFSG.RankThree.PartOne.MB3

open Matrix Subgroup
open scoped commutatorElement

variable {J : Type} [Fintype J] [DecidableEq J]

@[expose] def blk₁ (S : Matrix J J (ZMod 2)) : Matrix (Fin 3 ⊕ J) (Fin 3 ⊕ J) (ZMod 2) :=
  fromBlocks 1 0 0 S

omit [DecidableEq J] in
theorem blk₁_mul (S S' : Matrix J J (ZMod 2)) : blk₁ (S * S') = blk₁ S * blk₁ S' := by
  simp [blk₁, fromBlocks_multiply]

omit [Fintype J] in
theorem blk₁_one : blk₁ (1 : Matrix J J (ZMod 2)) = 1 := by simp [blk₁]

theorem blk₁_det (S : Matrix J J (ZMod 2)) : (blk₁ S).det = S.det := by
  simp [blk₁, det_fromBlocks_zero₂₁]

omit [Fintype J] [DecidableEq J] in
theorem blk₁_inj {S S' : Matrix J J (ZMod 2)} (h : blk₁ S = blk₁ S') : S = S' := by
  simpa [blk₁, fromBlocks_inj] using h

@[expose] def β₁ : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2) :=
  ⟨fromBlocks cM 0 0 1, by rw [det_fromBlocks_zero₂₁, cM_det, det_one, mul_one]⟩

@[expose] def ι₁ : SpecialLinearGroup J (ZMod 2) →* SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2) where
  toFun S := ⟨blk₁ (S : Matrix J J (ZMod 2)), by rw [blk₁_det]; exact S.2⟩
  map_one' := Subtype.ext (by
    show blk₁ (↑(1 : SpecialLinearGroup J (ZMod 2)) : Matrix J J (ZMod 2)) = 1
    rw [Matrix.SpecialLinearGroup.coe_one, blk₁_one])
  map_mul' S S' := by
    refine Subtype.ext ?_
    show blk₁ (↑(S * S') : Matrix J J (ZMod 2)) = blk₁ ↑S * blk₁ ↑S'
    rw [Matrix.SpecialLinearGroup.coe_mul, blk₁_mul]

theorem coe_β₁ : ((β₁ : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) :
    Matrix (Fin 3 ⊕ J) (Fin 3 ⊕ J) (ZMod 2)) = fromBlocks cM 0 0 1 := rfl

theorem coe_ι₁ (S : SpecialLinearGroup J (ZMod 2)) :
    ((ι₁ S : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) :
      Matrix (Fin 3 ⊕ J) (Fin 3 ⊕ J) (ZMod 2)) = blk₁ (S : Matrix J J (ZMod 2)) :=
  rfl

theorem ι₁_injective : Function.Injective (ι₁ (J := J)) := fun _ _ h =>
  Subtype.ext (blk₁_inj (congrArg Subtype.val h))

theorem coe_β₁_pow (i : ℕ) : ((β₁ ^ i : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) :
    Matrix (Fin 3 ⊕ J) (Fin 3 ⊕ J) (ZMod 2)) = fromBlocks (cM ^ i) 0 0 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, coe_β₁]
    simp [fromBlocks_multiply, pow_succ]

theorem commute_β₁_ι₁ (S : SpecialLinearGroup J (ZMod 2)) : Commute β₁ (ι₁ S) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_β₁, coe_ι₁]
  simp [blk₁, fromBlocks_multiply]

theorem exists_pow_mul_ι₁_of_commute {A : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)}
    (h : A * β₁ = β₁ * A) : ∃ (i : ℕ) (S : SpecialLinearGroup J (ZMod 2)), A = β₁ ^ i * ι₁ S := by
  have hA := congrArg Subtype.val h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_β₁] at hA
  obtain ⟨P, Q, R, S, hPQRS⟩ : ∃ (P : Matrix (Fin 3) (Fin 3) (ZMod 2))
      (Q : Matrix (Fin 3) J (ZMod 2)) (R : Matrix J (Fin 3) (ZMod 2))
      (S : Matrix J J (ZMod 2)), (A : Matrix (Fin 3 ⊕ J) (Fin 3 ⊕ J) (ZMod 2)) =
        fromBlocks P Q R S := ⟨_, _, _, _, (fromBlocks_toBlocks _).symm⟩
  rw [hPQRS] at hA
  simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.mul_one, Matrix.one_mul, fromBlocks_inj] at hA
  obtain ⟨hP, hQ, hR, -⟩ := hA
  have hQ0 : Q = 0 := eq_zero_of_cM_mul Q hQ.symm
  have hR0 : R = 0 := eq_zero_of_mul_cM R hR
  subst hQ0 hR0
  have hdet := A.2
  rw [hPQRS, det_fromBlocks_zero₂₁] at hdet
  have key : ∀ a b : ZMod 2, a * b = 1 → a = 1 ∧ b = 1 := by decide
  obtain ⟨hdP, hdS⟩ := key _ _ hdet
  have hne : P ≠ 0 := by
    rintro rfl
    rw [Matrix.det_zero] at hdP
    exact zero_ne_one hdP
  rcases comm_cM P hP with h0 | ⟨i, hi⟩
  · exact absurd h0 hne
  let S' : SpecialLinearGroup J (ZMod 2) := ⟨S, hdS⟩
  refine ⟨i, S', Subtype.ext ?_⟩
  rw [hPQRS, Matrix.SpecialLinearGroup.coe_mul, coe_β₁_pow, coe_ι₁ S', hi]
  simp [S', blk₁, fromBlocks_multiply]

@[expose] def T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) :=
  Subgroup.centralizer {(β₁ : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))}

theorem mem_T₁ {A : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)} :
    A ∈ (T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))) ↔ A * β₁ = β₁ * A := by
  rw [T₁, Subgroup.mem_centralizer_singleton_iff]

theorem ι₁_mem_T₁ (S : SpecialLinearGroup J (ZMod 2)) :
    ι₁ S ∈ (T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))) :=
  mem_T₁.mpr (commute_β₁_ι₁ S).symm.eq

theorem β₁_mem_T₁ : (β₁ : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) ∈ T₁ :=
  mem_T₁.mpr rfl

omit [Fintype J] [DecidableEq J] in
theorem commutatorElement_mul_central {Y : Type*} [Group Y] {x y c : Y}
    (hc : c ∈ Subgroup.center Y) : ⁅x * c, y⁆ = ⁅x, y⁆ := by
  have hcy : c * y = y * c := (Subgroup.mem_center_iff.mp hc y).symm
  calc ⁅x * c, y⁆ = x * (c * y) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [commutatorElement_def]; group
    _ = x * (y * c) * c⁻¹ * x⁻¹ * y⁻¹ := by rw [hcy]
    _ = ⁅x, y⁆ := by rw [commutatorElement_def]; group

omit [Fintype J] [DecidableEq J] in
theorem commutatorElement_mul_central' {Y : Type*} [Group Y] {x y c : Y}
    (hc : c ∈ Subgroup.center Y) : ⁅x, y * c⁆ = ⁅x, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_central hc, commutatorElement_inv]

@[expose] def ι₁' : SpecialLinearGroup J (ZMod 2) →*
    ↥(T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))) :=
  (ι₁ (J := J)).codRestrict _ ι₁_mem_T₁

theorem ι₁'_injective : Function.Injective (ι₁' (J := J)) := fun _ _ h =>
  ι₁_injective (congrArg Subtype.val h)

@[expose] def zc₁ (i : ℕ) : ↥(T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))) :=
  ⟨β₁ ^ i, pow_mem β₁_mem_T₁ i⟩

theorem commutator_eq_ι₁'
    (x y : ↥(T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)))) :
    ∃ s : SpecialLinearGroup J (ZMod 2), ⁅x, y⁆ = ι₁' s := by
  have hz : ∀ i : ℕ, zc₁ (J := J) i ∈ Subgroup.center _ := by
    intro i
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg := mem_T₁.mp g.2
    show (g : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) * β₁ ^ i =
      β₁ ^ i * (g : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))
    exact (Commute.pow_right
      (show Commute (g : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) β₁ from hg) i).eq
  have hx : ∀ x : ↥(T₁ : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))),
      ∃ (S : SpecialLinearGroup J (ZMod 2)) (i : ℕ), x = ι₁' S * zc₁ i := by
    intro x
    obtain ⟨i, S, hS⟩ := exists_pow_mul_ι₁_of_commute (mem_T₁.mp x.2)
    refine ⟨S, i, Subtype.ext ?_⟩
    show (x : SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2)) = ι₁ S * β₁ ^ i
    rw [hS]
    exact ((commute_β₁_ι₁ S).pow_left i).eq
  obtain ⟨S, i, rfl⟩ := hx x
  obtain ⟨S', k, rfl⟩ := hx y
  refine ⟨⁅S, S'⁆, ?_⟩
  rw [commutatorElement_mul_central (hz i), commutatorElement_mul_central' (hz k),
    map_commutatorElement]

theorem eq_range_ι₁_of_isComponent (hJ : IsSimpleGroup (SpecialLinearGroup J (ZMod 2)))
    {E : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))} (hE : E ≤ T₁)
    (hcomp : CFSG.IsComponent (E.subgroupOf T₁)) : E = (ι₁ (J := J)).range := by
  have hS : IsSimpleGroup ↥((ι₁' (J := J)).range) :=
    (MonoidHom.ofInjective (ι₁'_injective (J := J))).symm.isSimpleGroup
  have h1 : E.subgroupOf T₁ = (ι₁' (J := J)).range := by
    refine eq_of_isComponent hS (fun x y => ?_) hcomp
    obtain ⟨s, hs⟩ := commutator_eq_ι₁' x y
    rw [hs]
    exact ⟨s, rfl⟩
  have h2 : E = (E.subgroupOf T₁).map T₁.subtype := (Subgroup.map_subgroupOf_eq_of_le hE).symm
  have h3 : (T₁.subtype.comp (ι₁' (J := J))) = ι₁ (J := J) := MonoidHom.ext fun _ => rfl
  rw [h2, h1, ← MonoidHom.range_comp, h3]

theorem nonempty_mulEquiv_of_isComponent (hJ : IsSimpleGroup (SpecialLinearGroup J (ZMod 2)))
    {E : Subgroup (SpecialLinearGroup (Fin 3 ⊕ J) (ZMod 2))} (hE : E ≤ T₁)
    (hcomp : CFSG.IsComponent (E.subgroupOf T₁)) :
    Nonempty (↥E ≃* SpecialLinearGroup J (ZMod 2)) := by
  have h := eq_range_ι₁_of_isComponent hJ hE hcomp
  subst h
  exact ⟨(MonoidHom.ofInjective (ι₁_injective (J := J))).symm⟩

end CFSG.RankThree.PartOne.MB3
