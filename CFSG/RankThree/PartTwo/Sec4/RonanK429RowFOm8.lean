module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFOm8Model
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFBlock
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowESp6
public import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalMinus

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.RonanK429E
open CFSG.Open (StatedOmega StatedQuadMinus StatedQuadPlus StatedClassicalModel StatedProj StatedSp)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open Matrix
open scoped commutatorElement

namespace Om8

abbrev ι : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

abbrev κ : Type := (Fin 3 ⊕ Fin 3) ⊕ Fin 2

abbrev ι6 : Type := Fin 3 ⊕ Fin 3

abbrev Q8 : (ι → ZMod 2) → ZMod 2 := StatedQuadMinus 4 (ZMod 2) 1 1

@[expose] def qP (p : Fin 2 → ZMod 2) : ZMod 2 := p 0 ^ 2 + p 0 * p 1 + p 1 ^ 2

@[expose] def eO : ι ≃ κ := (Equiv.sumAssoc (Fin 3) (Fin 3) (Fin 2)).symm

@[expose] def emb (M : Matrix ι6 ι6 (ZMod 2)) : Matrix ι ι (ZMod 2) :=
  (fromBlocks M 0 0 1).submatrix eO eO

theorem bl_emb (M : Matrix ι6 ι6 (ZMod 2)) : bl eO (emb M) = fromBlocks M 0 0 1 :=
  bl_submatrix eO _

theorem emb_mul (M N : Matrix ι6 ι6 (ZMod 2)) : emb (M * N) = emb M * emb N := by
  apply bl_injective eO
  rw [bl_mul, bl_emb, bl_emb, bl_emb, fromBlocks_diag_mul, Matrix.mul_one]

theorem emb_one : emb 1 = 1 := by
  apply bl_injective eO
  rw [bl_emb, bl_one, fromBlocks_one]

theorem emb_injective : Function.Injective emb := by
  intro M N h
  have h1 := congrArg (bl eO) h
  rw [bl_emb, bl_emb] at h1
  exact (fromBlocks_inj.mp h1).1

@[expose] def embHom : Matrix ι6 ι6 (ZMod 2) →* Matrix ι ι (ZMod 2) where
  toFun := emb
  map_one' := emb_one
  map_mul' := emb_mul

@[expose] def eps : GL ι6 (ZMod 2) →* GL ι (ZMod 2) := Units.map embHom

@[expose] def matO : Om8 →* Matrix ι ι (ZMod 2) :=
  (Units.coeHom (Matrix ι ι (ZMod 2))).comp (StatedOmega Q8).subtype

theorem matO_injective : Function.Injective matO := by
  intro x y h
  exact Subtype.ext (Units.ext h)

@[expose] def a3 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 1; 1, 1, 0; 0, 0, 1]
@[expose] def a3i : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 1; 1, 0, 1; 0, 0, 1]
@[expose] def b3 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 1, 1; 1, 0, 0]
@[expose] def b3i : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 0; 1, 1, 1]

@[expose] def Y6 : Matrix ι6 ι6 (ZMod 2) := fromBlocks a3 0 0 a3iᵀ
@[expose] def Y6i : Matrix ι6 ι6 (ZMod 2) := fromBlocks a3i 0 0 a3ᵀ
@[expose] def Z6 : Matrix ι6 ι6 (ZMod 2) := fromBlocks b3 0 0 b3iᵀ
@[expose] def Z6i : Matrix ι6 ι6 (ZMod 2) := fromBlocks b3i 0 0 b3ᵀ

theorem Y6_mul_Y6i : Y6 * Y6i = 1 := by decide +kernel
theorem Y6i_mul_Y6 : Y6i * Y6 = 1 := by decide +kernel
theorem Z6_mul_Z6i : Z6 * Z6i = 1 := by decide +kernel
theorem Z6i_mul_Z6 : Z6i * Z6 = 1 := by decide +kernel

theorem comm_Y6_Z6 : Y6 * Z6 * Y6i * Z6i = Sp6.y0M := by decide +kernel

theorem emb_Y6_iso : ∀ v : ι → ZMod 2, Q8 ((emb Y6 : Matrix ι ι (ZMod 2)) *ᵥ v) = Q8 v := by
  decide +kernel

theorem emb_Z6_iso : ∀ v : ι → ZMod 2, Q8 ((emb Z6 : Matrix ι ι (ZMod 2)) *ᵥ v) = Q8 v := by
  decide +kernel

@[expose] def Yg : GL ι6 (ZMod 2) := Units.mk Y6 Y6i Y6_mul_Y6i Y6i_mul_Y6

@[expose] def Zg : GL ι6 (ZMod 2) := Units.mk Z6 Z6i Z6_mul_Z6i Z6i_mul_Z6

theorem eps_Yg_mem : eps Yg ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => emb_Y6_iso v

theorem eps_Zg_mem : eps Zg ∈ CFSG.MatrixModel.isometryCore Q8 :=
  Subgroup.subset_closure fun v => emb_Z6_iso v

theorem y7_mem : ⁅eps Yg, eps Zg⁆ ∈ StatedOmega Q8 := by
  unfold StatedOmega
  exact Subgroup.commutator_mem_commutator eps_Yg_mem eps_Zg_mem

@[expose] def y7 : Om8 := ⟨⁅eps Yg, eps Zg⁆, y7_mem⟩

theorem matO_y7 : matO y7 = emb Sp6.y0M := by
  have h : (⁅eps Yg, eps Zg⁆ : GL ι (ZMod 2)) = eps ⁅Yg, Zg⁆ :=
    (map_commutatorElement eps Yg Zg).symm
  show ((⁅eps Yg, eps Zg⁆ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = emb Sp6.y0M
  rw [h]
  show emb ((⁅Yg, Zg⁆ : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) = emb Sp6.y0M
  congr 1
  simp only [commutatorElement_def, Yg, Zg, Units.val_mul, Units.inv_mk, Units.val_mk]
  exact comm_Y6_Z6

theorem emb_y0M_pow_seven : emb Sp6.y0M ^ 7 = 1 := by
  rw [← show embHom Sp6.y0M = emb Sp6.y0M from rfl, ← map_pow, Sp6.y0M_pow_seven, map_one]

theorem emb_y0M_ne_one : emb Sp6.y0M ≠ 1 := by
  intro h
  apply Sp6.y0M_ne_one
  apply emb_injective
  rw [h, emb_one]

theorem orderOf_y7 : orderOf y7 = 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime (matO_injective ?_) fun h => emb_y0M_ne_one ?_
  · rw [map_pow, matO_y7, emb_y0M_pow_seven, map_one]
  · rw [← matO_y7, h, map_one]

theorem card_Om8 {b c : GaloisField 2 1} (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nat.card Om8 = 197406720 := by
  obtain ⟨φ⟩ := nonempty_projOmegaMinus_equiv_om8 hbc
  rw [← Nat.card_congr φ.toEquiv, CFSG.RankThree.PartTwo.Sec19.Step1911Proof.card_projOmegaMinus hbc]
  simp [CFSG.Open.ordTwistedD, Finset.prod_Icc_succ_top]

theorem not_sq_seven_dvd {b c : GaloisField 2 1} (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    ¬ 7 ^ 2 ∣ Nat.card Om8 := by
  rw [card_Om8 hbc]
  norm_num


@[expose] def rho : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

theorem plane_three : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 2), A ^ 3 = 1 →
    A = 1 ∨ A = rho ∨ A = rho ^ 2 := by
  decide +kernel

theorem comm_rho : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 2), B * rho ^ 2 = rho ^ 2 * B →
    B * rho = rho * B := by
  decide +kernel

theorem comm_of_rho : ∀ A B : Matrix (Fin 2) (Fin 2) (ZMod 2), A * rho = rho * A →
    B * rho = rho * B → A * B = B * A := by
  decide +kernel

theorem sum_block_check : ∀ r : Matrix (Fin 2) (Fin 2) (ZMod 2), (r = rho ∨ r = rho ^ 2) →
    fromBlocks (1 : Matrix ι6 ι6 (ZMod 2)) 0 0 r +
      (fromBlocks (1 : Matrix ι6 ι6 (ZMod 2)) 0 0 r) ^ 2 = fromBlocks 0 0 0 1 := by
  decide +kernel

theorem t_form {t : Om8} (ht : t * y7 = y7 * t) (h3 : t ^ 3 = 1) (ht1 : t ≠ 1) :
    bl eO (matO t) = fromBlocks 1 0 0 rho ∨ bl eO (matO t) = fromBlocks 1 0 0 (rho ^ 2) := by
  have hX : matO t * emb Sp6.y0M = emb Sp6.y0M * matO t := by
    rw [← matO_y7, ← map_mul, ← map_mul, ht]
  have hE : matO t * (∑ i ∈ Finset.range 7, emb Sp6.y0M ^ i) =
      (∑ i ∈ Finset.range 7, emb Sp6.y0M ^ i) * matO t := by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Commute.pow_right (show Commute (matO t) (emb Sp6.y0M) from hX) i).eq
  have hsum : bl eO (∑ i ∈ Finset.range 7, emb Sp6.y0M ^ i) = fromBlocks 0 0 0 1 := by
    decide +kernel
  have hbd : IsBlockDiag (bl eO (matO t)) :=
    isBlockDiag_of_commute (by rw [← hsum, ← bl_mul, ← bl_mul, hE])
  set X6 := (bl eO (matO t)).toBlocks₁₁ with hX6def
  set X2 := (bl eO (matO t)).toBlocks₂₂ with hX2def
  have hXeq : bl eO (matO t) = fromBlocks X6 0 0 X2 := eq_fromBlocks_of_isBlockDiag hbd
  have h6 : X6 * Sp6.y0M = Sp6.y0M * X6 := by
    have h := bl_commute eO hX
    rw [hXeq, bl_emb, fromBlocks_diag_mul, fromBlocks_diag_mul] at h
    exact (fromBlocks_inj.mp h).1
  have hcube : fromBlocks (X6 ^ 3) 0 0 (X2 ^ 3) = fromBlocks 1 0 0 1 := by
    rw [← fromBlocks_diag_pow, ← hXeq, ← bl_pow, ← map_pow, h3, map_one, bl_one, fromBlocks_one]
  have hX6c : X6 ^ 3 = 1 := (fromBlocks_inj.mp hcube).1
  have hX2c : X2 ^ 3 = 1 := (fromBlocks_inj.mp hcube).2.2.2
  have hX6 : X6 = 1 := by
    have heq := eq_krylovPoly_of_commute (kr := Sp6.kr6) (kr' := Sp6.kr6i) (v := Sp6.v6)
      (e := Sp6.ex6) (fun _ _ => rfl) Sp6.kr6i_mul_kr6 h6
    rw [heq]
    exact Sp6.commute_y0_check _ (by rw [← heq]; exact hX6c)
  rcases plane_three X2 hX2c with h2 | h2 | h2
  · exfalso
    have hX1 : matO t = 1 := by
      apply bl_injective eO
      rw [hXeq, hX6, h2, fromBlocks_one, bl_one]
    exact ht1 (matO_injective (by rw [hX1, map_one]))
  · left
    rw [hXeq, hX6, h2]
  · right
    rw [hXeq, hX6, h2]

theorem cent_block {t x : Om8} {r : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hr : r = rho ∨ r = rho ^ 2)
    (ht : bl eO (matO t) = fromBlocks 1 0 0 r) (hx : x * t = t * x) :
    IsBlockDiag (bl eO (matO x)) ∧
      (bl eO (matO x)).toBlocks₂₂ * rho = rho * (bl eO (matO x)).toBlocks₂₂ := by
  have hc : matO x * matO t = matO t * matO x := by rw [← map_mul, ← map_mul, hx]
  have hE : matO x * (matO t + matO t ^ 2) = (matO t + matO t ^ 2) * matO x := by
    rw [mul_add, add_mul, hc, (Commute.pow_right (show Commute (matO x) (matO t) from hc) 2).eq]
  have hsum : bl eO (matO t + matO t ^ 2) = fromBlocks 0 0 0 1 := by
    rw [bl_add, bl_pow, ht]
    exact sum_block_check r hr
  have hbd : IsBlockDiag (bl eO (matO x)) :=
    isBlockDiag_of_commute (by rw [← hsum, ← bl_mul, ← bl_mul, hE])
  refine ⟨hbd, ?_⟩
  have h' := bl_commute eO hc
  rw [eq_fromBlocks_of_isBlockDiag hbd, ht, fromBlocks_diag_mul, fromBlocks_diag_mul] at h'
  have hp := (fromBlocks_inj.mp h').2.2.2
  rcases hr with rfl | rfl
  · exact hp
  · exact comm_rho _ hp

theorem Q8_split : ∀ v : κ → ZMod 2,
    Q8 (v ∘ eO) = StatedQuadPlus 3 (ZMod 2) (v ∘ Sum.inl) + qP (v ∘ Sum.inr) := by
  decide +kernel

theorem qP_zero : qP 0 = 0 := by simp [qP]

theorem mulVec_bl (X : Matrix ι ι (ZMod 2)) (v : κ → ZMod 2) :
    bl eO X *ᵥ v = (X *ᵥ (v ∘ eO)) ∘ eO.symm :=
  Matrix.submatrix_mulVec_equiv X v eO.symm eO.symm

theorem fromBlocks_mulVec_elim (A : Matrix ι6 ι6 (ZMod 2)) (B : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (v : κ → ZMod 2) :
    fromBlocks A 0 0 B *ᵥ v = Sum.elim (A *ᵥ (v ∘ Sum.inl)) (B *ᵥ (v ∘ Sum.inr)) := by
  funext k
  rcases k with k | k
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  · fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

theorem Q8_fromBlocks (A : Matrix ι6 ι6 (ZMod 2)) (B : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (v : κ → ZMod 2) :
    Q8 ((fromBlocks A 0 0 B *ᵥ v) ∘ eO) =
      StatedQuadPlus 3 (ZMod 2) (A *ᵥ (v ∘ Sum.inl)) + qP (B *ᵥ (v ∘ Sum.inr)) := by
  rw [fromBlocks_mulVec_elim, Q8_split, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem isom6_of_block {M : Matrix ι ι (ZMod 2)} {A : Matrix ι6 ι6 (ZMod 2)}
    {B : Matrix (Fin 2) (Fin 2) (ZMod 2)}
    (hM : ∀ w : ι → ZMod 2, Q8 (M *ᵥ w) = Q8 w) (hbd : bl eO M = fromBlocks A 0 0 B)
    (u : ι6 → ZMod 2) : StatedQuadPlus 3 (ZMod 2) (A *ᵥ u) = StatedQuadPlus 3 (ZMod 2) u := by
  set v : κ → ZMod 2 := Sum.elim u (0 : Fin 2 → ZMod 2) with hv
  have hvL : v ∘ Sum.inl = u := Sum.elim_comp_inl _ _
  have hvR : v ∘ Sum.inr = 0 := Sum.elim_comp_inr _ _
  have h1 : Q8 (v ∘ eO) = StatedQuadPlus 3 (ZMod 2) u := by
    rw [Q8_split, hvL, hvR, qP_zero, add_zero]
  have h2 : M *ᵥ (v ∘ eO) = (fromBlocks A 0 0 B *ᵥ v) ∘ eO := by
    have h := mulVec_bl M v
    rw [hbd] at h
    funext i
    have := congrFun h (eO i)
    simpa using this.symm
  have h3 := Q8_fromBlocks A B v
  rw [← h2, hM, h1, hvL, hvR, Matrix.mulVec_zero, qP_zero, add_zero] at h3
  exact h3.symm

theorem eps_isom {g : GL ι6 (ZMod 2)}
    (hg : g ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6)
    (w : ι → ZMod 2) : Q8 ((eps g : Matrix ι ι (ZMod 2)) *ᵥ w) = Q8 w := by
  have hgQ : ∀ v : ι6 → ZMod 2,
      StatedQuadPlus 3 (ZMod 2) ((g : Matrix ι6 ι6 (ZMod 2)) *ᵥ v) =
        StatedQuadPlus 3 (ZMod 2) v :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.mem_O6.mp hg
  set v : κ → ZMod 2 := w ∘ eO.symm with hv
  have hw : v ∘ eO = w := by
    funext i
    simp [hv]
  have h1 : (eps g : Matrix ι ι (ZMod 2)) *ᵥ w =
      (fromBlocks (g : Matrix ι6 ι6 (ZMod 2)) 0 0 1 *ᵥ v) ∘ eO :=
    Matrix.submatrix_mulVec_equiv _ _ eO eO
  rw [h1, Q8_fromBlocks, ← hw, Q8_split, hgQ, Matrix.one_mulVec]

theorem eps_mem_Om8 {P : GL ι6 (ZMod 2)} (hP : P ∈ StatedOmega (StatedQuadPlus 3 (ZMod 2))) :
    eps P ∈ StatedOmega Q8 := by
  have hle : StatedOmega (StatedQuadPlus 3 (ZMod 2)) ≤ (StatedOmega Q8).comap eps := by
    show ⁅CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6,
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6⁆ ≤
        (StatedOmega Q8).comap eps
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_comap, map_commutatorElement]
    unfold StatedOmega
    exact Subgroup.commutator_mem_commutator
      (Subgroup.subset_closure fun v => eps_isom hg₁ v)
      (Subgroup.subset_closure fun v => eps_isom hg₂ v)
  exact hle hP

@[expose] def psiD : ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2))) →* Om8 :=
  ((eps.comp (StatedOmega (StatedQuadPlus 3 (ZMod 2))).subtype).codRestrict (StatedOmega Q8)
    fun P => eps_mem_Om8 P.2)

theorem psiD_injective : Function.Injective psiD := by
  intro P Q h
  have h1 : emb ((P : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) =
      emb ((Q : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) := congrArg matO h
  exact Subtype.ext (Units.ext (emb_injective h1))

def IsTForm (t : Om8) : Prop :=
  ∃ r : Matrix (Fin 2) (Fin 2) (ZMod 2), (r = rho ∨ r = rho ^ 2) ∧
    bl eO (matO t) = fromBlocks 1 0 0 r

@[expose] def Cen (t : Om8) : Subgroup Om8 := Subgroup.centralizer ({t} : Set Om8)

theorem cent_bd {t x : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) :
    IsBlockDiag (bl eO (matO x)) ∧
      (bl eO (matO x)).toBlocks₂₂ * rho = rho * (bl eO (matO x)).toBlocks₂₂ := by
  obtain ⟨r, hr, hrt⟩ := ht
  exact cent_block hr hrt (Subgroup.mem_centralizer_singleton_iff.mp hx)


@[expose] def B6 (x : Om8) : Matrix ι6 ι6 (ZMod 2) := (bl eO (matO x)).toBlocks₁₁

@[expose] def B2 (x : Om8) : Matrix (Fin 2) (Fin 2) (ZMod 2) := (bl eO (matO x)).toBlocks₂₂

theorem B6_mul {t x y : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) (hy : y ∈ Cen t) :
    B6 (x * y) = B6 x * B6 y := by
  unfold B6
  rw [map_mul, bl_mul]
  exact IsBlockDiag.toBlocks₁₁_mul (cent_bd ht hx).1 (cent_bd ht hy).1

theorem B2_mul {t x y : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) (hy : y ∈ Cen t) :
    B2 (x * y) = B2 x * B2 y := by
  unfold B2
  rw [map_mul, bl_mul]
  exact IsBlockDiag.toBlocks₂₂_mul (cent_bd ht hx).1 (cent_bd ht hy).1

theorem B6_one : B6 1 = 1 := by
  unfold B6
  rw [map_one, bl_one, toBlocks₁₁_one]

theorem B2_one : B2 1 = 1 := by
  unfold B2
  rw [map_one, bl_one, toBlocks₂₂_one]

theorem B6_mul_inv {t x : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) : B6 x * B6 x⁻¹ = 1 := by
  rw [← B6_mul ht hx (inv_mem hx), mul_inv_cancel, B6_one]

theorem B6_inv_mul {t x : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) : B6 x⁻¹ * B6 x = 1 := by
  rw [← B6_mul ht (inv_mem hx) hx, inv_mul_cancel, B6_one]

theorem B2_mul_inv {t x : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) : B2 x * B2 x⁻¹ = 1 := by
  rw [← B2_mul ht hx (inv_mem hx), mul_inv_cancel, B2_one]

theorem exists_unit6 {t x : Om8} (ht : IsTForm t) (hx : x ∈ Cen t) :
    ∃ A : GL ι6 (ZMod 2), (A : Matrix ι6 ι6 (ZMod 2)) = B6 x ∧
      ((A⁻¹ : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) = B6 x⁻¹ ∧
      A ∈ CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6 :=
  ⟨Units.mk (B6 x) (B6 x⁻¹) (B6_mul_inv ht hx) (B6_inv_mul ht hx), rfl, rfl,
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.mem_O6.mpr fun u =>
      isom6_of_block (CFSG.ComponentClassification.CatFC.KGHS3.statedOmega_isometry Q8 x.2)
        (eq_fromBlocks_of_isBlockDiag (cent_bd ht hx).1) u⟩

theorem comm_mem_D {t a b : Om8} (ht : IsTForm t) (ha : a ∈ Cen t) (hb : b ∈ Cen t) :
    ⁅a, b⁆ ∈ psiD.range := by
  obtain ⟨A, hAv, hAi, hAO⟩ := exists_unit6 ht ha
  obtain ⟨B, hBv, hBi, hBO⟩ := exists_unit6 ht hb
  have hcomm : ⁅A, B⁆ ∈ StatedOmega (StatedQuadPlus 3 (ZMod 2)) := by
    show ⁅A, B⁆ ∈ ⁅CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6,
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.SmallOmegaSix.O6⁆
    exact Subgroup.commutator_mem_commutator hAO hBO
  refine ⟨⟨⁅A, B⁆, hcomm⟩, ?_⟩
  have hab' : a * b ∈ Cen t := mul_mem ha hb
  have haba : a * b * a⁻¹ ∈ Cen t := mul_mem hab' (inv_mem ha)
  have hab : ⁅a, b⁆ ∈ Cen t := by
    rw [commutatorElement_def]
    exact mul_mem haba (inv_mem hb)
  have h11 : (bl eO (matO ⁅a, b⁆)).toBlocks₁₁ = ((⁅A, B⁆ : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) := by
    show B6 ⁅a, b⁆ = _
    rw [commutatorElement_def a b, B6_mul ht haba (inv_mem hb), B6_mul ht hab' (inv_mem ha),
      B6_mul ht ha hb, commutatorElement_def A B, Units.val_mul, Units.val_mul, Units.val_mul,
      hAv, hBv, hAi, hBi]
  have hPQ : B2 a * B2 b = B2 b * B2 a := comm_of_rho _ _ (cent_bd ht ha).2 (cent_bd ht hb).2
  have hai : B2 a * B2 a⁻¹ = 1 := B2_mul_inv ht ha
  have hbi : B2 b * B2 b⁻¹ = 1 := B2_mul_inv ht hb
  have h22 : (bl eO (matO ⁅a, b⁆)).toBlocks₂₂ = 1 := by
    show B2 ⁅a, b⁆ = 1
    rw [commutatorElement_def a b, B2_mul ht haba (inv_mem hb), B2_mul ht hab' (inv_mem ha),
      B2_mul ht ha hb, hPQ]
    have e : B2 b * B2 a * B2 a⁻¹ * B2 b⁻¹ = B2 b * (B2 a * B2 a⁻¹) * B2 b⁻¹ := by
      simp only [mul_assoc]
    rw [e, hai, mul_one, hbi]
  apply Subtype.ext
  apply Units.ext
  apply bl_injective eO
  show bl eO (emb ((⁅A, B⁆ : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2))) = bl eO (matO ⁅a, b⁆)
  rw [bl_emb, eq_fromBlocks_of_isBlockDiag (cent_bd ht hab).1, h11, h22]

theorem psiD_mem_cent {t : Om8} (ht : IsTForm t)
    (P : ↥(StatedOmega (StatedQuadPlus 3 (ZMod 2)))) : psiD P ∈ Cen t := by
  obtain ⟨r, -, hrt⟩ := ht
  show psiD P ∈ Subgroup.centralizer ({t} : Set Om8)
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply matO_injective
  rw [map_mul, map_mul]
  apply bl_injective eO
  have hP : matO (psiD P) = emb ((P : GL ι6 (ZMod 2)) : Matrix ι6 ι6 (ZMod 2)) := rfl
  rw [bl_mul, bl_mul, hP, bl_emb, hrt]
  simp only [fromBlocks_diag_mul, Matrix.mul_one, Matrix.one_mul]


@[expose] def c1 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def c2 : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * Equiv.swap 1 3

@[expose] def c6 : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * (Equiv.swap 3 4 * Equiv.swap 5 6)

theorem c1_mem : c1 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem c2_mem : c2 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem c6_mem : c6 ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem c1_ne_c2 : c1 * c2 ≠ c2 * c1 := by decide

theorem c6_orderOf : orderOf c6 = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem card_D : Nat.card psiD.range = 20160 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective psiD_injective).toEquiv,
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.card_statedOmega_quadPlus_three]

noncomputable def ED : psiD.range ≃* ↥(alternatingGroup (Fin 8)) :=
  (MonoidHom.ofInjective psiD_injective).symm.trans
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.statedOmega_quadPlus_three_mulEquiv_alt8

theorem D_simple : IsSimpleGroup psiD.range := by
  haveI := CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.isSimpleGroup_statedOmega_quadPlus_three
  exact (MonoidHom.ofInjective psiD_injective).symm.isSimpleGroup

theorem D_nonab : ∃ a b : psiD.range, a * b ≠ b * a := by
  refine ⟨ED.symm ⟨c1, c1_mem⟩, ED.symm ⟨c2, c2_mem⟩, fun h => ?_⟩
  have h' := congrArg ED h
  simp only [MulEquiv.apply_symm_apply, map_mul] at h'
  exact c1_ne_c2 (congrArg Subtype.val h')

theorem D_order6 : ∃ g : psiD.range, orderOf g = 6 :=
  ⟨ED.symm ⟨c6, c6_mem⟩, by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, c6_orderOf]⟩

theorem isTForm_of {t : Om8}
    (h : bl eO (matO t) = fromBlocks 1 0 0 rho ∨ bl eO (matO t) = fromBlocks 1 0 0 (rho ^ 2)) :
    IsTForm t := by
  rcases h with h | h
  · exact ⟨rho, Or.inl rfl, h⟩
  · exact ⟨rho ^ 2, Or.inr rfl, h⟩

theorem good429_t {t : Om8} (ht : IsTForm t) :
    Good429 (Cen t) := by
  have hDC : psiD.range ≤ Cen t := by
    rintro _ ⟨P, rfl⟩
    exact psiD_mem_cent ht P
  haveI := D_simple
  haveI : Group.IsPerfect psiD.range := isPerfect_of_simple D_nonab
  have hGood : Good429 psiD.range :=
    good429_self card_D (B := 28) (by norm_num) (by norm_num) (by decide +kernel)
      (not_isType429_quot_of_simple_20160 card_D D_order6)
  exact Good429.of_perfect_le hDC
    (fun K hKC hKp => le_of_commutator_mem (fun a ha b hb => comm_mem_D ht ha hb) hKC hKp) hGood

theorem good429_om8 {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) (s : Om8) (hs : orderOf s = 3) :
    Good429 (Subgroup.centralizer ({s} : Set Om8)) := by
  refine good429_of_sylowRoute (by norm_num) orderOf_y7 (not_sq_seven_dvd hbc) (N := 197406720)
    (B := 600) (card_Om8 hbc).dvd (by norm_num) (by norm_num) (by decide +kernel) ?_ s hs
  intro t ht h3 h1
  exact good429_t (isTForm_of (t_form ht h3 h1))


open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData in
theorem not_three_dvd_card_outer_projOmegaMinus {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    ¬ 3 ∣ Nat.card (Outer (projOmegaMinus 3 (GaloisField 2 1) b c)) := by
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have e₀ : projOmegaMinus 3 (GaloisField 2 1) b c ≃*
      StatedProj (StatedOmega (StatedQuadMinus 4 (GaloisField 2 1) b c)) :=
    ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c))).symm
  have hmod : StatedClassicalModel (projOmegaMinus 3 (GaloisField 2 1) b c) .POmegaMinus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, GaloisField 2 1, inferInstance, inferInstance, hK, b, c, hbc,
      ⟨e₀⟩⟩
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus hmod (GaloisField 2 1) hK b c hbc e₀
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus
    (GaloisField 2 1) 4 le_rfl b c hbc
  have hQ := CFSG.RankThree.PartOne.KCOrthComm.exists_ne_zero_of_nondegenerate hnd hT
  have hsub : Subsingleton (GaloisField 2 1 ≃+* GaloisField 2 1) :=
    CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.subsingleton_ringEquiv_of_card_units
      (by rw [Nat.card_units, hK]; norm_num)
  have hsq : ∀ α : MulAut (matrixProjectiveDerived
      (coordinateQuadMinus 4 (GaloisField 2 1) (by omega) b c)),
      α ^ 2 ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner _ := by
    intro α
    obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ α).mp (htop ▸ Subgroup.mem_top α)
    have hlin : g ∈ linearSimilarityPairs _ := by
      rw [mem_linearSimilarityPairs_iff]
      exact Subsingleton.elim _ _
    exact CFSG.RankThree.PartOne.OutStructure.orthD_sq_mem_inner _ hQ hnd hT
      ((CFSG.RankThree.PartOne.OutStructure.mem_orthD_iff _ α).mpr ⟨⟨g, hlin⟩, hg⟩)
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (coordinateMinusWitnessEquiv (GaloisField 2 1) (by omega) b c e₀)).toEquiv]
  intro h3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
  have hx2 : ((α : Outer (matrixProjectiveDerived
      (coordinateQuadMinus 4 (GaloisField 2 1) (by omega) b c)))) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hsq α
  have h1 := orderOf_dvd_of_pow_eq_one hx2
  rw [hx] at h1
  norm_num at h1

end Om8

theorem noCfgS429_om8 {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a) {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0)
    (e : S ≃* projOmegaMinus 3 (GaloisField 2 1) b c) : NoCfgS429 S := by
  obtain ⟨φ⟩ := nonempty_projOmegaMinus_equiv_om8 hbc
  have hOut : ¬ 3 ∣ Nat.card (Outer Om8) :=
    not_three_dvd_outer_of_mulEquiv φ.symm (Om8.not_three_dvd_card_outer_projOmegaMinus hbc)
  exact noCfgS429_of_model (e.trans φ) (center_eq_bot_of_simple_nonab hna)
    (not_three_dvd_outer_of_mulEquiv (e.trans φ) hOut)
    (fun x hx => Om8.good429_om8 hbc x hx)

theorem eight_OmegaMinus :
    ∀ b c : GaloisField 2 1, (∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) →
      RowSOf429 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  intro b c hbc
  exact rowSOf429_of_noCfg fun S _ _ hs hna ⟨e⟩ => by
    haveI := hs
    exact noCfgS429_om8 hna hbc e

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
