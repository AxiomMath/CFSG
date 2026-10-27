module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Gen
public import CFSG.Quasithin.Vol2.Ch11G2Q8Point
public import CFSG.Quasithin.Vol2.KGNatSL3PointFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)
open CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open scoped commutatorElement

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem eu_eq_q6 : (eu 0 (1 : F) : Ix3 → F) = q6 1 0 0 0 0 0 := by
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

@[expose] def stabV0 (F : Type) [Field F] [CharP F 2] : Subgroup ↥(cayleyGroup F) where
  carrier := {g | g2Act g (eu 0 1) = eu 0 1}
  one_mem' := by
    change g2Act 1 _ = _
    rw [map_one, AddMonoid.End.coe_one, id_eq]
  mul_mem' := fun {a b} ha hb => by
    change g2Act (a * b) _ = _
    rw [g2Act_mul_apply, show g2Act b (eu 0 1) = eu 0 1 from hb]
    exact ha
  inv_mem' := fun {a} ha => by
    change g2Act a⁻¹ _ = _
    have h := g2Act_inv_apply a (eu 0 (1 : F))
    rwa [show g2Act a (eu 0 1) = eu 0 1 from ha] at h

theorem mem_stabV0 {g : ↥(cayleyGroup F)} : g ∈ stabV0 F ↔ g2Act g (eu 0 1) = eu 0 1 :=
  Iff.rfl

theorem cgE_zU0_of_mem {g : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F) :
    cgE g (zU0 F) = zU0 F := by
  have hz : zU0 F = zI (eu 0 (1 : F)) := by
    rw [eu_eq_q6, zI_q6]
    rfl
  have h1 := g2_zI_eq g (eu 0 (1 : F))
  rw [show g2Act g (eu 0 1) = eu 0 1 from hg, ← hz] at h1
  set r := (cgE g (zU0 F)).1 with hr_def
  have hn := cg_norm g (zU0 F)
  rw [h1] at hn
  have hr : r = 0 := by
    have e : zU0 F + r • cayleyOne F = zmk r 1 0 0 0 0 0 r := by
      rw [zU0, cayleyOne_eq, zmk_smul, zmk_add]
      apply zmk_congr <;> ring
    rw [e, cayleyNorm_zmk, zU0, cayleyNorm_zmk] at hn
    have h2 : r * r = 0 := by linear_combination hn
    exact mul_self_eq_zero.mp h2
  rw [h1, hr, zero_smul, add_zero]

theorem exists_eq_of_mem_stabV0 {g : ↥(cayleyGroup F)} (hg : g ∈ stabV0 F) :
    ∃ (α β γ : F) (A : SL3 F), (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
      g = g2X ![α, 0, 0] * g2Y ![0, β, γ] * g2A A :=
  eq_uW_mul_g2A (cgE_zU0_of_mem hg)

theorem g2Act_y12q (β γ a b c d e f : F) :
    g2Act (g2Y ![0, β, γ]) (q6 a b c d e f) =
      q6 (a + β * f + γ * e) (b + γ * d) (c + β * d) d (e + (β * b + γ * c) * β)
        (f + (β * b + γ * c) * γ) := by
  rw [g2Act_g2Y]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2Act_uSL_p00 (p a b c d e f : F) :
    g2Act (g2A (uSL p 0 0)) (q6 a b c d e f) = q6 (a + p * b) b c d (e + p * d) f := by
  rw [g2Act_g2A_uSL]
  simp only [q6, Sum.elim_inl, Sum.elim_inr, cons_val_zero, cons_val_one, cons_val_two,
    head_cons, tail_cons]
  congr 1 <;> funext k <;> fin_cases k <;> (simp; try ring)

theorem g2X_e0_mem_stabV0 (α : F) : g2X ![α, 0, 0] ∈ stabV0 F := by
  rw [mem_stabV0, eu_eq_q6, g2Act_x0q]
  simp

theorem g2Y_mem_stabV0 (β γ : F) : g2Y ![0, β, γ] ∈ stabV0 F := by
  rw [mem_stabV0, eu_eq_q6, g2Act_y12q]
  simp

theorem g2A_mem_stabV0 {A : SL3 F}
    (hA : (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0]) : g2A A ∈ stabV0 F := by
  rw [mem_stabV0, eu_eq_q6, g2Act_g2A]
  have h0 := congrFun hA 0
  have h1 := congrFun hA 1
  have h2 := congrFun hA 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
  simp [h0, h1, h2]

omit [CharP F 2] in
theorem uSL_mulVec_e0 (a b c : F) :
    ((uSL a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  have hA : ((uSL a b c : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, a, b; 0, 1, c; 0, 0, 1] := rfl
  rw [hA]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem swap12_mulVec_e0 :
    ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  have hA : ((swap12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![1, 0, 0; 0, 0, 1; 0, 1, 0] := rfl
  rw [hA]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem U0_le_stabV0 : U0 F ≤ stabV0 F := by
  intro u hu
  rw [mem_stabV0]
  have h1 : InF 1 (eu 0 (1 : F)) := mem_stdF.mp (mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩)
  have h0 := (mem_U0.mp hu) 0 (eu 0 1) h1
  exact sub_eq_zero.mp (eq_zero_of_inF_zero h0)

theorem stabV0_le_stabQ : stabV0 F ≤ stabQ (stdF F 1) := by
  have key : ∀ g ∈ stabV0 F, ∀ w ∈ stdF F 1, g2Act g w ∈ stdF F 1 := by
    intro g hg w hw
    obtain ⟨t, rfl⟩ := mem_stdF_one_iff.mp hw
    rw [g2Act_smul, show g2Act g (eu 0 1) = eu 0 1 from hg]
    exact mem_stdF_one_iff.mpr ⟨t, rfl⟩
  intro g hg
  refine mem_stabQ.mpr fun w => ⟨key g hg w, fun h => ?_⟩
  have h1 := key g⁻¹ ((stabV0 F).inv_mem hg) _ h
  rwa [g2Act_inv_apply] at h1

theorem exists_smul_of_mem_stabQ_one {g : ↥(cayleyGroup F)} (hg : g ∈ stabQ (stdF F 1)) :
    ∃ c : F, c ≠ 0 ∧ g2Act g (eu 0 1) = c • eu 0 1 := by
  have h1 : (eu 0 (1 : F)) ∈ stdF F 1 := mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩
  obtain ⟨c, hc⟩ := mem_stdF_one_iff.mp ((mem_stabQ.mp hg _).mp h1)
  refine ⟨c, fun h0 => ?_, hc⟩
  rw [h0, zero_smul] at hc
  have h2 := congrArg (g2Act g⁻¹) hc
  rw [g2Act_inv_apply, map_zero] at h2
  have h3 := congrFun h2 (.inl 0)
  simp at h3

theorem inv_smul_of_smul {g : ↥(cayleyGroup F)} {c : F} (hc : c ≠ 0) {w : Ix3 → F}
    (h : g2Act g w = c • w) : g2Act g⁻¹ w = c⁻¹ • w := by
  have h1 := congrArg (g2Act g⁻¹) h
  rw [g2Act_inv_apply, g2Act_smul] at h1
  calc g2Act g⁻¹ w = c⁻¹ • (c • g2Act g⁻¹ w) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • w := by rw [← h1]

theorem commutator_stabQ_one_le : ⁅stabQ (stdF F 1), stabQ (stdF F 1)⁆ ≤ stabV0 F := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one ha
  obtain ⟨d, hd0, hd⟩ := exists_smul_of_mem_stabQ_one hb
  have hb' := inv_smul_of_smul hd0 hd
  have ha' := inv_smul_of_smul hc0 hc
  rw [mem_stabV0, commutatorElement_def, g2Act_mul_apply, g2Act_mul_apply, g2Act_mul_apply]
  simp only [g2Act_smul, hb', ha', hd, hc, smul_smul]
  convert one_smul F (eu 0 (1 : F)) using 2
  field_simp

theorem y2_mul (s t : F) : g2Y ![0, 0, s] * g2Y ![0, 0, t] = g2Y ![0, 0, s + t] := by
  have e : ∀ c : F, (![0, 0, c] : Fin 3 → F) = c • ![0, 0, 1] := fun c => by
    funext i; fin_cases i <;> simp
  rw [e s, e t, e (s + t), g2Y_smul_mul]

theorem g2Y_inv (b : Fin 3 → F) : (g2Y b)⁻¹ = g2Y b :=
  inv_eq_of_mul_eq_one_right (g2Y_mul_self b)

theorem g2Y_decomp (β γ : F) :
    g2Y ![0, β, γ] = g2Y ![0, β, 0] * g2Y ![0, 0, γ] * g2X ![β * γ, 0, 0] *
      g2A (uSL (β * β * γ) 0 0) := by
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w]
  simp only [g2Act_mul_apply, g2Act_y12q, g2Act_uSL_p00, g2Act_x0q]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine q6_congr ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination (-(β * β * γ * w (.inl 1)) - β * β * γ * γ * w (.inr 0) -
      β * γ * γ * w (.inl 2)) * h2
  · ring
  · ring
  · ring
  · linear_combination (-(β * β * γ * w (.inr 0))) * h2
  · ring

theorem stabV0_perfect [Finite F] (h4 : 4 ≤ Nat.card F) : ⁅stabV0 F, stabV0 F⁆ = stabV0 F := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  set C := ⁅stabV0 F, stabV0 F⁆ with hC
  have hconj : ∀ h ∈ stabV0 F, ∀ x ∈ C, h * x * h⁻¹ ∈ C := fun h hh x hx => by
    have h1 := Subgroup.commutator_mem_commutator hh (Subgroup.commutator_le_self _ hx)
    rw [commutatorElement_def] at h1
    have h2 := C.mul_mem h1 hx
    rwa [show h * x * h⁻¹ * x⁻¹ * x = h * x * h⁻¹ by group] at h2
  have hA : ∀ A : SL3 F, (A : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] →
      g2A A ∈ C := by
    intro A hAe
    have hSL := commutator_SL2_eq_top h4
    let φ : SpecialLinearGroup (Fin 1 ⊕ Fin 2) F →* ↥(cayleyGroup F) :=
      g2A.comp (reindexSL F h12).toMonoidHom
    let J := perfectCore (parQ : Subgroup (SpecialLinearGroup (Fin 1 ⊕ Fin 2) F))
    have hJ : J = parJR F (Fin 1) (Fin 2) := perfectCore_parQ12 hSL
    have hJS : J.map φ ≤ stabV0 F := by
      rintro _ ⟨M, hM, rfl⟩
      rw [hJ] at hM
      exact g2A_mem_stabV0 ((mem_parJR12_iff M).mp hM)
    have hM : (reindexSL F h12).symm A ∈ ⁅J, J⁆ := by
      change _ ∈ ⁅perfectCore parQ, perfectCore parQ⁆
      rw [perfectCore_perfect, perfectCore_parQ12 hSL, mem_parJR12_iff, MulEquiv.apply_symm_apply]
      exact hAe
    have h1 : φ ((reindexSL F h12).symm A) ∈ C := by
      have h2 : (⁅J, J⁆).map φ ≤ C := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono hJS hJS
      exact h2 ⟨_, hM, rfl⟩
    have h3 : φ ((reindexSL F h12).symm A) = g2A A := by
      change g2A ((reindexSL F h12) ((reindexSL F h12).symm A)) = _
      rw [MulEquiv.apply_symm_apply]
    rwa [h3] at h1
  obtain ⟨d, hd0, hd1⟩ := exists_ne_zero_ne_one (by omega : 2 < Nat.card F)
  have hdd : d⁻¹ + 1 ≠ 0 := by
    intro h
    apply hd1
    have h1 : d⁻¹ = 1 := by
      rw [← sub_eq_zero, CharTwo.sub_eq_add]
      exact h
    exact inv_eq_one.mp h1
  have hD : (1 : F) * d * d⁻¹ = 1 := by field_simp
  have hDe : ((diag3 1 d d⁻¹ hD : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
      ![1, 0, 0] := by
    funext i
    fin_cases i <;> simp [diag3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hDadj : (adjugate ((diag3 1 d d⁻¹ hD : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ =
      diagonal ![1⁻¹, d⁻¹, d⁻¹⁻¹] := by
    have h1 : adjugate ((diag3 1 d d⁻¹ hD : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
        diagonal ![1⁻¹, d⁻¹, d⁻¹⁻¹] := by
      change (((diag3 1 d d⁻¹ hD)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) = _
      rw [diag3_inv]
      rfl
    rw [h1, diagonal_transpose]
  have hy1 : ∀ t : F, g2Y ![0, t, 0] ∈ C := by
    intro t
    have h1 := Subgroup.commutator_mem_commutator (g2A_mem_stabV0 hDe)
      (g2Y_mem_stabV0 (t * (d⁻¹ + 1)⁻¹) 0)
    rw [commutatorElement_def, g2A_mul_g2Y, mul_inv_cancel_right, g2Y_inv, hDadj] at h1
    have e : diagonal ![1⁻¹, d⁻¹, d⁻¹⁻¹] *ᵥ (![0, t * (d⁻¹ + 1)⁻¹, 0] : Fin 3 → F) =
        ![0, d⁻¹ * (t * (d⁻¹ + 1)⁻¹), 0] := by
      funext i
      fin_cases i <;> simp [mulVec_diagonal]
    have hs : d⁻¹ * (t * (d⁻¹ + 1)⁻¹) + t * (d⁻¹ + 1)⁻¹ = t := by
      rw [← add_one_mul, mul_left_comm, mul_inv_cancel₀ hdd, mul_one]
    rw [e, y1_mul, hs] at h1
    exact h1
  have hy2 : ∀ t : F, g2Y ![0, 0, t] ∈ C := by
    intro t
    rw [← conj_swap12_y1]
    exact hconj _ (g2A_mem_stabV0 swap12_mulVec_e0) _ (hy1 t)
  have hx0 : ∀ δ : F, g2X ![δ, 0, 0] ∈ C := by
    intro δ
    have hconjT : g2A (uSL 0 0 δ) * g2Y ![0, 1, 0] * (g2A (uSL 0 0 δ))⁻¹ = g2Y ![0, 1, δ] := by
      rw [g2A_mul_g2Y, mul_inv_cancel_right, adjugate_uSL]
      congr 1
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, transpose_apply,
        CharTwo.neg_eq]
    have hY : g2Y ![0, 1, δ] ∈ C := by
      rw [← hconjT]
      exact hconj _ (g2A_mem_stabV0 (uSL_mulVec_e0 0 0 δ)) _ (hy1 1)
    have e := g2Y_decomp (1 : F) δ
    simp only [one_mul] at e
    have e2 : g2X ![δ, 0, 0] = (g2Y ![0, 1, 0] * g2Y ![0, 0, δ])⁻¹ * g2Y ![0, 1, δ] *
        (g2A (uSL δ 0 0))⁻¹ := by
      rw [e]
      group
    rw [e2]
    exact C.mul_mem (C.mul_mem (C.inv_mem (C.mul_mem (hy1 1) (hy2 δ))) hY)
      (C.inv_mem (hA _ (uSL_mulVec_e0 δ 0 0)))
  intro g hg
  obtain ⟨α, β, γ, A, hAe, rfl⟩ := exists_eq_of_mem_stabV0 hg
  rw [g2Y_decomp β γ]
  exact C.mul_mem (C.mul_mem (hx0 α) (C.mul_mem (C.mul_mem (C.mul_mem (hy1 β) (hy2 γ))
    (hx0 _)) (hA _ (uSL_mulVec_e0 _ 0 0)))) (hA A hAe)

theorem perfectCore_stabQ_one [Finite F] (h4 : 4 ≤ Nat.card F) :
    perfectCore (stabQ (stdF F 1)) = stabV0 F :=
  le_antisymm ((perfectCore_le_derivedSeriesOf _ 1).trans commutator_stabQ_one_le)
    (le_perfectCore_of_perfect stabV0_le_stabQ (stabV0_perfect h4))

theorem U0_le_perfectCore_stabQ_one [Finite F] (h4 : 4 ≤ Nat.card F) :
    U0 F ≤ perfectCore (stabQ (stdF F 1)) := by
  rw [perfectCore_stabQ_one h4]
  exact U0_le_stabV0

end CFSG.Quasithin.Vol2.Ch11.G2Q8
