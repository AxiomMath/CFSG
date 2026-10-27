module

public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsForms
public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsDefs
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH3
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelRing
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS.TableFacts

variable {p : ℕ} [Fact p.Prime]

private lemma tfmd_blockSucc_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p)) :
    (Matrix.blockSucc M).transpose = Matrix.blockSucc M.transpose := by
  ext i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  | cast i => induction j using Fin.lastCases with
    | last => simp
    | cast j => simp

private lemma tfmd_diagonal_snoc_one {n : ℕ} (w : Fin n → ZMod p) :
    Matrix.diagonal (Fin.snoc w 1) = Matrix.blockSucc (Matrix.diagonal w) := by
  ext i j
  induction i using Fin.lastCases with
  | last => induction j using Fin.lastCases with
    | last => simp
    | cast j => rw [Matrix.diagonal_apply, if_neg (Fin.castSucc_lt_last j).ne']; simp
  | cast i => induction j using Fin.lastCases with
    | last => rw [Matrix.diagonal_apply, if_neg (Fin.castSucc_lt_last i).ne]; simp
    | cast j => simp [Matrix.diagonal_apply]

private lemma tfmd_blockSucc_orth {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p))
    (w : Fin n → ZMod p)
    (h : M.transpose * Matrix.diagonal w * M = Matrix.diagonal w) :
    (Matrix.blockSucc M).transpose * Matrix.blockSucc (Matrix.diagonal w) *
        Matrix.blockSucc M = Matrix.blockSucc (Matrix.diagonal w) := by
  rw [tfmd_blockSucc_transpose, ← Matrix.blockSucc_mul, ← Matrix.blockSucc_mul, h]

private lemma tfmd_blockSucc_orth_last {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod p))
    (w : Fin n → ZMod p) (c : ZMod p)
    (h : M.transpose * Matrix.diagonal w * M = Matrix.diagonal w) :
    (Matrix.blockSucc M).transpose * Matrix.diagonal (Fin.snoc w c) * Matrix.blockSucc M =
      Matrix.diagonal (Fin.snoc w c) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_castSucc]
    | cast j => simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_castSucc,
        (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_castSucc,
        (Fin.castSucc_lt_last i).ne]
    | cast j =>
      have hh := congrArg (fun A : Matrix (Fin n) (Fin n) (ZMod p) => A i j) h
      simpa [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_castSucc] using hh

private lemma tfmd_h3SignMat_orth {α : ZMod p} (i : Fin 3) :
    (diagSignMat i : Matrix (Fin 3) (Fin 3) (ZMod p)).transpose *
        Matrix.diagonal ![1 + α, 1 + α, 1] * diagSignMat i =
      Matrix.diagonal ![1 + α, 1 + α, 1] := by
  fin_cases i <;>
    ext r c <;> fin_cases r <;> fin_cases c <;>
      simp [diagSignMat, Matrix.mul_apply, Matrix.diagonal_apply]

private lemma tfmd_h3BlockMat_orth (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (h3BlockMat α).transpose * Matrix.diagonal ![1 + α, 1 + α, 1] * h3BlockMat α =
      Matrix.diagonal ![1 + α, 1 + α, 1] := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hα3 : α ^ 3 = 2 * α + 1 := by linear_combination (α + 1) * hα
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h3BlockMat, Matrix.transpose_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.of_apply, Fin.sum_univ_three, smul_eq_mul] <;>
    field_simp [h2] <;>
    first
      | (ring_nf; done)
      | (ring_nf; try simp only [hα3, hα]; ring_nf)

private lemma tfmd_h4BlockMat_orth (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (h4BlockMat α).transpose * Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α] * h4BlockMat α =
      Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α] := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hα3 : α ^ 3 = 2 * α + 1 := by linear_combination (α + 1) * hα
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h4BlockMat, Matrix.transpose_apply, Matrix.mul_apply, Matrix.diagonal_apply,
      Matrix.of_apply, Fin.sum_univ_four, smul_eq_mul] <;>
    field_simp [h2] <;>
    first
      | (ring_nf; done)
      | (ring_nf; try simp only [hα3, hα]; ring_nf)

private lemma tfmd_weylF4Mats_orth (hp : p ≠ 2) :
    ∀ M ∈ (weylF4Mats : Set (Matrix (Fin 4) (Fin 4) (ZMod p))),
      M.transpose * Matrix.diagonal 1 * M = Matrix.diagonal 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  intro M hM
  rw [weylF4Mats, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSignMat, Matrix.mul_apply, Matrix.diagonal_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pijMat, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pijMat, Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_four]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfOnesMat, Matrix.transpose_apply, Matrix.mul_apply, Matrix.sub_apply,
        Matrix.one_apply, Matrix.of_apply, Fin.sum_univ_four, smul_eq_mul] <;>
      field_simp [h2] <;>
      ring_nf

private lemma tfmd_h3Mats_blockSucc_orth (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    {K : Matrix (Fin 3) (Fin 3) (ZMod p)} (hK : K ∈ h3BlockMats α) :
    (Matrix.blockSucc K).transpose * Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α] *
        Matrix.blockSucc K = Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α] := by
  have h3 : K.transpose * Matrix.diagonal ![1 + α, 1 + α, 1] * K =
      Matrix.diagonal ![1 + α, 1 + α, 1] := by
    rw [h3BlockMats, Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hK
    rcases hK with rfl | rfl | rfl | rfl
    · exact tfmd_h3SignMat_orth 0
    · exact tfmd_h3SignMat_orth 1
    · exact tfmd_h3SignMat_orth 2
    · exact tfmd_h3BlockMat_orth hp hα
  have h := tfmd_blockSucc_orth_last K ![1 + α, 1 + α, 1] (1 + α) h3
  simpa using h

private lemma tfmd_h4Mats_orth (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    ∀ M ∈ h4Mats α,
      M.transpose * Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α, 1] * M =
        Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α, 1] := by
  have hD : Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α, 1] =
      Matrix.blockSucc (Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α]) := by
    simpa using tfmd_diagonal_snoc_one (p := p) ![1 + α, 1 + α, 1, 1 + α]
  intro M hM
  rw [h4Mats, Set.mem_image] at hM
  obtain ⟨N, hN, rfl⟩ := hM
  rw [hD]
  refine tfmd_blockSucc_orth N ![1 + α, 1 + α, 1, 1 + α] ?_
  rw [h4BlockMats, Set.mem_insert_iff] at hN
  rcases hN with rfl | hN
  · exact tfmd_h4BlockMat_orth hp hα
  · rw [h3Mats, Set.mem_image] at hN
    obtain ⟨K, hK, rfl⟩ := hN
    exact tfmd_h3Mats_blockSucc_orth hp hα hK

private lemma tfmd_f4ExtMats_orth (hp : p ≠ 2) :
    ∀ M ∈ (f4ExtMats : Set (Matrix (Fin 5) (Fin 5) (ZMod p))),
      M.transpose * Matrix.diagonal 1 * M = Matrix.diagonal 1 := by
  intro M hM
  rw [f4ExtMats, Set.mem_image] at hM
  obtain ⟨N, hN, rfl⟩ := hM
  have hD : Matrix.diagonal (1 : Fin 5 → ZMod p) =
      Matrix.blockSucc (Matrix.diagonal (1 : Fin 4 → ZMod p)) := by
    rw [Matrix.diagonal_one', Matrix.diagonal_one', Matrix.blockSucc_one]
  rw [hD]
  exact tfmd_blockSucc_orth N (1 : Fin 4 → ZMod p) (tfmd_weylF4Mats_orth hp N hN)

theorem one_add_ne_zero_of_sq_eq {α : ZMod p} (hα : α ^ 2 = α + 1) : 1 + α ≠ 0 := by
  intro h
  have hα' : α = -1 := eq_neg_of_add_eq_zero_right h
  have h1 : (1 : ZMod p) = 0 := by
    calc (1 : ZMod p) = (-1 : ZMod p) ^ 2 := by ring_nf
      _ = -1 + 1 := by rw [← hα']; exact hα
      _ = 0 := by ring_nf
  exact one_ne_zero h1

theorem h4Mats_orthogonal (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    ∀ M ∈ h4Mats α, M.transpose * Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α, 1] * M =
      Matrix.diagonal ![1 + α, 1 + α, 1, 1 + α, 1] := by
  exact tfmd_h4Mats_orth hp hα

theorem f4ExtMats_orthogonal (hp : p ≠ 2) :
    ∀ M ∈ (f4ExtMats : Set (Matrix (Fin 5) (Fin 5) (ZMod p))),
      M.transpose * Matrix.diagonal 1 * M = Matrix.diagonal 1 := by
  exact tfmd_f4ExtMats_orth hp

variable {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3_pair_exists : ∀ j : Fin 15, h3Ord j = 5 →
    ∃ k : Fin 15,
      (reflZ (h3Tab.root 0) (h3Tab.coroot 0) *
        reflZ (h3Tab.root k) (h3Tab.coroot k)) ^ 2 =
        (4 : ZAl) ^ 2 • (1 : Matrix (Fin 4) (Fin 4) ZAl) ∧
      (reflZ (h3Tab.root j) (h3Tab.coroot j) *
        reflZ (h3Tab.root k) (h3Tab.coroot k)) ^ 3 =
        (4 : ZAl) ^ 3 • (1 : Matrix (Fin 4) (Fin 4) ZAl) ∧
      (∃ q : Fin 4 × Fin 4, GoodAl
        ((reflZ (h3Tab.root 0) (h3Tab.coroot 0) *
          reflZ (h3Tab.root k) (h3Tab.coroot k) -
          (4 : ZAl) • (1 : Matrix (Fin 4) (Fin 4) ZAl)) q.1 q.2)) ∧
      (∃ q : Fin 4 × Fin 4, GoodAl
        ((reflZ (h3Tab.root j) (h3Tab.coroot j) *
          reflZ (h3Tab.root k) (h3Tab.coroot k) -
          (4 : ZAl) • (1 : Matrix (Fin 4) (Fin 4) ZAl)) q.1 q.2)) := by
  decide +kernel

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_orderOf_conj (g x : U ≃ₗ[ZMod p] U) :
    orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (by unfold SemiconjBy; group)).symm

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3_pair_orders (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 4) (ZMod p) U) (j : Fin 15) (hj : h3Ord j = 5) :
    ∃ k : Fin 15,
      orderOf (h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f k) = 2 ∧
      orderOf (h3Tab.refl (evalAl hα) f j * h3Tab.refl (evalAl hα) f k) = 3 := by
  obtain ⟨k, h2, h3, ⟨q0, hg0⟩, ⟨q1, hg1⟩⟩ := tfmd_h3_pair_exists j hj
  refine ⟨k, ?_, ?_⟩
  · exact @orderOf_eq_prime (U ≃ₗ[ZMod p] U) _ _ 2 ⟨by norm_num⟩
      (ReflTable.pow_mul_refl_eq_one (T := h3Tab) (φ := evalAl hα) (f := f)
        h3Tab_valid hp h2)
      (ReflTable.mul_refl_ne_one (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid
        (fun x hx => evalAl_ne_zero hp hα hx) hp (a := q0.1) (b := q0.2) hg0)
  · exact @orderOf_eq_prime (U ≃ₗ[ZMod p] U) _ _ 3 ⟨by norm_num⟩
      (ReflTable.pow_mul_refl_eq_one (T := h3Tab) (φ := evalAl hα) (f := f)
        h3Tab_valid hp h3)
      (ReflTable.mul_refl_ne_one (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid
        (fun x hx => evalAl_ne_zero hp hα hx) hp (a := q1.1) (b := q1.2) hg1)

open CFSG.StandardType.ZS.PrimModel in
private theorem tfmd_h3_conj_pair {G : Subgroup (U ≃ₗ[ZMod p] U)} {a₀ : U ≃ₗ[ZMod p] U}
    (hcl : ∀ x ∈ G, IsRefl p x → ∃ g ∈ G, x = g * a₀ * g⁻¹)
    (hkey : ∀ b ∈ G, IsRefl p b → orderOf (a₀ * b) = 5 →
      ∃ t ∈ G, IsRefl p t ∧ orderOf (a₀ * t) = 2 ∧ orderOf (b * t) = 3) :
    ∀ a ∈ G, ∀ b ∈ G, ∀ w ∈ G, IsRefl p a → IsRefl p b → IsRefl p w →
      orderOf (a * b) = 5 →
      ∃ g ∈ G, orderOf (a * (g * w * g⁻¹)) = 2 ∧ orderOf (b * (g * w * g⁻¹)) = 3 := by
  intro a ha b hb w hw har hbr hwr hab
  obtain ⟨g₀, hg₀, ha_eq⟩ := hcl a ha har
  let b₁ : U ≃ₗ[ZMod p] U := g₀⁻¹ * b * g₀
  have hb₁G : b₁ ∈ G := Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀) hb) hg₀
  have hb₁r : IsRefl p b₁ := IsRefl.conj hbr g₀⁻¹
  have hord1 : orderOf (a₀ * b₁) = 5 := by
    have hc : g₀ * (a₀ * b₁) * g₀⁻¹ = a * b := by
      rw [ha_eq]; simp only [b₁]; group
    rw [← hab, ← hc, tfmd_orderOf_conj]
  obtain ⟨t, htG, htr, ht2, ht3⟩ := hkey b₁ hb₁G hb₁r hord1
  let w₁ : U ≃ₗ[ZMod p] U := g₀⁻¹ * w * g₀
  have hw₁G : w₁ ∈ G := Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₀) hw) hg₀
  have hw₁r : IsRefl p w₁ := IsRefl.conj hwr g₀⁻¹
  obtain ⟨u, huG, hwu⟩ := hcl w₁ hw₁G hw₁r
  obtain ⟨v, hvG, htv⟩ := hcl t htG htr
  refine ⟨g₀ * (v * u⁻¹) * g₀⁻¹, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₀
      (Subgroup.mul_mem _ hvG (Subgroup.inv_mem _ huG))) (Subgroup.inv_mem _ hg₀)
  · have hw_eq : w = g₀ * (u * a₀ * u⁻¹) * g₀⁻¹ := by
      rw [← hwu]; simp only [w₁]; group
    have hgw : g₀ * (v * u⁻¹) * g₀⁻¹ * w * (g₀ * (v * u⁻¹) * g₀⁻¹)⁻¹ =
        g₀ * t * g₀⁻¹ := by
      rw [hw_eq, htv]; group
    have heq : a * (g₀ * (v * u⁻¹) * g₀⁻¹ * w * (g₀ * (v * u⁻¹) * g₀⁻¹)⁻¹) =
        g₀ * (a₀ * t) * g₀⁻¹ := by
      rw [hgw, ha_eq]; group
    rw [heq, tfmd_orderOf_conj, ht2]
  · have hw_eq : w = g₀ * (u * a₀ * u⁻¹) * g₀⁻¹ := by
      rw [← hwu]; simp only [w₁]; group
    have hgw : g₀ * (v * u⁻¹) * g₀⁻¹ * w * (g₀ * (v * u⁻¹) * g₀⁻¹)⁻¹ =
        g₀ * t * g₀⁻¹ := by
      rw [hw_eq, htv]; group
    have heq : b * (g₀ * (v * u⁻¹) * g₀⁻¹ * w * (g₀ * (v * u⁻¹) * g₀⁻¹)⁻¹) =
        g₀ * (b₁ * t) * g₀⁻¹ := by
      rw [hgw, show b = g₀ * b₁ * g₀⁻¹ by simp only [b₁]; group]; group
    rw [heq, tfmd_orderOf_conj, ht3]

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_vec4_apply (j : Fin 4) :
    (![-1, -1, -1, 1] : Fin 4 → ZMod p) j = if j = 0 ∨ j = 1 ∨ j = 2 then -1 else 1 := by
  fin_cases j <;> simp

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3_sign_product :
    (diagSignMat (Fin.castSucc (0 : Fin 3)) : Matrix (Fin 4) (Fin 4) (ZMod p)) *
      diagSignMat (Fin.castSucc (1 : Fin 3)) * diagSignMat (Fin.castSucc (2 : Fin 3)) =
    Matrix.diagonal ![-1, -1, -1, 1] := by
  rw [diagSignMat, diagSignMat, diagSignMat, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  fin_cases j <;> simp [tfmd_vec4_apply]

private lemma tfmd_h3_neg_apply (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) (d : W ≃ₗ[ZMod p] W)
    (hdf : ∀ i : Fin 3, d (f i.castSucc) = - f i.castSucc)
    {v : W} (hv : v ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)) :
    d v = -v := by
  refine Submodule.span_induction (p := fun x _ => d x = -x) ?_ ?_ ?_ ?_ hv
  · rintro x ⟨i, rfl⟩; exact hdf i
  · simp
  · intro a b _ _ iha ihb; rw [map_add, iha, ihb]; abel
  · intro c a _ iha; rw [map_smul, iha, smul_neg]

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3_neg_span (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) :
    HardMathSupport.Kantor79.commutatorSpace (basisClosure f (h3Mats α)) =
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  have hset : f '' (↑(Finset.univ.erase (3 : Fin 4)) : Set (Fin 4)) =
      Set.range (fun i : Fin 3 => f i.castSucc) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy3, -⟩ := Finset.mem_erase.mp hy
      obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hy3
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last i, Finset.mem_univ _⟩, rfl⟩
  rw [commutatorSpace_basisClosure_h3Mats hp f hα,
    ← span_image_erase_eq_ker_coord f 3, hset]

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3_neg_mem_moved (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) :
    (LinearEquiv.neg (ZMod p) : HardMathSupport.Kantor79.commutatorSpace
      (basisClosure f (h3Mats α)) ≃ₗ[ZMod p] _) ∈
      movedGroup (basisClosure f (h3Mats α)) := by
  let H : Subgroup (W ≃ₗ[ZMod p] W) := basisClosure f (h3Mats α)
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  show LinearEquiv.neg (ZMod p) ∈ φ.range
  have h0 := h3_toMatrix_diag hp f hα (0 : Fin 3)
  have h14 := h3_toMatrix_diag hp f hα (1 : Fin 3)
  have h13 := h3_toMatrix_diag hp f hα (2 : Fin 3)
  let d : W ≃ₗ[ZMod p] W := h3Tab.refl (evalAl hα) f (h3UnitIdx 0) *
    h3Tab.refl (evalAl hα) f (h3UnitIdx 1) * h3Tab.refl (evalAl hα) f (h3UnitIdx 2)
  have hdG : d ∈ h3Tab.group (evalAl hα) f := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
    · exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp _
    · exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp _
    · exact ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα) (f := f) h3Tab_valid hp _
  have hdH : d ∈ H := by
    rw [show H = h3Tab.group (evalAl hα) f from h3_basisClosure_eq hp f hα]
    exact hdG
  refine MonoidHom.mem_range.mpr ⟨⟨d, hdH⟩, ?_⟩
  have hmat : LinearMap.toMatrix f f (d : W →ₗ[ZMod p] W) = Matrix.diagonal ![-1, -1, -1, 1] := by
    have hd_eq : (d : W →ₗ[ZMod p] W) =
        (h3Tab.refl (evalAl hα) f (h3UnitIdx 0) : W →ₗ[ZMod p] W) *
          (h3Tab.refl (evalAl hα) f (h3UnitIdx 1) : W →ₗ[ZMod p] W) *
          (h3Tab.refl (evalAl hα) f (h3UnitIdx 2) : W →ₗ[ZMod p] W) := by
      simp only [d, LinearEquiv.coe_toLinearMap_mul]
    rw [hd_eq, LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, h0, h14, h13]
    exact tfmd_h3_sign_product
  have hdf : ∀ i : Fin 3, d (f i.castSucc) = - f i.castSucc := by
    intro i
    have h := apply_basis_of_toMatrix_eq_diagonal f hmat i.castSucc
    rw [h, show (![-1, -1, -1, 1] : Fin 4 → ZMod p) i.castSucc = -1 from by
      rw [tfmd_vec4_apply]; fin_cases i <;> simp]
    exact neg_one_smul (R := ZMod p) (f i.castSucc)
  have hV : V = Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) :=
    tfmd_h3_neg_span hp hα W f
  ext v
  rw [restrictHom_apply, LinearEquiv.neg_apply]
  have hmem : (v : W) ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
    rw [← hV]; exact v.2
  exact tfmd_h3_neg_apply W f d hdf hmem

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3data_hkey (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) :
    ∀ b ∈ h3Tab.group (evalAl hα) f, IsRefl p b →
      orderOf (h3Tab.refl (evalAl hα) f 0 * b) = 5 →
      ∃ t' ∈ h3Tab.group (evalAl hα) f, IsRefl p t' ∧
        orderOf (h3Tab.refl (evalAl hα) f 0 * t') = 2 ∧ orderOf (b * t') = 3 := by
  intro b hbG hbr hb5
  have htv : QTwoLin.TransvectionFree (h3Tab.group (evalAl hα) f) :=
    h3_transvectionFree hp f hα
  obtain ⟨j, rfl⟩ := ReflTable.exists_eq_refl (T := h3Tab) (φ := evalAl hα) (f := f)
    h3Tab_valid hp htv hbG hbr
  have hb5' : orderOf (h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f j) = 5 :=
    hb5
  have hj5 : h3Ord j = 5 := by
    by_contra h
    rcases (h3_ord_cases j).resolve_left h with ⟨hpos, hle3⟩
    have hpow := ReflTable.pow_mul_refl_eq_one (T := h3Tab) (φ := evalAl hα) (f := f)
      h3Tab_valid hp (h3_ord j)
    have hle := orderOf_le_of_pow_eq_one hpos hpow
    have hb5t : orderOf (h3Tab.refl (evalAl hα) f 0 * h3Tab.refl (evalAl hα) f j) = 5 :=
      hb5'
    omega
  obtain ⟨k, hk2, hk3⟩ := tfmd_h3_pair_orders hp hα f j hj5
  exact ⟨h3Tab.refl (evalAl hα) f k, ReflTable.refl_mem_group (T := h3Tab) (φ := evalAl hα)
    (f := f) h3Tab_valid hp k, ReflTable.isRefl_refl (T := h3Tab) (φ := evalAl hα) (f := f)
    h3Tab_valid hp k, hk2, hk3⟩

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3data_core (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) :
    ∀ x ∈ h3Tab.group (evalAl hα) f, ∀ y ∈ h3Tab.group (evalAl hα) f,
      ∀ w ∈ h3Tab.group (evalAl hα) f,
      IsRefl p x → IsRefl p y → IsRefl p w → orderOf (x * y) = 5 →
      ∃ g ∈ h3Tab.group (evalAl hα) f,
        orderOf (x * (g * w * g⁻¹)) = 2 ∧ orderOf (y * (g * w * g⁻¹)) = 3 := by
  intro x hx y hy w hw hxr hyr hwr hxy
  have htv : QTwoLin.TransvectionFree (h3Tab.group (evalAl hα) f) :=
    h3_transvectionFree hp f hα
  have hcl : ∀ z ∈ h3Tab.group (evalAl hα) f, IsRefl p z →
      ∃ g ∈ h3Tab.group (evalAl hα) f, z = g * h3Tab.refl (evalAl hα) f 0 * g⁻¹ := by
    intro z hz hzr
    obtain ⟨i, -, hconj⟩ := h3_forall_conj hp f hα hz hzr
    exact hconj
  have hkey := tfmd_h3data_hkey hp hα W f
  exact tfmd_h3_conj_pair hcl hkey x hx y hy w hw hxr hyr hwr hxy

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3data_descend (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (H : Subgroup (W ≃ₗ[ZMod p] W))
    (φ : H →* (HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H))
    (hinj : Function.Injective φ)
    {x y w : HardMathSupport.Kantor79.commutatorSpace H ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace H}
    {x' y' w' : W ≃ₗ[ZMod p] W}
    (hx'H : x' ∈ H) (hy'H : y' ∈ H) (hw'H : w' ∈ H)
    (hx' : φ ⟨x', hx'H⟩ = x) (hy' : φ ⟨y', hy'H⟩ = y) (hw' : φ ⟨w', hw'H⟩ = w)
    {g' : W ≃ₗ[ZMod p] W} (hg'H : g' ∈ H)
    (hg'2 : orderOf (x' * (g' * w' * g'⁻¹)) = 2)
    (hg'3 : orderOf (y' * (g' * w' * g'⁻¹)) = 3) :
    ∃ g ∈ φ.range, orderOf (x * (g * w * g⁻¹)) = 2 ∧
      orderOf (y * (g * w * g⁻¹)) = 3 := by
  refine ⟨φ ⟨g', hg'H⟩, MonoidHom.mem_range.mpr ⟨⟨g', hg'H⟩, rfl⟩, ?_, ?_⟩
  · have heq : x * (φ ⟨g', hg'H⟩ * w * (φ ⟨g', hg'H⟩)⁻¹) =
        φ (⟨x', hx'H⟩ * (⟨g', hg'H⟩ * ⟨w', hw'H⟩ * (⟨g', hg'H⟩)⁻¹)) := by
      rw [← hx', ← hw', map_mul, map_mul, map_mul, map_inv]
    rw [heq, orderOf_injective φ hinj]
    have hcoe := Subgroup.orderOf_coe (⟨x', hx'H⟩ * (⟨g', hg'H⟩ * ⟨w', hw'H⟩ * (⟨g', hg'H⟩)⁻¹))
    rw [← hcoe]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hg'2
  · have heq : y * (φ ⟨g', hg'H⟩ * w * (φ ⟨g', hg'H⟩)⁻¹) =
        φ (⟨y', hy'H⟩ * (⟨g', hg'H⟩ * ⟨w', hw'H⟩ * (⟨g', hg'H⟩)⁻¹)) := by
      rw [← hy', ← hw', map_mul, map_mul, map_mul, map_inv]
    rw [heq, orderOf_injective φ hinj]
    have hcoe := Subgroup.orderOf_coe (⟨y', hy'H⟩ * (⟨g', hg'H⟩ * ⟨w', hw'H⟩ * (⟨g', hg'H⟩)⁻¹))
    rw [← hcoe]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hg'3

open CFSG.StandardType.ZS.PrimModel in
private lemma tfmd_h3data_conj (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) :
    ∀ x ∈ movedGroup (basisClosure f (h3Mats α)),
      ∀ y ∈ movedGroup (basisClosure f (h3Mats α)),
      ∀ w ∈ movedGroup (basisClosure f (h3Mats α)),
      IsRefl p x → IsRefl p y → IsRefl p w → orderOf (x * y) = 5 →
      ∃ g ∈ movedGroup (basisClosure f (h3Mats α)),
        orderOf (x * (g * w * g⁻¹)) = 2 ∧ orderOf (y * (g * w * g⁻¹)) = 3 := by
  let H : Subgroup (W ≃ₗ[ZMod p] W) := basisClosure f (h3Mats α)
  let V := HardMathSupport.Kantor79.commutatorSpace H
  let φ := restrictHom H V (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
  let G : Subgroup (W ≃ₗ[ZMod p] W) := h3Tab.group (evalAl hα) f
  have hs : SplitSupport H 3 := splitSupport_basisClosure_h3Mats hp f hα
  have hinj : Function.Injective φ := restrictHom_injective_of_splitSupport hs
  have htab : H = G := h3_basisClosure_eq hp f hα
  intro x hx y hy w hw hxr hyr hwr hxy
  obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨y', hy'⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨w', hw'⟩ := MonoidHom.mem_range.mp hw
  have hxr' : IsRefl p (x' : W ≃ₗ[ZMod p] W) :=
    isRefl_of_isRefl_restrictHom hs (hx'.symm ▸ hxr)
  have hyr' : IsRefl p (y' : W ≃ₗ[ZMod p] W) :=
    isRefl_of_isRefl_restrictHom hs (hy'.symm ▸ hyr)
  have hwr' : IsRefl p (w' : W ≃ₗ[ZMod p] W) :=
    isRefl_of_isRefl_restrictHom hs (hw'.symm ▸ hwr)
  have hxy' : orderOf ((x' : W ≃ₗ[ZMod p] W) * (y' : W ≃ₗ[ZMod p] W)) = 5 := by
    have h := hxy
    rw [← hx', ← hy', ← map_mul] at h
    rw [orderOf_injective φ hinj] at h
    rw [← Subgroup.orderOf_coe ((x' : H) * y')] at h
    simpa [Subgroup.coe_mul] using h
  have hx'G : (x' : W ≃ₗ[ZMod p] W) ∈ G := by rw [← htab]; exact x'.2
  have hy'G : (y' : W ≃ₗ[ZMod p] W) ∈ G := by rw [← htab]; exact y'.2
  have hw'G : (w' : W ≃ₗ[ZMod p] W) ∈ G := by rw [← htab]; exact w'.2
  obtain ⟨g', hg'G, hg'2, hg'3⟩ :=
    tfmd_h3data_core hp hα W f (x' : W ≃ₗ[ZMod p] W) hx'G (y' : W ≃ₗ[ZMod p] W) hy'G
      (w' : W ≃ₗ[ZMod p] W) hw'G hxr' hyr' hwr' hxy'
  have hg'H : g' ∈ H := by rw [htab]; exact hg'G
  exact tfmd_h3data_descend W H φ hinj x'.2 y'.2 w'.2 hx' hy' hw' hg'H hg'2 hg'3

open CFSG.StandardType.ZS.PrimModel in
private theorem tfmd_h3data_model (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (W : Type) [AddCommGroup W] [Module (ZMod p) W]
    (f : Module.Basis (Fin 4) (ZMod p) W) :
    H3Data p (movedGroup (basisClosure f (h3Mats α))) :=
  ⟨tfmd_h3_neg_mem_moved hp hα W f, tfmd_h3data_conj hp hα W f⟩

theorem tfH3DataModel_holds : TFH3DataModel p := by
  intro W _ _ f α hp hα
  exact tfmd_h3data_model hp hα W f

end CFSG.StandardType.ZS.TableFacts

end
