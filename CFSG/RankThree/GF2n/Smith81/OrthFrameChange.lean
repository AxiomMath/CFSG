module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorAlg
public import CFSG.RankThree.GF2n.Smith81.OrthTypes

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)
open scoped Matrix

section Equiv

variable {K ι : Type} [Field K]

theorem orthTensor_id_comp (g g' : Matrix (Fin 2) (Fin 2) K) (p : (ι → K) × (ι → K)) :
    orthTensor g id (orthTensor g' id p) = orthTensor (g * g') id p := by
  simpa using orthTensor_comp g g' LinearMap.id LinearMap.id p

theorem orthTensor_pure_apply (g : Matrix (Fin 2) (Fin 2) K) (c : Fin 2 → K) (u : ι → K) :
    orthTensor g id (c 0 • u, c 1 • u) = ((g *ᵥ c) 0 • u, (g *ᵥ c) 1 • u) := by
  have h0 : (g *ᵥ c) 0 = g 0 0 * c 0 + g 0 1 * c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (g *ᵥ c) 1 = g 1 0 * c 0 + g 1 1 * c 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  simp only [orthTensor, id_eq, Prod.mk.injEq]
  constructor <;> module

theorem det_units_inv_eq_one (h : GL (Fin 2) K)
    (hdet : (h : Matrix (Fin 2) (Fin 2) K).det = 1) :
    ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  have h1 := congrArg Matrix.det (Units.mul_inv h)
  rw [Matrix.det_mul, hdet, one_mul, Matrix.det_one] at h1
  exact h1

theorem mul_conj_cancel_of_mul_eq_one {H Hi : Matrix (Fin 2) (Fin 2) K} (hHHi : H * Hi = 1)
    (g : Matrix (Fin 2) (Fin 2) K) : H * (Hi * g * H) * Hi = g := by
  calc H * (Hi * g * H) * Hi = (H * Hi) * g * (H * Hi) := by simp only [mul_assoc]
    _ = g := by rw [hHHi, one_mul, mul_one]

@[expose] def orthTensorEquiv (h : GL (Fin 2) K) :
    ((ι → K) × (ι → K)) ≃ₗ[K] ((ι → K) × (ι → K)) where
  toFun p := orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p
  invFun p := orthTensor ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) id p
  map_add' p q := by
    simp only [orthTensor, Prod.fst_add, Prod.snd_add, id_eq, Prod.mk_add_mk, Prod.mk.injEq]
    constructor <;> module
  map_smul' c p := by
    simp only [orthTensor, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, id_eq, RingHom.id_apply,
      Prod.mk.injEq]
    constructor <;> module
  left_inv p := by
    show orthTensor _ id (orthTensor _ id p) = p
    rw [orthTensor_id_comp, Units.inv_mul, orthTensor_one_id]
  right_inv p := by
    show orthTensor _ id (orthTensor _ id p) = p
    rw [orthTensor_id_comp, Units.mul_inv, orthTensor_one_id]

theorem orthTensorEquiv_apply (h : GL (Fin 2) K) (p : (ι → K) × (ι → K)) :
    orthTensorEquiv h p = orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p :=
  rfl

end Equiv

section Polar

variable {K ι : Type} [Field K]

theorem polar_orthTensor_id [CharP K 2] (qU : QuadraticForm K (ι → K))
    (h : Matrix (Fin 2) (Fin 2) K) (p : (ι → K) × (ι → K)) :
    QuadraticMap.polar qU (orthTensor h id p).1 (orthTensor h id p).2 =
      h.det * QuadraticMap.polar qU p.1 p.2 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdiag : ∀ a : ι → K, QuadraticMap.polar qU a a = 0 := by
    intro a
    rw [QuadraticMap.polar_self, two_nsmul, ← two_mul, h2, zero_mul]
  obtain ⟨a, b⟩ := p
  simp only [orthTensor, id_eq, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hdiag, Matrix.det_fin_two,
    smul_eq_mul]
  rw [QuadraticMap.polar_comm qU b a]
  linear_combination (h 0 1 * h 1 0 * QuadraticMap.polar qU a b) * h2

end Polar

section TypeA

variable {K ι : Type} [Field K] [CharP K 2]

theorem pairTypeA_orthTensor_id_iff (h : GL (Fin 2) K) (qU : QuadraticForm K (ι → K))
    (p : (ι → K) × (ι → K)) :
    PairTypeA qU (orthTensor (h : Matrix (Fin 2) (Fin 2) K) id p) ↔ PairTypeA qU p := by
  have key : ∀ (g : GL (Fin 2) K) (p : (ι → K) × (ι → K)), PairTypeA qU p →
      PairTypeA qU (orthTensor (g : Matrix (Fin 2) (Fin 2) K) id p) := by
    intro g p hp
    have hdet : (g : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (Units.mul_inv g)
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
      exact zero_ne_one h1
    exact pairTypeA_orthTensor qU (RingEquiv.refl K) (g : Matrix (Fin 2) (Fin 2) K) hdet id
      Function.bijective_id (fun _ _ => rfl) (fun _ _ => rfl) 1 one_ne_zero
      (fun u => by simp) hp
  refine ⟨fun hp => ?_, key h p⟩
  have h' := key h⁻¹ _ hp
  rwa [orthTensor_id_comp, Units.inv_mul, orthTensor_one_id] at h'

end TypeA

section Frame

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem OrthPreFrame.change [CharP K 2] (hF : OrthPreFrame Q Z M₀ qU φ) {h : GL (Fin 2) K}
    (hdet : (h : Matrix (Fin 2) (Fin 2) K).det = 1) :
    OrthPreFrame Q Z M₀ qU (φ.trans (orthTensorEquiv h)) := by
  refine ⟨hF.nondeg, fun e => ?_⟩
  simp only [LinearEquiv.trans_apply, orthTensorEquiv_apply]
  rw [polar_orthTensor_id, hdet, one_mul]
  exact hF.qf e

theorem OrthFrame.change [CharP K 2] (hF : OrthFrame Q Z M₀ qU φ) {h : GL (Fin 2) K}
    (hdet : (h : Matrix (Fin 2) (Fin 2) K).det = 1) :
    OrthFrame Q Z M₀ qU (φ.trans (orthTensorEquiv h)) where
  nondeg := hF.nondeg
  qf := (hF.toPreFrame.change hdet).qf
  root z hz hz1 x hx hxZ := by
    rw [LinearEquiv.trans_apply, orthTensorEquiv_apply, pairTypeA_orthTensor_id_iff]
    exact hF.root z hz hz1 x hx hxZ

end Frame

section Acts

variable {G : Type} [Group G] {Q Z : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem ActsAsTensor.change {s : G} {g : Matrix (Fin 2) (Fin 2) K} {o : (ι → K) → (ι → K)}
    (hs : ActsAsTensor Q Z M₀ φ s g o) (h : GL (Fin 2) K)
    (ho : ∀ x y : ι → K, o (x + y) = o x + o y) (ho' : ∀ (c : K) x, o (c • x) = c • o x) :
    ActsAsTensor Q Z M₀ (φ.trans (orthTensorEquiv h)) s
      ((h : Matrix (Fin 2) (Fin 2) K) * g * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      o := by
  obtain ⟨O, rfl⟩ : ∃ O : (ι → K) →ₗ[K] (ι → K), ⇑O = o :=
    ⟨{ toFun := o, map_add' := ho, map_smul' := fun c x => ho' c x }, rfl⟩
  intro x hx
  have hL := orthTensor_comp (h : Matrix (Fin 2) (Fin 2) K) g LinearMap.id O (φ (M₀.π x))
  have hR := orthTensor_comp
    ((h : Matrix (Fin 2) (Fin 2) K) * g * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
    (h : Matrix (Fin 2) (Fin 2) K) O LinearMap.id (φ (M₀.π x))
  simp only [LinearMap.id_coe, LinearMap.id_comp, LinearMap.comp_id] at hL hR
  have hHH : (h : Matrix (Fin 2) (Fin 2) K) * g * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      * (h : Matrix (Fin 2) (Fin 2) K) = (h : Matrix (Fin 2) (Fin 2) K) * g := by
    rw [mul_assoc ((h : Matrix (Fin 2) (Fin 2) K) * g)
      ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) (h : Matrix (Fin 2) (Fin 2) K),
      Units.inv_mul, mul_one]
  rw [hHH] at hR
  simp only [LinearEquiv.trans_apply, orthTensorEquiv_apply]
  rw [hs x hx]
  exact hL.trans hR.symm

theorem OrthAct.change {S : Subgroup G} (hA : OrthAct Q Z M₀ qU φ S) {h : GL (Fin 2) K}
    (hdet : (h : Matrix (Fin 2) (Fin 2) K).det = 1) :
    OrthAct Q Z M₀ qU (φ.trans (orthTensorEquiv h)) S where
  act s hs := by
    obtain ⟨g, o, hg, hq, hsa⟩ := hA.act s hs
    refine ⟨(h : Matrix (Fin 2) (Fin 2) K) * g * ((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K),
      o, ?_, hq, hsa.change h (fun x y => map_add o x y) (fun c x => map_smul o c x)⟩
    simp only [Matrix.det_mul, hg, hdet, det_units_inv_eq_one h hdet, one_mul, mul_one]
  sl g hg := by
    obtain ⟨s, hs, hsa⟩ := hA.sl
      (((h⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * g * (h : Matrix (Fin 2) (Fin 2) K))
      (by simp only [Matrix.det_mul, hg, hdet, det_units_inv_eq_one h hdet, one_mul, mul_one])
    refine ⟨s, hs, ?_⟩
    have hc := hsa.change h (fun x y => rfl) (fun c x => rfl)
    rwa [mul_conj_cancel_of_mul_eq_one (Units.mul_inv h) g] at hc
  eich a w ha hw := by
    obtain ⟨s, hs, hsa⟩ := hA.eich a w ha hw
    refine ⟨s, hs, ?_⟩
    have hc := hsa.change h (fun x y => map_add (eichler qU a w) x y)
      (fun c x => map_smul (eichler qU a w) c x)
    rwa [mul_one, Units.mul_inv] at hc

end Acts

section SL2

variable {K : Type} [Field K]

theorem exists_SL_mulVec_eq (c : Fin 2 → K) (hc : c ≠ 0) :
    ∃ h : GL (Fin 2) K, (h : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      (h : Matrix (Fin 2) (Fin 2) K) *ᵥ c = ![1, 0] := by
  have key : ∀ M : Matrix (Fin 2) (Fin 2) K, M.det = 1 → M *ᵥ c = ![1, 0] →
      ∃ h : GL (Fin 2) K, (h : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
        (h : Matrix (Fin 2) (Fin 2) K) *ᵥ c = ![1, 0] := by
    intro M hM hMc
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), ?_, ?_⟩
    · simpa using hM
    · simpa using hMc
  by_cases h0 : c 0 = 0
  · have h1 : c 1 ≠ 0 := by
      intro h1
      apply hc
      funext k
      fin_cases k <;> simp [h0, h1]
    refine key !![0, (c 1)⁻¹; -c 1, 0] ?_ ?_
    · simp [Matrix.det_fin_two_of, h1]
    · funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · refine key !![(c 0)⁻¹, 0; -c 1, c 0] ?_ ?_
    · simp [Matrix.det_fin_two_of, h0]
    · funext k
      fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0] <;> ring

theorem exists_change_pure {ι : Type} (c : Fin 2 → K) (hc : c ≠ 0) (u : ι → K) :
    ∃ h : GL (Fin 2) K, (h : Matrix (Fin 2) (Fin 2) K).det = 1 ∧
      orthTensor (h : Matrix (Fin 2) (Fin 2) K) id (c 0 • u, c 1 • u) = (u, 0) := by
  obtain ⟨h, hdet, hmul⟩ := exists_SL_mulVec_eq c hc
  refine ⟨h, hdet, ?_⟩
  rw [orthTensor_pure_apply, hmul]
  simp

end SL2

end CFSG.RankThree.GF2n.Smith81
