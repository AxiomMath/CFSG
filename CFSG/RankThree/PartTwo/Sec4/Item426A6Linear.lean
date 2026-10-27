module

public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426

open Matrix

variable {E : Type*} [Field E]

theorem mulVec_injective_of_isUnit {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n E} (hA : IsUnit A.det) : Function.Injective A.mulVec := by
  intro v w h
  have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have := congrArg (A⁻¹).mulVec h
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec,
    Matrix.one_mulVec] at this

theorem eq_top_of_invariant {A B : Matrix (Fin 3) (Fin 3) E} (hA : IsUnit A.det)
    (hB : IsUnit B.det) {ω : E} (hω : orderOf ω = 3) {W : Submodule E (Fin 3 → E)}
    (hW : W ≠ ⊥) (hAW : ∀ v ∈ W, A.mulVec v ∈ W) (hBW : ∀ v ∈ W, B.mulVec v ∈ W)
    (hAB : ∀ v ∈ W, A.mulVec (B.mulVec v) = ω • B.mulVec (A.mulVec v)) : W = ⊤ := by
  set f := Matrix.toLin' A with hf
  set g := Matrix.toLin' B with hg
  have hfW : ∀ v ∈ W, f v ∈ W := fun v hv => by rw [hf, Matrix.toLin'_apply]; exact hAW v hv
  have hgW : ∀ v ∈ W, g v ∈ W := fun v hv => by rw [hg, Matrix.toLin'_apply]; exact hBW v hv
  set fW := f.restrict hfW with hfWdef
  set gW := g.restrict hgW with hgWdef
  have hrel : fW ∘ₗ gW = ω • (gW ∘ₗ fW) := by
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, hfWdef, hgWdef,
      LinearMap.restrict_apply, Submodule.coe_smul, hf, hg, Matrix.toLin'_apply]
    exact congrFun (hAB v v.2) _
  have hinj : ∀ {M : Matrix (Fin 3) (Fin 3) E} (hM : IsUnit M.det)
      (hMW : ∀ v ∈ W, Matrix.toLin' M v ∈ W),
      LinearMap.det ((Matrix.toLin' M).restrict hMW) ≠ 0 := by
    intro M hM hMW
    have hi : Function.Injective ((Matrix.toLin' M).restrict hMW) := by
      intro v w h
      apply Subtype.ext
      have h' := congrArg Subtype.val h
      simp only [LinearMap.restrict_apply, Matrix.toLin'_apply] at h'
      exact mulVec_injective_of_isUnit hM h'
    have hu : IsUnit ((Matrix.toLin' M).restrict hMW) :=
      (Module.End.isUnit_iff _).mpr ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩
    exact ((LinearMap.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hdf : LinearMap.det fW ≠ 0 := hinj hA hfW
  have hdg : LinearMap.det gW ≠ 0 := hinj hB hgW
  have hdet := congrArg LinearMap.det hrel
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_comp] at hdet
  have hpow : ω ^ Module.finrank E W = 1 := by
    have h1 : LinearMap.det fW * LinearMap.det gW * (ω ^ Module.finrank E W - 1) = 0 := by
      linear_combination (-1 : E) * hdet
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (mul_ne_zero hdf hdg)
    · exact sub_eq_zero.mp h
  have h3 : 3 ∣ Module.finrank E W := by
    have h := orderOf_dvd_of_pow_eq_one hpow
    rwa [hω] at h
  have hle : Module.finrank E W ≤ 3 := by
    have := Submodule.finrank_le W
    rwa [Module.finrank_fin_fun] at this
  have hne : Module.finrank E W ≠ 0 := by
    rwa [Ne, Submodule.finrank_eq_zero]
  have heq : Module.finrank E W = Module.finrank E (Fin 3 → E) := by
    rw [Module.finrank_fin_fun]
    omega
  exact Submodule.eq_top_of_finrank_eq heq

theorem eq_one_of_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n E}
    (h : ∀ v, C.mulVec v = v) : C = 1 := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_one, LinearMap.id_apply]
  exact h v

theorem eq_smul_one_of_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n] {C : Matrix n n E}
    {l : E} (h : ∀ v, C.mulVec v = l • v) : C = l • (1 : Matrix n n E) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun v => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  exact h v

theorem mulVec_mem_eigenspace {n : Type*} [Fintype n] [DecidableEq n] {C A : Matrix n n E}
    (hCA : C * A = A * C) {l : E} {v : n → E}
    (hv : v ∈ Module.End.eigenspace (Matrix.toLin' C) l) :
    A.mulVec v ∈ Module.End.eigenspace (Matrix.toLin' C) l := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
  rw [Matrix.mulVec_mulVec, hCA, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

theorem eq_smul_one_of_commute [IsAlgClosed E] (h3 : (3 : E) ≠ 0)
    {A B C : Matrix (Fin 3) (Fin 3) E} (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hABC : A * B = C * (B * A)) (hCA : C * A = A * C) (hCB : C * B = B * C) (hC3 : C ^ 3 = 1)
    (hC1 : C ≠ 1) : ∃ l : E, orderOf l = 3 ∧ C = l • (1 : Matrix (Fin 3) (Fin 3) E) := by
  obtain ⟨v, hv⟩ : ∃ v, C.mulVec v ≠ v := by
    by_contra h
    exact hC1 (eq_one_of_mulVec_eq fun v => by
      by_contra hv
      exact h ⟨v, hv⟩)
  set Q := C ^ 2 + C + 1 with hQ
  set U := LinearMap.ker (Matrix.toLin' Q) with hU
  have hQC : Q * C = C * Q := by rw [hQ]; noncomm_ring
  have hCU : ∀ x ∈ U, Matrix.toLin' C x ∈ U := by
    intro x hx
    rw [hU, LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hQC, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero]
  set w := C.mulVec v - v with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hv
  have hwU : w ∈ U := by
    rw [hU, LinearMap.mem_ker, Matrix.toLin'_apply, hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    have h1 : Q * C = C ^ 3 + C ^ 2 + C := by rw [hQ]; noncomm_ring
    have h2 : C ^ 3 + C ^ 2 + C = Q + (C ^ 3 - 1) := by rw [hQ]; noncomm_ring
    rw [h1, h2, hC3, sub_self, add_zero, sub_self]
  have : Nontrivial U := ⟨⟨⟨w, hwU⟩, 0, fun h => hw0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨l, hl⟩ := Module.End.exists_eigenvalue ((Matrix.toLin' C).restrict hCU)
  obtain ⟨u, hu, hu0⟩ := hl.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hu
  have hCu : C.mulVec (u : Fin 3 → E) = l • (u : Fin 3 → E) := by
    have := congrArg Subtype.val hu
    simpa [LinearMap.restrict_apply, Matrix.toLin'_apply] using this
  have hu0' : (u : Fin 3 → E) ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hl2 : l ^ 2 + l + 1 = 0 := by
    have hQu : Q.mulVec (u : Fin 3 → E) = 0 := by
      have hu2 : (u : Fin 3 → E) ∈ LinearMap.ker (Matrix.toLin' Q) := u.2
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hu2
      exact hu2
    have hQu' : Q.mulVec (u : Fin 3 → E) = (l ^ 2 + l + 1) • (u : Fin 3 → E) := by
      rw [hQ, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, sq,
        ← Matrix.mulVec_mulVec, hCu, Matrix.mulVec_smul, hCu, smul_smul, add_smul, add_smul,
        one_smul, sq]
    rw [hQu'] at hQu
    exact (smul_eq_zero.mp hQu).resolve_right hu0'
  have hl3 : l ^ 3 = 1 := by linear_combination (l - 1) * hl2
  have hl1 : l ≠ 1 := by
    intro h
    rw [h] at hl2
    apply h3
    linear_combination hl2
  have hlo : orderOf l = 3 := orderOf_eq_prime hl3 hl1
  set W := Module.End.eigenspace (Matrix.toLin' C) l with hWdef
  have huW : (u : Fin 3 → E) ∈ W := by
    rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    exact hCu
  have hW : W ≠ ⊥ := fun h => hu0' (by rw [h] at huW; exact huW)
  have hAW : ∀ x ∈ W, A.mulVec x ∈ W := fun x hx => mulVec_mem_eigenspace hCA hx
  have hBW : ∀ x ∈ W, B.mulVec x ∈ W := fun x hx => mulVec_mem_eigenspace hCB hx
  have hrel : ∀ x ∈ W, A.mulVec (B.mulVec x) = l • B.mulVec (A.mulVec x) := by
    intro x hx
    have hBA : B.mulVec (A.mulVec x) ∈ W := hBW _ (hAW x hx)
    rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hBA
    rw [Matrix.mulVec_mulVec, hABC, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBA]
  have htop := eq_top_of_invariant hA hB hlo hW hAW hBW hrel
  refine ⟨l, hlo, eq_smul_one_of_mulVec_eq fun x => ?_⟩
  have hx : x ∈ W := htop ▸ Submodule.mem_top
  rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
  exact hx

theorem exists_scalar_of_commute {F : Type*} [Field F] (h3 : (3 : F) ≠ 0)
    {a b c y : Matrix (Fin 3) (Fin 3) F} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (habc : a * b = c * (b * a)) (hca : c * a = a * c) (hcb : c * b = b * c) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hya : y * a = a * y) (hyb : y * b = b * y) :
    ∃ μ : F, y = Matrix.scalar (Fin 3) μ := by
  set E := AlgebraicClosure F
  set φ := algebraMap F E with hφ
  have hφi : Function.Injective φ := φ.injective
  set Φ := φ.mapMatrix (m := Fin 3) with hΦ
  have hΦi : Function.Injective Φ := by
    intro M N h
    rw [hΦ, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    exact Matrix.map_injective hφi h
  have hunit : ∀ {M : Matrix (Fin 3) (Fin 3) F}, IsUnit M.det → IsUnit (Φ M).det := fun h => by
    rw [hΦ, ← RingHom.map_det]
    exact h.map φ
  have h3E : (3 : E) ≠ 0 := by
    intro h
    apply h3
    apply hφi
    rw [map_ofNat, h, map_zero]
  obtain ⟨l, hlo, hC⟩ := eq_smul_one_of_commute h3E (hunit ha) (hunit hb)
    (by rw [← map_mul, ← map_mul, ← map_mul, habc]) (by rw [← map_mul, ← map_mul, hca])
    (by rw [← map_mul, ← map_mul, hcb]) (by rw [← map_pow, hc3, map_one])
    (fun h => hc1 (hΦi (by rw [h, map_one])))
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (Φ y))
  obtain ⟨u, hu, hu0⟩ := hμ.exists_hasEigenvector
  set W := Module.End.eigenspace (Matrix.toLin' (Φ y)) μ with hWdef
  have hW : W ≠ ⊥ := fun h => hu0 (by
    have hu' : u ∈ W := hu
    rw [h] at hu'
    exact hu')
  have hAW : ∀ x ∈ W, (Φ a).mulVec x ∈ W := fun x hx =>
    mulVec_mem_eigenspace (by rw [← map_mul, ← map_mul, hya]) hx
  have hBW : ∀ x ∈ W, (Φ b).mulVec x ∈ W := fun x hx =>
    mulVec_mem_eigenspace (by rw [← map_mul, ← map_mul, hyb]) hx
  have hrel : ∀ x ∈ W, (Φ a).mulVec ((Φ b).mulVec x) = l • (Φ b).mulVec ((Φ a).mulVec x) := by
    intro x _
    rw [Matrix.mulVec_mulVec, ← map_mul, habc, map_mul, hC, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_mulVec, map_mul, ← Matrix.mulVec_mulVec]
  have htop := eq_top_of_invariant (hunit ha) (hunit hb) hlo hW hAW hBW hrel
  have hY : Φ y = μ • (1 : Matrix (Fin 3) (Fin 3) E) := eq_smul_one_of_mulVec_eq fun x => by
    have hx : x ∈ W := htop ▸ Submodule.mem_top
    rw [hWdef, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hx
    exact hx
  have hent : ∀ i j, φ (y i j) = if i = j then μ else 0 := fun i j => by
    have := congrFun (congrFun hY i) j
    rw [hΦ, RingHom.mapMatrix_apply, Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨y 0 0, Matrix.ext fun i j => ?_⟩
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · subst hij
    apply hφi
    rw [hent, hent]
    simp
  · apply hφi
    rw [hent, map_zero]
    simp [hij]

end CFSG.RankThree.PartTwo.Sec4.Item426
