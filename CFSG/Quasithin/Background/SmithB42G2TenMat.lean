module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTensor

public section

namespace CFSG.Quasithin.B42G2Ten

open Matrix CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7a
open scoped Kronecker

section Pivot

variable {G : Type*} [Group G] {k : Type*} [Field k] {κ ν : Type*} [Fintype κ]

structure IsPivot [DecidableEq κ] [Fintype ν] [DecidableEq ν] (R : G →* Matrix κ κ k)
    (ι : ν → κ) (S : Matrix κ ν k) : Prop where
  sec : S.submatrix ι id = 1
  inv : ∀ g, R g * S = S * (R g * S).submatrix ι id

omit [Fintype κ] in
theorem submatrix_mul_id {μ μ' : Type*} [Fintype μ] (ι : ν → κ) (A : Matrix κ μ k)
    (B : Matrix μ μ' k) : (A * B).submatrix ι id = A.submatrix ι id * B := by
  ext π π'
  simp [Matrix.mul_apply]

omit [Fintype κ] in
theorem submatrix_mulVec_id {μ : Type*} [Fintype μ] (ι : ν → κ) (A : Matrix κ μ k) (x : μ → k)
    (π : ν) : (A.submatrix ι id).mulVec x π = A.mulVec x (ι π) := rfl

variable [DecidableEq κ] [Fintype ν] [DecidableEq ν]

@[expose] def pivotRep {R : G →* Matrix κ κ k} {ι : ν → κ} {S : Matrix κ ν k}
    (h : IsPivot R ι S) : G →* Matrix ν ν k where
  toFun g := (R g * S).submatrix ι id
  map_one' := by rw [map_one, Matrix.one_mul, h.sec]
  map_mul' g g' := by
    have e : R (g * g') * S = R g * S * (R g' * S).submatrix ι id := by
      conv_lhs => rw [map_mul, Matrix.mul_assoc, h.inv g', ← Matrix.mul_assoc]
    change (R (g * g') * S).submatrix ι id = _
    rw [e, submatrix_mul_id ι (R g * S)]

variable {R : G →* Matrix κ κ k} {ι : ν → κ} {S : Matrix κ ν k}

theorem pivotRep_apply (h : IsPivot R ι S) (g : G) :
    pivotRep h g = (R g * S).submatrix ι id := rfl

theorem sec_mul_pivotRep (h : IsPivot R ι S) (g : G) : S * pivotRep h g = R g * S :=
  (h.inv g).symm

theorem pivotRep_mulVec (h : IsPivot R ι S) (g : G) (x : ν → k) (π : ν) :
    (pivotRep h g).mulVec x π = (R g).mulVec (S.mulVec x) (ι π) := by
  rw [pivotRep_apply, submatrix_mulVec_id, ← Matrix.mulVec_mulVec]

theorem sec_mulVec_pivotRep (h : IsPivot R ι S) (g : G) (x : ν → k) :
    S.mulVec ((pivotRep h g).mulVec x) = (R g).mulVec (S.mulVec x) := by
  rw [Matrix.mulVec_mulVec, sec_mul_pivotRep, ← Matrix.mulVec_mulVec]

theorem sec_mulVec_restrict (h : IsPivot R ι S) (x : ν → k) (π : ν) :
    S.mulVec x (ι π) = x π := by
  rw [← submatrix_mulVec_id, h.sec, Matrix.one_mulVec]

theorem IsPivot.of_subspace (V : Submodule k (κ → k))
    (hV : ∀ g, ∀ w ∈ V, (R g).mulVec w ∈ V) (hS : ∀ x, S.mulVec x ∈ V)
    (hsec : S.submatrix ι id = 1) (hdet : ∀ w ∈ V, S.mulVec (fun π => w (ι π)) = w) :
    IsPivot R ι S := by
  refine ⟨hsec, fun g => ?_⟩
  ext c π'
  have hw : (R g).mulVec (S.mulVec (Pi.single π' 1)) ∈ V := hV g _ (hS _)
  have e1 := hdet _ hw
  have e2 : ∀ M : Matrix κ ν k, M c π' = M.mulVec (Pi.single π' 1) c := fun M => by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [e2 (R g * S), e2 (S * (R g * S).submatrix ι id), ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← e1]
  congr 2
  funext π
  rw [submatrix_mulVec_id, Matrix.mulVec_mulVec]

theorem IsPivot.of_subspace' (V : Submodule k (κ → k))
    (hV : ∀ g, ∀ w ∈ V, (R g).mulVec w ∈ V) (hS : ∀ x, S.mulVec x ∈ V)
    (hsec : S.submatrix ι id = 1) (hinj : ∀ z ∈ V, (∀ π, z (ι π) = 0) → z = 0) :
    IsPivot R ι S :=
  IsPivot.of_subspace V hV hS hsec fun w hw => by
    have h := hinj (S.mulVec (fun π => w (ι π)) - w) (V.sub_mem (hS _) hw) fun π => by
      rw [Pi.sub_apply, ← submatrix_mulVec_id, hsec, Matrix.one_mulVec, sub_self]
    exact sub_eq_zero.mp h

end Pivot

section Kron

variable {G : Type*} [Group G] {k : Type*} [Field k]

@[expose] def kronRep {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (R : ∀ i, G →* Matrix (κ i) (κ i) k) :
    G →* Matrix (∀ i, κ i) (∀ i, κ i) k where
  toFun g := kron fun i => R i g
  map_one' := by
    simp only [map_one]
    exact kron_one
  map_mul' g h := by
    simp only [map_mul]
    exact kron_mul _ _

theorem kronRep_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (R : ∀ i, G →* Matrix (κ i) (κ i) k) (g : G) :
    kronRep R g = kron fun i => R i g := rfl

theorem kron_mulVec_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {κ κ' : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] (M : ∀ i, Matrix (κ' i) (κ i) k)
    (v : ∀ i, κ i → k) :
    (kron M).mulVec (fun x => ∏ i, v i (x i)) = fun x' => ∏ i, (M i).mulVec (v i) (x' i) := by
  funext x'
  simp only [Matrix.mulVec, dotProduct, kron_apply]
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (κ i)))
    (fun i b => M i (x' i) b * v i b)]
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib]

@[expose] def kron2Rep {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (R : G →* Matrix κ κ k) (R' : G →* Matrix κ' κ' k) : G →* Matrix (κ × κ') (κ × κ') k where
  toFun g := R g ⊗ₖ R' g
  map_one' := by rw [map_one, map_one, Matrix.one_kronecker_one]
  map_mul' g h := by rw [map_mul, map_mul, Matrix.mul_kronecker_mul]

theorem kron2Rep_apply {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (R : G →* Matrix κ κ k) (R' : G →* Matrix κ' κ' k) (g : G) :
    kron2Rep R R' g = R g ⊗ₖ R' g := rfl

theorem kron2_mulVec {κ κ' μ μ' : Type*} [Fintype κ] [Fintype κ'] (A : Matrix μ κ k)
    (B : Matrix μ' κ' k) (v : κ → k) (w : κ' → k) :
    (A ⊗ₖ B).mulVec (fun p : κ × κ' => v p.1 * w p.2) =
      fun p : μ × μ' => A.mulVec v p.1 * B.mulVec w p.2 := by
  funext p
  change ∑ q : κ × κ', A p.1 q.1 * B p.2 q.2 * (v q.1 * w q.2) =
    (∑ a, A p.1 a * v a) * ∑ b, B p.2 b * w b
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Kron

theorem sum_symm_eq_zero {ι k : Type*} [Fintype ι] [Field k] [CharP k 2] (f : ι × ι → k)
    (hsym : ∀ a b, f (a, b) = f (b, a)) (hdiag : ∀ a, f (a, a) = 0) : ∑ p, f p = 0 := by
  classical
  refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => ?_) (fun p _ hp => ?_)
    (fun p _ => Finset.mem_univ _) (fun p _ => Prod.swap_swap p)
  · obtain ⟨a, b⟩ := p
    rw [Prod.swap_prod_mk, ← hsym a b, CharTwo.add_self_eq_zero]
  · intro he
    apply hp
    obtain ⟨a, b⟩ := p
    have hab : b = a := congrArg Prod.fst he
    subst hab
    exact hdiag b

section Form

variable {G : Type*} [Group G] {k : Type*} [Field k] {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem transpose_mul_mul_of_dotProduct {R P : Matrix κ κ k}
    (h : ∀ x y : κ → k, R.mulVec x ⬝ᵥ P.mulVec (R.mulVec y) = x ⬝ᵥ P.mulVec y) :
    Rᵀ * P * R = P := by
  have e : ∀ (A : Matrix κ κ k) (a b : κ), A a b = Pi.single a 1 ⬝ᵥ A.mulVec (Pi.single b 1) :=
    fun A a b => by simp
  ext a b
  rw [e (Rᵀ * P * R), e P, ← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem gram_mul_rep (R : G →* Matrix κ κ k) (P : Matrix κ κ k)
    (h : ∀ g, (R g)ᵀ * P * R g = P) (g : G) : P * R g = (R g⁻¹)ᵀ * P := by
  have e : R g⁻¹ * R g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc P * R g = (R g⁻¹)ᵀ * P * R g⁻¹ * R g := by rw [h g⁻¹]
    _ = (R g⁻¹)ᵀ * P := by rw [Matrix.mul_assoc, e, Matrix.mul_one]

end Form

section Criterion

variable {p : ℕ} {G V : Type*} {k : Type*} [Group G] [Field k] [CharP k p] [AddCommGroup V]
  [Module k V]

theorem fixed_line_and_irreducible (hp : p.Prime) (ρ : Representation k G V) (P : Subgroup G)
    [Finite P] (hP : IsPGroup p P) (v : V) (hv0 : v ≠ 0) (hv : v ∈ fixedSub ρ P) (n : G)
    (hspan : Submodule.span k (Set.range fun u : P => ρ u (ρ n v)) = ⊤)
    (hline : ∃ m ∈ fixedSub ρ P, ∀ w ∈ fixedSub ρ P, ∃ c : k, w = c • m) :
    fixedSub ρ P = Submodule.span k {v} ∧ ρ.IsIrreducible := by
  classical
  obtain ⟨m, -, hm⟩ := hline
  obtain ⟨c₀, hc₀⟩ := hm v hv
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    exact hv0 (by simpa using hc₀)
  have hfix : fixedSub ρ P = Submodule.span k {v} := by
    apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hm w hw
      refine Submodule.mem_span_singleton.mpr ⟨c / c₀, ?_⟩
      rw [hc₀, smul_smul, div_mul_cancel₀ _ hc₀ne, hc]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hv
  refine ⟨hfix, (isIrreducible_iff ρ).mpr ⟨⟨v, 0, hv0⟩, fun W hW => ?_⟩⟩
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨w, hwW, hw0, hwfix⟩ := exists_fixed_mem_of_pGroup k hp hP (ρ.comp P.subtype) W
    (fun g w hw => hW g.1 w hw) hbot
  have hwmem : w ∈ fixedSub ρ P := fun h hh => hwfix ⟨h, hh⟩
  rw [hfix] at hwmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hwmem
  have hcne : c ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [← hc, zero_smul])
  have hvW : v ∈ W := by
    have : v = c⁻¹ • w := by rw [← hc, smul_smul, inv_mul_cancel₀ hcne, one_smul]
    rw [this]
    exact W.smul_mem _ hwW
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨u, rfl⟩
  exact hW _ _ (hW n v hvW)

end Criterion

end CFSG.Quasithin.B42G2Ten
