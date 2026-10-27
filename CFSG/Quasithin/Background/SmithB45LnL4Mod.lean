module

public import CFSG.Quasithin.Background.SmithB42LnL4Models
public import CFSG.Quasithin.Background.SmithB42LnL4Gen
public import CFSG.Quasithin.Background.SmithB45LnRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Iso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45Ln

open Matrix CFSG.Quasithin.B42Ln CFSG.Quasithin.JonesParshall CFSG.Quasithin.SmithCurtis
open CFSG.QuasithinUnique.Setup.X7 (dualMat dualMat_apply matRep matRep_apply)

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem forall_of_xy4 {p : G4 → Prop} (h1 : p 1) (hmul : ∀ g h, p g → p h → p (g * h))
    (hx : ∀ s, p (x4 s)) (hy : ∀ s, p (y4 s)) (g : G4) : p g := by
  have hS : ∀ t ∈ Set.range x4 ∪ Set.range y4, p t := by
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact hx s
    · exact hy s
  have hSi : ∀ t ∈ Set.range x4 ∪ Set.range y4, t⁻¹ = t := by
    rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact x4_inv s
    · exact y4_inv s
  have hg : g ∈ (Subgroup.closure (Set.range x4 ∪ Set.range y4)).toSubmonoid := by
    rw [closure_xy4]
    trivial
  rw [Subgroup.closure_toSubmonoid] at hg
  induction hg using Submonoid.closure_induction with
  | mem t ht =>
    rcases ht with ht | ht
    · exact hS t ht
    · have ht' : t⁻¹ ∈ Set.range x4 ∪ Set.range y4 := ht
      have e : t = t⁻¹ := by
        conv_lhs => rw [← inv_inv t]
        exact hSi _ ht'
      rw [e]
      exact hS _ ht'
  | one => exact h1
  | mul g h _ _ hg hh => exact hmul g h hg hh

@[expose] def kron24 : G4 →* Matrix (Fin 4 × Fin 6) (Fin 4 × Fin 6) (ZMod 2) where
  toFun g := kroneckerMap (· * ·) (g : 𝕄₄) (wedgeMat4 (g : 𝕄₄))
  map_one' := by
    rw [Matrix.SpecialLinearGroup.coe_one, wedgeMat4_one, one_kronecker_one]
  map_mul' g h := by
    rw [Matrix.SpecialLinearGroup.coe_mul, wedgeMat4_mul, mul_kronecker_mul]

@[expose] def tripPairs : Fin 4 → List (Fin 4 × Fin 6) :=
  ![[(0, 3), (1, 1), (2, 0)], [(0, 4), (1, 2), (3, 0)], [(0, 5), (2, 2), (3, 1)],
    [(1, 5), (2, 4), (3, 3)]]

@[expose] def piMat : Matrix (Fin 4) (Fin 4 × Fin 6) (ZMod 2) :=
  Matrix.of fun t a => if a ∈ tripPairs t then 1 else 0

@[expose] def piv20 : Fin 4 → Fin 4 × Fin 6 := ![(0, 3), (0, 4), (0, 5), (1, 5)]

@[expose] def free20 : Fin 20 → Fin 4 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (2, 0), (2, 1), (2, 2), (2, 3),
    (2, 4), (2, 5), (3, 0), (3, 1), (3, 2), (3, 3), (3, 4), (3, 5)]

@[expose] def C20 : Matrix (Fin 20) (Fin 4 × Fin 6) (ZMod 2) :=
  Matrix.of fun r a => if a = free20 r then 1 else 0

@[expose] def S20 : Matrix (Fin 4 × Fin 6) (Fin 20) (ZMod 2) :=
  Matrix.of fun a r =>
    if a = free20 r then 1 else ∑ t, if a = piv20 t then piMat t (free20 r) else 0

@[expose] def Z20 : Matrix (Fin 4 × Fin 6) (Fin 4) (ZMod 2) :=
  Matrix.of fun a t => if a = piv20 t then 1 else 0

theorem C20_mul_S20 : C20 * S20 = 1 := by decide +kernel

theorem S20_mul_C20 : S20 * C20 = 1 + Z20 * piMat := by decide +kernel

theorem piMat_mul_S20 : piMat * S20 = 0 := by decide +kernel

theorem piMat_kron24_gens : (∀ s, piMat * kron24 (x4 s) * S20 = 0) ∧
    ∀ s, piMat * kron24 (y4 s) * S20 = 0 := by
  decide +kernel

theorem S20_C20_mul_of {M : Matrix (Fin 4 × Fin 6) (Fin 20) (ZMod 2)} (h : piMat * M = 0) :
    S20 * C20 * M = M := by
  rw [S20_mul_C20, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_zero,
    add_zero]

theorem piMat_kron24 (g : G4) : piMat * kron24 g * S20 = 0 := by
  refine forall_of_xy4 (p := fun g => piMat * kron24 g * S20 = 0) ?_ (fun g h hg hh => ?_)
    piMat_kron24_gens.1 piMat_kron24_gens.2 g
  · rw [map_one, Matrix.mul_one, piMat_mul_S20]
  · have hh' : S20 * C20 * (kron24 h * S20) = kron24 h * S20 :=
      S20_C20_mul_of (by rw [← Matrix.mul_assoc]; exact hh)
    change piMat * kron24 (g * h) * S20 = 0
    rw [map_mul, Matrix.mul_assoc piMat, Matrix.mul_assoc, ← hh']
    simp only [← Matrix.mul_assoc]
    simp only [hg, Matrix.zero_mul]

@[expose] def mat20 : G4 →* Matrix (Fin 20) (Fin 20) (ZMod 2) where
  toFun g := C20 * kron24 g * S20
  map_one' := by rw [map_one, Matrix.mul_one, C20_mul_S20]
  map_mul' g h := by
    have hh : S20 * C20 * (kron24 h * S20) = kron24 h * S20 :=
      S20_C20_mul_of (by rw [← Matrix.mul_assoc]; exact piMat_kron24 h)
    change C20 * kron24 (g * h) * S20 = C20 * kron24 g * S20 * (C20 * kron24 h * S20)
    rw [map_mul, Matrix.mul_assoc C20, Matrix.mul_assoc, ← hh]
    simp only [Matrix.mul_assoc]

theorem mat20_apply (g : G4) : mat20 g = C20 * kron24 g * S20 := rfl

@[expose] noncomputable def rep20 : Representation (ZMod 2) G4 (Fin 20 → ZMod 2) := matRep mat20

@[expose] noncomputable def rep20d : Representation (ZMod 2) G4 (Fin 20 → ZMod 2) :=
  matRep (dualMat mat20)

@[expose] def conj4 : Representation (ZMod 2) G4 𝕄₄ where
  toFun g :=
    { toFun := fun X => (g : 𝕄₄) * X * ((g⁻¹ : G4) : 𝕄₄)
      map_add' := fun X Y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := LinearMap.ext fun X => by
    change ((1 : G4) : 𝕄₄) * X * (((1 : G4)⁻¹ : G4) : 𝕄₄) = X
    rw [inv_one, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
  map_mul' g h := LinearMap.ext fun X => by
    change ((g * h : G4) : 𝕄₄) * X * (((g * h)⁻¹ : G4) : 𝕄₄) =
      (g : 𝕄₄) * ((h : 𝕄₄) * X * ((h⁻¹ : G4) : 𝕄₄)) * ((g⁻¹ : G4) : 𝕄₄)
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    simp only [Matrix.mul_assoc]

theorem conj4_apply (g : G4) (X : 𝕄₄) : conj4 g X = (g : 𝕄₄) * X * ((g⁻¹ : G4) : 𝕄₄) := rfl

@[expose] def c14v (X : 𝕄₄) : Fin 14 → ZMod 2 :=
  ![X 0 1, X 0 2, X 0 3, X 1 0, X 1 2, X 1 3, X 2 0, X 2 1, X 2 3, X 3 0, X 3 1, X 3 2,
    X 0 0 + X 3 3, X 1 1 + X 3 3]

@[expose] def s14v (v : Fin 14 → ZMod 2) : 𝕄₄ :=
  !![v 12, v 0, v 1, v 2; v 3, v 13, v 4, v 5; v 6, v 7, v 12 + v 13, v 8; v 9, v 10, v 11, 0]

@[expose] def c14 : 𝕄₄ →ₗ[ZMod 2] (Fin 14 → ZMod 2) where
  toFun := c14v
  map_add' X Y := by
    funext i
    fin_cases i <;> simp [c14v, add_add_add_comm]
  map_smul' c X := by
    funext i
    fin_cases i <;> simp [c14v, mul_add]

@[expose] def s14 : (Fin 14 → ZMod 2) →ₗ[ZMod 2] 𝕄₄ where
  toFun := s14v
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s14v, add_add_add_comm]
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s14v, mul_add]

theorem c14_s14 (v : Fin 14 → ZMod 2) : c14 (s14 v) = v := by
  funext i
  fin_cases i <;> simp [c14, s14, c14v, s14v]

theorem c14_smul_one (c : ZMod 2) : c14 (c • (1 : 𝕄₄)) = 0 := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  funext i
  fin_cases i <;> simp [c14, c14v, h11]

theorem trace_s14 (v : Fin 14 → ZMod 2) : (s14 v).trace = 0 := by
  have h2 : v 12 + v 12 = 0 := CharTwo.add_self_eq_zero _
  have h3 : v 13 + v 13 = 0 := CharTwo.add_self_eq_zero _
  simp [s14, s14v, Matrix.trace, Fin.sum_univ_four]
  linear_combination h2 + h3

theorem s14_c14 {X : 𝕄₄} (hX : X.trace = 0) : s14 (c14 X) = X + X 3 3 • (1 : 𝕄₄) := by
  simp only [Matrix.trace, Fin.sum_univ_four, Matrix.diag] at hX
  have h22 : X 2 2 + X 2 2 = 0 := CharTwo.add_self_eq_zero _
  have h33 : X 3 3 + X 3 3 = 0 := CharTwo.add_self_eq_zero _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s14, c14, s14v, c14v]
  all_goals first | linear_combination hX - h22 | linear_combination -h33

theorem trace_conj4 (g : G4) (X : 𝕄₄) : (conj4 g X).trace = X.trace := by
  rw [conj4_apply, Matrix.trace_mul_cycle, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

theorem c14_conj4_s14 (g h : G4) (v : Fin 14 → ZMod 2) :
    c14 (conj4 g (s14 (c14 (conj4 h (s14 v))))) = c14 (conj4 g (conj4 h (s14 v))) := by
  have ht : (conj4 h (s14 v)).trace = 0 := by rw [trace_conj4, trace_s14]
  rw [s14_c14 ht, map_add, map_add, map_smul, conj4_apply g 1, Matrix.mul_one,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    c14_smul_one, add_zero]

@[expose] noncomputable def rep14 : Representation (ZMod 2) G4 (Fin 14 → ZMod 2) :=
  coordRep conj4 c14 s14 c14_s14 c14_conj4_s14

theorem rep14_apply (g : G4) (v : Fin 14 → ZMod 2) :
    rep14 g v = c14v ((g : 𝕄₄) * s14v v * ((g⁻¹ : G4) : 𝕄₄)) := rfl

@[expose] def gen4 : Fin 6 → G4 := ![x4 0, x4 1, x4 2, n4 0, n4 1, n4 2]

@[expose] def xIdx : Fin 3 → Fin 6 := ![0, 1, 2]

@[expose] def nIdx : Fin 3 → Fin 6 := ![3, 4, 5]

theorem gen4_xIdx (s : Fin 3) : gen4 (xIdx s) = x4 s := by
  fin_cases s <;> rfl

theorem gen4_nIdx (s : Fin 3) : gen4 (nIdx s) = n4 s := by
  fin_cases s <;> rfl

theorem gen4_inv (i : Fin 6) : (gen4 i)⁻¹ = gen4 i := by
  fin_cases i
  · exact x4_inv 0
  · exact x4_inv 1
  · exact x4_inv 2
  · exact n4_inv 0
  · exact n4_inv 1
  · exact n4_inv 2

@[expose] def wordG (w : List (Fin 6)) : G4 := (w.map gen4).prod

theorem rep_wordG {n : ℕ} {ρ : Representation (ZMod 2) G4 (Fin n → ZMod 2)}
    {act : Fin 6 → (Fin n → ZMod 2) → Fin n → ZMod 2} (hact : ∀ i v, ρ (gen4 i) v = act i v)
    (w : List (Fin 6)) (v : Fin n → ZMod 2) : ρ (wordG w) v = w.foldr act v := by
  induction w with
  | nil =>
    change ρ 1 v = v
    rw [map_one, Module.End.one_apply]
  | cons i w ih =>
    change ρ (gen4 i * wordG w) v = act i (w.foldr act v)
    rw [map_mul, Module.End.mul_apply, ih, hact]

theorem simple_type_of_data {n : ℕ} (ρ : Representation (ZMod 2) G4 (Fin n → ZMod 2))
    (act : Fin 6 → (Fin n → ZMod 2) → Fin n → ZMod 2) (hact : ∀ i v, ρ (gen4 i) v = act i v)
    (M : Fin 3 → Matrix (Fin n) (Fin n) (ZMod 2)) (hM : ∀ s v, act (xIdx s) v = M s *ᵥ v)
    (hr : n - 1 ≤ (stackMat M).rank) (y : Fin n → ZMod 2) (hy0 : y ≠ 0)
    (hyU : ∀ s, act (xIdx s) y = y) (words : Fin n → List (Fin 6))
    (binv : Matrix (Fin n) (Fin n) (ZMod 2))
    (hgen : Matrix.of (fun a i => (words i).foldr act y a) * binv = 1) (μ : Fin 3 → ZMod 2)
    (hμ : ∀ s, act (nIdx s) y + act (xIdx s) (act (nIdx s) y) = μ s • y) :
    IsSimpleRep ρ ∧ IsType4 ρ y μ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Fin n → ZMod 2) := ⟨⟨y, 0, hy0⟩⟩
  have hx : ∀ s v, ρ (x4 s) v = M s *ᵥ v := fun s v => by
    rw [← gen4_xIdx, hact, hM]
  have hyfix : y ∈ datum4.fixU ρ := by
    let K : Subgroup G4 :=
      { carrier := {g | ρ g y = y}
        one_mem' := by
          change ρ 1 y = y
          rw [map_one, Module.End.one_apply]
        mul_mem' := fun {a b} ha hb => by
          change ρ (a * b) y = y
          rw [map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          change ρ a⁻¹ y = y
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    intro u hu
    have hK : ∀ s, x4 s ∈ K := fun s => by
      change ρ (x4 s) y = y
      rw [← gen4_xIdx, hact, hyU]
    exact mem_of_x4_mem hK hu
  have hfix : ∀ x ∈ datum4.fixU ρ, ∃ c : ZMod 2, x = c • y := by
    intro x hx'
    have h1 : ∀ s, M s *ᵥ x = x := fun s => by
      rw [← hx]
      exact hx' (x4 s) (x4_mem s)
    have h2 : ∀ s, M s *ᵥ y = y := fun s => by
      rw [← hx]
      exact hyfix (x4 s) (x4_mem s)
    exact eq_smul_of_rank hr hy0 h2 h1
  have hgen' : orbitSpan ρ y = ⊤ := by
    refine orbitSpan_eq_top_of_mul ρ y (fun i => (words i).foldr act y) (fun i => ?_) binv hgen
    rw [← rep_wordG hact]
    exact Submodule.subset_span ⟨_, rfl⟩
  refine ⟨datum4.isSimpleRep_of_fixU ρ hfix hgen', hyfix, hy0, fun h hh => ?_, fun s => ?_⟩
  · rw [datum4_H, Subgroup.mem_bot] at hh
    rw [hh, map_one, one_smul]
    rfl
  · rw [heckeT4, map_mul, Module.End.mul_apply, ← gen4_nIdx, ← gen4_xIdx, hact, hact]
    exact hμ s

@[expose] def act20 (i : Fin 6) (v : Fin 20 → ZMod 2) : Fin 20 → ZMod 2 :=
  C20 *ᵥ (kron24 (gen4 i) *ᵥ (S20 *ᵥ v))

theorem rep20_gen4 (i : Fin 6) (v : Fin 20 → ZMod 2) : rep20 (gen4 i) v = act20 i v := by
  rw [rep20, matRep_apply, mat20_apply, act20, mulVec_mulVec, mulVec_mulVec]

theorem hact20 (s : Fin 3) (v : Fin 20 → ZMod 2) : act20 (xIdx s) v = mat20 (x4 s) *ᵥ v := by
  rw [act20, gen4_xIdx, mat20_apply, mulVec_mulVec, mulVec_mulVec]

@[expose] def y20 : Fin 20 → ZMod 2 := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def words20 : Fin 20 → List (Fin 6) :=
  ![[], [3], [4], [4, 3], [3, 4], [5, 4], [1, 4, 3], [3, 4, 3], [5, 4, 3], [0, 3, 4], [5, 3, 4],
    [5, 1, 4, 3], [5, 3, 4, 3], [2, 5, 4, 3], [5, 0, 3, 4], [4, 5, 3, 4], [2, 5, 3, 4, 3],
    [4, 5, 3, 4, 3], [4, 5, 0, 3, 4], [1, 4, 5, 3, 4]]

@[expose] def binv20 : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]

@[expose] def fixRows20 : Fin 19 → Fin 3 × Fin 20 :=
  ![(0, 0), (0, 1), (0, 2), (0, 4), (0, 5), (0, 9), (0, 10), (0, 15), (0, 16), (1, 0), (1, 3),
    (1, 4), (1, 5), (1, 7), (1, 14), (1, 18), (2, 1), (2, 4), (2, 9)]

@[expose] def fixCols20 : Fin 19 → Fin 20 :=
  ![3, 6, 7, 8, 14, 11, 12, 17, 18, 1, 4, 9, 10, 13, 15, 19, 2, 5, 16]

@[expose] def fixY20 : Matrix (Fin 19) (Fin 19) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1]

theorem rank_rep20 : 20 - 1 ≤ (stackMat fun s => mat20 (x4 s)).rank :=
  le_rank_of_submatrix _ fixRows20 fixCols20 fixY20 (by decide +kernel)

theorem fix_y20 : ∀ s, act20 (xIdx s) y20 = y20 := by decide +kernel

theorem gen_y20 : Matrix.of (fun a i => (words20 i).foldr act20 y20 a) * binv20 = 1 := by
  decide +kernel

theorem hecke_y20 : ∀ s, act20 (nIdx s) y20 + act20 (xIdx s) (act20 (nIdx s) y20) =
    (![1, 1, 0] : Fin 3 → ZMod 2) s • y20 := by
  decide +kernel

theorem rep20_simple_type : IsSimpleRep rep20 ∧ IsType4 rep20 y20 ![1, 1, 0] :=
  simple_type_of_data rep20 act20 rep20_gen4 (fun s => mat20 (x4 s)) hact20 rank_rep20 y20
    (by decide) fix_y20 words20 binv20 gen_y20 ![1, 1, 0] hecke_y20

@[expose] def act20d (i : Fin 6) (v : Fin 20 → ZMod 2) : Fin 20 → ZMod 2 :=
  vecMul (vecMul (vecMul v C20) (kron24 (gen4 i))) S20

theorem act20d_eq (i : Fin 6) (v : Fin 20 → ZMod 2) : act20d i v = (mat20 (gen4 i))ᵀ *ᵥ v := by
  rw [mulVec_transpose, mat20_apply, act20d, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]

theorem rep20d_gen4 (i : Fin 6) (v : Fin 20 → ZMod 2) : rep20d (gen4 i) v = act20d i v := by
  rw [rep20d, matRep_apply, dualMat_apply, gen4_inv, act20d_eq]

theorem hact20d (s : Fin 3) (v : Fin 20 → ZMod 2) :
    act20d (xIdx s) v = (mat20 (x4 s))ᵀ *ᵥ v := by
  rw [act20d_eq, gen4_xIdx]

@[expose] def y20d :
    Fin 20 → ZMod 2 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

@[expose] def words20d : Fin 20 → List (Fin 6) :=
  ![[], [4], [5], [3, 4], [5, 4], [4, 5], [5, 3, 4], [2, 5, 4], [4, 5, 4], [1, 4, 5], [3, 4, 5],
    [2, 5, 3, 4], [4, 5, 3, 4], [3, 4, 5, 4], [3, 1, 4, 5], [0, 3, 4, 5], [4, 2, 5, 3, 4],
    [1, 4, 5, 3, 4], [3, 4, 5, 3, 4], [0, 3, 4, 5, 4]]

@[expose] def binv20d : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def fixRows20d : Fin 19 → Fin 3 × Fin 20 :=
  ![(0, 3), (0, 6), (0, 7), (0, 8), (0, 11), (0, 12), (0, 14), (0, 17), (0, 18), (1, 4), (1, 9),
    (1, 11), (1, 13), (1, 15), (1, 17), (1, 19), (2, 12), (2, 18), (2, 19)]

@[expose] def fixCols20d : Fin 19 → Fin 20 :=
  ![0, 1, 2, 4, 9, 10, 5, 15, 16, 3, 8, 6, 7, 14, 12, 18, 11, 17, 13]

@[expose] def fixY20d : Matrix (Fin 19) (Fin 19) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem rank_rep20d : 20 - 1 ≤ (stackMat fun s => (mat20 (x4 s))ᵀ).rank :=
  le_rank_of_submatrix _ fixRows20d fixCols20d fixY20d (by decide +kernel)

theorem fix_y20d : ∀ s, act20d (xIdx s) y20d = y20d := by decide +kernel

theorem gen_y20d : Matrix.of (fun a i => (words20d i).foldr act20d y20d a) * binv20d = 1 := by
  decide +kernel

theorem hecke_y20d : ∀ s, act20d (nIdx s) y20d + act20d (xIdx s) (act20d (nIdx s) y20d) =
    (![0, 1, 1] : Fin 3 → ZMod 2) s • y20d := by
  decide +kernel

theorem rep20d_simple_type : IsSimpleRep rep20d ∧ IsType4 rep20d y20d ![0, 1, 1] :=
  simple_type_of_data rep20d act20d rep20d_gen4 (fun s => (mat20 (x4 s))ᵀ) hact20d rank_rep20d y20d
    (by decide) fix_y20d words20d binv20d gen_y20d ![0, 1, 1] hecke_y20d

@[expose] def act14 (i : Fin 6) (v : Fin 14 → ZMod 2) : Fin 14 → ZMod 2 :=
  c14v ((gen4 i : 𝕄₄) * s14v v * (gen4 i : 𝕄₄))

theorem rep14_gen4 (i : Fin 6) (v : Fin 14 → ZMod 2) : rep14 (gen4 i) v = act14 i v := by
  rw [rep14_apply, gen4_inv]
  rfl

@[expose] def mat14 (A : 𝕄₄) : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  Matrix.of fun a j => c14v (A * s14v (Pi.single j 1) * A) a

theorem c14v_conj_eq (A : 𝕄₄) (v : Fin 14 → ZMod 2) :
    c14v (A * s14v v * A) = mat14 A *ᵥ v := by
  let f : (Fin 14 → ZMod 2) →ₗ[ZMod 2] (Fin 14 → ZMod 2) :=
    c14.comp ((LinearMap.mulRight (ZMod 2) A).comp ((LinearMap.mulLeft (ZMod 2) A).comp s14))
  have hf : ∀ w, f w = c14v (A * s14v w * A) := fun w => rfl
  have hm : LinearMap.toMatrix' f = mat14 A := Matrix.ext fun a j => by
    rw [LinearMap.toMatrix'_apply, hf]
    rfl
  rw [← hf, ← LinearMap.toMatrix'_mulVec f v, hm]

theorem hact14 (s : Fin 3) (v : Fin 14 → ZMod 2) : act14 (xIdx s) v = mat14 (xM4 s) *ᵥ v := by
  rw [act14, gen4_xIdx, coe_x4, c14v_conj_eq]

@[expose] def y14 : Fin 14 → ZMod 2 := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def words14 : Fin 14 → List (Fin 6) :=
  ![[], [3], [5], [4, 3], [5, 3], [4, 5], [5, 4, 3], [4, 5, 3], [3, 4, 5], [2, 5, 4, 3],
    [4, 5, 4, 3], [1, 4, 5, 3], [3, 4, 5, 3], [3, 4, 5, 4, 3]]

@[expose] def binv14 : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  !![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

@[expose] def fixRows14 : Fin 13 → Fin 3 × Fin 14 :=
  ![(0, 0), (0, 1), (0, 2), (0, 7), (0, 10), (0, 12), (1, 1), (1, 4), (1, 5), (1, 11), (1, 13),
    (2, 2), (2, 8)]

@[expose] def fixCols14 : Fin 13 → Fin 14 :=
  ![3, 4, 5, 6, 9, 12, 0, 7, 8, 10, 13, 1, 11]

@[expose] def fixY14 : Matrix (Fin 13) (Fin 13) (ZMod 2) :=
  !![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]

theorem rank_rep14 : 14 - 1 ≤ (stackMat fun s => mat14 (xM4 s)).rank :=
  le_rank_of_submatrix _ fixRows14 fixCols14 fixY14 (by decide +kernel)

theorem fix_y14 : ∀ s, act14 (xIdx s) y14 = y14 := by decide +kernel

theorem gen_y14 : Matrix.of (fun a i => (words14 i).foldr act14 y14 a) * binv14 = 1 := by
  decide +kernel

theorem hecke_y14 : ∀ s, act14 (nIdx s) y14 + act14 (xIdx s) (act14 (nIdx s) y14) =
    (![1, 0, 1] : Fin 3 → ZMod 2) s • y14 := by
  decide +kernel

theorem rep14_simple_type : IsSimpleRep rep14 ∧ IsType4 rep14 y14 ![1, 0, 1] :=
  simple_type_of_data rep14 act14 rep14_gen4 (fun s => mat14 (xM4 s)) hact14 rank_rep14 y14
    (by decide) fix_y14 words14 binv14 gen_y14 ![1, 0, 1] hecke_y14

end CFSG.Quasithin.B45Ln
