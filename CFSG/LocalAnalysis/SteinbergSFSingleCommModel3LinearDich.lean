module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3LinearDefs
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem model3LinDich_ring_four {R : Type} [Ring R] (n : R) (h2 : n + n = 0)
    (h3 : n * n * n = 0) : (1 + n) * ((1 + n) * ((1 + n) * (1 + n))) = 1 := by
  have hs : n * n + n * n = 0 := by rw [← _root_.add_mul, h2, MulZeroClass.zero_mul]
  have hn4 : n * n * (n * n) = 0 := by
    rw [← _root_.mul_assoc (n * n) n n, h3, MulZeroClass.zero_mul]
  have hu2 : (1 + n) * (1 + n) = 1 + n * n := by
    rw [show (1 + n) * (1 + n) = 1 + (n + n) + n * n by noncomm_ring, h2, _root_.add_zero]
  have hq : (1 + n * n) * (1 + n * n) = 1 + (n * n + n * n) + n * n * (n * n) := by
    noncomm_ring
  calc (1 + n) * ((1 + n) * ((1 + n) * (1 + n)))
      = ((1 + n) * (1 + n)) * ((1 + n) * (1 + n)) := by simp only [_root_.mul_assoc]
    _ = (1 + n * n) * (1 + n * n) := by rw [hu2]
    _ = 1 + (n * n + n * n) + n * n * (n * n) := hq
    _ = 1 := by rw [hs, hn4]; simp

theorem model3LinDich_one_add_mul {R : Type} [Ring R] (n m : R) :
    (1 + n) * (1 + m) = 1 + (n + m + n * m) := by
  noncomm_ring

theorem model3LinDich_pow_four {G : Type} [Group G] (x : G) (h : x * (x * (x * x)) = 1) :
    x ^ 2 ^ 2 = 1 := by
  have e : x ^ 4 = x * (x * (x * x)) := by
    simp only [pow_succ, pow_zero, _root_.one_mul, _root_.mul_assoc]
  show x ^ 4 = 1
  rw [e, h]

theorem model3LinDich_double {F' : Type} [Field F'] [CharP F' 2]
    {p q : Matrix (Fin 3) (Fin 3) F'} (x y z : F') :
    (x • p + y • q + z • (q * p)) + (x • p + y • q + z • (q * p)) = 0 := by
  have hr : ∀ (r : F') (v : Matrix (Fin 3) (Fin 3) F'), r • v + r • v = 0 := fun r v => by
    rw [← _root_.add_smul, CharTwo.add_self_eq_zero, _root_.zero_smul]
  calc (x • p + y • q + z • (q * p)) + (x • p + y • q + z • (q * p))
      = (x • p + x • p) + (y • q + y • q) + (z • (q * p) + z • (q * p)) := by abel
    _ = 0 := by simp only [hr, _root_.add_zero, _root_.zero_add]

theorem model3LinDich_mul {F' : Type} [Field F'] {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0) (x y z x' y' z' : F') :
    (x • p + y • q + z • (q * p)) * (x' • p + y' • q + z' • (q * p)) = (y * x') • (q * p) := by
  have hpqp : p * (q * p) = 0 := by rw [← _root_.mul_assoc, hpq, MulZeroClass.zero_mul]
  have hqqp : q * (q * p) = 0 := by rw [← _root_.mul_assoc, hqq, MulZeroClass.zero_mul]
  simp only [_root_.add_mul, _root_.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    _root_.smul_smul, _root_.mul_assoc, hpp, hpq, hqq, hpqp, hqqp, MulZeroClass.mul_zero,
    _root_.smul_zero, _root_.add_zero, _root_.zero_add]
  rw [_root_.mul_comm x' y]

theorem model3LinDich_cube {F' : Type} [Field F'] {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0) (x y z : F') :
    (x • p + y • q + z • (q * p)) * (x • p + y • q + z • (q * p)) *
      (x • p + y • q + z • (q * p)) = 0 := by
  have hpqp : p * (q * p) = 0 := by rw [← _root_.mul_assoc, hpq, MulZeroClass.zero_mul]
  have hqpn : (q * p) * (x • p + y • q + z • (q * p)) = 0 := by
    simp only [_root_.mul_add, _root_.mul_assoc, Matrix.mul_smul, hpp, hpq, hpqp,
      MulZeroClass.mul_zero, _root_.smul_zero, _root_.add_zero]
  rw [model3LinDich_mul hpp hqq hpq, Matrix.smul_mul, hqpn, _root_.smul_zero]

def model3LinDichSet {F' : Type} [Field F'] (p q : Matrix (Fin 3) (Fin 3) F') :
    Set (SpecialLinearGroup (Fin 3) F') :=
  {g | ∃ x y z : F', (g : Matrix (Fin 3) (Fin 3) F') = 1 + (x • p + y • q + z • (q * p))}

theorem model3LinDich_mul_mem {F' : Type} [Field F'] {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0)
    {g h : SpecialLinearGroup (Fin 3) F'}
    (hg : g ∈ model3LinDichSet p q) (hh : h ∈ model3LinDichSet p q) :
    g * h ∈ model3LinDichSet p q := by
  obtain ⟨x, y, z, hg⟩ := hg
  obtain ⟨x', y', z', hh⟩ := hh
  refine ⟨x + x', y + y', z + z' + y * x', ?_⟩
  show (g : Matrix (Fin 3) (Fin 3) F') * (h : Matrix (Fin 3) (Fin 3) F') = _
  rw [hg, hh, model3LinDich_one_add_mul, model3LinDich_mul hpp hqq hpq]
  congr 1
  module

theorem model3LinDich_four_eq_one {F' : Type} [Field F'] [CharP F' 2]
    {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0) {g : SpecialLinearGroup (Fin 3) F'}
    (hg : g ∈ model3LinDichSet p q) : g * (g * (g * g)) = 1 := by
  obtain ⟨x, y, z, hg⟩ := hg
  apply Subtype.ext
  show (g : Matrix (Fin 3) (Fin 3) F') * ((g : Matrix (Fin 3) (Fin 3) F') *
    ((g : Matrix (Fin 3) (Fin 3) F') * (g : Matrix (Fin 3) (Fin 3) F'))) = 1
  rw [hg]
  exact model3LinDich_ring_four _ (model3LinDich_double (p := p) (q := q) x y z)
    (model3LinDich_cube hpp hqq hpq x y z)

theorem model3LinDich_inv_mem {F' : Type} [Field F'] [CharP F' 2]
    {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0) {g : SpecialLinearGroup (Fin 3) F'}
    (hg : g ∈ model3LinDichSet p q) : g⁻¹ ∈ model3LinDichSet p q := by
  rw [inv_eq_of_mul_eq_one_right (model3LinDich_four_eq_one hpp hqq hpq hg)]
  exact model3LinDich_mul_mem hpp hqq hpq hg (model3LinDich_mul_mem hpp hqq hpq hg hg)

def model3LinDichSub {F' : Type} [Field F'] [CharP F' 2] {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0) :
    Subgroup (SpecialLinearGroup (Fin 3) F') where
  carrier := model3LinDichSet p q
  mul_mem' := fun hg hh => model3LinDich_mul_mem hpp hqq hpq hg hh
  one_mem' := ⟨0, 0, 0, by simp⟩
  inv_mem' := fun hg => model3LinDich_inv_mem hpp hqq hpq hg

theorem model3LinDich_isPGroup {F' : Type} [Field F'] [CharP F' 2]
    (τ : SpecialLinearGroup (Fin 3) F') {p q : Matrix (Fin 3) (Fin 3) F'}
    (hpp : p * p = 0) (hqq : q * q = 0) (hpq : p * q = 0)
    (hZ : linZ F' ≤ model3LinDichSub hpp hqq hpq)
    (hZτ : (linZ F').map (MulAut.conj τ⁻¹).toMonoidHom ≤ model3LinDichSub hpp hqq hpq) :
    IsPGroup 2 ↥(linZ F' ⊔ (linZ F').map (MulAut.conj τ⁻¹).toMonoidHom) := by
  intro g
  refine ⟨2, ?_⟩
  have hg : (g : SpecialLinearGroup (Fin 3) F') ∈ model3LinDichSet p q :=
    sup_le hZ hZτ g.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact model3LinDich_pow_four _ (model3LinDich_four_eq_one hpp hqq hpq hg)

theorem model3LinDich_corner {F' : Type} [Field F'] (c : F') :
    transvection (⟨0, by omega⟩ : Fin 3) ⟨3 - 1, by omega⟩ c = 1 + c • linE13 F' := by
  rw [show linE13 F' = Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : F') from rfl,
    Matrix.smul_single, _root_.smul_eq_mul, _root_.mul_one]
  rfl

theorem model3LinDich_linZ_mem {F' : Type} [Field F'] {g : SpecialLinearGroup (Fin 3) F'}
    (hg : g ∈ linZ F') :
    ∃ c : F', (g : Matrix (Fin 3) (Fin 3) F') = 1 + c • linE13 F' := by
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hg
  obtain ⟨c, hc⟩ : ∃ c : F', ((u : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F')
      ⟨0, by omega⟩ ⟨3 - 1, by omega⟩ = c := ⟨_, rfl⟩
  have hz := CFSG.ComponentClassification.SymmetricLocal.eq_utTransvection_of_mem_center
    (by norm_num : 2 ≤ 3) hu
  rw [hc] at hz
  refine ⟨c, ?_⟩
  show ((u : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') = _
  rw [hz, CFSG.ComponentClassification.SymmetricLocal.coe_utTransvection]
  exact model3LinDich_corner c

theorem model3LinDich_conj_apply_coe {F' : Type} [Field F'] (τ y : SpecialLinearGroup (Fin 3) F') :
    (((MulAut.conj τ⁻¹).toMonoidHom y : SpecialLinearGroup (Fin 3) F') :
        Matrix (Fin 3) (Fin 3) F') =
      ((τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') *
        (y : Matrix (Fin 3) (Fin 3) F') * (τ : Matrix (Fin 3) (Fin 3) F') := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, _root_.inv_inv]
  rfl

theorem model3LinDich_conj_linZ {F' : Type} [Field F'] (τ : SpecialLinearGroup (Fin 3) F')
    {y : SpecialLinearGroup (Fin 3) F'}
    (hy : ∃ c : F', (y : Matrix (Fin 3) (Fin 3) F') = 1 + c • linE13 F') :
    ∃ c : F', (((MulAut.conj τ⁻¹).toMonoidHom y : SpecialLinearGroup (Fin 3) F') :
        Matrix (Fin 3) (Fin 3) F') = 1 + c • linConj τ := by
  obtain ⟨c, hc⟩ := hy
  refine ⟨c, ?_⟩
  have hτ : ((τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') *
      (τ : Matrix (Fin 3) (Fin 3) F') = 1 := by
    have h1 : τ⁻¹ * τ = 1 := by simp
    have h2 : ((τ⁻¹ * τ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') =
        ((1 : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') :=
      congrArg Subtype.val h1
    exact h2
  rw [model3LinDich_conj_apply_coe, hc]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hτ]

theorem model3LinDich_E_mul_E {F' : Type} [Field F'] : linE13 F' * linE13 F' = 0 := by
  show Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : F') *
    Matrix.single (0 : Fin 3) (2 : Fin 3) (1 : F') = 0
  simp

theorem model3LinDich_conj_mul_conj {F' : Type} [Field F'] (τ : SpecialLinearGroup (Fin 3) F') :
    linConj τ * linConj τ = 0 := by
  have hTA : (τ : Matrix (Fin 3) (Fin 3) F') *
      ((τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') = 1 := by
    have h1 : τ * τ⁻¹ = 1 := by simp
    have h2 : ((τ * τ⁻¹ : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') =
        ((1 : SpecialLinearGroup (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') :=
      congrArg Subtype.val h1
    exact h2
  have key : ∀ (A T E : Matrix (Fin 3) (Fin 3) F'), T * A = 1 → E * E = 0 →
      (A * E * T) * (A * E * T) = 0 := by
    intro A T E hTA' hE
    calc (A * E * T) * (A * E * T) = A * (E * (T * A) * E) * T := by
          simp only [_root_.mul_assoc]
      _ = A * (E * 1 * E) * T := by rw [hTA']
      _ = A * (E * E) * T := by rw [_root_.mul_one]
      _ = 0 := by rw [hE, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
  exact key _ _ _ hTA model3LinDich_E_mul_E

theorem model3_linear_dichotomy {F' : Type} [Field F'] [CharP F' 2]
    (τ : SpecialLinearGroup (Fin 3) F')
    (h : linE13 F' * linConj τ = 0 ∨ linConj τ * linE13 F' = 0) :
    IsPGroup 2 ↥(linZ F' ⊔ (linZ F').map (MulAut.conj τ⁻¹).toMonoidHom) := by
  have hpp : linE13 F' * linE13 F' = 0 := model3LinDich_E_mul_E
  have hqq : linConj τ * linConj τ = 0 := model3LinDich_conj_mul_conj τ
  rcases h with h | h
  · refine model3LinDich_isPGroup τ hpp hqq h ?_ ?_
    · intro g hg
      obtain ⟨c, hc⟩ := model3LinDich_linZ_mem hg
      exact ⟨c, 0, 0, by rw [hc]; simp⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, hc⟩ := model3LinDich_conj_linZ τ (model3LinDich_linZ_mem hy)
      exact ⟨0, c, 0, by rw [hc]; simp⟩
  · refine model3LinDich_isPGroup τ hqq hpp h ?_ ?_
    · intro g hg
      obtain ⟨c, hc⟩ := model3LinDich_linZ_mem hg
      exact ⟨0, c, 0, by rw [hc]; simp⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, hc⟩ := model3LinDich_conj_linZ τ (model3LinDich_linZ_mem hy)
      exact ⟨c, 0, 0, by rw [hc]; simp⟩

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
