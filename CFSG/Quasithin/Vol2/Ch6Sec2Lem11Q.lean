module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11P
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11N

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
  CFSG.LieType.BorelTits CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {d u₁ z : G}

namespace Data611

variable (D : Data611 G T M L V d u₁ z)
include D

omit [Finite G] D in
theorem ZS_le_U : ch6ZS T L V ≤ uCh611 T L V := le_conjClosure _ _

omit [Finite G] D in
theorem ZS_le_V : ch6ZS T L V ≤ V := inf_le_left

theorem card_ZS : Nat.card ↥(ch6ZS T L V) = 4 := by
  rw [D.hyp.toHyp611Nat.card_ZS]; norm_num

theorem zS : z ∈ ch6ZS T L V := D.ZZS D.zZ

theorem zU : z ∈ uCh611 T L V := ZS_le_U D.zS

theorem conj_d_mem {x : G} (hx : x ∈ uCh611 T L V) : d * x * d⁻¹ ∈ uCh611 T L V :=
  (Subgroup.mem_normalizer_iff.mp D.dU x).mp hx

theorem isMulCommutative : IsMulCommutative ↥(uCh611 T L V) :=
  ⟨⟨fun a b => Subtype.ext (D.comm a a.2 b b.2)⟩⟩

@[expose] def basis : Fin 4 → ↥(uCh611 T L V) :=
  ![⟨z, D.zU⟩, ⟨d * z * d⁻¹, D.conj_d_mem D.zU⟩, ⟨u₁, D.u₁U⟩, ⟨d * u₁ * d⁻¹, D.conj_d_mem D.u₁U⟩]

theorem basis_sq : ∀ i, D.basis i ^ 2 = 1 := fun i => Subtype.ext (by
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
  exact D.sq _ (D.basis i).2)

@[expose] noncomputable def kv (c : Fin 4 → ZMod 2) : G :=
  @kvCh611 G _ (uCh611 T L V) D.isMulCommutative D.basis D.basis_sq c

theorem kv_eq (c : Fin 4 → ZMod 2) :
    D.kv c = z ^ (c 0).val * (d * z * d⁻¹) ^ (c 1).val * u₁ ^ (c 2).val *
      (d * u₁ * d⁻¹) ^ (c 3).val := by
  unfold kv kvCh611 kapCh611
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_ofMul, Fin.prod_univ_four,
    Subgroup.coe_mul, SubgroupClass.coe_pow]
  rfl

omit [Group G] [Finite G] D in
theorem zv0 : (0 : ZMod 2).val = 0 := rfl

omit [Group G] [Finite G] D in
theorem zv1 : (1 : ZMod 2).val = 1 := rfl

theorem kv_add (c c' : Fin 4 → ZMod 2) : D.kv (c + c') = D.kv c * D.kv c' := by
  have := D.isMulCommutative
  exact kvCh611_add _ _ c c'

theorem kv_mem (c : Fin 4 → ZMod 2) : D.kv c ∈ uCh611 T L V := by
  have := D.isMulCommutative
  exact kvCh611_mem _ _ c

theorem z'_ne : d * z * d⁻¹ ≠ 1 ∧ d * z * d⁻¹ ≠ z := by
  constructor
  · intro h1
    apply D.z1
    have := congrArg (fun y => d⁻¹ * y * d) h1
    simpa [mul_assoc] using this
  · intro h1
    exact D.z1 (D.dV z (ZS_le_V D.zS) h1)

theorem z'_mem : d * z * d⁻¹ ∈ ch6ZS T L V :=
  (Subgroup.mem_normalizer_iff.mp D.dZS z).mp D.zS

theorem mem_Z_iff {x : G} : x ∈ zCh611 T ↔ x = 1 ∨ x = z := by
  have hz2 : z ^ 2 = 1 := D.sq z D.zU
  have hle : Subgroup.zpowers z ≤ zCh611 T := (Subgroup.zpowers_le).mpr D.zZ
  have heq : Subgroup.zpowers z = zCh611 T :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [D.Z2, card_zpowers_of_sq hz2 D.z1])
  rw [← heq, mem_zpowers_iff_of_sq hz2]

theorem comm' {a b : G} (ha : a ∈ uCh611 T L V) (hb : b ∈ uCh611 T L V) : a * b = b * a :=
  D.comm a ha b hb

theorem inv_eq {a : G} (ha : a ∈ uCh611 T L V) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact D.sq a ha)

theorem mem_ZS_iff {x : G} : x ∈ ch6ZS T L V ↔
    ∃ a b : ZMod 2, x = z ^ a.val * (d * z * d⁻¹) ^ b.val := by
  classical
  obtain ⟨hz'1, hz'z⟩ := D.z'_ne
  have hz'Z := D.z'_mem
  set z' := d * z * d⁻¹ with hz'
  have hzU := D.zU
  have hz'U : z' ∈ uCh611 T L V := ZS_le_U hz'Z
  let f : ZMod 2 × ZMod 2 → G := fun p => z ^ p.1.val * z' ^ p.2.val
  have hf : Function.Injective f := by
    have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    have hzz' : z * z' ≠ 1 := by
      intro h1
      apply hz'z
      have : z' = z⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [this, D.inv_eq hzU]
    have hzz'2 : z * z' ≠ z := by
      intro h1
      apply hz'1
      have := congrArg (fun y => z⁻¹ * y) h1
      simpa using this
    have hzz'3 : z * z' ≠ z' := by
      intro h1
      apply D.z1
      have := congrArg (fun y => y * z'⁻¹) h1
      simpa using this
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only [f] at hab
    rcases hz a with rfl | rfl <;> rcases hz b with rfl | rfl <;> rcases hz a' with rfl | rfl <;>
      rcases hz b' with rfl | rfl <;>
      simp only [zv0, zv1, pow_zero, pow_one, one_mul, mul_one] at hab <;>
      first
      | rfl
      | exact absurd hab D.z1.symm
      | exact absurd hab D.z1
      | exact absurd hab hz'1.symm
      | exact absurd hab hz'1
      | exact absurd hab hz'z.symm
      | exact absurd hab hz'z
      | exact absurd hab hzz'.symm
      | exact absurd hab hzz'
      | exact absurd hab hzz'2.symm
      | exact absurd hab hzz'2
      | exact absurd hab hzz'3.symm
      | exact absurd hab hzz'3
  have hfZ : ∀ p, f p ∈ ch6ZS T L V := fun p =>
    (ch6ZS T L V).mul_mem ((ch6ZS T L V).pow_mem D.zS _) ((ch6ZS T L V).pow_mem hz'Z _)
  have hcard : Nat.card (Set.range f) = 4 := by
    rw [Nat.card_range_of_injective hf, Nat.card_eq_fintype_card]
    rfl
  have hsub : Set.range f ⊆ (ch6ZS T L V : Set G) := by
    rintro _ ⟨p, rfl⟩
    exact hfZ p
  have heq : Set.range f = (ch6ZS T L V : Set G) := by
    apply Set.eq_of_subset_of_ncard_le hsub
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
        D.card_ZS, hcard]
  constructor
  · intro hx
    rw [← SetLike.mem_coe, ← heq] at hx
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact hfZ (a, b)

end Data611

end CFSG.Quasithin.H13
