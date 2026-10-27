module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Four
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Dick

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists
open scoped MatrixGroups

@[expose] def QuatPair {G : Type*} [Group G] (c d : G) : Prop :=
  c ^ 4 = 1 ∧ c ^ 2 ≠ 1 ∧ d ^ 2 = c ^ 2 ∧ d * c * d⁻¹ = c⁻¹

section Pair

variable {G : Type*} [Group G] {c d : G}

theorem QuatPair.map {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f)
    (h : QuatPair c d) : QuatPair (f c) (f d) := by
  obtain ⟨h4, h2, hd, hcd⟩ := h
  refine ⟨by rw [← map_pow, h4, map_one], fun e => h2 (hf (by rw [map_pow, e, map_one])), ?_, ?_⟩
  · rw [← map_pow, ← map_pow, hd]
  · rw [← map_mul, ← map_inv, ← map_mul, hcd, map_inv]

theorem QuatPair.c_inv (h : QuatPair c d) : c⁻¹ = c ^ 3 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', h.1]

theorem QuatPair.d_inv (h : QuatPair c d) : d⁻¹ = d * c ^ 2 := by
  rw [inv_eq_iff_mul_eq_one, ← mul_assoc, ← pow_two, h.2.2.1, ← pow_add]
  exact h.1

theorem QuatPair.c_mul_d (h : QuatPair c d) : c * d = d * c ^ 3 := by
  have h1 : d * c⁻¹ * d⁻¹ = c := by
    calc d * c⁻¹ * d⁻¹ = (d * c * d⁻¹)⁻¹ := by group
      _ = c⁻¹⁻¹ := by rw [h.2.2.2]
      _ = c := inv_inv c
  rw [← h.c_inv]
  exact ((mul_inv_eq_iff_eq_mul.mp h1).symm)

theorem QuatPair.c_pow_mul_d (h : QuatPair c d) (n : ℕ) : c ^ n * d = d * c ^ (3 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc c ^ (n + 1) * d = c ^ n * (c * d) := by rw [pow_succ, mul_assoc]
      _ = c ^ n * (d * c ^ 3) := by rw [h.c_mul_d]
      _ = (c ^ n * d) * c ^ 3 := by rw [mul_assoc]
      _ = d * c ^ (3 * n) * c ^ 3 := by rw [ih]
      _ = d * c ^ (3 * (n + 1)) := by rw [mul_assoc, ← pow_add]; ring_nf

theorem QuatPair.closure_elem (h : QuatPair c d) {x : G}
    (hx : x ∈ Subgroup.closure ({c, d} : Set G)) : ∃ k : ℕ, x = c ^ k ∨ x = d * c ^ k := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, Or.inl (pow_one _).symm⟩
    · exact ⟨0, Or.inr (by simp)⟩
  | one => exact ⟨0, Or.inl (pow_zero _).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, rfl | rfl⟩ := hx <;> obtain ⟨j, rfl | rfl⟩ := hy
    · exact ⟨i + j, Or.inl (pow_add _ _ _).symm⟩
    · refine ⟨3 * i + j, Or.inr ?_⟩
      rw [← mul_assoc, h.c_pow_mul_d, mul_assoc, ← pow_add]
    · refine ⟨i + j, Or.inr ?_⟩
      rw [mul_assoc, ← pow_add]
    · refine ⟨2 + 3 * i + j, Or.inl ?_⟩
      calc d * c ^ i * (d * c ^ j) = d * (c ^ i * d) * c ^ j := by simp only [mul_assoc]
        _ = d * (d * c ^ (3 * i)) * c ^ j := by rw [h.c_pow_mul_d]
        _ = d ^ 2 * (c ^ (3 * i) * c ^ j) := by simp only [pow_two, mul_assoc]
        _ = c ^ (2 + 3 * i + j) := by rw [h.2.2.1, ← pow_add, ← pow_add, add_assoc]
  | inv x _ hx =>
    obtain ⟨k, rfl | rfl⟩ := hx
    · refine ⟨3 * k, Or.inl ?_⟩
      rw [← inv_pow, h.c_inv, ← pow_mul, mul_comm]
    · refine ⟨9 * k + 2, Or.inr ?_⟩
      rw [_root_.mul_inv_rev, ← inv_pow, h.c_inv, h.d_inv, ← pow_mul, ← mul_assoc,
        show (c ^ (3 * k)) * d = d * c ^ (3 * (3 * k)) from h.c_pow_mul_d _, mul_assoc, ← pow_add]
      ring_nf

theorem QuatPair.isPGroup_two_closure (h : QuatPair c d) :
    IsPGroup 2 ↥(Subgroup.closure ({c, d} : Set G)) := by
  intro x
  refine ⟨2, Subtype.ext ?_⟩
  obtain ⟨k, hk | hk⟩ := h.closure_elem x.2
  · simp only [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 4 by norm_num]
    rw [hk, ← pow_mul, mul_comm, pow_mul, h.1, one_pow]
  · simp only [Subgroup.coe_pow, Subgroup.coe_one, show 2 ^ 2 = 4 by norm_num]
    have h2 : (d * c ^ k) ^ 2 = c ^ 2 := by
      calc (d * c ^ k) ^ 2 = d * (c ^ k * d) * c ^ k := by simp only [pow_two, mul_assoc]
        _ = d * (d * c ^ (3 * k)) * c ^ k := by rw [h.c_pow_mul_d]
        _ = d ^ 2 * c ^ (4 * k) := by
          simp only [pow_two, mul_assoc, ← pow_add]
          rw [show 3 * k + k = 4 * k by ring]
        _ = c ^ 2 := by rw [h.2.2.1, pow_mul, h.1, one_pow, mul_one]
    rw [hk, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, ← pow_mul, h.1]

theorem QuatPair.of_coe {H : Subgroup G} {c d : H} (h : QuatPair (c : G) (d : G)) :
    QuatPair c d := by
  obtain ⟨h4, h2, hd, hcd⟩ := h
  refine ⟨Subtype.ext (by simpa using h4), fun e => h2 (by simpa using congrArg Subtype.val e),
    Subtype.ext (by simpa using hd), Subtype.ext (by simpa using hcd)⟩

end Pair

theorem exists_quatPair_sl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ c d : SL(2, ZMod p), QuatPair c d := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1)
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  let c : SL(2, ZMod p) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  let d : SL(2, ZMod p) := ⟨!![a, b; b, -a], by
    simp [Matrix.det_fin_two]; linear_combination -hab⟩
  have hc2 : ((c ^ 2 : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c, Matrix.mul_apply, Fin.sum_univ_two]
  have hd2 : ((d ^ 2 : SL(2, ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := by
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hab | ring
  refine ⟨c, d, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hc2]
    simp
  · intro h
    have := congrArg (fun g : SL(2, ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p))) h
    simp only [hc2, Matrix.SpecialLinearGroup.coe_one] at this
    have h00 := congrFun (congrFun this 0) 0
    simp at h00
    apply h2
    linear_combination -h00
  · apply Subtype.ext
    rw [hd2, hc2]
  · rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [c, d, Matrix.mul_apply, Fin.sum_univ_two]

theorem blockGL3_injective {K : Type} [Field K] :
    Function.Injective (blockGL3 : GL (Fin 2) K →* GL (Fin 3) K) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  apply Units.ext
  have h := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hA
  simp only [coe_blockGL3, Units.val_one] at h
  ext i j
  have := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
  fin_cases i <;> fin_cases j <;> simpa [leviMat, Matrix.one_apply] using this

theorem exists_quatPair_su3 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ 2) : ∃ c d : ↥(StatedSU 3 (p ^ 1) F), QuatPair c d := by
  obtain ⟨c, d, h⟩ := exists_quatPair_sl2 hp2
  obtain ⟨e⟩ := exists_su2_equiv hF
  have hp1 : 1 ≤ p ^ 1 := by rw [pow_one]; exact (Fact.out : p.Prime).one_lt.le
  let ψ : SL(2, ZMod p) →* GL (Fin 3) F :=
    blockGL3.comp ((StatedSU 2 (p ^ 1) F).subtype.comp e.toMonoidHom)
  have hψ : ∀ x, ψ x ∈ StatedSU 3 (p ^ 1) F := fun x =>
    map_blockGL3_statedSU_le hp1 ⟨_, (e x).2, rfl⟩
  let φ : SL(2, ZMod p) →* ↥(StatedSU 3 (p ^ 1) F) := ψ.codRestrict _ hψ
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : ψ x = ψ y := congrArg Subtype.val hxy
    exact e.injective (Subtype.ext (blockGL3_injective h1))
  exact ⟨φ c, φ d, h.map φ hφ⟩

theorem exists_conj_le_of_isPGroup {G : Type*} [Group G] [Finite G] {M : Subgroup G}
    (hodd : Odd M.index) {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    ∃ g : G, ∀ x ∈ Q, g * x * g⁻¹ ∈ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSM⟩ := exists_sylow_le_of_odd_index hodd
  obtain ⟨Q₁, hQ₁⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q₁ S
  refine ⟨g, fun x hx => hSM ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨x, hQ₁ hx, by simp [MulAut.conj_apply]⟩

theorem exists_quaternion_pair {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ 2) (M : Subgroup ↥(StatedSU 3 (p ^ 1) K))
    (hodd : Odd M.index) : ∃ c d : ↥M, QuatPair c d := by
  obtain ⟨c₁, d₁, h₁⟩ := exists_quatPair_su3 hp2 hK
  obtain ⟨g, hg⟩ := exists_conj_le_of_isPGroup hodd h₁.isPGroup_two_closure
  have hc : g * c₁ * g⁻¹ ∈ M := hg c₁ (Subgroup.subset_closure (by simp))
  have hd : g * d₁ * g⁻¹ ∈ M := hg d₁ (Subgroup.subset_closure (by simp))
  have h2 := h₁.map (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine ⟨⟨g * c₁ * g⁻¹, hc⟩, ⟨g * d₁ * g⁻¹, hd⟩, QuatPair.of_coe ?_⟩
  simpa [MulAut.conj_apply] using h2

end CFSG.Quasithin.A312U3
