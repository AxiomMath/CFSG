module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec11.Item116Holes
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

structure IsR2Rotation {G : Type} [Group G] (A : Subgroup G) (c a d ζ : G) : Prop where
  mem : ζ ∈ Subgroup.normalizer (A : Set G)
  inv_a : ζ * a * ζ⁻¹ = a⁻¹
  sq_c : ζ ^ 2 * c * (ζ ^ 2)⁻¹ ∈ Subgroup.zpowers d
  sq_d : ζ ^ 2 * d * (ζ ^ 2)⁻¹ ∈ Subgroup.zpowers c
  cover : ∀ w ∈ Subgroup.normalizer (A : Set G),
    ∃ k : ℕ, (ζ ^ k)⁻¹ * w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)

namespace HuppertFin

open Matrix

abbrev Anti (p q s t : ZMod 3) : Prop := p * p + q * s = 0 ∧ s * q + t * t = 0

theorem fs1 : ∀ p q s t : ZMod 3, p * t - q * s ≠ 0 →
    ((s = p ∧ t = 2 * q) ∨ (s = 2 * p ∧ t = q)) →
    Anti p q s t ∨ Anti p (2 * q) s (2 * t) := by
  decide +kernel

theorem F4_cover : ∀ p q s t : ZMod 3, p * t - q * s ≠ 0 → Anti p q s t →
    ∀ v0 v1 : ZMod 3, ∃ k : Fin 4, ∃ x : ZMod 3,
      (!![p, q; s, t] ^ (k : ℕ)) 0 0 * x = v0 ∧ (!![p, q; s, t] ^ (k : ℕ)) 1 0 * x = v1 := by
  decide +kernel

theorem unit_zmod3 : ∀ a b : ZMod 3, a * b = 1 → a = 1 ∨ a = 2 := by
  decide +kernel

theorem two_ne_one_imp : ∀ a b : ZMod 3, a * b = 1 → a ≠ 1 → a = 2 := by
  decide +kernel
theorem zneg0 : -(0 : ZMod 3) = 0 := by decide

section Shape

@[expose] def Shape (M : KFacts.Mat33) : Prop := M 2 0 = 0 ∧ M 2 1 = 0

theorem chi_mul {M N : KFacts.Mat33} (hM : Shape M) : (M * N) 2 2 = M 2 2 * N 2 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, hM.1, hM.2]

theorem blk_one : Item116Fusion.blk (1 : KFacts.Mat33) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Item116Fusion.blk, Matrix.one_apply]

theorem blk_pow {M : KFacts.Mat33} (hM : Shape M) (k : ℕ) :
    Item116Fusion.blk (M ^ k) = Item116Fusion.blk M ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, blk_one]
  | succ k ih => rw [pow_succ, pow_succ, Item116Fusion.blk_mul hM.1 hM.2, ih]

end Shape

section Coords

variable {G : Type} [Group G] {A : Subgroup G}

theorem coordMat_one_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} :
    coordMat f 1 = 1 := by
  refine coordMat_eq fun j => ?_
  have e : (fun i => (1 : KFacts.Mat33) i j) = Pi.single j 1 := by
    funext i
    simp [Matrix.one_apply, Pi.single_apply]
  simp only [e, Subgroup.coe_one, one_mul, inv_one, mul_one]

theorem coordMat_mul_inv_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (w : Subgroup.normalizer (A : Set G)) : coordMat f w * coordMat f w⁻¹ = 1 := by
  rw [← coordMat_mul, mul_inv_cancel, coordMat_one_eq]

theorem coordMat_pow_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (w : Subgroup.normalizer (A : Set G)) (k : ℕ) :
    coordMat f (w ^ k) = coordMat f w ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, coordMat_one_eq]
  | succ k ih => rw [pow_succ, pow_succ, coordMat_mul, ih]

theorem hw_of_normalizer_le {c d w : G} (hN : w ∈ Subgroup.normalizer (A : Set G))
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G)) :
    ∀ x ∈ Subgroup.closure ({c, d} : Set G),
      w * x * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
  fun x hx => (Subgroup.mem_normalizer_iff.mp (hle hN) x).mp hx

end Coords

section Membership

variable {G : Type} [Group G] {A : Subgroup G} {c d a : G}

theorem fc_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) = c := by
  rw [hv]
  simp [Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem fd_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) = d := by
  rw [hv]
  simp [Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem fa_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    (f (Multiplicative.ofAdd (Pi.single 2 1)) : G) = a := by
  rw [hv]
  simp [Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem f_neg_mul {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} (u : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd (-u)) : G) * (f (Multiplicative.ofAdd u) : G) = 1 := by
  have h0 : (-u + u : Fin 3 → ZMod 3) = 0 := neg_add_cancel u
  have h1 : Multiplicative.ofAdd (-u) * Multiplicative.ofAdd u =
      (1 : Multiplicative (Fin 3 → ZMod 3)) := by
    rw [← ofAdd_add, h0, ofAdd_zero]
  rw [← Subgroup.coe_mul, ← map_mul, h1, map_one, Subgroup.coe_one]

theorem f_inv {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} (u : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd u) : G)⁻¹ = (f (Multiplicative.ofAdd (-u)) : G) :=
  (eq_inv_of_mul_eq_one_left (f_neg_mul u)).symm

theorem cd_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    c * d = (f (Multiplicative.ofAdd (Pi.single 0 1 + Pi.single 1 1)) : G) := by
  rw [ofAdd_add, map_mul, Subgroup.coe_mul, fc_eq hv, fd_eq hv]

theorem cdinv_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    c * d⁻¹ = (f (Multiplicative.ofAdd (Pi.single 0 1 + -Pi.single 1 1)) : G) := by
  have h2 : (f (Multiplicative.ofAdd (-Pi.single 1 1)) : G) = d⁻¹ := by
    rw [← fd_eq hv, f_inv]
  rw [ofAdd_add, map_mul, Subgroup.coe_mul, fc_eq hv, h2]

theorem mem_cd_closure_coord {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) {x : G}
    (hx : x ∈ Subgroup.closure ({c, d} : Set G)) :
    ∃ u : Fin 3 → ZMod 3, u 2 = 0 ∧ x = (f (Multiplicative.ofAdd u) : G) := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨Pi.single 0 1, by simp [Pi.single_apply], (fc_eq hv).symm⟩
    · exact ⟨Pi.single 1 1, by simp [Pi.single_apply], (fd_eq hv).symm⟩
  | one => exact ⟨0, rfl, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv', rfl⟩ := hy
    exact ⟨u + v, by simp [hu, hv'], by rw [ofAdd_add, map_mul, Subgroup.coe_mul]⟩
  | inv x _ hx =>
    obtain ⟨u, hu, hxu⟩ := hx
    refine ⟨-u, ?_, ?_⟩
    · show -(u 2) = 0
      rw [hu, zneg0]
    · rw [hxu]
      exact f_inv u

theorem mem_cd_iff {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) (u : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd u) : G) ∈ Subgroup.closure ({c, d} : Set G) ↔ u 2 = 0 := by
  constructor
  · intro hmem
    obtain ⟨v, hv2, heq⟩ := mem_cd_closure_coord hv hmem
    have huv : Multiplicative.ofAdd u = Multiplicative.ofAdd v :=
      f.injective (Subtype.ext heq)
    rw [Multiplicative.ofAdd.injective huv]
    exact hv2
  · intro hu2
    have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
    have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
    rw [hv, hu2]
    simp only [ZMod.val_zero, pow_zero, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hcB _) (Subgroup.pow_mem _ hdB _)

theorem mem_zpowers_coord {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} {e v : Fin 3 → ZMod 3}
    (hx : (f (Multiplicative.ofAdd v) : G) ∈ Subgroup.zpowers (f (Multiplicative.ofAdd e) : G)) :
    ∃ n : ℤ, v = n • e := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h1 : f (Multiplicative.ofAdd (n • e)) = f (Multiplicative.ofAdd v) := by
    rw [ofAdd_zsmul, map_zpow]
    exact Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)
  exact ⟨n, (Multiplicative.ofAdd.injective (f.injective h1)).symm⟩

theorem mem_zpowers_c_iff {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) (u : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd u) : G) ∈ Subgroup.zpowers c ↔ u 1 = 0 ∧ u 2 = 0 := by
  constructor
  · intro hx
    rw [← fc_eq hv] at hx
    obtain ⟨n, rfl⟩ := mem_zpowers_coord hx
    simp [Pi.single_apply]
  · rintro ⟨h1, h2⟩
    have hu : u = (((u 0).val : ℤ)) • (Pi.single 0 1 : Fin 3 → ZMod 3) := by
      funext i
      fin_cases i <;> simp [Pi.single_apply, h1, h2, show (1 : ZMod 3).val = 1 from rfl]
    have key : ∀ n : ℤ, (f (Multiplicative.ofAdd (n • (Pi.single 0 1 : Fin 3 → ZMod 3))) : G) =
        (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) ^ n := by
      intro n
      rw [ofAdd_zsmul, map_zpow, Subgroup.coe_zpow]
    rw [← fc_eq hv]
    refine Subgroup.mem_zpowers_iff.mpr ⟨((u 0).val : ℤ), ?_⟩
    rw [← key, ← hu]

theorem mem_zpowers_d_iff {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) (u : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd u) : G) ∈ Subgroup.zpowers d ↔ u 0 = 0 ∧ u 2 = 0 := by
  constructor
  · intro hx
    rw [← fd_eq hv] at hx
    obtain ⟨n, rfl⟩ := mem_zpowers_coord hx
    simp [Pi.single_apply]
  · rintro ⟨h1, h2⟩
    have hu : u = (((u 1).val : ℤ)) • (Pi.single 1 1 : Fin 3 → ZMod 3) := by
      funext i
      fin_cases i <;> simp [Pi.single_apply, h1, h2, show (1 : ZMod 3).val = 1 from rfl]
    have key : ∀ n : ℤ, (f (Multiplicative.ofAdd (n • (Pi.single 1 1 : Fin 3 → ZMod 3))) : G) =
        (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) ^ n := by
      intro n
      rw [ofAdd_zsmul, map_zpow, Subgroup.coe_zpow]
    rw [← fd_eq hv]
    refine Subgroup.mem_zpowers_iff.mpr ⟨((u 1).val : ℤ), ?_⟩
    rw [← key, ← hu]

theorem mem_zpowers_cd_imp {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) (u : Fin 3 → ZMod 3)
    (hx : (f (Multiplicative.ofAdd u) : G) ∈ Subgroup.zpowers (c * d)) :
    u 0 = u 1 ∧ u 2 = 0 := by
  rw [cd_eq hv] at hx
  obtain ⟨n, rfl⟩ := mem_zpowers_coord hx
  simp [Pi.single_apply]

theorem mem_zpowers_cdinv_imp {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) (u : Fin 3 → ZMod 3)
    (hx : (f (Multiplicative.ofAdd u) : G) ∈ Subgroup.zpowers (c * d⁻¹)) :
    u 1 = -u 0 ∧ u 2 = 0 := by
  rw [cdinv_eq hv] at hx
  obtain ⟨n, rfl⟩ := mem_zpowers_coord hx
  constructor
  · simp [Pi.single_apply, zsmul_eq_mul, mul_neg, zneg0]
    exact mul_neg_one _
  · simp [Pi.single_apply, zneg0]

end Membership

section Conj

variable {G : Type} [Group G] {A : Subgroup G} {c d a : G}

theorem conj_general {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (g : Subgroup.normalizer (A : Set G)) (v : Fin 3 → ZMod 3) :
    (g : G) * (f (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ =
      (f (Multiplicative.ofAdd (Matrix.mulVec (coordMat f g) v)) : G) := by
  have e0 := Item116Fusion.conj_eq_coordMat f g 0
  have e1 := Item116Fusion.conj_eq_coordMat f g 1
  have e2 := Item116Fusion.conj_eq_coordMat f g 2
  rw [fc_eq hv] at e0
  rw [fd_eq hv] at e1
  rw [fa_eq hv] at e2
  have hvec_pw : ∀ i, Matrix.mulVec (coordMat f g) v i =
      (v 0).val • coordMat f g i 0 + (v 1).val • coordMat f g i 1 +
        (v 2).val • coordMat f g i 2 := by
    intro i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, nsmul_eq_mul,
        ZMod.natCast_zmod_val, ZMod.cast_id] <;> ring
  have hvec : Matrix.mulVec (coordMat f g) v =
      (v 0).val • (fun i => coordMat f g i 0) + (v 1).val • (fun i => coordMat f g i 1) +
        (v 2).val • (fun i => coordMat f g i 2) := funext hvec_pw
  have hsplit : (g : G) * (c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) * (g : G)⁻¹ =
      ((g : G) * c * (g : G)⁻¹) ^ (v 0).val * ((g : G) * d * (g : G)⁻¹) ^ (v 1).val *
        ((g : G) * a * (g : G)⁻¹) ^ (v 2).val := by
    rw [conj_pow, conj_pow, conj_pow]
    group
  rw [hv v, hsplit, e0, e1, e2, hvec]
  simp only [ofAdd_add, ofAdd_nsmul, map_mul, map_pow, Subgroup.coe_mul, Subgroup.coe_pow]

end Conj

section Chain

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c d a : G}

theorem zneg_two (x : ZMod 3) : -x = 2 * x := by
  revert x
  decide

theorem f_mul_ofAdd {f : Multiplicative (Fin 3 → ZMod 3) ≃* A} (u v : Fin 3 → ZMod 3) :
    (f (Multiplicative.ofAdd u) : G) * (f (Multiplicative.ofAdd v) : G) =
      (f (Multiplicative.ofAdd (u + v)) : G) := by
  rw [← Subgroup.coe_mul, ← map_mul, ofAdd_add]

theorem coordMat_row2 {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (hw : ∀ x ∈ Subgroup.closure ({c, d} : Set G),
      (w : G) * x * (w : G)⁻¹ ∈ Subgroup.closure ({c, d} : Set G))
    (j : Fin 3) (hj : j ≠ 2) : coordMat f w 2 j = 0 := by
  have hmem : (w : G) * (f (Multiplicative.ofAdd (Pi.single j 1)) : G) * (w : G)⁻¹ ∈
      Subgroup.closure ({c, d} : Set G) := by
    apply hw
    rw [mem_cd_iff hv, Pi.single_apply, if_neg (Ne.symm hj)]
  rw [Item116Fusion.conj_eq_coordMat f w j, mem_cd_iff hv] at hmem
  exact hmem

theorem shape_of_le {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (w : Subgroup.normalizer (A : Set G)) : Shape (coordMat f w) :=
  ⟨coordMat_row2 hv w (hw_of_normalizer_le w.2 hle) 0 (by decide),
    coordMat_row2 hv w (hw_of_normalizer_le w.2 hle) 1 (by decide)⟩

theorem coordMat_22_eq_one {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hcj : ∀ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G))
    (w : Subgroup.normalizer (A : Set G))
    (hwc : (w : G) ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    coordMat f w 2 2 = 1 := by
  have ha : a ∈ A := by
    have h2 := (f (Multiplicative.ofAdd (Pi.single 2 1))).2
    rwa [fa_eq hv] at h2
  have key := hcj (w : G)⁻¹ (Subgroup.inv_mem _ w.2) (Subgroup.inv_mem _ hwc) a ha
  rw [inv_inv] at key
  have hcol := Item116Fusion.conj_eq_coordMat f w 2
  rw [fa_eq hv] at hcol
  rw [hcol, ← fa_eq hv, f_inv, f_mul_ofAdd, mem_cd_iff hv] at key
  simp only [Pi.add_apply, Pi.neg_apply, Pi.single_eq_same] at key
  exact (neg_add_eq_zero.mp key).symm

theorem mem_normalizer_zpowers_of_central {l x : G} (h : l * x = x * l) :
    l ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
  Sec10.mem_normalizer_zpowers_of_conj_mem (by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.mem_zpowers x)

theorem coordMat_of_central {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hcj : ∀ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G))
    (l : G) (hlN : l ∈ Subgroup.normalizer (A : Set G))
    (hlc : l * c = c * l) (hld : l * d * l⁻¹ = d⁻¹) :
    coordMat f ⟨l, hlN⟩ 0 0 = 1 ∧ coordMat f ⟨l, hlN⟩ 1 0 = 0 ∧
      coordMat f ⟨l, hlN⟩ 2 0 = 0 ∧ coordMat f ⟨l, hlN⟩ 0 1 = 0 ∧
      coordMat f ⟨l, hlN⟩ 1 1 = 2 ∧ coordMat f ⟨l, hlN⟩ 2 1 = 0 ∧
      coordMat f ⟨l, hlN⟩ 2 2 = 1 := by
  have hcl : l * c * l⁻¹ = c := by
    rw [hlc, mul_assoc, mul_inv_cancel, mul_one]
  have hc0 : ((⟨l, hlN⟩ : Subgroup.normalizer (A : Set G)) : G) *
      (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) *
      ((⟨l, hlN⟩ : Subgroup.normalizer (A : Set G)) : G)⁻¹ =
      (f (Multiplicative.ofAdd (Pi.single 0 1)) : G) := by
    rw [fc_eq hv]
    exact hcl
  have hd1 : ((⟨l, hlN⟩ : Subgroup.normalizer (A : Set G)) : G) *
      (f (Multiplicative.ofAdd (Pi.single 1 1)) : G) *
      ((⟨l, hlN⟩ : Subgroup.normalizer (A : Set G)) : G)⁻¹ =
      (f (Multiplicative.ofAdd (-Pi.single 1 1)) : G) := by
    rw [fd_eq hv, ← f_inv, fd_eq hv]
    exact hld
  have hcent : l ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    mem_normalizer_zpowers_of_central hlc
  have h22 := coordMat_22_eq_one hv hcj ⟨l, hlN⟩ hcent
  have e00 := Item116Fusion.coordMat_apply_of_conj hc0 0
  have e10 := Item116Fusion.coordMat_apply_of_conj hc0 1
  have e20 := Item116Fusion.coordMat_apply_of_conj hc0 2
  have e01 := Item116Fusion.coordMat_apply_of_conj hd1 0
  have e11 := Item116Fusion.coordMat_apply_of_conj hd1 1
  have e21 := Item116Fusion.coordMat_apply_of_conj hd1 2
  simp only [Pi.single_apply, Pi.neg_apply] at e00 e10 e20 e01 e11 e21
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h22⟩
  · simpa using e00
  · simpa using e10
  · simpa using e20
  · exact e01.trans zneg0
  · rw [e11]
    decide
  · exact e21.trans zneg0

theorem exists_chi_ne_one {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (hχ : ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ g : Subgroup.normalizer (A : Set G), coordMat f g 2 2 ≠ 1 := by
  obtain ⟨w0, hw0, x0, hx0, hnot⟩ := hχ
  have hsurj : ∀ x ∈ A, ∃ u : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd u) : G) = x := by
    intro x hx
    exact ⟨Multiplicative.toAdd (f.symm ⟨x, hx⟩), by simp⟩
  obtain ⟨u, hu⟩ := hsurj x0 hx0
  obtain ⟨g, hgdef⟩ : ∃ g : Subgroup.normalizer (A : Set G), (g : G) = w0⁻¹ :=
    ⟨⟨w0⁻¹, Subgroup.inv_mem _ hw0⟩, rfl⟩
  have hshape := shape_of_le hv hle g
  have hconj := conj_general hv g u
  rw [hgdef, inv_inv] at hconj
  rw [← hu, hconj, f_inv, f_mul_ofAdd, mem_cd_iff hv] at hnot
  have hM2 : (Matrix.mulVec (coordMat f g) u) 2 = coordMat f g 2 2 * u 2 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hshape.1, hshape.2]
  refine ⟨g, fun h1 => hnot ?_⟩
  rw [Pi.add_apply, Pi.neg_apply, hM2, h1, one_mul]
  exact neg_add_cancel _

end Chain

section Trans

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c d a : G}

theorem conj_c_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G)) :
    (w : G) * c * (w : G)⁻¹ = (f (Multiplicative.ofAdd (fun i => coordMat f w i 0)) : G) := by
  rw [← fc_eq hv]
  exact Item116Fusion.conj_eq_coordMat f w 0

theorem conj_d_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G)) :
    (w : G) * d * (w : G)⁻¹ = (f (Multiplicative.ofAdd (fun i => coordMat f w i 1)) : G) := by
  rw [← fd_eq hv]
  exact Item116Fusion.conj_eq_coordMat f w 1

theorem mem_zpowers_c_conj {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G)) :
    (w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers c ↔
      coordMat f w 1 0 = 0 ∧ coordMat f w 2 0 = 0 := by
  rw [conj_c_eq hv w]
  exact mem_zpowers_c_iff hv _

theorem mem_zpowers_d_conj {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G)) :
    (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers d ↔
      coordMat f w 0 1 = 0 ∧ coordMat f w 2 1 = 0 := by
  rw [conj_d_eq hv w]
  exact mem_zpowers_d_iff hv _

theorem mem_zpowers_d_of_c {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G)) :
    (w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers d ↔
      coordMat f w 0 0 = 0 ∧ coordMat f w 2 0 = 0 := by
  rw [conj_c_eq hv w]
  exact mem_zpowers_d_iff hv _

theorem mem_zpowers_c_of_d {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G)) :
    (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers c ↔
      coordMat f w 1 1 = 0 ∧ coordMat f w 2 1 = 0 := by
  rw [conj_d_eq hv w]
  exact mem_zpowers_c_iff hv _

theorem c_cd_imp {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (h : (w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d)) :
    coordMat f w 0 0 = coordMat f w 1 0 ∧ coordMat f w 2 0 = 0 := by
  rw [conj_c_eq hv w] at h
  exact mem_zpowers_cd_imp hv _ h

theorem d_cd_imp {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (h : (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d)) :
    coordMat f w 0 1 = coordMat f w 1 1 ∧ coordMat f w 2 1 = 0 := by
  rw [conj_d_eq hv w] at h
  exact mem_zpowers_cd_imp hv _ h

theorem c_cdinv_imp {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (h : (w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) :
    coordMat f w 1 0 = -coordMat f w 0 0 ∧ coordMat f w 2 0 = 0 := by
  rw [conj_c_eq hv w] at h
  exact mem_zpowers_cdinv_imp hv _ h

theorem d_cdinv_imp {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (h : (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) :
    coordMat f w 1 1 = -coordMat f w 0 1 ∧ coordMat f w 2 1 = 0 := by
  rw [conj_d_eq hv w] at h
  exact mem_zpowers_cdinv_imp hv _ h

theorem cond_of_34 {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (h : ((w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d) ∧
        (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      ((w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧
        (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d))) :
    (coordMat f w 1 0 = coordMat f w 0 0 ∧ coordMat f w 1 1 = 2 * coordMat f w 0 1) ∨
      (coordMat f w 1 0 = 2 * coordMat f w 0 0 ∧ coordMat f w 1 1 = coordMat f w 0 1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨e1, -⟩ := c_cd_imp hv w h1
    obtain ⟨e2, -⟩ := d_cdinv_imp hv w h2
    exact Or.inl ⟨e1.symm, by rw [e2, zneg_two]⟩
  · obtain ⟨e1, -⟩ := c_cdinv_imp hv w h1
    obtain ⟨e2, -⟩ := d_cd_imp hv w h2
    exact Or.inr ⟨by rw [e1, zneg_two], e2.symm⟩

theorem cond_of_sd16 {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (w : Subgroup.normalizer (A : Set G))
    (h : ((w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers c ∧ (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers d) ∨
      ((w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers d ∧ (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers c) ∨
      ((w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d) ∧
        (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      ((w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧
        (w : G) * d * (w : G)⁻¹ ∈ Subgroup.zpowers (c * d))) :
    (coordMat f w 1 0 = 0 ∧ coordMat f w 0 1 = 0) ∨
      (coordMat f w 0 0 = 0 ∧ coordMat f w 1 1 = 0) ∨
      (coordMat f w 1 0 = coordMat f w 0 0 ∧ coordMat f w 1 1 = 2 * coordMat f w 0 1) ∨
      (coordMat f w 1 0 = 2 * coordMat f w 0 0 ∧ coordMat f w 1 1 = coordMat f w 0 1) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h34
  · exact Or.inl ⟨((mem_zpowers_c_conj hv w).mp h1).1, ((mem_zpowers_d_conj hv w).mp h2).1⟩
  · exact Or.inr (Or.inl ⟨((mem_zpowers_d_of_c hv w).mp h1).1,
      ((mem_zpowers_c_of_d hv w).mp h2).1⟩)
  · exact Or.inr (Or.inr (cond_of_34 hv w h34))

end Trans

section Inv

theorem det_ne_zero_of_blk {M N : KFacts.Mat33}
    (h : Item116Fusion.blk M * Item116Fusion.blk N = 1) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 ≠ 0 := by
  intro h0
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  have hBM : (Item116Fusion.blk M).det = M 0 0 * M 1 1 - M 0 1 * M 1 0 := by
    rw [Matrix.det_fin_two]
    simp [Item116Fusion.blk]
  rw [hBM, h0, zero_mul] at hd
  exact zero_ne_one hd

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c d a : G}

theorem blk_mul_inv_one {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (w : Subgroup.normalizer (A : Set G)) :
    Item116Fusion.blk (coordMat f w) * Item116Fusion.blk (coordMat f w⁻¹) = 1 := by
  have hs := shape_of_le hv hle w⁻¹
  rw [← Item116Fusion.blk_mul hs.1 hs.2, coordMat_mul_inv_eq, blk_one]

theorem blk_inv_mul_one {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (w : Subgroup.normalizer (A : Set G)) :
    Item116Fusion.blk (coordMat f w⁻¹) * Item116Fusion.blk (coordMat f w) = 1 := by
  have hs := shape_of_le hv hle w
  rw [← Item116Fusion.blk_mul hs.1 hs.2, ← coordMat_mul, inv_mul_cancel, coordMat_one_eq,
    blk_one]

theorem chi_mul_inv_one {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (w : Subgroup.normalizer (A : Set G)) :
    coordMat f w 2 2 * coordMat f w⁻¹ 2 2 = 1 := by
  have hs := shape_of_le hv hle w
  have h : coordMat f w * coordMat f w⁻¹ = 1 := coordMat_mul_inv_eq w
  have h22 := congrFun (congrFun h 2) 2
  rw [chi_mul hs] at h22
  simpa using h22

end Inv

section Entries

theorem coord_mul_phi (B M : KFacts.Mat33) (h00 : M 0 0 = 1) (h10 : M 1 0 = 0)
    (h20 : M 2 0 = 0) (h01 : M 0 1 = 0) (h11 : M 1 1 = 2) (h21 : M 2 1 = 0) :
    (B * M) 0 0 = B 0 0 ∧ (B * M) 0 1 = 2 * B 0 1 ∧
      (B * M) 1 0 = B 1 0 ∧ (B * M) 1 1 = 2 * B 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h00, h10, h20, h01, h11, h21]
  exact ⟨by ring, by ring, by ring, by ring⟩

theorem mul_10_eq (N M : KFacts.Mat33) (hM : M 2 0 = 0) :
    (N * M) 1 0 = N 1 0 * M 0 0 + N 1 1 * M 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, hM]

theorem mul_20_eq_zero (N M : KFacts.Mat33) (hN0 : N 2 0 = 0) (hN1 : N 2 1 = 0)
    (hM : M 2 0 = 0) : (N * M) 2 0 = 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, hN0, hN1, hM]

theorem col0_zero (B B' : Matrix (Fin 2) (Fin 2) (ZMod 3)) (x v0 v1 : ZMod 3)
    (hBB : B' * B = 1) (h0 : B 0 0 * x = v0) (h1 : B 1 0 * x = v1) :
    B' 1 0 * v0 + B' 1 1 * v1 = 0 := by
  have h : B' 1 0 * B 0 0 + B' 1 1 * B 1 0 = 0 := by
    have := congrFun (congrFun hBB 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  rw [← h0, ← h1]
  calc B' 1 0 * (B 0 0 * x) + B' 1 1 * (B 1 0 * x)
      = (B' 1 0 * B 0 0 + B' 1 1 * B 1 0) * x := by ring
    _ = 0 := by rw [h, zero_mul]

end Entries

section Finite

theorem prod_case34 : ∀ p0 q0 s0 t0 q s : ZMod 3, q ≠ 0 → s ≠ 0 →
    ((s0 = p0 ∧ t0 = 2 * q0) ∨ (s0 = 2 * p0 ∧ t0 = q0)) →
    ((s * p0 = q * s0 ∧ s * q0 = 2 * (q * t0)) ∨ (s * p0 = 2 * (q * s0) ∧ s * q0 = q * t0)) := by
  decide +kernel

theorem entries_case2 {N M : KFacts.Mat33} (hM0 : M 2 0 = 0) (hM1 : M 2 1 = 0)
    (hN00 : N 0 0 = 0) (hN11 : N 1 1 = 0) :
    (N * M) 0 0 = N 0 1 * M 1 0 ∧ (N * M) 0 1 = N 0 1 * M 1 1 ∧
      (N * M) 1 0 = N 1 0 * M 0 0 ∧ (N * M) 1 1 = N 1 0 * M 0 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, hM0, hM1, hN00, hN11]

theorem sq_entries (M : KFacts.Mat33) (hM0 : M 2 0 = 0) (hM1 : M 2 1 = 0) :
    (M ^ 2) 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0 ∧ (M ^ 2) 2 0 = 0 ∧
      (M ^ 2) 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1 ∧ (M ^ 2) 2 1 = 0 := by
  rw [pow_two]
  simp [Matrix.mul_apply, Fin.sum_univ_three, hM0, hM1]

end Finite

section Core

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c d a : G}

theorem a_mem_norm_of_mem {x : G} (hx : x ∈ A) :
    x ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact A.mul_mem (A.mul_mem hx hy) (A.inv_mem hx)
  · intro hy
    have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    rw [← e]
    exact A.mul_mem (A.mul_mem (A.inv_mem hx) hy) hx

theorem a_mem_norm {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    a ∈ Subgroup.normalizer (A : Set G) := by
  have ha : a ∈ A := by
    have h2 := (f (Multiplicative.ofAdd (Pi.single 2 1))).2
    rwa [fa_eq hv] at h2
  exact a_mem_norm_of_mem ha

theorem a_sq_eq_inv {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val) :
    a * a = a⁻¹ := by
  have e : (Pi.single 2 1 + Pi.single 2 1 + Pi.single 2 1 : Fin 3 → ZMod 3) = 0 := by
    funext i
    fin_cases i <;> simp [Pi.single_apply] <;> decide
  have h1 := f_mul_ofAdd (f := f) (Pi.single 2 1) (Pi.single 2 1)
  have h2 := f_mul_ofAdd (f := f) (Pi.single 2 1 + Pi.single 2 1) (Pi.single 2 1)
  rw [e, ofAdd_zero, map_one, Subgroup.coe_one] at h2
  rw [fa_eq hv] at h1 h2
  apply eq_inv_of_mul_eq_one_left
  rw [h1]
  exact h2

theorem exists_case34_chi2 {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (hcj : ∀ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G))
    (hsd : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)))
    (hR2 : ∃ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)))
    (hχ : ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ h : Subgroup.normalizer (A : Set G), coordMat f h 2 2 = 2 ∧
      ((coordMat f h 1 0 = coordMat f h 0 0 ∧ coordMat f h 1 1 = 2 * coordMat f h 0 1) ∨
        (coordMat f h 1 0 = 2 * coordMat f h 0 0 ∧ coordMat f h 1 1 = coordMat f h 0 1)) := by
  obtain ⟨w0, hw0, h34⟩ := hR2
  have hc34 := cond_of_34 hv ⟨w0, hw0⟩ h34
  rcases unit_zmod3 _ _ (chi_mul_inv_one hv hle ⟨w0, hw0⟩) with h1 | h2
  · obtain ⟨g, hg⟩ := exists_chi_ne_one hv hle hχ
    have hg2 : coordMat f g 2 2 = 2 := two_ne_one_imp _ _ (chi_mul_inv_one hv hle g) hg
    have hgs := shape_of_le hv hle g
    rcases cond_of_sd16 hv g (hsd g g.2) with ⟨e1, e2⟩ | ⟨e1, e2⟩ | h3 | h4
    · exfalso
      have hcg : (g : G) * c * (g : G)⁻¹ ∈ Subgroup.zpowers c :=
        (mem_zpowers_c_conj hv g).mpr ⟨e1, hgs.1⟩
      have h22 := coordMat_22_eq_one hv hcj g (Sec10.mem_normalizer_zpowers_of_conj_mem hcg)
      rw [hg2] at h22
      exact absurd h22 (by decide)
    · have hW := shape_of_le hv hle (⟨w0, hw0⟩ : Subgroup.normalizer (A : Set G))
      have hdet := det_ne_zero_of_blk (blk_mul_inv_one hv hle g)
      have hq : coordMat f g 0 1 ≠ 0 := fun h0 => hdet (by simp [e1, e2, h0])
      have hs : coordMat f g 1 0 ≠ 0 := fun h0 => hdet (by simp [e1, e2, h0])
      refine ⟨g * (⟨w0, hw0⟩ : Subgroup.normalizer (A : Set G)), ?_, ?_⟩
      · rw [coordMat_mul, chi_mul hgs, hg2, h1, mul_one]
      · obtain ⟨E00, E01, E10, E11⟩ := entries_case2 hW.1 hW.2 e1 e2
        rw [coordMat_mul, E00, E01, E10, E11]
        exact prod_case34 _ _ _ _ _ _ hq hs hc34
    · exact ⟨g, hg2, Or.inl h3⟩
    · exact ⟨g, hg2, Or.inr h4⟩
  · exact ⟨⟨w0, hw0⟩, h2, hc34⟩

end Core

section Final

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c d a : G}

theorem exists_anti_chi2 {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (hcj : ∀ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G))
    (hsd : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)))
    (hR2 : ∃ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)))
    (hχ : ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G))
    (m : G) (hmN : m ∈ Subgroup.normalizer (A : Set G))
    (hmc : m * c = c * m) (hmd : m * d * m⁻¹ = d⁻¹) :
    ∃ r : Subgroup.normalizer (A : Set G),
      Anti (coordMat f r 0 0) (coordMat f r 0 1) (coordMat f r 1 0) (coordMat f r 1 1) ∧
        coordMat f r 2 2 = 2 := by
  obtain ⟨h00, h10, h20, h01, h11, h21, h22⟩ := coordMat_of_central hv hcj m hmN hmc hmd
  obtain ⟨h, hh2, hcond⟩ := exists_case34_chi2 hv hle hcj hsd hR2 hχ
  have hdet := det_ne_zero_of_blk (blk_mul_inv_one hv hle h)
  rcases fs1 _ _ _ _ hdet hcond with hA | hB
  · exact ⟨h, hA, hh2⟩
  · refine ⟨h * (⟨m, hmN⟩ : Subgroup.normalizer (A : Set G)), ?_, ?_⟩
    · obtain ⟨e00, e01, e10, e11⟩ :=
        coord_mul_phi (coordMat f h) (coordMat f (⟨m, hmN⟩ : Subgroup.normalizer (A : Set G)))
          h00 h10 h20 h01 h11 h21
      rw [coordMat_mul, e00, e01, e10, e11]
      exact hB
    · rw [coordMat_mul, chi_mul (shape_of_le hv hle h), hh2, h22, mul_one]

theorem conj_a_eq {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (r : Subgroup.normalizer (A : Set G)) (hr22 : coordMat f r 2 2 = 2) :
    ∃ b ∈ Subgroup.closure ({c, d} : Set G), (r : G) * a * (r : G)⁻¹ = a⁻¹ * b := by
  have hcol := Item116Fusion.conj_eq_coordMat f r 2
  rw [fa_eq hv] at hcol
  have e : (f (Multiplicative.ofAdd (fun i => coordMat f r i 2)) : G) =
      c ^ (coordMat f r 0 2).val * d ^ (coordMat f r 1 2).val * a ^ (coordMat f r 2 2).val :=
    hv _
  rw [hr22, show (2 : ZMod 3).val = 2 from rfl, pow_two a, a_sq_eq_inv hv] at e
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  refine ⟨a * (c ^ (coordMat f r 0 2).val * d ^ (coordMat f r 1 2).val) * a⁻¹, ?_, ?_⟩
  · exact hw_of_normalizer_le (a_mem_norm hv) hle _
      (Subgroup.mul_mem _ (Subgroup.pow_mem _ hcB _) (Subgroup.pow_mem _ hdB _))
  · rw [hcol, e]
    simp only [mul_assoc, inv_mul_cancel_left]

theorem sq_conj {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (r : Subgroup.normalizer (A : Set G))
    (hA : Anti (coordMat f r 0 0) (coordMat f r 0 1) (coordMat f r 1 0) (coordMat f r 1 1))
    (hsr : Shape (coordMat f r)) :
    (r : G) ^ 2 * c * ((r : G) ^ 2)⁻¹ ∈ Subgroup.zpowers d ∧
      (r : G) ^ 2 * d * ((r : G) ^ 2)⁻¹ ∈ Subgroup.zpowers c := by
  have hc2 : coordMat f (r ^ 2) = coordMat f r ^ 2 := coordMat_pow_eq r 2
  have hr2 : ((r ^ 2 : Subgroup.normalizer (A : Set G)) : G) = (r : G) ^ 2 := rfl
  have hs := sq_entries (coordMat f r) hsr.1 hsr.2
  rw [← hc2] at hs
  constructor
  · rw [← hr2]
    exact (mem_zpowers_d_of_c hv (r ^ 2)).mpr ⟨hs.1.trans hA.1, hs.2.1⟩
  · rw [← hr2]
    exact (mem_zpowers_c_of_d hv (r ^ 2)).mpr ⟨hs.2.2.1.trans hA.2, hs.2.2.2⟩

theorem forall_k {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (r : Subgroup.normalizer (A : Set G))
    (hA : Anti (coordMat f r 0 0) (coordMat f r 0 1) (coordMat f r 1 0) (coordMat f r 1 1))
    (hdet : coordMat f r 0 0 * coordMat f r 1 1 - coordMat f r 0 1 * coordMat f r 1 0 ≠ 0)
    (w' : G) (hw' : w' ∈ Subgroup.normalizer (A : Set G)) :
    ∃ k : ℕ, ((r : G) ^ k)⁻¹ * w' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  have hsr : Shape (coordMat f r) := shape_of_le hv hle r
  obtain ⟨k, x, hx0, hx1⟩ := F4_cover _ _ _ _ hdet hA
    (coordMat f (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G)) 0 0)
    (coordMat f (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G)) 1 0)
  have hblk : Item116Fusion.blk (coordMat f r) =
      !![coordMat f r 0 0, coordMat f r 0 1; coordMat f r 1 0, coordMat f r 1 1] := rfl
  rw [← hblk] at hx0 hx1
  have hBB := blk_inv_mul_one hv hle (r ^ (k : ℕ))
  rw [coordMat_pow_eq, blk_pow hsr] at hBB
  have hcol := col0_zero _ _ x _ _ hBB hx0 hx1
  have hM := shape_of_le hv hle (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G))
  have hN := shape_of_le hv hle (r ^ (k : ℕ))⁻¹
  have hg : (((r ^ (k : ℕ))⁻¹ * (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G)) :
      Subgroup.normalizer (A : Set G)) : G) = ((r : G) ^ (k : ℕ))⁻¹ * w' := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  have hN10 : coordMat f ((r ^ (k : ℕ))⁻¹ * (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G))) 1 0
      = 0 := by
    rw [coordMat_mul, mul_10_eq _ _ hM.1]
    exact hcol
  have hN20 : coordMat f ((r ^ (k : ℕ))⁻¹ * (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G))) 2 0
      = 0 := by
    rw [coordMat_mul]
    exact mul_20_eq_zero _ _ hN.1 hN.2 hM.1
  refine ⟨(k : ℕ), ?_⟩
  rw [← hg]
  apply Sec10.mem_normalizer_zpowers_of_conj_mem
  exact (mem_zpowers_c_conj hv ((r ^ (k : ℕ))⁻¹ * (⟨w', hw'⟩ : Subgroup.normalizer (A : Set G)))).mpr
    ⟨hN10, hN20⟩

theorem core_order_eight {f : Multiplicative (Fin 3 → ZMod 3) ≃* A}
    (hv : ∀ v : Fin 3 → ZMod 3, (f (Multiplicative.ofAdd v) : G) =
      c ^ (v 0).val * d ^ (v 1).val * a ^ (v 2).val)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure ({c, d} : Set G) : Subgroup G) : Set G))
    (hcj : ∀ w ∈ Subgroup.normalizer (A : Set G),
      w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
        ∀ x ∈ A, x⁻¹ * (w⁻¹ * x * w) ∈ Subgroup.closure ({c, d} : Set G))
    (hsd : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)))
    (hR2 : ∃ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹)) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers (c * d⁻¹) ∧ w * d * w⁻¹ ∈ Subgroup.zpowers (c * d)))
    (hχ : ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G))
    (m : G) (hmN : m ∈ Subgroup.normalizer (A : Set G))
    (hmc : m * c = c * m) (hmd : m * d * m⁻¹ = d⁻¹) :
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      (∃ b ∈ Subgroup.closure ({c, d} : Set G), w * a * w⁻¹ = a⁻¹ * b) ∧
      w ^ 2 * c * (w ^ 2)⁻¹ ∈ Subgroup.zpowers d ∧ w ^ 2 * d * (w ^ 2)⁻¹ ∈ Subgroup.zpowers c ∧
      ∀ w' ∈ Subgroup.normalizer (A : Set G),
        ∃ k : ℕ, (w ^ k)⁻¹ * w' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  obtain ⟨r, hA, hr22⟩ := exists_anti_chi2 hv hle hcj hsd hR2 hχ m hmN hmc hmd
  have hsr : Shape (coordMat f r) := shape_of_le hv hle r
  have hdet := det_ne_zero_of_blk (blk_mul_inv_one hv hle r)
  obtain ⟨hp2, hc2⟩ := sq_conj hv r hA hsr
  exact ⟨(r : G), r.2, conj_a_eq hv hle r hr22, hp2, hc2, forall_k hv hle r hA hdet⟩

end Final

end HuppertFin

section Certified

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d : G}

theorem exists_not_mem_of_residue (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hctx : A ∉ partTwoT G ∨ A ∈ partTwoS G) (hΩ : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1}) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G) := by
  by_contra hcon
  push Not at hcon
  exact false_of_fusion_trivial h45 (h.toSec11StdOfCtx hctx) h.inf_eq_zpowers h.isSylowOf_top hΩ
    hcon

theorem exists_order_eight_of_R2 (h : ResidueConfig G A c L a R Y d)
    (hctx : A ∉ partTwoT G ∨ A ∈ partTwoS G) (hR2 : ResidueR2 G A c d)
    (hχ : ∃ w ∈ Subgroup.normalizer (A : Set G), ∃ x ∈ A,
      x⁻¹ * (w⁻¹ * x * w) ∉ Subgroup.closure ({c, d} : Set G)) :
    ∃ w ∈ Subgroup.normalizer (A : Set G),
      (∃ b ∈ Subgroup.closure ({c, d} : Set G), w * a * w⁻¹ = a⁻¹ * b) ∧
      w ^ 2 * c * (w ^ 2)⁻¹ ∈ Subgroup.zpowers d ∧ w ^ 2 * d * (w ^ 2)⁻¹ ∈ Subgroup.zpowers c ∧
      ∀ w' ∈ Subgroup.normalizer (A : Set G),
        ∃ k : ℕ, (w ^ k)⁻¹ * w' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  obtain ⟨f, -, -, -, hv⟩ :=
    Item116Fusion.exists_coords_cda (h.toSec11StdOfCtx hctx) h.inf_eq_zpowers h.not_mem_zpowers
  obtain ⟨m, hmN, hmc, hmd, -⟩ := TheoremO.exists_inverting_fixing (h.toSec11StdOfCtx hctx)
    h.inf_eq_zpowers h.normalizer_le h.isIrreducibleOn h.not_mem_zpowers
  exact HuppertFin.core_order_eight hv h.normalizer_le h.conj_mem_of_mem_normalizer h.mem_sd16
    hR2 hχ m hmN (mul_inv_eq_iff_eq_mul.mp hmc) hmd

theorem exists_rotation_of_chi_neg (h : ResidueConfig G A c L a R Y d) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G))
    (hwa : ∃ b ∈ Subgroup.closure ({c, d} : Set G), w * a * w⁻¹ = a⁻¹ * b)
    (hc : w ^ 2 * c * (w ^ 2)⁻¹ ∈ Subgroup.zpowers d)
    (hd : w ^ 2 * d * (w ^ 2)⁻¹ ∈ Subgroup.zpowers c)
    (hcover : ∀ w' ∈ Subgroup.normalizer (A : Set G),
      ∃ k : ℕ, (w ^ k)⁻¹ * w' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    ∃ ζ : G, IsR2Rotation A c a d ζ := by
  obtain ⟨b0, hb0, hwa'⟩ := hwa
  obtain ⟨t, ht, htB, hta⟩ := h.exists_transvection b0 hb0
  have hcB : c ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hdB : d ∈ Subgroup.closure ({c, d} : Set G) := Subgroup.subset_closure (by simp)
  have hBw : ∀ y ∈ Subgroup.closure ({c, d} : Set G),
      w * y * w⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
    fun y hy => (Subgroup.mem_normalizer_iff.mp (h.normalizer_le hw) y).mp hy
  have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [h.inf_eq_zpowers]; exact Subgroup.mem_zpowers d).1
  have hBA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> rw [hx]
    · exact h.mem_A
    · exact hdA
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hab : a * b0 = b0 * a := hcomm a h.a_mem b0 (hBA hb0)
  have hza : (t * w) * a * (t * w)⁻¹ = a⁻¹ := by
    have e : (t * w) * a * (t * w)⁻¹ = t * (w * a * w⁻¹) * t⁻¹ := by group
    have e2 : t * (a⁻¹ * b0) * t⁻¹ = (t * a * t⁻¹)⁻¹ * (t * b0 * t⁻¹) := by group
    rw [e, hwa', e2, hta, htB b0 hb0, hab]
    group
  have hζB : ∀ y ∈ Subgroup.closure ({c, d} : Set G),
      (t * w) * y * (t * w)⁻¹ = w * y * w⁻¹ := by
    intro y hy
    have e : (t * w) * y * (t * w)⁻¹ = t * (w * y * w⁻¹) * t⁻¹ := by group
    rw [e, htB _ (hBw y hy)]
  have hP : ∀ k : ℕ, ∀ y ∈ Subgroup.closure ({c, d} : Set G),
      (t * w) ^ k * y * ((t * w) ^ k)⁻¹ = w ^ k * y * (w ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      have e1 : (t * w) ^ (k + 1) * y * ((t * w) ^ (k + 1))⁻¹ =
          (t * w) ^ k * ((t * w) * y * (t * w)⁻¹) * ((t * w) ^ k)⁻¹ := by
        rw [pow_succ]; group
      have e2 : w ^ (k + 1) * y * (w ^ (k + 1))⁻¹ =
          w ^ k * (w * y * w⁻¹) * (w ^ k)⁻¹ := by
        rw [pow_succ]; group
      rw [e1, e2, hζB y hy, ih _ (hBw y hy)]
  have hcover' : ∀ w' ∈ Subgroup.normalizer (A : Set G),
      ∃ k : ℕ, ((t * w) ^ k)⁻¹ * w' ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro w' hw'
    obtain ⟨k, hk⟩ := hcover w' hw'
    refine ⟨k, ?_⟩
    have hPk : (t * w) ^ k * c * ((t * w) ^ k)⁻¹ = w ^ k * c * (w ^ k)⁻¹ := hP k c hcB
    have hgc : ((t * w) ^ k)⁻¹ * w ^ k * c * (((t * w) ^ k)⁻¹ * w ^ k)⁻¹ = c := by
      have e : ((t * w) ^ k)⁻¹ * w ^ k * c * (((t * w) ^ k)⁻¹ * w ^ k)⁻¹ =
          ((t * w) ^ k)⁻¹ * (w ^ k * c * (w ^ k)⁻¹) * (t * w) ^ k := by group
      rw [e, ← hPk]; group
    have hcg : Commute c (((t * w) ^ k)⁻¹ * w ^ k) := (mul_inv_eq_iff_eq_mul.mp hgc).symm
    have hg : ((t * w) ^ k)⁻¹ * w ^ k ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro x hx
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (hcg.zpow_left n).eq
    have e : ((t * w) ^ k)⁻¹ * w' = ((t * w) ^ k)⁻¹ * w ^ k * ((w ^ k)⁻¹ * w') := by group
    rw [e]
    exact Subgroup.mul_mem _ hg hk
  refine ⟨t * w, ⟨Subgroup.mul_mem _ ht hw, hza, ?_, ?_, hcover'⟩⟩
  · rw [hP 2 c hcB]; exact hc
  · rw [hP 2 d hdB]; exact hd

theorem exists_rotation_R2 (h45 : Sec4.Item4_5) (h : ResidueConfig G A c L a R Y d)
    (hctx : A ∉ partTwoT G ∨ A ∈ partTwoS G) (hΩ : A = Subgroup.closure {y | y ∈ R ∧ y ^ 3 = 1})
    (hR2 : ResidueR2 G A c d) : ∃ ζ : G, IsR2Rotation A c a d ζ := by
  obtain ⟨w, hw, hwa, hc, hd, hcover⟩ :=
    exists_order_eight_of_R2 h hctx hR2 (exists_not_mem_of_residue h45 h hctx hΩ)
  exact exists_rotation_of_chi_neg h hw hwa hc hd hcover

end Certified

end CFSG.RankThree.PartTwo.Sec11
