module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
public import CFSG.CharacterTheory.Semidihedral.Local.ProperSubgroupFormsSupport

public section

namespace CFSG.Quasithin

open Subgroup

namespace F112J2

section Closure

variable {G : Type*} [Group G]

theorem quat_closure {x y z : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1)
    (hx : x ^ 2 = z) (hy : y ^ 2 = z) (hxy : x * y = z * (y * x)) :
    Nonempty (QuaternionGroup 2 ≃* ↥(closure ({x, y} : Set G))) := by
  set H := closure ({x, y} : Set G)
  have hxH : x ∈ H := subset_closure (by simp)
  have hyH : y ∈ H := subset_closure (by simp)
  have hzz : z * z = 1 := by rw [← sq, hz2]
  have hgen : closure ({⟨x, hxH⟩, ⟨y, hyH⟩} : Set H) = ⊤ := by
    convert Subgroup.closure_closure_coe_preimage (k := ({x, y} : Set G)) using 2
    ext g
    simp [Subtype.ext_iff]
  have hxo : orderOf (⟨x, hxH⟩ : H) = 2 * 2 := by
    rw [Subgroup.orderOf_mk]
    refine orderOf_eq_prime_pow (n := 1) (by rwa [pow_one, hx]) ?_
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hx, hz2]
  have hy' : (⟨y, hyH⟩ : H) ∉ zpowers ⟨x, hxH⟩ := by
    rintro ⟨n, hn⟩
    dsimp only at hn
    have hc : x * y = y * x := by
      have := ((Commute.refl (⟨x, hxH⟩ : H)).zpow_right n).eq
      rw [hn] at this
      exact congrArg Subtype.val this
    apply hz
    rw [hc] at hxy
    simpa using hxy.symm
  have hy2' : (⟨y, hyH⟩ : H) ^ 2 = ⟨x, hxH⟩ ^ 2 := Subtype.ext (by simp [hx, hy])
  have hyx : (⟨y, hyH⟩ : H) * ⟨x, hxH⟩ * (⟨y, hyH⟩ : H)⁻¹ = (⟨x, hxH⟩ : H)⁻¹ := by
    refine Subtype.ext ?_
    have hxinv : x⁻¹ = z * x := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [mul_assoc, ← sq, hx, hzz]
    have hyx' : y * x = z * (x * y) := by rw [hxy, ← mul_assoc, hzz, one_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyx', hxinv]
    group
  obtain ⟨⟨e, -, -⟩, -⟩ :=
    CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2) (by norm_num) hgen hxo
      hy' hy2' hyx
  exact ⟨e⟩

theorem dih_closure {u x : G} (hu : orderOf u = 4) (hx : x ∉ zpowers u) (hx2 : x ^ 2 = 1)
    (hxu : x * u * x⁻¹ = u⁻¹) :
    Nonempty (DihedralGroup 4 ≃* ↥(closure ({u, x} : Set G))) := by
  set H := closure ({u, x} : Set G)
  have huH : u ∈ H := subset_closure (by simp)
  have hxH : x ∈ H := subset_closure (by simp)
  have hgen : closure ({⟨u, huH⟩, ⟨x, hxH⟩} : Set H) = ⊤ := by
    convert Subgroup.closure_closure_coe_preimage (k := ({u, x} : Set G)) using 2
    ext g
    simp [Subtype.ext_iff]
  have hu' : orderOf (⟨u, huH⟩ : H) = 4 := by rw [Subgroup.orderOf_mk]; exact hu
  have hx' : (⟨x, hxH⟩ : H) ∉ zpowers ⟨u, huH⟩ := by
    rintro ⟨n, hn⟩
    apply hx
    refine ⟨n, ?_⟩
    exact congrArg Subtype.val hn
  have hx2' : (⟨x, hxH⟩ : H) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
  have hxu' : (⟨x, hxH⟩ : H) * ⟨u, huH⟩ * (⟨x, hxH⟩ : H)⁻¹ = (⟨u, huH⟩ : H)⁻¹ :=
    Subtype.ext (by simpa using hxu)
  obtain ⟨e, -, -⟩ := CFSG.Semidihedral.Local.dihedral_normal_form hgen hu' hx' hx2' hxu'
  exact ⟨e⟩

theorem card_eq_of_commuting {P : Type*} [Group P] (A B : Subgroup P)
    (hcomm : A ≤ Subgroup.centralizer (B : Set P)) (hsup : A ⊔ B = ⊤)
    (eA : QuaternionGroup 2 ≃* A) (eB : DihedralGroup 4 ≃* B) (z : P) (hzA : z ∈ A)
    (hzB : z ∈ B) (hz : z ≠ 1) (hz2 : z * z = 1) : Nat.card P = 32 := by
  classical
  have hA8 : Nat.card A = 8 := by
    rw [← Nat.card_congr eA.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hB8 : Nat.card B = 8 := by
    rw [← Nat.card_congr eB.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
  have hBn : B.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le (hcomm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hfinA : Finite A := Finite.of_equiv _ eA.toEquiv
  have hfinI : Finite ↥(B ⊓ A) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_right : B ⊓ A ≤ A))
      (Subgroup.inclusion_injective _)
  have hinf2 : Nat.card ↥(B ⊓ A) = 2 := by
    have hlow : 2 ≤ Nat.card ↥(B ⊓ A) := by
      have hle : Subgroup.zpowers z ≤ B ⊓ A := by
        rw [Subgroup.zpowers_le]
        exact ⟨hzB, hzA⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, orderOf_eq_prime (by rwa [← pow_two] at hz2) hz] at h1
      exact h1
    have hup : Nat.card ↥(B ⊓ A) ≤ 2 := by
      let f : ↥(B ⊓ A) → {q : QuaternionGroup 2 // ∀ r, q * r = r * q} := fun x =>
        ⟨eA.symm ⟨x.1, x.2.2⟩, fun r => by
          have hr : (eA r : P) ∈ A := (eA r).2
          have hcx : (eA r : P) * x.1 = x.1 * (eA r : P) := by
            have := Subgroup.mem_centralizer_iff.mp (hcomm hr) x.1 x.2.1
            exact this.symm
          apply eA.injective
          rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
          exact Subtype.ext hcx.symm⟩
      have hf : Function.Injective f := by
        intro x y hxy
        have h1 := eA.symm.injective (Subtype.ext_iff.mp hxy)
        have h2 : (x : P) = y := by
          have := congrArg Subtype.val h1
          simpa using this
        exact Subtype.ext h2
      have h1 := Nat.card_le_card_of_injective f hf
      have h2 : Nat.card {q : QuaternionGroup 2 // ∀ r, q * r = r * q} = 2 := by
        rw [Nat.card_eq_fintype_card]
        decide
      omega
    omega
  have := hBn
  have h1 : B.relIndex (A ⊔ B) = B.relIndex A := Subgroup.relIndex_sup_right A B
  rw [hsup, Subgroup.relIndex_top_right] at h1
  have h2 := Subgroup.relIndex_mul_card B A
  rw [hinf2, hA8] at h2
  have h3 := Subgroup.index_mul_card B
  rw [h1, hB8] at h3
  omega

end Closure

section Five

variable {P : Type*} [Group P] (z : P) (w : Fin 5 → P)

structure FiveRel : Prop where
  hz : z ≠ 1
  hz2 : z * z = 1
  hzc : ∀ g : P, g * z = z * g
  hw2 : ∀ i, w i * w i = 1
  hww : ∀ i j, i ≠ j → w i * w j = z * (w j * w i)

variable {z w}

namespace FiveRel

theorem sq (h : FiveRel z w) {i j : Fin 5} (hij : i ≠ j) : (w i * w j) * (w i * w j) = z := by
  calc (w i * w j) * (w i * w j) = w i * (w j * w i) * w j := by group
    _ = w i * (z * (w i * w j)) * w j := by rw [h.hww j i hij.symm]
    _ = (w i * z) * (w i * w j) * w j := by group
    _ = (z * w i) * (w i * w j) * w j := by rw [h.hzc (w i)]
    _ = z * (w i * w i) * (w j * w j) := by group
    _ = z := by rw [h.hw2, h.hw2]; group

theorem commute_pair (h : FiveRel z w) {i j k : Fin 5} (hij : i ≠ j) (hik : i ≠ k) :
    w i * (w j * w k) = (w j * w k) * w i := by
  calc w i * (w j * w k) = (w i * w j) * w k := by group
    _ = (z * (w j * w i)) * w k := by rw [h.hww i j hij]
    _ = z * w j * (w i * w k) := by group
    _ = z * w j * (z * (w k * w i)) := by rw [h.hww i k hik]
    _ = z * (w j * z) * (w k * w i) := by group
    _ = z * (z * w j) * (w k * w i) := by rw [h.hzc (w j)]
    _ = (z * z) * (w j * w k) * w i := by group
    _ = (w j * w k) * w i := by rw [h.hz2, one_mul]

theorem anti (h : FiveRel z w) :
    (w 2 * w 3) * (w 3 * w 4) = z * ((w 3 * w 4) * (w 2 * w 3)) := by
  have h1 : (w 2 * w 3) * (w 3 * w 4) = w 2 * w 4 := by
    calc (w 2 * w 3) * (w 3 * w 4) = w 2 * (w 3 * w 3) * w 4 := by group
      _ = w 2 * w 4 := by rw [h.hw2]; group
  have h2 : (w 3 * w 4) * (w 2 * w 3) = z * (w 2 * w 4) := by
    calc (w 3 * w 4) * (w 2 * w 3) = w 3 * (w 4 * w 2) * w 3 := by group
      _ = w 3 * (z * (w 2 * w 4)) * w 3 := by rw [h.hww 4 2 (by decide)]
      _ = (w 3 * z) * (w 2 * w 4) * w 3 := by group
      _ = (z * w 3) * (w 2 * w 4) * w 3 := by rw [h.hzc (w 3)]
      _ = z * (w 3 * (w 2 * w 4)) * w 3 := by group
      _ = z * ((w 2 * w 4) * w 3) * w 3 := by
          rw [h.commute_pair (i := 3) (j := 2) (k := 4) (by decide) (by decide)]
      _ = z * (w 2 * w 4) * (w 3 * w 3) := by group
      _ = z * (w 2 * w 4) := by rw [h.hw2]; group
  rw [h1, h2, ← mul_assoc, h.hz2, one_mul]

theorem inv_eq (h : FiveRel z w) (i : Fin 5) : (w i)⁻¹ = w i :=
  inv_eq_of_mul_eq_one_right (h.hw2 i)

theorem not_commute_01 (h : FiveRel z w) : ¬ Commute (w 0) (w 0 * w 1) := by
  intro hc
  apply h.hz
  have h1 : w 0 * (w 0 * w 1) = (w 0 * w 1) * w 0 := hc
  have h2 : w 1 = w 0 * w 1 * w 0 := by
    calc w 1 = (w 0 * w 0) * w 1 := by rw [h.hw2 0, one_mul]
      _ = w 0 * (w 0 * w 1) := by group
      _ = (w 0 * w 1) * w 0 := h1
  have h3 : w 0 * w 1 = w 1 * w 0 := by
    calc w 0 * w 1 = w 0 * (w 0 * w 1 * w 0) := by rw [← h2]
      _ = (w 0 * w 0) * w 1 * w 0 := by group
      _ = w 1 * w 0 := by rw [h.hw2 0, one_mul]
  have h4 := h.hww 0 1 (by decide)
  rw [h3] at h4
  calc z = z * (w 1 * w 0) * (w 1 * w 0)⁻¹ := by group
    _ = (w 1 * w 0) * (w 1 * w 0)⁻¹ := by rw [← h4]
    _ = 1 := mul_inv_cancel _

theorem mul_z_left (h : FiveRel z w) (a b : P) : a * (z * b) = z * (a * b) := by
  rw [← mul_assoc, h.hzc a, mul_assoc]

theorem commute_prod (h : FiveRel z w) (j : Fin 5) :
    w j * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 0 * w 1 * w 2 * w 3 * w 4) * w j := by
  fin_cases j
  · have cp12 : w 0 * (w 1 * w 2) = (w 1 * w 2) * w 0 :=
      h.commute_pair (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    have cp34 : w 0 * (w 3 * w 4) = (w 3 * w 4) * w 0 :=
      h.commute_pair (i := 0) (j := 3) (k := 4) (by decide) (by decide)
    have hQ : w 0 * ((w 1 * w 2) * (w 3 * w 4)) = ((w 1 * w 2) * (w 3 * w 4)) * w 0 := by
      calc w 0 * ((w 1 * w 2) * (w 3 * w 4)) = (w 0 * (w 1 * w 2)) * (w 3 * w 4) := by group
        _ = ((w 1 * w 2) * w 0) * (w 3 * w 4) := by rw [cp12]
        _ = (w 1 * w 2) * (w 0 * (w 3 * w 4)) := by group
        _ = (w 1 * w 2) * ((w 3 * w 4) * w 0) := by rw [cp34]
        _ = ((w 1 * w 2) * (w 3 * w 4)) * w 0 := by group
    show w 0 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 0 * w 1 * w 2 * w 3 * w 4) * w 0
    calc w 0 * (w 0 * w 1 * w 2 * w 3 * w 4) = w 0 * (w 0 * ((w 1 * w 2) * (w 3 * w 4))) := by
          group
      _ = w 0 * (((w 1 * w 2) * (w 3 * w 4)) * w 0) := by rw [hQ]
      _ = (w 0 * ((w 1 * w 2) * (w 3 * w 4))) * w 0 := by group
      _ = (w 0 * w 1 * w 2 * w 3 * w 4) * w 0 := by group
  · have cp123 : w 1 * (w 2 * w 3) = (w 2 * w 3) * w 1 :=
      h.commute_pair (i := 1) (j := 2) (k := 3) (by decide) (by decide)
    show w 1 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 0 * w 1 * w 2 * w 3 * w 4) * w 1
    have hA : w 1 * (w 0 * w 1 * w 2 * w 3 * w 4) = z * (w 0 * (w 2 * w 3) * w 4) := by
      calc w 1 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 1 * w 0) * w 1 * (w 2 * w 3) * w 4 := by group
        _ = (z * (w 0 * w 1)) * w 1 * (w 2 * w 3) * w 4 := by rw [h.hww 1 0 (by decide)]
        _ = z * (w 0 * (w 1 * w 1) * (w 2 * w 3) * w 4) := by group
        _ = z * (w 0 * (w 2 * w 3) * w 4) := by rw [h.hw2 1, mul_one]
    have hB : (w 0 * w 1 * w 2 * w 3 * w 4) * w 1 = z * (w 0 * (w 2 * w 3) * w 4) := by
      calc (w 0 * w 1 * w 2 * w 3 * w 4) * w 1
          = w 0 * w 1 * (w 2 * w 3) * (w 4 * w 1) := by group
        _ = w 0 * w 1 * (w 2 * w 3) * (z * (w 1 * w 4)) := by rw [h.hww 4 1 (by decide)]
        _ = z * (w 0 * w 1 * (w 2 * w 3) * (w 1 * w 4)) := h.mul_z_left _ _
        _ = z * (w 0 * (w 1 * (w 2 * w 3)) * (w 1 * w 4)) := by group
        _ = z * (w 0 * ((w 2 * w 3) * w 1) * (w 1 * w 4)) := by rw [cp123]
        _ = z * (w 0 * (w 2 * w 3) * (w 1 * w 1) * w 4) := by group
        _ = z * (w 0 * (w 2 * w 3) * w 4) := by rw [h.hw2 1, mul_one]
    rw [hA, hB]
  · have cp01 : w 2 * (w 0 * w 1) = (w 0 * w 1) * w 2 :=
      h.commute_pair (i := 2) (j := 0) (k := 1) (by decide) (by decide)
    have cp34 : w 2 * (w 3 * w 4) = (w 3 * w 4) * w 2 :=
      h.commute_pair (i := 2) (j := 3) (k := 4) (by decide) (by decide)
    show w 2 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 0 * w 1 * w 2 * w 3 * w 4) * w 2
    calc w 2 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 2 * (w 0 * w 1)) * w 2 * (w 3 * w 4) := by group
      _ = ((w 0 * w 1) * w 2) * w 2 * (w 3 * w 4) := by rw [cp01]
      _ = (w 0 * w 1) * w 2 * (w 2 * (w 3 * w 4)) := by group
      _ = (w 0 * w 1) * w 2 * ((w 3 * w 4) * w 2) := by rw [cp34]
      _ = (w 0 * w 1 * w 2 * w 3 * w 4) * w 2 := by group
  · have cp01 : w 3 * (w 0 * w 1) = (w 0 * w 1) * w 3 :=
      h.commute_pair (i := 3) (j := 0) (k := 1) (by decide) (by decide)
    show w 3 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 0 * w 1 * w 2 * w 3 * w 4) * w 3
    have hA : w 3 * (w 0 * w 1 * w 2 * w 3 * w 4) = z * (w 0 * w 1 * w 2 * w 4) := by
      calc w 3 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 3 * (w 0 * w 1)) * w 2 * w 3 * w 4 := by group
        _ = ((w 0 * w 1) * w 3) * w 2 * w 3 * w 4 := by rw [cp01]
        _ = (w 0 * w 1) * (w 3 * w 2) * w 3 * w 4 := by group
        _ = (w 0 * w 1) * (z * (w 2 * w 3)) * w 3 * w 4 := by rw [h.hww 3 2 (by decide)]
        _ = z * ((w 0 * w 1) * (w 2 * w 3)) * w 3 * w 4 := by rw [h.mul_z_left]
        _ = z * (w 0 * w 1 * w 2 * (w 3 * w 3) * w 4) := by group
        _ = z * (w 0 * w 1 * w 2 * w 4) := by rw [h.hw2 3, mul_one]
    have hB : (w 0 * w 1 * w 2 * w 3 * w 4) * w 3 = z * (w 0 * w 1 * w 2 * w 4) := by
      calc (w 0 * w 1 * w 2 * w 3 * w 4) * w 3 = w 0 * w 1 * w 2 * w 3 * (w 4 * w 3) := by group
        _ = w 0 * w 1 * w 2 * w 3 * (z * (w 3 * w 4)) := by rw [h.hww 4 3 (by decide)]
        _ = z * (w 0 * w 1 * w 2 * w 3 * (w 3 * w 4)) := h.mul_z_left _ _
        _ = z * (w 0 * w 1 * w 2 * (w 3 * w 3) * w 4) := by group
        _ = z * (w 0 * w 1 * w 2 * w 4) := by rw [h.hw2 3, mul_one]
    rw [hA, hB]
  · have cp01 : w 4 * (w 0 * w 1) = (w 0 * w 1) * w 4 :=
      h.commute_pair (i := 4) (j := 0) (k := 1) (by decide) (by decide)
    have cp23 : w 4 * (w 2 * w 3) = (w 2 * w 3) * w 4 :=
      h.commute_pair (i := 4) (j := 2) (k := 3) (by decide) (by decide)
    show w 4 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 0 * w 1 * w 2 * w 3 * w 4) * w 4
    calc w 4 * (w 0 * w 1 * w 2 * w 3 * w 4) = (w 4 * (w 0 * w 1)) * (w 2 * w 3) * w 4 := by group
      _ = ((w 0 * w 1) * w 4) * (w 2 * w 3) * w 4 := by rw [cp01]
      _ = (w 0 * w 1) * (w 4 * (w 2 * w 3)) * w 4 := by group
      _ = (w 0 * w 1) * ((w 2 * w 3) * w 4) * w 4 := by rw [cp23]
      _ = (w 0 * w 1 * w 2 * w 3 * w 4) * w 4 := by group

theorem isQ8D8 (h : FiveRel z w) (hy : w 0 * w 1 * w 2 * w 3 * w 4 ∈ zpowers z)
    (hgen : closure (insert z (Set.range w)) = ⊤) : CFSG.Quasithin.IsQ8D8 P := by
  classical
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact h.hz2
  set A : Subgroup P := closure ({w 2 * w 3, w 3 * w 4} : Set P) with hA
  set B : Subgroup P := closure ({w 0 * w 1, w 0} : Set P) with hB
  obtain ⟨eA⟩ : Nonempty (QuaternionGroup 2 ≃* A) :=
    quat_closure h.hz hz2' (by rw [pow_two]; exact h.sq (i := 2) (j := 3) (by decide))
      (by rw [pow_two]; exact h.sq (i := 3) (j := 4) (by decide)) h.anti
  have hu4 : orderOf (w 0 * w 1) = 4 := by
    have hs : (w 0 * w 1) ^ 2 = z := by rw [pow_two]; exact h.sq (i := 0) (j := 1) (by decide)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := orderOf_eq_prime_pow (x := w 0 * w 1) (p := 2) (n := 1)
      (by simpa [hs] using h.hz) (by
        rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hs, hz2'])
    simpa using this
  obtain ⟨eB⟩ : Nonempty (DihedralGroup 4 ≃* B) :=
    dih_closure hu4 (by
      intro hmem
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply h.not_commute_01
      have h1 : Commute ((w 0 * w 1) ^ n) (w 0 * w 1) := (Commute.refl (w 0 * w 1)).zpow_left n
      rw [hn] at h1
      exact h1) (by rw [pow_two]; exact h.hw2 0) (by
      rw [h.inv_eq 0, mul_inv_rev, h.inv_eq 0, h.inv_eq 1]
      calc w 0 * (w 0 * w 1) * w 0 = (w 0 * w 0) * w 1 * w 0 := by group
        _ = w 1 * w 0 := by rw [h.hw2 0, one_mul])
  have ha : w 2 * w 3 ∈ A := subset_closure (by simp)
  have hb : w 3 * w 4 ∈ A := subset_closure (by simp)
  have hu : w 0 * w 1 ∈ B := subset_closure (by simp)
  have hx0 : w 0 ∈ B := subset_closure (by simp)
  have hzA : z ∈ A := by
    have := A.mul_mem ha ha
    rwa [h.sq (i := 2) (j := 3) (by decide)] at this
  have hzB : z ∈ B := by
    have := B.mul_mem hu hu
    rwa [h.sq (i := 0) (j := 1) (by decide)] at this
  have hw1 : w 1 ∈ B := by
    have : w 1 = w 0 * (w 0 * w 1) := by
      calc w 1 = (w 0 * w 0) * w 1 := by rw [h.hw2 0, one_mul]
        _ = w 0 * (w 0 * w 1) := by group
    rw [this]
    exact B.mul_mem hx0 hu
  have hcomm : A ≤ Subgroup.centralizer (B : Set P) := by
    rw [hB, Subgroup.centralizer_closure]
    rw [hA, Subgroup.closure_le]
    have c0a : Commute (w 0) (w 2 * w 3) :=
      h.commute_pair (i := 0) (j := 2) (k := 3) (by decide) (by decide)
    have c0b : Commute (w 0) (w 3 * w 4) :=
      h.commute_pair (i := 0) (j := 3) (k := 4) (by decide) (by decide)
    have c1a : Commute (w 1) (w 2 * w 3) :=
      h.commute_pair (i := 1) (j := 2) (k := 3) (by decide) (by decide)
    have c1b : Commute (w 1) (w 3 * w 4) :=
      h.commute_pair (i := 1) (j := 3) (k := 4) (by decide) (by decide)
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hk with rfl | rfl
    · rcases hg with rfl | rfl
      · exact (c0a.mul_left c1a).symm.eq.symm
      · exact (c0b.mul_left c1b).symm.eq.symm
    · rcases hg with rfl | rfl
      · exact c0a.symm.eq.symm
      · exact c0b.symm.eq.symm
  have hsup : A ⊔ B = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    have hAB : ∀ g, g ∈ A → g ∈ A ⊔ B := fun g hg => Subgroup.mem_sup_left hg
    have hBA : ∀ g, g ∈ B → g ∈ A ⊔ B := fun g hg => Subgroup.mem_sup_right hg
    have hyA : w 0 * w 1 * w 2 * w 3 * w 4 ∈ A := (Subgroup.zpowers_le.mpr hzA) hy
    have hc : w 2 * w 3 * w 4 ∈ A ⊔ B := by
      have e : w 2 * w 3 * w 4 = (w 1 * w 0) * (w 0 * w 1 * w 2 * w 3 * w 4) := by
        calc w 2 * w 3 * w 4 = (w 1 * w 1) * (w 2 * w 3 * w 4) := by rw [h.hw2 1, one_mul]
          _ = w 1 * (w 0 * w 0) * (w 1 * (w 2 * w 3 * w 4)) := by rw [h.hw2 0, mul_one]; group
          _ = (w 1 * w 0) * (w 0 * w 1 * w 2 * w 3 * w 4) := by group
      rw [e]
      exact Subgroup.mul_mem _ (hBA _ (B.mul_mem hw1 hx0)) (hAB _ hyA)
    have hw2' : w 2 ∈ A ⊔ B := by
      have e : w 2 = (w 2 * w 3 * w 4) * (w 4 * w 3) := by
        calc w 2 = w 2 * (w 3 * (w 4 * w 4) * w 3) := by
              rw [h.hw2 4, mul_one, h.hw2 3, mul_one]
          _ = (w 2 * w 3 * w 4) * (w 4 * w 3) := by group
      rw [e]
      refine Subgroup.mul_mem _ hc (hAB _ ?_)
      have := A.inv_mem hb
      rwa [mul_inv_rev, h.inv_eq 3, h.inv_eq 4] at this
    have hw3 : w 3 ∈ A ⊔ B := by
      have e : w 3 = w 2 * (w 2 * w 3) := by
        calc w 3 = (w 2 * w 2) * w 3 := by rw [h.hw2 2, one_mul]
          _ = w 2 * (w 2 * w 3) := by group
      rw [e]
      exact Subgroup.mul_mem _ hw2' (hAB _ ha)
    have hw4 : w 4 ∈ A ⊔ B := by
      have e : w 4 = w 3 * (w 3 * w 4) := by
        calc w 4 = (w 3 * w 3) * w 4 := by rw [h.hw2 3, one_mul]
          _ = w 3 * (w 3 * w 4) := by group
      rw [e]
      exact Subgroup.mul_mem _ hw3 (hAB _ hb)
    rintro g (rfl | ⟨i, rfl⟩)
    · exact hAB _ hzA
    · fin_cases i
      · exact hBA _ hx0
      · exact hBA _ hw1
      · exact hw2'
      · exact hw3
      · exact hw4
  exact ⟨card_eq_of_commuting A B hcomm hsup eA eB z hzA hzB h.hz h.hz2, A, B, ⟨hcomm, hsup⟩,
    ⟨eA.symm⟩, ⟨eB.symm⟩⟩

end FiveRel

end Five

end F112J2

end CFSG.Quasithin
