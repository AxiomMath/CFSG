module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Geom
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.RankThree.PartTwo.Sec21.FF81Sec42B
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import Mathlib.GroupTheory.Perm.Centralizer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)

section Coord

variable {G : Type} [Group G] [Finite G] {B : Subgroup G} {b₀ b₁ b₂ b₃ : G}

theorem ε4_neg (hE : IsElemAb 3 4 B) (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) (v : V) :
    S36.ε4 b₀ b₁ b₂ b₃ (-v) = (S36.ε4 b₀ b₁ b₂ b₃ v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← S36.ε4_add hE hcl, neg_add_cancel, S36.ε4_zero]

theorem ε4_conj (hE : IsElemAb 3 4 B) (hcl : B = Subgroup.closure {b₀, b₁, b₂, b₃}) {n : G}
    (c : Fin 4 → V) (h0 : n * b₀ * n⁻¹ = S36.ε4 b₀ b₁ b₂ b₃ (c 0))
    (h1 : n * b₁ * n⁻¹ = S36.ε4 b₀ b₁ b₂ b₃ (c 1)) (h2 : n * b₂ * n⁻¹ = S36.ε4 b₀ b₁ b₂ b₃ (c 2))
    (h3 : n * b₃ * n⁻¹ = S36.ε4 b₀ b₁ b₂ b₃ (c 3)) (v : V) :
    n * S36.ε4 b₀ b₁ b₂ b₃ v * n⁻¹ =
      S36.ε4 b₀ b₁ b₂ b₃ (v 0 • c 0 + v 1 • c 1 + v 2 • c 2 + v 3 • c 3) := by
  have h := fun x y : G => map_mul (MulAut.conj n) x y
  simp only [MulAut.conj_apply] at h
  rw [S36.ε4, h, h, h]
  simp only [← conj_pow, h0, h1, h2, h3]
  rw [S36.ε4_add hE hcl, S36.ε4_add hE hcl, S36.ε4_add hE hcl, S36.ε4_smul hE hcl,
    S36.ε4_smul hE hcl, S36.ε4_smul hE hcl, S36.ε4_smul hE hcl]

end Coord

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Basic

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.hcl : B = Subgroup.closure {b, b₁, b₂, b₃} := h5.basis.mono.2.1

theorem FF81Sec5.hE : IsElemAb 3 4 B := h5.basis.mono.1

abbrev FF81Sec5.ε (_h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (v : V) : G := S36.ε4 b b₁ b₂ b₃ v

theorem FF81Sec5.ε_mem (v : V) : h5.ε v ∈ B := S36.ε4_mem h5.hcl v

theorem FF81Sec5.ε_add (v w : V) : h5.ε (v + w) = h5.ε v * h5.ε w := S36.ε4_add h5.hE h5.hcl v w

theorem FF81Sec5.ε_neg (v : V) : h5.ε (-v) = (h5.ε v)⁻¹ := ε4_neg h5.hE h5.hcl v

theorem FF81Sec5.ε_smul (c : ZMod 3) (v : V) : h5.ε (c • v) = h5.ε v ^ c.val :=
  S36.ε4_smul h5.hE h5.hcl c v

theorem FF81Sec5.ε_inj {v w : V} (h : h5.ε v = h5.ε w) : v = w := S36.ε4_inj h5.hE h5.hcl h

theorem FF81Sec5.ε_surj {x : G} (hx : x ∈ B) : ∃ v, h5.ε v = x := S36.ε4_surj h5.hE h5.hcl hx

theorem FF81Sec5.ε_zero : h5.ε 0 = 1 := S36.ε4_zero

theorem FF81Sec5.ε_eq_one {v : V} (h : h5.ε v = 1) : v = 0 := h5.ε_inj (h.trans h5.ε_zero.symm)

theorem FF81Sec5.ε_e0 : h5.ε (e 0) = b := by
  simp [FF81Sec5.ε, S36.ε4, e, Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem FF81Sec5.ε_e1 : h5.ε (e 1) = b₁ := by
  simp [FF81Sec5.ε, S36.ε4, e, Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem FF81Sec5.ε_e2 : h5.ε (e 2) = b₂ := by
  simp [FF81Sec5.ε, S36.ε4, e, Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem FF81Sec5.ε_e3 : h5.ε (e 3) = b₃ := by
  simp [FF81Sec5.ε, S36.ε4, e, Pi.single_apply, show (1 : ZMod 3).val = 1 from rfl]

theorem FF81Sec5.ε_lit (a₀ a₁ a₂ a₃ : ZMod 3) :
    h5.ε ![a₀, a₁, a₂, a₃] = b ^ a₀.val * b₁ ^ a₁.val * b₂ ^ a₂.val * b₃ ^ a₃.val := rfl

theorem FF81Sec5.ε_β : h5.ε ![0, 0, 1, 2] = β' b₂ b₃ := by
  rw [FF81Sec5.ε_lit]
  simp only [ZMod.val_zero, pow_zero, one_mul, β', show (1 : ZMod 3).val = 1 from rfl,
    show (2 : ZMod 3).val = 2 from rfl, pow_one]

theorem FF81Sec5.ε_u₃ : h5.ε ![0, 0, 1, 1] = b₂ * b₃ := by
  rw [FF81Sec5.ε_lit]
  simp only [ZMod.val_zero, pow_zero, one_mul, show (1 : ZMod 3).val = 1 from rfl, pow_one]

theorem FF81Sec5.mem_A₁_of {v : V} (hv : v 2 = v 3) :
    h5.ε v ∈ Subgroup.closure {b, b₁, b₂ * b₃} := by
  have hv' : v = v 0 • e 0 + v 1 • e 1 + v 2 • ![0, 0, 1, 1] := by
    ext j; fin_cases j <;> simp [e, Pi.single_apply, hv]
  rw [hv', h5.ε_add, h5.ε_add, h5.ε_smul, h5.ε_smul, h5.ε_smul, h5.ε_e0, h5.ε_e1, h5.ε_u₃]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ ?_ _)
    (Subgroup.pow_mem _ ?_ _)) (Subgroup.pow_mem _ ?_ _) <;>
    exact Subgroup.subset_closure (by simp)

theorem FF81Sec5.coord_of_mem_A₁ {x : G} (hx : x ∈ Subgroup.closure {b, b₁, b₂ * b₃}) :
    ∃ v : V, v 2 = v 3 ∧ h5.ε v = x := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨e 0, by simp [e, Pi.single_apply], h5.ε_e0⟩
    · exact ⟨e 1, by simp [e, Pi.single_apply], h5.ε_e1⟩
    · exact ⟨![0, 0, 1, 1], rfl, h5.ε_u₃⟩
  | one => exact ⟨0, rfl, h5.ε_zero⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, hv, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨v + w, by simp [hv, hw], h5.ε_add v w⟩
  | inv x _ hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨-v, by simp [hv], h5.ε_neg v⟩

theorem FF81Sec5.A₁_le_B' : Subgroup.closure {b, b₁, b₂ * b₃} ≤ B := h5.A₁_le_B

theorem FF81Sec5.β_mem : β' b₂ b₃ ∈ B := h5.ε_β ▸ h5.ε_mem _

theorem FF81Sec5.β_ne_one : β' b₂ b₃ ≠ 1 := fun h => by
  have := h5.ε_eq_one (h5.ε_β.trans h)
  exact absurd (congrFun this 2) (by decide)

theorem FF81Sec5.β_cube : β' b₂ b₃ ^ 3 = 1 := h5.basis.B_cube h5.β_mem

theorem FF81Sec5.β_orderOf : orderOf (β' b₂ b₃) = 3 :=
  orderOf_eq_prime h5.β_cube h5.β_ne_one

theorem FF81Sec5.s₀_comm {a : G} (ha : a ∈ Subgroup.closure {b, b₁, b₂ * b₃}) :
    a * s₀ = s₀ * a :=
  Subgroup.mem_centralizer_iff.mp h5.hs₀A a ha

theorem FF81Sec5.s₀_sq : s₀ * s₀ = 1 := by rw [← sq, ← h5.hs₀, pow_orderOf_eq_one]

theorem FF81Sec5.s₀_inv : s₀⁻¹ = s₀ := inv_eq_of_mul_eq_one_right h5.s₀_sq

theorem FF81Sec5.s₀_ne_one : s₀ ≠ 1 := fun h => by
  have := h5.hs₀; rw [h, orderOf_one] at this; exact absurd this (by decide)

theorem FF81Sec5.s₀_not_mem_B : s₀ ∉ B := fun h => by
  have h3 := h5.basis.B_cube h
  have : s₀ = 1 := by
    calc s₀ = s₀ ^ 3 * (s₀ * s₀)⁻¹ := by group
      _ = 1 := by rw [h3, h5.s₀_sq, inv_one, one_mul]
  exact h5.s₀_ne_one this

theorem FF81Sec5.s₀_b₂_b₃ : s₀ * b₂ * s₀⁻¹ = b₃ ∧ s₀ * b₃ * s₀⁻¹ = b₂ := by
  have hu : s₀ * (b₂ * b₃) * s₀⁻¹ = b₂ * b₃ := by
    rw [← h5.s₀_comm (Subgroup.subset_closure (by simp)), mul_inv_cancel_right]
  have hv : s₀ * (b₂ * b₃ ^ 2) * s₀⁻¹ = (b₂ * b₃ ^ 2)⁻¹ := h5.hs₀b
  have hY : s₀ * b₃ * s₀⁻¹ = (b₂ * b₃)⁻¹ * (b₂ * b₃ ^ 2)⁻¹ := by
    rw [← hu, ← hv]; group
  have hc : b₂ * b₃ = b₃ * b₂ := h5.basis.B_comm (h5.basis.mem_B (by simp))
    (h5.basis.mem_B (by simp))
  have h2 := h5.basis.B_cube (h5.basis.mem_B (x := b₂) (by simp))
  have h3 := h5.basis.B_cube (h5.basis.mem_B (x := b₃) (by simp))
  have hY' : s₀ * b₃ * s₀⁻¹ = b₂ := by
    have e1 : (b₂ * b₃) * (b₂ * b₃ ^ 2) = b₂ ^ 2 := by
      rw [show (b₂ * b₃) * (b₂ * b₃ ^ 2) = b₂ * (b₃ * b₂) * b₃ ^ 2 by group, ← hc,
        show b₂ * (b₂ * b₃) * b₃ ^ 2 = b₂ ^ 2 * b₃ ^ 3 by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc], h3, mul_one]
    have hcm : (b₂ * b₃ ^ 2) * (b₂ * b₃) = (b₂ * b₃) * (b₂ * b₃ ^ 2) :=
      h5.basis.B_comm h5.β_mem (B.mul_mem (h5.basis.mem_B (by simp)) (h5.basis.mem_B (by simp)))
    rw [hY, ← mul_inv_rev, hcm, e1]
    exact inv_eq_of_mul_eq_one_left (by rw [← pow_succ', h2])
  refine ⟨?_, hY'⟩
  calc s₀ * b₂ * s₀⁻¹ = s₀ * (b₂ * b₃) * s₀⁻¹ * (s₀ * b₃ * s₀⁻¹)⁻¹ := by group
    _ = b₂ * b₃ * b₂⁻¹ := by rw [hu, hY']
    _ = b₃ := by rw [hc]; group

theorem FF81Sec5.s₀_ε (v : V) : s₀ * h5.ε v * s₀⁻¹ = h5.ε ![v 0, v 1, v 3, v 2] := by
  obtain ⟨h2, h3⟩ := h5.s₀_b₂_b₃
  have hb : s₀ * b * s₀⁻¹ = h5.ε (e 0) := by
    rw [← h5.s₀_comm (Subgroup.subset_closure (by simp)), mul_inv_cancel_right, h5.ε_e0]
  have hb₁ : s₀ * b₁ * s₀⁻¹ = h5.ε (e 1) := by
    rw [← h5.s₀_comm (Subgroup.subset_closure (by simp)), mul_inv_cancel_right, h5.ε_e1]
  rw [ε4_conj h5.hE h5.hcl ![e 0, e 1, e 3, e 2] hb hb₁ (h2.trans h5.ε_e3.symm)
    (h3.trans h5.ε_e2.symm)]
  congr 1
  ext j; fin_cases j <;> simp [e, Pi.single_apply]

theorem FF81Sec5.s₀_mem_nor_B : s₀ ∈ Nor B := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨v, rfl⟩ := h5.ε_surj hx
  rw [h5.s₀_ε]; exact h5.ε_mem _

theorem FF81Sec5.mem_zpowers_β {z : G} (hz : z ∈ B) (hs : s₀ * z * s₀⁻¹ = z⁻¹) :
    ∃ k : ℕ, z = β' b₂ b₃ ^ k := by
  obtain ⟨v, rfl⟩ := h5.ε_surj hz
  rw [h5.s₀_ε, ← h5.ε_neg] at hs
  have hv := h5.ε_inj hs
  have key : ∀ v : V, ![v 0, v 1, v 3, v 2] = -v → v = v 2 • ![0, 0, 1, 2] := by decide
  refine ⟨(v 2).val, ?_⟩
  rw [key v hv, h5.ε_smul, h5.ε_β]
  simp

theorem FF81Sec5.B_le_cenS_A₁ : B ≤ CenS (Subgroup.closure {b, b₁, b₂ * b₃}) :=
  fun _ hz => Subgroup.mem_centralizer_iff.mpr fun _ ha =>
    h5.basis.B_comm (h5.A₁_le_B ha) hz

theorem FF81Sec5.β_comm_A₁ {a : G} (ha : a ∈ Subgroup.closure {b, b₁, b₂ * b₃}) :
    a * β' b₂ b₃ = β' b₂ b₃ * a :=
  h5.basis.B_comm (h5.A₁_le_B ha) h5.β_mem

end Basic

theorem FF81Sec5.cenS_A₁ (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {y : G}
    (hy : y ∈ CenS (Subgroup.closure {b, b₁, b₂ * b₃})) : ∃ z ∈ B, y = z ∨ y = z * s₀ := by
  have hB := h5.basis
  have h0 := h5.opp_eq_bot
  have hset : ({b₂, b₁, b₃} : Set G) = {b₁, b₂, b₃} := Set.insert_comm _ _ _
  obtain ⟨⟨J', hJ'L, ⟨φ'⟩, hb₂J, hb₃J, hdecJ⟩, -⟩ := hKF G L hB.hyp.model b₂ b₁ b₃ hB.hb₂ hB.hb₁
    hB.hb₃ (by rw [hset]; exact hB.elem) (by rw [hset]; exact hB.selfcen) (by
      intro n hn hnN x hx
      rw [hset] at hnN
      have hx' : x ∈ ({b₁, b₂, b₃} : Set G) := hset ▸ hx
      have := hB.monoL_stab n hn hnN x hx'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this ⊢
      tauto)
  have hA : ∀ a ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G), a * y = y * a :=
    fun a ha => Subgroup.mem_centralizer_iff.mp hy a ha
  have hmemA : ∀ x ∈ ({b, b₁, b₂ * b₃} : Set G), x ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) :=
    fun x hx => Subgroup.subset_closure hx
  have hbB : b ∈ B := hB.mem_B (by simp)
  have hb₁B : b₁ ∈ B := hB.mem_B (by simp)
  have hu₃B : b₂ * b₃ ∈ B := B.mul_mem (hB.mem_B (by simp)) (hB.mem_B (by simp))
  have hyb : y ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr (hA b (hmemA b (by simp))).symm
  obtain ⟨i, l, hl, rfl⟩ := hB.cen_dec' h0 hyb
  have hcomm_l : ∀ x ∈ ({b₁, b₂ * b₃} : Set G), l * x = x * l := by
    intro x hx
    have hxA : x ∈ Subgroup.closure ({b, b₁, b₂ * b₃} : Set G) := hmemA x (by
      rcases hx with rfl | rfl <;> simp)
    have hxB : x ∈ B := h5.A₁_le_B hxA
    have h1 : Commute (b ^ i) x := Commute.zpow_left (hB.B_comm hbB hxB) i
    have h2 : Commute (b ^ i * l) x := (hA x hxA).symm
    have hl' : l = (b ^ i)⁻¹ * (b ^ i * l) := by group
    rw [hl']
    exact ((h1.inv_left).mul_left h2).eq
  obtain ⟨k, j, hj, rfl⟩ := hdecJ l ⟨hl, Subgroup.mem_centralizer_singleton_iff.mpr
    (hcomm_l b₁ (by simp))⟩
  have hjc : j * (b₂ * b₃) = (b₂ * b₃) * j := by
    have h1 : Commute (b₁ ^ k) (b₂ * b₃) := Commute.pow_left (hB.B_comm hb₁B hu₃B) k
    have h2 : Commute (b₁ ^ k * j) (b₂ * b₃) := hcomm_l _ (by simp)
    have hj' : j = (b₁ ^ k)⁻¹ * (b₁ ^ k * j) := by group
    rw [hj']
    exact ((h1.inv_left).mul_left h2).eq
  set C₀ := J' ⊓ Cen (b₂ * b₃) with hC₀
  have hu₃J : b₂ * b₃ ∈ J' := J'.mul_mem hb₂J hb₃J
  set x' : J' := ⟨b₂ * b₃, hu₃J⟩
  have hx'3 : orderOf (φ' x') = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hB.B_cube hu₃B) (by
      intro h
      have := h5.ε_eq_one (h5.ε_u₃.trans h)
      exact absurd (congrFun this 2) (by decide))
  have hC₀card : Nat.card C₀ = 18 := by
    have hS6 : ∀ x : Equiv.Perm (Fin 6), orderOf x = 3 →
        Nat.card (Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 6)))) = 18 := by
      intro x hx
      obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hx ▸ Nat.prime_three)
      rw [hx] at hn
      have hsum := Equiv.Perm.sum_cycleType_le x
      rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
      have : n = 0 ∨ n = 1 := by omega
      rw [Equiv.Perm.nat_card_centralizer, hn, Fintype.card_fin]
      rcases this with rfl | rfl
      · simp [Nat.factorial]
      · simp [Multiset.toFinset_replicate]
    rw [← hS6 _ hx'3]
    exact Nat.card_congr
      { toFun := fun g => ⟨φ' ⟨g, g.2.1⟩, by
          rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
          congr 1
          exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2.2)⟩
        invFun := fun g => ⟨(φ'.symm g : G), (φ'.symm g).2,
          Subgroup.mem_centralizer_singleton_iff.mpr (by
            have h1 := Subgroup.mem_centralizer_singleton_iff.mp g.2
            have h2 : φ'.symm g * x' = x' * φ'.symm g := φ'.injective (by
              rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact h1)
            exact congrArg Subtype.val h2)⟩
        left_inv := fun g => by ext; simp
        right_inv := fun g => by ext; simp }
  have hb₂B : b₂ ∈ B := hB.mem_B (by simp)
  have hb₃B : b₃ ∈ B := hB.mem_B (by simp)
  set P' := Subgroup.closure ({b₂, b₃} : Set G) with hP'
  have hP'B : P' ≤ B := (Subgroup.closure_le _).mpr (by rintro x (rfl | rfl) <;> assumption)
  have hP'C : P' ≤ C₀ := (Subgroup.closure_le _).mpr (by
    rintro x (rfl | rfl)
    · exact ⟨hb₂J, Subgroup.mem_centralizer_singleton_iff.mpr (hB.B_comm hb₂B hu₃B)⟩
    · exact ⟨hb₃J, Subgroup.mem_centralizer_singleton_iff.mpr (hB.B_comm hb₃B hu₃B)⟩)
  have hidx : (P'.subgroupOf C₀).index = 2 := by
    have h1 := (P'.subgroupOf C₀).index_mul_card
    rw [hC₀card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP'C).toEquiv, hB.card_E] at h1
    omega
  have hs₀b₁ : s₀ ∈ L ⊓ Cen b₁ := ⟨h5.hs₀L, Subgroup.mem_centralizer_singleton_iff.mpr
    (h5.s₀_comm (hmemA b₁ (by simp))).symm⟩
  obtain ⟨k₀, j₀, hj₀, hs₀eq⟩ := hdecJ s₀ hs₀b₁
  have hJb₁ : ∀ j ∈ J', Commute b₁ j := fun j hj =>
    (show Commute j b₁ from Subgroup.mem_centralizer_singleton_iff.mp (hJ'L hj).2).symm
  have hs₀J : s₀ ∈ J' := by
    have hcj : Commute (b₁ ^ k₀) j₀ := (hJb₁ j₀ hj₀).pow_left k₀
    have e1 : (b₁ ^ k₀ * j₀) * (b₁ ^ k₀ * j₀) = b₁ ^ k₀ * b₁ ^ k₀ * (j₀ * j₀) := by
      rw [mul_assoc, ← mul_assoc j₀, ← hcj.eq]; group
    have h := h5.s₀_sq
    rw [hs₀eq, e1] at h
    have hxJ : b₁ ^ k₀ * b₁ ^ k₀ ∈ J' := by
      rw [eq_inv_of_mul_eq_one_left h]; exact J'.inv_mem (J'.mul_mem hj₀ hj₀)
    have hx1 := eq_one_of_central φ' hxJ fun j hj =>
      (((hJb₁ j hj).pow_left k₀).mul_left ((hJb₁ j hj).pow_left k₀)).eq
    have hk1 : b₁ ^ k₀ = 1 := by
      have h3 : (b₁ ^ k₀) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hB.B_cube hb₁B, one_pow]
      calc b₁ ^ k₀ = (b₁ ^ k₀) ^ 3 * (b₁ ^ k₀ * b₁ ^ k₀)⁻¹ := by group
        _ = 1 := by rw [h3, hx1, inv_one, one_mul]
    rw [hs₀eq, hk1, one_mul]; exact hj₀
  have hs₀P' : s₀⁻¹ ∉ P' := fun h => h5.s₀_not_mem_B (by
    rw [← inv_inv s₀]; exact B.inv_mem (hP'B h))
  have hs₀C : s₀⁻¹ ∈ C₀ := C₀.inv_mem ⟨hs₀J, Subgroup.mem_centralizer_singleton_iff.mpr
    (h5.s₀_comm (hmemA _ (by simp))).symm⟩
  have hjC : j ∈ C₀ := ⟨hj, Subgroup.mem_centralizer_singleton_iff.mpr hjc⟩
  by_cases hjP : j ∈ P'
  · exact ⟨b ^ i * (b₁ ^ k * j), B.mul_mem (B.zpow_mem hbB i) (B.mul_mem (B.pow_mem hb₁B k)
      (hP'B hjP)), Or.inl rfl⟩
  · have hm := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨j, hjC⟩) (b := ⟨s₀⁻¹, hs₀C⟩)).mpr
      (by simp only [Subgroup.mem_subgroupOf]; exact iff_of_false hjP hs₀P')
    rw [Subgroup.mem_subgroupOf] at hm
    refine ⟨b ^ i * (b₁ ^ k * (j * s₀⁻¹)), B.mul_mem (B.zpow_mem hbB i)
      (B.mul_mem (B.pow_mem hb₁B k) (hP'B hm)), Or.inr (by group)⟩

abbrev A₁sub (b b₁ b₂ b₃ : G) : Subgroup G := Subgroup.closure {b, b₁, b₂ * b₃}

abbrev H₅₂ (b b₁ b₂ b₃ s₀ : G) : Subgroup G :=
  CenS (Subgroup.closure {β' b₂ b₃, s₀}) ⊓ Nor (A₁sub b b₁ b₂ b₃)

theorem conj_mem_cenS_of_mem_nor {K : Subgroup G} {n x : G} (hn : n ∈ Nor K) (hx : x ∈ CenS K) :
    n * x * n⁻¹ ∈ CenS K := by
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  have ha' : n⁻¹ * a * n⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) a).mp ha
  rw [inv_inv] at ha'
  have := Subgroup.mem_centralizer_iff.mp hx _ ha'
  calc a * (n * x * n⁻¹) = n * (n⁻¹ * a * n * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * a * n)) * n⁻¹ := by rw [this]
    _ = n * x * n⁻¹ * a := by group

theorem mem_nor_of_mem_cenS {K : Subgroup G} {x : G} (hx : x ∈ CenS K) : x ∈ Nor K :=
  Subgroup.mem_normalizer_fintype fun a ha => by
    rw [← Subgroup.mem_centralizer_iff.mp hx a ha, mul_inv_cancel_right]; exact ha

section Basic2

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.s₀_β_pow (k : ℕ) : s₀ * β' b₂ b₃ ^ k * s₀⁻¹ = (β' b₂ b₃ ^ k)⁻¹ := by
  rw [← conj_pow, show s₀ * β' b₂ b₃ * s₀⁻¹ = (β' b₂ b₃)⁻¹ from h5.hs₀b, inv_pow]

theorem FF81Sec5.β_pow_mul_self (k : ℕ) :
    β' b₂ b₃ ^ k * β' b₂ b₃ ^ k = (β' b₂ b₃ ^ k)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_add, ← pow_add, show k + k + k = 3 * k by ring, pow_mul, h5.β_cube, one_pow]

theorem FF81Sec5.comm_s₀ {n : G} {k : ℕ} (hk : n * s₀ * n⁻¹ = β' b₂ b₃ ^ k * s₀) :
    β' b₂ b₃ ^ k * n * s₀ = s₀ * (β' b₂ b₃ ^ k * n) := by
  have hs : (β' b₂ b₃ ^ k)⁻¹ * s₀ = s₀ * β' b₂ b₃ ^ k := by
    rw [← h5.s₀_β_pow k]; group
  calc β' b₂ b₃ ^ k * n * s₀ = β' b₂ b₃ ^ k * (n * s₀ * n⁻¹) * n := by group
    _ = (β' b₂ b₃ ^ k * β' b₂ b₃ ^ k) * s₀ * n := by rw [hk]; group
    _ = s₀ * (β' b₂ b₃ ^ k * n) := by rw [h5.β_pow_mul_self, hs]; group

theorem FF81Sec5.β_mem_nor : β' b₂ b₃ ∈ Nor (A₁sub b b₁ b₂ b₃) :=
  mem_nor_of_mem_cenS (h5.B_le_cenS_A₁ h5.β_mem)

theorem FF81Sec5.s₀_mem_nor : s₀ ∈ Nor (A₁sub b b₁ b₂ b₃) := mem_nor_of_mem_cenS h5.hs₀A

end Basic2

section Nor

variable (hKF : KF_Sp6Levi) (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include hKF h5

theorem FF81Sec5.nor_A₁_le_nor_B : Nor (A₁sub b b₁ b₂ b₃) ≤ Nor B := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hzc : n * z * n⁻¹ ∈ CenS (A₁sub b b₁ b₂ b₃) :=
    conj_mem_cenS_of_mem_nor hn (h5.B_le_cenS_A₁ hz)
  obtain ⟨w, hw, h | h⟩ := h5.cenS_A₁ hKF hzc
  · rw [h]; exact hw
  · exfalso
    have h3 : (n * z * n⁻¹) ^ 3 = 1 := by rw [conj_pow, h5.basis.B_cube hz]; group
    rw [h] at h3
    have key : w * (s₀ * w * s₀⁻¹) * w * s₀ = 1 := by
      rw [h5.s₀_inv, ← h3, pow_three']; group
    have hw' : s₀ * w * s₀⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp h5.s₀_mem_nor_B w).mp hw
    refine h5.s₀_not_mem_B ?_
    rw [eq_inv_of_mul_eq_one_right key]
    exact B.inv_mem (B.mul_mem (B.mul_mem hw hw') hw)

theorem FF81Sec5.conj_s₀ {n : G} (hn : n ∈ Nor (A₁sub b b₁ b₂ b₃)) :
    ∃ k : ℕ, n * s₀ * n⁻¹ = β' b₂ b₃ ^ k * s₀ := by
  have hc : n * s₀ * n⁻¹ ∈ CenS (A₁sub b b₁ b₂ b₃) := conj_mem_cenS_of_mem_nor hn h5.hs₀A
  have hsq : (n * s₀ * n⁻¹) * (n * s₀ * n⁻¹) = 1 := by
    rw [show (n * s₀ * n⁻¹) * (n * s₀ * n⁻¹) = n * (s₀ * s₀) * n⁻¹ by group, h5.s₀_sq]; group
  obtain ⟨z, hz, h | h⟩ := h5.cenS_A₁ hKF hc
  · exfalso
    rw [h] at hsq
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [h5.basis.B_cube hz, hsq, inv_one, one_mul]
    rw [hz1] at h
    refine h5.s₀_ne_one ?_
    calc s₀ = n⁻¹ * (n * s₀ * n⁻¹) * n := by group
      _ = 1 := by rw [h]; group
  · rw [h] at hsq
    have hinv : s₀ * z * s₀⁻¹ = z⁻¹ := by
      rw [h5.s₀_inv]
      exact eq_inv_of_mul_eq_one_right (by rw [← hsq]; group)
    obtain ⟨k, rfl⟩ := h5.mem_zpowers_β hz hinv
    exact ⟨k, h⟩

theorem FF81Sec5.exists_mem_H {n : G} (hn : n ∈ Nor (A₁sub b b₁ b₂ b₃))
    (hβ : n * β' b₂ b₃ * n⁻¹ = β' b₂ b₃) : ∃ k : ℕ, β' b₂ b₃ ^ k * n ∈ H₅₂ b b₁ b₂ b₃ s₀ := by
  obtain ⟨k, hk⟩ := h5.conj_s₀ hKF hn
  refine ⟨k, mem_cenS_pair_iff.mpr ⟨?_, (h5.comm_s₀ hk)⟩,
    Subgroup.mul_mem _ (Subgroup.pow_mem _ h5.β_mem_nor _) hn⟩
  have hnβ : n * β' b₂ b₃ = β' b₂ b₃ * n := by
    calc n * β' b₂ b₃ = n * β' b₂ b₃ * n⁻¹ * n := by group
      _ = β' b₂ b₃ * n := by rw [hβ]
  exact ((Commute.refl _).pow_left k).mul_left hnβ

theorem FF81Sec5.nor_A₁_eq :
    Nor (A₁sub b b₁ b₂ b₃) = Subgroup.closure {β' b₂ b₃, s₀} ⊔ H₅₂ b b₁ b₂ b₃ s₀ := by
  refine le_antisymm (fun n hn => ?_) (sup_le ((Subgroup.closure_le _).mpr (by
    rintro x (rfl | rfl)
    · exact h5.β_mem_nor
    · exact h5.s₀_mem_nor)) inf_le_right)
  obtain ⟨k, hk⟩ := h5.conj_s₀ hKF hn
  set m := β' b₂ b₃ ^ k * n with hm
  have hms : m * s₀ = s₀ * m := h5.comm_s₀ hk
  have hmN : m ∈ Nor (A₁sub b b₁ b₂ b₃) := Subgroup.mul_mem _ (Subgroup.pow_mem _ h5.β_mem_nor _) hn
  have hmB : m ∈ Nor B := h5.nor_A₁_le_nor_B hKF hmN
  have hy : m * β' b₂ b₃ * m⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hmB _).mp h5.β_mem
  have hyinv : s₀ * (m * β' b₂ b₃ * m⁻¹) * s₀⁻¹ = (m * β' b₂ b₃ * m⁻¹)⁻¹ := by
    have hm' : m⁻¹ * s₀⁻¹ = s₀⁻¹ * m⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, hms]
    calc s₀ * (m * β' b₂ b₃ * m⁻¹) * s₀⁻¹ = m * (s₀ * β' b₂ b₃ * s₀⁻¹) * m⁻¹ := by
          rw [show s₀ * (m * β' b₂ b₃ * m⁻¹) * s₀⁻¹ = (s₀ * m) * β' b₂ b₃ * (m⁻¹ * s₀⁻¹) by group,
            ← hms, hm']; group
      _ = (m * β' b₂ b₃ * m⁻¹)⁻¹ := by rw [h5.hs₀b]; group
  obtain ⟨j, hj⟩ := h5.mem_zpowers_β hy hyinv
  have hj3 : m * β' b₂ b₃ * m⁻¹ = β' b₂ b₃ ^ (j % 3) := by
    rw [hj, ← pow_mod_orderOf, h5.β_orderOf]
  have hnm : n = (β' b₂ b₃ ^ k)⁻¹ * m := by rw [hm]; group
  have hβS : ∀ i : ℕ, (β' b₂ b₃ ^ i)⁻¹ ∈ Subgroup.closure {β' b₂ b₃, s₀} := fun i =>
    Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hj3' : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hjm : j % 3
  · exfalso
    rw [pow_zero] at hj3
    exact h5.β_ne_one (conj_eq_one_iff.mp hj3)
  · rw [hnm]
    refine Subgroup.mul_mem_sup (hβS k) ⟨mem_cenS_pair_iff.mpr ⟨?_, hms⟩, hmN⟩
    rw [pow_one] at hj3
    calc m * β' b₂ b₃ = m * β' b₂ b₃ * m⁻¹ * m := by group
      _ = β' b₂ b₃ * m := by rw [hj3]
  · rw [hnm, show (β' b₂ b₃ ^ k)⁻¹ * m = ((β' b₂ b₃ ^ k)⁻¹ * s₀⁻¹) * (s₀ * m) by group]
    refine Subgroup.mul_mem_sup (Subgroup.mul_mem _ (hβS k)
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))
      ⟨mem_cenS_pair_iff.mpr ⟨?_, by rw [mul_assoc, hms]⟩,
        Subgroup.mul_mem _ h5.s₀_mem_nor hmN⟩
    have h2 : m * β' b₂ b₃ = β' b₂ b₃ ^ 2 * m := by
      calc m * β' b₂ b₃ = m * β' b₂ b₃ * m⁻¹ * m := by group
        _ = β' b₂ b₃ ^ 2 * m := by rw [hj3]
    have hb2 : (β' b₂ b₃ ^ 2)⁻¹ = β' b₂ b₃ :=
      inv_eq_of_mul_eq_one_left (by rw [← pow_succ', h5.β_cube])
    have hsβ : s₀ * β' b₂ b₃ ^ 2 = β' b₂ b₃ * s₀ := by
      calc s₀ * β' b₂ b₃ ^ 2 = (s₀ * β' b₂ b₃ ^ 2 * s₀⁻¹) * s₀ := by group
        _ = β' b₂ b₃ * s₀ := by rw [h5.s₀_β_pow 2, hb2]
    rw [mul_assoc, h2, ← mul_assoc, hsβ, mul_assoc]

theorem FF81Sec5.A₁_le_H : A₁sub b b₁ b₂ b₃ ≤ H₅₂ b b₁ b₂ b₃ s₀ := fun a ha =>
  ⟨mem_cenS_pair_iff.mpr ⟨h5.β_comm_A₁ ha, h5.s₀_comm ha⟩, Subgroup.le_normalizer ha⟩

end Nor

end CFSG.RankThree.PartTwo.Sec21.FF81
