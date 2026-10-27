module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.Quasithin.Background.HModChk
public import CFSG.Permutation.FinPack

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16V1K

open Equiv CFSG.Quasithin CFSG.Quasithin.G6 CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Permutation.FinPack

@[expose] def X1 : List ℕ := [0, 6, 12, 10]

@[expose] def X2 : List ℕ := [0, 24, 48, 40]

@[expose] def X3 : List ℕ := [0, 96, 192, 160]

@[expose] def X4 : List ℕ := [0, 384, 768, 640]

@[expose] def EL : List ℕ := [0, 1023, 1, 1022]

@[expose] def UL : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 256, 512]

theorem xor_closed : (∀ a ∈ X1, ∀ b ∈ X1, a ^^^ b ∈ X1) ∧ (∀ a ∈ X2, ∀ b ∈ X2, a ^^^ b ∈ X2) ∧
    (∀ a ∈ X3, ∀ b ∈ X3, a ^^^ b ∈ X3) ∧ (∀ a ∈ X4, ∀ b ∈ X4, a ^^^ b ∈ X4) ∧
    ∀ a ∈ EL, ∀ b ∈ EL, a ^^^ b ∈ EL := by
  decide +kernel

theorem decomp_UL : ∀ k ∈ UL, ∃ x1 ∈ X1, ∃ x2 ∈ X2, ∃ x3 ∈ X3, ∃ x4 ∈ X4, ∃ e ∈ EL,
    k = x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ e := by
  decide +kernel

theorem mem_combos_UL : ∀ j < 10, 2 ^ j ∈ combos UL := by decide +kernel

theorem decomp_all : ∀ k < 2 ^ 10, ∃ x1 ∈ X1, ∃ x2 ∈ X2, ∃ x3 ∈ X3, ∃ x4 ∈ X4, ∃ e ∈ EL,
    k = x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ e := by
  intro k hk
  have hU : k ∈ combos UL :=
    mem_combos_of_xorLin (f := id) (fun _ _ => rfl) mem_combos_UL k hk
  refine mem_of_combos (fun k => ∃ x1 ∈ X1, ∃ x2 ∈ X2, ∃ x3 ∈ X3, ∃ x4 ∈ X4, ∃ e ∈ EL,
    k = x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ e) ⟨0, by decide, 0, by decide, 0, by decide, 0, by decide,
      0, by decide, rfl⟩ ?_ UL decomp_UL k hU
  rintro a b ⟨x1, hx1, x2, hx2, x3, hx3, x4, hx4, e, he, ha⟩
    ⟨y1, hy1, y2, hy2, y3, hy3, y4, hy4, f, hf, hb⟩
  obtain ⟨c1, c2, c3, c4, c5⟩ := xor_closed
  refine ⟨x1 ^^^ y1, c1 _ hx1 _ hy1, x2 ^^^ y2, c2 _ hx2 _ hy2, x3 ^^^ y3, c3 _ hx3 _ hy3,
    x4 ^^^ y4, c4 _ hx4 _ hy4, e ^^^ f, c5 _ he _ hf, ?_⟩
  rw [ha, hb]
  ac_rfl

theorem X_core : (∀ x ∈ X1, toW 10 x ∈ coreMod 10) ∧ (∀ x ∈ X2, toW 10 x ∈ coreMod 10) ∧
    (∀ x ∈ X3, toW 10 x ∈ coreMod 10) ∧ (∀ x ∈ X4, toW 10 x ∈ coreMod 10) := by
  simp only [mem_coreMod]
  decide +kernel

theorem odd_not_core : toW 10 1 ∉ coreMod 10 ∧ toW 10 1022 ∉ coreMod 10 := by
  simp only [mem_coreMod]
  decide +kernel

theorem core_of_xor {y e k : ℕ} (hk : k = y ^^^ e) (hy : toW 10 y ∈ coreMod 10)
    (hm : toW 10 k ∈ coreMod 10) : toW 10 e ∈ coreMod 10 := by
  have h2 : e = y ^^^ k := by rw [hk, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have h3 : toW 10 (y ^^^ k) = toW 10 y * toW 10 k := toW_xor 10 y k
  rw [h2, h3]
  exact mul_mem hy hm

theorem pick {f : PermMod 10 → PermMod 10} {L : List (PermMod 10)} {X : List ℕ}
    (h : L.map f = X.map (toW 10)) {x : ℕ} (hx : x ∈ X) : ∃ a ∈ L, f a = toW 10 x := by
  have hm : toW 10 x ∈ X.map (toW 10) := List.mem_map_of_mem hx
  rw [← h] at hm
  exact List.mem_map.1 hm

theorem coreMod_of {σ τ υ ω : Perm (Fin 10)} {L1 L2 L3 L4 : List (PermMod 10)}
    (h1 : L1.map (fun a => permAct 10 σ a * a⁻¹) = X1.map (toW 10))
    (h2 : L2.map (fun a => permAct 10 τ a * a⁻¹) = X2.map (toW 10))
    (h3 : L3.map (fun a => permAct 10 υ a * a⁻¹) = X3.map (toW 10))
    (h4 : L4.map (fun a => permAct 10 ω a * a⁻¹) = X4.map (toW 10))
    (hone : allOnes 10 = toW 10 1023) :
    ∀ m : PermMod 10, m ∈ coreMod 10 → ∃ a ∈ L1, ∃ b ∈ L2, ∃ c ∈ L3, ∃ d ∈ L4,
      m = permAct 10 σ a * a⁻¹ * (permAct 10 τ b * b⁻¹) * (permAct 10 υ c * c⁻¹) *
          (permAct 10 ω d * d⁻¹) ∨
        m = permAct 10 σ a * a⁻¹ * (permAct 10 τ b * b⁻¹) * (permAct 10 υ c * c⁻¹) *
          (permAct 10 ω d * d⁻¹) * allOnes 10 := by
  intro m hm
  obtain ⟨k, hk, rfl⟩ := toW_surj 10 m
  obtain ⟨x1, hx1, x2, hx2, x3, hx3, x4, hx4, e, he, hke⟩ := decomp_all k hk
  obtain ⟨a, ha, hga⟩ := pick h1 hx1
  obtain ⟨b, hb, hgb⟩ := pick h2 hx2
  obtain ⟨c, hc, hgc⟩ := pick h3 hx3
  obtain ⟨d, hd, hgd⟩ := pick h4 hx4
  refine ⟨a, ha, b, hb, c, hc, d, hd, ?_⟩
  beta_reduce at hga hgb hgc hgd
  have hcv : toW 10 (x1 ^^^ x2 ^^^ x3 ^^^ x4) = permAct 10 σ a * a⁻¹ * (permAct 10 τ b * b⁻¹) *
      (permAct 10 υ c * c⁻¹) * (permAct 10 ω d * d⁻¹) := by
    rw [toW_xor, toW_xor, toW_xor, ← hga, ← hgb, ← hgc, ← hgd]
  obtain ⟨k1, k2, k3, k4⟩ := X_core
  have hcm : toW 10 (x1 ^^^ x2 ^^^ x3 ^^^ x4) ∈ coreMod 10 := by
    rw [toW_xor, toW_xor, toW_xor]
    exact mul_mem (mul_mem (mul_mem (k1 _ hx1) (k2 _ hx2)) (k3 _ hx3)) (k4 _ hx4)
  simp only [EL, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · left
    rw [hke, Nat.xor_zero, hcv]
  · right
    rw [hke, toW_xor 10 _ 1023, ← hone, hcv]
  · exact absurd (core_of_xor hke hcm hm) odd_not_core.1
  · exact absurd (core_of_xor hke hcm hm) odd_not_core.2

theorem toW_inv (k : ℕ) : (toW 10 k)⁻¹ = toW 10 k := by
  have h := toW_xor 10 k k
  rw [Nat.xor_self, toW_zero] at h
  exact inv_eq_of_mul_eq_one_right h.symm

theorem xorLin_comm (cs : List ℕ) : XorLin fun k => actM cs k ^^^ k := fun a b => by
  change actM cs (a ^^^ b) ^^^ (a ^^^ b) = (actM cs a ^^^ a) ^^^ (actM cs b ^^^ b)
  rw [actM_xor cs a b, Nat.xor_assoc, ← Nat.xor_assoc (actM cs b) a b,
    Nat.xor_comm (actM cs b) a, Nat.xor_assoc a (actM cs b) b, ← Nat.xor_assoc (actM cs a) a]

theorem comm_mem_of {σ : Perm (Fin 10)} {cs B : List ℕ} {S : Finset (PermMod 10)}
    (hlen : cs.length = 10)
    (hcol : ∀ j < 10, permAct 10 σ (toW 10 (2 ^ j)) = toW 10 (cs.getD j 0))
    (hB : ∀ j < 10, actM cs (2 ^ j) ^^^ 2 ^ j ∈ combos B)
    (hS : ∀ x ∈ combos B, toW 10 x ∈ S) : ∀ m : PermMod 10, permAct 10 σ m * m⁻¹ ∈ S := by
  intro m
  obtain ⟨k, hk, rfl⟩ := toW_surj 10 m
  have hact : permAct 10 σ (toW 10 k) = toW 10 (actM cs k) :=
    congrArg Multiplicative.ofAdd (addHom_bvec (MonoidHom.toAdditive (permAct 10 σ).toMonoidHom)
      cs hlen (fun j hj => congrArg Multiplicative.toAdd (hcol j hj)) k)
  have he : permAct 10 σ (toW 10 k) * (toW 10 k)⁻¹ = toW 10 (actM cs k ^^^ k) := by
    rw [hact, toW_inv]
    exact (toW_xor 10 _ _).symm
  rw [he]
  exact hS _ (mem_combos_of_xorLin (xorLin_comm cs) hB k hk)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S16V1K
