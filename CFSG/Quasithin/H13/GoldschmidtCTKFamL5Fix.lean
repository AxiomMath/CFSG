module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.ContinuousFunctionalCalculus

public section

namespace CFSG.Quasithin.H13.CTK.L5

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
variable {Γ : Type} [Group Γ] (act : Γ →* (W ≃ₗ[K] W))

@[expose] def actPerm : Γ →* Equiv.Perm W where
  toFun g := (act g).toEquiv
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

theorem card_modEq_fix [Finite W] (H : Subgroup Γ) {p : ℕ} [Fact p.Prime] (hH : IsPGroup p H)
    (U : Set W) (hU : ∀ h ∈ H, ∀ w ∈ U, act h w ∈ U) :
    U.ncard ≡ {w | w ∈ U ∧ ∀ h ∈ H, act h w = w}.ncard [MOD p] := by
  let _ : MulAction H W := MulAction.compHom W ((actPerm act).comp H.subtype)
  let U' : SubMulAction H W := ⟨U, fun h w hw => hU h h.2 w hw⟩
  have h1 := hH.card_modEq_card_fixedPoints ↥U'
  have e1 : Nat.card ↥U' = U.ncard := Nat.card_coe_set_eq U
  have e2 : Nat.card ↥(MulAction.fixedPoints H ↥U') = {w | w ∈ U ∧ ∀ h ∈ H, act h w = w}.ncard := by
    rw [← Nat.card_coe_set_eq]
    apply Nat.card_congr
    exact {
      toFun := fun a => ⟨(a.1 : W), a.1.2, fun h hh => by
        have := a.2 ⟨h, hh⟩
        exact congrArg Subtype.val this⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, fun h => Subtype.ext (a.2.2 h h.2)⟩
      left_inv := fun a => rfl
      right_inv := fun a => rfl }
  rw [e1, e2] at h1
  exact h1

theorem card_submodule [Finite W] (hK : Nat.card K = 2) (U : Submodule K W) :
    ∃ u : ℕ, Nat.card U = 2 ^ u := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have : Fintype K := Fintype.ofFinite K
  have : Fintype U := Fintype.ofFinite U
  refine ⟨Module.finrank K U, ?_⟩
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := U),
    ← Nat.card_eq_fintype_card, hK]

theorem zpowers_stable {x : Γ} (hx : orderOf x = 5) (U : Set W)
    (hU : ∀ w ∈ U, act x w ∈ U) : ∀ h ∈ Subgroup.zpowers x, ∀ w ∈ U, act h w ∈ U := by
  have hpow : ∀ n : ℕ, ∀ w ∈ U, act (x ^ n) w ∈ U := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ', map_mul]
      exact hU _ (ih w hw)
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  have h1 : x ^ k = x ^ (k % 5).toNat := by
    rw [← zpow_mod_orderOf, hx, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    norm_cast
  rw [h1]
  exact hpow _

@[expose] def fixSub (x : Γ) : Submodule K W where
  carrier := {w | act x w = w}
  add_mem' := fun {a b} (ha : act x a = a) (hb : act x b = b) => by
    show act x (a + b) = a + b
    rw [map_add, ha, hb]
  zero_mem' := by
    show act x 0 = 0
    simp
  smul_mem' := fun c w (hw : act x w = w) => by
    show act x (c • w) = c • w
    rw [map_smul, hw]

theorem mem_fixSub {x : Γ} {w : W} : w ∈ fixSub act x ↔ act x w = w := Iff.rfl

theorem modEq_fixSet [Finite W] {x : Γ} (hx : orderOf x = 5) (U : Set W)
    (hU : ∀ w ∈ U, act x w ∈ U) :
    U.ncard ≡ {w | w ∈ U ∧ act x w = w}.ncard [MOD 5] := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hH : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  have h1 := card_modEq_fix act (Subgroup.zpowers x) hH U (zpowers_stable act hx U hU)
  have e : {w | w ∈ U ∧ ∀ h ∈ Subgroup.zpowers x, act h w = w} = {w | w ∈ U ∧ act x w = w} := by
    ext w
    refine and_congr_right fun _ => ⟨fun h => h x (Subgroup.mem_zpowers x), fun h g hg => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    have : ∀ n : ℕ, act (x ^ n) w = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', map_mul, LinearEquiv.mul_apply, ih, h]
    have h1 : x ^ k = x ^ (k % 5).toNat := by
      rw [← zpow_mod_orderOf, hx, ← zpow_natCast,
        Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
      norm_cast
    rw [h1]
    exact this _
  rwa [e] at h1

theorem nat_card_fixSub [Finite W] (x : Γ) :
    Nat.card (fixSub act x) = ((fixSub act x : Submodule K W) : Set W).ncard :=
  Nat.card_coe_set_eq _

theorem ncard_fix_x [Finite W] (hK : Nat.card K = 2) (hW : Nat.card W = 32) {x : Γ}
    (hx : orderOf x = 5) (hne : ∃ w, act x w ≠ w) :
    ((fixSub act x : Submodule K W) : Set W).ncard = 2 := by
  have h1 := modEq_fixSet act hx Set.univ (fun w _ => Set.mem_univ _)
  have e1 : (Set.univ : Set W).ncard = 32 := by rw [Set.ncard_univ, hW]
  have e2 : {w | w ∈ (Set.univ : Set W) ∧ act x w = w} = (fixSub act x : Set W) := by
    ext w
    simp [mem_fixSub]
  rw [e1, e2] at h1
  obtain ⟨c, hc⟩ := card_submodule hK (fixSub act x)
  rw [nat_card_fixSub] at hc
  rw [hc] at h1
  have hle : 2 ^ c ≤ 32 := by
    rw [← hc]
    calc ((fixSub act x : Submodule K W) : Set W).ncard ≤ (Set.univ : Set W).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = 32 := e1
  have hc5 : c ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases c
  · exact absurd h1 (by decide)
  · simpa using hc
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exfalso
    have : ((fixSub act x : Submodule K W) : Set W) = Set.univ :=
      Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [hc, e1]; norm_num)
    obtain ⟨w, hw⟩ := hne
    exact hw (this ▸ Set.mem_univ w : w ∈ ((fixSub act x : Submodule K W) : Set W))

theorem classify [Finite W] (hK : Nat.card K = 2) (hW : Nat.card W = 32) {x : Γ}
    (hx : orderOf x = 5) (hne : ∃ w, act x w ≠ w) (U : Submodule K W)
    (hU : ∀ w ∈ U, act x w ∈ U) :
    Nat.card U = 1 ∨ (Nat.card U = 2 ∧ ∀ w, act x w = w → w ∈ U) ∨
      (Nat.card U = 16 ∧ ∀ w ∈ U, act x w = w → w = 0) ∨ Nat.card U = 32 := by
  have hS := modEq_fixSet act hx (U : Set W) hU
  have hC := ncard_fix_x act hK hW hx hne
  set S : Set W := {w | w ∈ (U : Set W) ∧ act x w = w} with hSdef
  have hSsub : S ⊆ ((fixSub act x : Submodule K W) : Set W) := fun w hw => hw.2
  have hSle : S.ncard ≤ 2 := hC ▸ Set.ncard_le_ncard hSsub (Set.toFinite _)
  have hS0 : (0 : W) ∈ S := ⟨U.zero_mem, by simp⟩
  have hSpos : 1 ≤ S.ncard := by
    rw [Nat.one_le_iff_ne_zero]
    exact (Set.ncard_pos (Set.toFinite _)).2 ⟨0, hS0⟩ |>.ne'
  obtain ⟨u, hu⟩ := card_submodule hK U
  have hUcard : (U : Set W).ncard = Nat.card U := (Nat.card_coe_set_eq _).symm
  rw [hUcard, hu] at hS
  have hle : 2 ^ u ≤ 32 := by
    rw [← hu, ← hW]
    exact Nat.card_le_card_of_injective (fun a => (a : W)) Subtype.val_injective
  have hu5 : u ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ u := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hSeq2 : S.ncard = 2 → ((fixSub act x : Submodule K W) : Set W) ⊆ S := fun h2 => by
    have := Set.eq_of_subset_of_ncard_le hSsub (by rw [h2, hC]) (Set.toFinite _)
    rw [this]
  interval_cases u
  · left
    simpa using hu
  · right; left
    refine ⟨by simpa using hu, fun w hw => ?_⟩
    have h2 : S.ncard = 2 := by
      have : (2 : ℕ) ≡ S.ncard [MOD 5] := by simpa using hS
      unfold Nat.ModEq at this
      omega
    exact (hSeq2 h2 hw).1
  · exfalso
    have : (4 : ℕ) ≡ S.ncard [MOD 5] := by simpa using hS
    unfold Nat.ModEq at this
    omega
  · exfalso
    have : (8 : ℕ) ≡ S.ncard [MOD 5] := by simpa using hS
    unfold Nat.ModEq at this
    omega
  · right; right; left
    refine ⟨by simpa using hu, fun w hw hwx => ?_⟩
    have h1 : S.ncard = 1 := by
      have : (16 : ℕ) ≡ S.ncard [MOD 5] := by simpa using hS
      unfold Nat.ModEq at this
      omega
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have h0 : (0 : W) = a := by simpa [ha] using hS0
    have hw' : w ∈ S := ⟨hw, hwx⟩
    rw [ha] at hw'
    rw [h0]
    exact hw'
  · right; right; right
    simpa using hu

end CFSG.Quasithin.H13.CTK.L5
