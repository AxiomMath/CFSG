module

public import CFSG.Sporadic.Co1.Module.U6OddChain
public import CFSG.Sporadic.Co1.Module.Pairs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative Matrix
open CFSG.Sporadic.Co1.U6OddNative
open CFSG.Sporadic.Co1.Module (co1Act)
open CFSG.Sporadic.Co1.Module.CoTwo
open CFSG.Perm.Native
open CFSG.Sporadic.Co1.Module.Pairs (tyOrb tyOrbC tyOrbC_eq tyOrbC_smul_mem tyLab tyLab_lt
  tyLab_spec)

attribute [local instance] Odd.vecAct Odd.vecSMul

variable {rr : ℕ → Array ℕ} {reg : ℕ → NativeSporadic.Co1}

@[expose] def LSpec (L : ℕ → ℕ) : Prop :=
  (∀ w, L w < 4) ∧ ∀ w < 2 ^ 24, ∀ j < 4, (L w = j ↔ toVecD 24 w ∈ tyOrb j)

theorem lSpec_tyLab :
    LSpec (tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280) :=
  ⟨fun w => tyLab_lt _ _ _ w, fun w hw j hj => tyLab_spec w hw j hj⟩

theorem lab_inv
    {L : ℕ → ℕ} (hL : LSpec L) {w w' : ℕ} (hw : w < 2 ^ 24) (hw' : w' < 2 ^ 24)
    {n : NativeSporadic.Co1} (h : toVecD 24 w' = co1Act n (toVecD 24 w)) : L w' = L w := by
  have hj := hL.1 w
  have h1 : toVecD 24 w ∈ tyOrb (L w) := (hL.2 w hw (L w) hj).1 rfl
  have h2 : toVecD 24 w ∈ tyOrbC (L w) := by rw [tyOrbC_eq]; exact h1
  have h3 : n • toVecD 24 w ∈ tyOrbC (L w) := tyOrbC_smul_mem n h2
  have h4 : toVecD 24 w' ∈ tyOrb (L w) := by
    rw [← tyOrbC_eq, h]
    exact h3
  exact (hL.2 w' hw' (L w) hj).2 h4

theorem co1Act_add (g : NativeSporadic.Co1) (v w : Vec24) :
    co1Act g (v + w) = co1Act g v + co1Act g w := by
  simp [Odd.co1Act_eq_mulVec, Matrix.mulVec_add]

theorem co1Act_zero (g : NativeSporadic.Co1) : co1Act g 0 = 0 := by
  simp [Odd.co1Act_eq_mulVec]

theorem xcN_zero (c : List ℕ) : xcN c 0 = 0 := by
  induction c with
  | nil => rfl
  | cons x xs ih => simp [xcN, ih]

theorem xcN_lt {c : List ℕ} (hc : ∀ v ∈ c, v < 2 ^ 24) (m : ℕ) : xcN c m < 2 ^ 24 := by
  induction c generalizing m with
  | nil => simp [xcN]
  | cons x xs ih =>
    simp only [xcN]
    refine Nat.xor_lt_two_pow ?_ (ih (fun v hv => hc v (List.mem_cons_of_mem _ hv)) _)
    split_ifs
    · exact hc x (List.mem_cons_self ..)
    · norm_num

theorem xcN_equiv {n : NativeSporadic.Co1} :
    ∀ (c c' : List ℕ), c.length = c'.length →
      (∀ i < c.length, toVecD 24 (c'.getD i 0) = co1Act n (toVecD 24 (c.getD i 0))) →
        ∀ m, toVecD 24 (xcN c' m) = co1Act n (toVecD 24 (xcN c m)) := by
  intro c
  induction c with
  | nil =>
    intro c' hlen _ m
    have : c' = [] := List.length_eq_zero_iff.1 hlen.symm
    subst this
    simp [xcN, toVecD_zero, co1Act_zero]
  | cons x xs ih =>
    intro c' hlen h m
    obtain ⟨y, ys, rfl⟩ : ∃ y ys, c' = y :: ys := by
      cases c' with
      | nil => simp at hlen
      | cons y ys => exact ⟨y, ys, rfl⟩
    simp only [xcN, toVecD_xor, co1Act_add]
    have hA : toVecD 24 (if m % 2 = 1 then y else 0) =
        co1Act n (toVecD 24 (if m % 2 = 1 then x else 0)) := by
      split_ifs
      · simpa using h 0 (by simp)
      · simp [toVecD_zero, co1Act_zero]
    have hB := ih ys (by simpa using hlen) (fun i hi => by
      simpa using h (i + 1) (by simpa using hi)) (m / 2)
    rw [hA, hB]

noncomputable def codeOf (v : Vec24) : ℕ := Classical.choose (Odd.exists_toVecD v)

theorem codeOf_lt (v : Vec24) : codeOf v < 2 ^ 24 :=
  (Classical.choose_spec (Odd.exists_toVecD v)).1

theorem toVecD_codeOf (v : Vec24) : toVecD 24 (codeOf v) = v :=
  (Classical.choose_spec (Odd.exists_toVecD v)).2

theorem codeOf_toVecD {x : ℕ} (hx : x < 2 ^ 24) : codeOf (toVecD 24 x) = x :=
  toVecD_injective (codeOf_lt _) hx (toVecD_codeOf _)

theorem xcN_mem_of {Wl : List ℕ} (h0 : 0 ∈ Wl) (hxor : ∀ x ∈ Wl, ∀ y ∈ Wl, (x ^^^ y) ∈ Wl) :
    ∀ (c : List ℕ), (∀ v ∈ c, v ∈ Wl) → ∀ m, xcN c m ∈ Wl := by
  intro c
  induction c with
  | nil => intro _ m; simpa [xcN] using h0
  | cons x xs ih =>
    intro hc m
    simp only [xcN]
    refine hxor _ ?_ _ (ih (fun v hv => hc v (List.mem_cons_of_mem _ hv)) _)
    split_ifs
    · exact hc x (List.mem_cons_self ..)
    · exact h0

theorem mem_normalizer_zpowers {G : Type*} [Group G] [Finite G] {g x : G} {j : ℕ}
    (h : x * g = g ^ j * x) :
    x ∈ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  have hconj : x * g * x⁻¹ = g ^ j := by rw [h]; group
  have hle : ∀ y ∈ Subgroup.zpowers g, x * y * x⁻¹ ∈ Subgroup.zpowers g := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have : x * g ^ k * x⁻¹ = (x * g * x⁻¹) ^ k := (conj_zpow).symm
    rw [this, hconj, ← zpow_natCast, ← _root_.zpow_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) _
  have hmap : (Subgroup.zpowers g).map (MulAut.conj x).toMonoidHom ≤ Subgroup.zpowers g := by
    rintro _ ⟨y, hy, rfl⟩
    exact hle y hy
  have hcard : Nat.card (Subgroup.zpowers g) ≤
      Nat.card ((Subgroup.zpowers g).map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hmap hcard
  intro y
  refine ⟨hle y, fun hy => ?_⟩
  rw [← heq] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hzy' : x * z * x⁻¹ = x * y * x⁻¹ := hzy
  have : z = y := mul_left_cancel (mul_right_cancel hzy')
  rw [← this]
  exact hz

theorem fixed_of_normalizer {g n : NativeSporadic.Co1}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) : Set _))
    {v : Vec24} (hv : co1Act g v = v) : co1Act g (co1Act n v) = co1Act n v := by
  have hn' : n⁻¹ ∈ Subgroup.normalizer
      ((Subgroup.zpowers g : Subgroup NativeSporadic.Co1) : Set _) :=
    (Subgroup.inv_mem_iff _).2 hn
  have h1 : n⁻¹ * g * n ∈ Subgroup.zpowers g := by
    have := (Subgroup.mem_normalizer_iff.1 hn' g).1 (Subgroup.mem_zpowers g)
    simpa using this
  have h2 : co1Act (n⁻¹ * g * n) v = v :=
    (Subgroup.zpowers_le.2 (show g ∈ vstab v from hv)) h1
  calc co1Act g (co1Act n v) = co1Act (g * n) v := (Odd.co1Act_mul' g n v).symm
    _ = co1Act (n * (n⁻¹ * g * n)) v := by rw [show n * (n⁻¹ * g * n) = g * n by group]
    _ = co1Act n (co1Act (n⁻¹ * g * n) v) := Odd.co1Act_mul' _ _ v
    _ = co1Act n v := by rw [h2]

end CFSG.Sporadic.Co1.Module.U6Odd
