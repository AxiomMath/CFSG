module

public import CFSG.Quasithin.Background.SmithD39TwoClif
public import CFSG.Quasithin.Background.SmithD321Type
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard

public section

namespace CFSG.Quasithin.SmithD321

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.SmithD391
open scoped Pointwise

section Defs

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

@[expose] noncomputable def mRel (B X : Subgroup Γ) : ℕ :=
  rk ↥B - rk ↥(B ⊓ Subgroup.centralizer (X : Set Γ))

@[expose] def IsCubicOn (P : Subgroup Γ) (Y : Subgroup Q) : Prop :=
  ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ y ∈ Y,
    c • (b • (a • y / y) / (a • y / y)) / (b • (a • y / y) / (a • y / y)) = 1

end Defs

section Extend

variable {Γ : Type*} [Group Γ]

private def extendBy {A : Subgroup Γ} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) {B : Subgroup Γ} (hBA : B ≤ A) {a : Γ} (ha : a ∈ A) :
    Subgroup Γ where
  carrier := {x | x ∈ B ∨ a⁻¹ * x ∈ B}
  mul_mem' := by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hA2 a ha])
    have hmemA : ∀ x, x ∈ B ∨ a⁻¹ * x ∈ B → x ∈ A := by
      rintro x (hx | hx)
      · exact hBA hx
      · have := A.mul_mem ha (hBA hx)
        rwa [mul_inv_cancel_left] at this
    intro x y hx hy
    have hxA := hmemA x hx
    have hyA := hmemA y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (B.mul_mem hx hy)
    · right
      have h1 : a⁻¹ * (x * y) = x * (a⁻¹ * y) := by
        rw [← mul_assoc, ← mul_assoc, hAc a⁻¹ (A.inv_mem ha) x hxA]
      rw [h1]
      exact B.mul_mem hx hy
    · right
      rw [← mul_assoc]
      exact B.mul_mem hx hy
    · left
      have h1 : x * y = (a⁻¹ * x) * (a⁻¹ * y) := by
        rw [hinv, mul_assoc, ← mul_assoc x a y, hAc x hxA a ha, mul_assoc, ← mul_assoc a a,
          ← pow_two, hA2 a ha, one_mul]
      rw [h1]
      exact B.mul_mem hx hy
  one_mem' := Or.inl B.one_mem
  inv_mem' := by
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hA2 a ha])
    rintro x (hx | hx)
    · exact Or.inl (B.inv_mem hx)
    · right
      have hxA : x ∈ A := by
        have := A.mul_mem ha (hBA hx)
        rwa [mul_inv_cancel_left] at this
      have h1 : a⁻¹ * x⁻¹ = (a⁻¹ * x)⁻¹ := by
        rw [mul_inv_rev, inv_inv, hinv, hAc a ha x⁻¹ (A.inv_mem hxA)]
      show a⁻¹ * x⁻¹ ∈ B
      rw [h1]
      exact B.inv_mem hx

private theorem mem_extendBy {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} {x : Γ} :
    x ∈ extendBy hAc hA2 hBA ha ↔ x ∈ B ∨ a⁻¹ * x ∈ B :=
  Iff.rfl

private theorem le_extendBy {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} :
    B ≤ extendBy hAc hA2 hBA ha :=
  fun _ hx => Or.inl hx

private theorem extendBy_le {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} :
    extendBy hAc hA2 hBA ha ≤ A := by
  intro x hx
  rcases hx with hx | hx
  · exact hBA hx
  · have := A.mul_mem ha (hBA hx)
    rwa [mul_inv_cancel_left] at this

private theorem mem_extendBy_self {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} :
    a ∈ extendBy hAc hA2 hBA ha :=
  Or.inr (by rw [inv_mul_cancel]; exact B.one_mem)

private theorem card_extendBy [Finite Γ] {A : Subgroup Γ}
    {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ}
    {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} (haB : a ∉ B) :
    Nat.card ↥(extendBy hAc hA2 hBA ha) = 2 * Nat.card ↥B := by
  classical
  have e : ↥(extendBy hAc hA2 hBA ha) ≃ ↥B ⊕ ↥B :=
    { toFun := fun x => if h : (x : Γ) ∈ B then Sum.inl ⟨x, h⟩
        else Sum.inr ⟨a⁻¹ * x, (mem_extendBy.1 x.2).resolve_left h⟩
      invFun := fun y => match y with
        | Sum.inl b => ⟨b, mem_extendBy.2 (Or.inl b.2)⟩
        | Sum.inr b => ⟨a * b, mem_extendBy.2 (Or.inr (by rw [inv_mul_cancel_left]; exact b.2))⟩
      left_inv := fun x => by
        by_cases h : (x : Γ) ∈ B
        · simp only [h, dite_true]
        · simp only [h, dite_false, mul_inv_cancel_left]
      right_inv := fun y => by
        rcases y with b | b
        · simp only [b.2, dite_true]
        · have hab : a * (b : Γ) ∉ B := fun h => haB (by
            have := B.mul_mem h (B.inv_mem b.2)
            rwa [mul_inv_cancel_right] at this)
          simp only [hab, dite_false, inv_mul_cancel_left] }
  rw [Nat.card_congr e, Nat.card_sum, two_mul]

private theorem rk_extendBy [Finite Γ] {A : Subgroup Γ}
    {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ}
    {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} (haB : a ∉ B) :
    rk ↥(extendBy hAc hA2 hBA ha) = rk ↥B + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold rk
  rw [card_extendBy haB, padicValNat.mul (by norm_num) Nat.card_pos.ne', padicValNat_self,
    add_comm]

variable {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private theorem orbSum_extendBy {A : Subgroup Γ} {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ} {hBA : B ≤ A} {a : Γ} {ha : a ∈ A}
    (S : Subgroup Q) :
    orbSum (extendBy hAc hA2 hBA ha) S = orbSum B S ⊔ a • orbSum B S := by
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rcases mem_extendBy.1 t.2 with ht | ht
    · exact (smul_le_orbSum S ht).trans le_sup_left
    · have h1 : (t : Γ) • S = a • ((a⁻¹ * t) • S) := by rw [smul_smul, mul_inv_cancel_left]
      rw [h1]
      exact ((Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2
        (smul_le_orbSum S ht)).trans le_sup_right
  · refine sup_le (orbSum_mono (fun x hx => mem_extendBy.2 (Or.inl hx)) S) ?_
    rw [smul_orbSum]
    refine iSup_le fun t => smul_le_orbSum S (mem_extendBy.2 (Or.inr ?_))
    rw [inv_mul_cancel_left]
    exact t.2

end Extend

section Orbit

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem nB_orbit_gen [Finite Γ] [Finite Q] {A : Subgroup Γ}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1) {S : Subgroup Q}
    (hdisj : ∀ B : Subgroup Γ, B ≤ A → stabIn A S ≤ B → ∀ a ∈ A, a ∉ B →
      orbSum B S ⊓ a • orbSum B S = ⊥) :
    rk ↥(orbSum A S) = 2 ^ (rk ↥A - rk ↥(stabIn A S)) * rk ↥S ∧
      nB A (orbSum A S) + rk ↥S =
        2 ^ (rk ↥A - rk ↥(stabIn A S)) * rk ↥S + nB (stabIn A S) S := by
  set A₀ := stabIn A S with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hAp : IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by simpa using hA2 x x.2)⟩
  have key : ∀ n : ℕ, n ≤ rk ↥A - rk ↥A₀ → ∃ B : Subgroup Γ, A₀ ≤ B ∧ B ≤ A ∧
      rk ↥B = rk ↥A₀ + n ∧ rk ↥(orbSum B S) = 2 ^ n * rk ↥S ∧
        nB B (orbSum B S) + rk ↥S = 2 ^ n * rk ↥S + nB A₀ S := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨A₀, le_rfl, hA₀A, by omega, ?_, ?_⟩ <;> rw [hA₀, orbSum_stabIn] <;> ring
    | succ n ih =>
      intro hn
      obtain ⟨B, h0B, hBA, hrkB, hrkY, hnB⟩ := ih (by omega)
      have hlt : B < A := by
        refine lt_of_le_of_ne hBA fun h => ?_
        rw [h] at hrkB
        omega
      obtain ⟨a, ha, haB⟩ := IsConcreteLE.exists_of_lt hlt
      set B' := extendBy hAc hA2 hBA ha with hB'
      have hBB' : B ≤ B' := le_extendBy
      have hB'A : B' ≤ A := extendBy_le
      have haB' : a ∈ B' := mem_extendBy_self
      have hd := hdisj B hBA h0B a ha haB
      have hsum := orbSum_extendBy (hAc := hAc) (hA2 := hA2) (hBA := hBA) (ha := ha) S
      rw [← hB'] at hsum
      have hrk2 : rk ↥(orbSum B' S) = 2 * rk ↥(orbSum B S) := by
        have h1 := rk_sup_add_rk_inf (orbSum B S) (a • orbSum B S)
        rw [hd, rk_bot, rk_smul] at h1
        rw [hsum]
        omega
      have hidx := nB_index_two (A := B') (A' := B) haB' (hA2 a ha)
        (fun x hx y hy => hAc x (hB'A hx) y (hB'A hy)) hBB'
        (fun x hx => mem_extendBy.1 hx) (P' := orbSum B S)
        (fun b q hq => smul_mem_orbSum b.2 hq) hd
      refine ⟨B', h0B.trans hBB', hB'A, by rw [hB', rk_extendBy haB, hrkB]; ring, ?_, ?_⟩
      · rw [hrk2, hrkY]
        ring
      · rw [hsum, hidx, hrkY]
        have : 2 ^ (n + 1) * rk ↥S = 2 ^ n * rk ↥S + 2 ^ n * rk ↥S := by ring
        omega
  have hrkA₀ : rk ↥A₀ ≤ rk ↥A := rk_mono hA₀A
  obtain ⟨B, -, hBA, hrkB, hrkY, hnB⟩ := key (rk ↥A - rk ↥A₀) le_rfl
  have hBeq : B = A := by
    refine Subgroup.eq_of_le_of_card_ge hBA ?_
    rw [card_eq_two_pow_of_isPGroup hAp, card_eq_two_pow_of_isPGroup (hAp.to_le hBA)]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hBeq] at hrkY hnB
  exact ⟨hrkY, hnB⟩

private theorem eq_one_of_smul_eq {B : Subgroup Γ} {S : Subgroup Q} {a : Γ}
    (hd : orbSum B S ⊓ a • orbSum B S = ⊥) {x : Q} (hx : x ∈ orbSum B S) (hax : a • x = x) :
    x = 1 := by
  have h1 : a • x ∈ a • orbSum B S := Subgroup.smul_mem_pointwise_smul _ _ _ hx
  rw [hax] at h1
  have h2 : x ∈ orbSum B S ⊓ a • orbSum B S := ⟨hx, h1⟩
  rwa [hd, Subgroup.mem_bot] at h2

private theorem div_mem_orbSum_extendBy {A : Subgroup Γ}
    {hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x} {hA2 : ∀ x ∈ A, x ^ 2 = 1} {B : Subgroup Γ}
    {hBA : B ≤ A} {a : Γ} {ha : a ∈ A} {S : Subgroup Q} {x : Q} (hx : x ∈ orbSum B S) :
    a • x / x ∈ orbSum (extendBy hAc hA2 hBA ha) S := by
  rw [orbSum_extendBy]
  exact Subgroup.div_mem _ (Subgroup.mem_sup_right (Subgroup.smul_mem_pointwise_smul _ _ _ hx))
    (Subgroup.mem_sup_left hx)

private theorem exists_not_mem_of_rk_lt [Finite Γ] {A B : Subgroup Γ} (hBA : B ≤ A)
    (hrk : rk ↥B < rk ↥A) : ∃ a ∈ A, a ∉ B := by
  have hlt : B < A := lt_of_le_of_ne hBA fun h => by rw [h] at hrk; omega
  exact IsConcreteLE.exists_of_lt hlt

theorem orbit_cubic [Finite Γ] {A : Subgroup Γ} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) {S Y : Subgroup Q} (hSY : S ≤ Y) (hS : S ≠ ⊥)
    (hcub : IsCubicOn A Y)
    (hdisj : ∀ B : Subgroup Γ, B ≤ A → stabIn A S ≤ B → ∀ a ∈ A, a ∉ B →
      orbSum B S ⊓ a • orbSum B S = ⊥) :
    rk ↥A - rk ↥(stabIn A S) ≤ 2 ∧
      (rk ↥A - rk ↥(stabIn A S) = 2 → ∀ c ∈ stabIn A S, ∀ s ∈ S, c • s = s) := by
  set A₀ := stabIn A S with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hA₀S : orbSum A₀ S = S := orbSum_stabIn A S
  have peel2 : ∀ (a₀ : Γ) (ha₀ : a₀ ∈ A), a₀ ∉ A₀ →
      ∀ (a₁ : Γ) (ha₁ : a₁ ∈ A), a₁ ∉ extendBy hAc hA2 hA₀A ha₀ →
      ∀ s ∈ S, a₁ • (a₀ • s / s) / (a₀ • s / s) = 1 → s = 1 := by
    intro a₀ ha₀ ha₀n a₁ ha₁ ha₁n s hs h
    set A₁ := extendBy hAc hA2 hA₀A ha₀ with hA₁
    have hA₀A₁ : A₀ ≤ A₁ := le_extendBy
    have hA₁A : A₁ ≤ A := extendBy_le
    have hsO : s ∈ orbSum A₀ S := by rw [hA₀S]; exact hs
    have hu : a₀ • s / s ∈ orbSum A₁ S := div_mem_orbSum_extendBy hsO
    have hu1 : a₀ • s / s = 1 :=
      eq_one_of_smul_eq (hdisj A₁ hA₁A hA₀A₁ a₁ ha₁ ha₁n) hu (div_eq_one.1 h)
    exact eq_one_of_smul_eq (hdisj A₀ hA₀A le_rfl a₀ ha₀ ha₀n) hsO (div_eq_one.1 hu1)
  refine ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    obtain ⟨a₀, ha₀, ha₀n⟩ := exists_not_mem_of_rk_lt hA₀A (by omega)
    set A₁ := extendBy hAc hA2 hA₀A ha₀ with hA₁
    have hrk₁ : rk ↥A₁ = rk ↥A₀ + 1 := rk_extendBy ha₀n
    have hA₁A : A₁ ≤ A := extendBy_le
    obtain ⟨a₁, ha₁, ha₁n⟩ := exists_not_mem_of_rk_lt hA₁A (by omega)
    set A₂ := extendBy hAc hA2 hA₁A ha₁ with hA₂
    have hrk₂ : rk ↥A₂ = rk ↥A₁ + 1 := rk_extendBy ha₁n
    have hA₂A : A₂ ≤ A := extendBy_le
    have hA₁A₂ : A₁ ≤ A₂ := le_extendBy
    have hA₀A₁ : A₀ ≤ A₁ := le_extendBy
    obtain ⟨a₂, ha₂, ha₂n⟩ := exists_not_mem_of_rk_lt hA₂A (by omega)
    obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS
    apply hs1
    have hsO : (s : Q) ∈ orbSum A₀ S := by rw [hA₀S]; exact hs
    have hu : a₀ • (s : Q) / s ∈ orbSum A₁ S := div_mem_orbSum_extendBy hsO
    have hv : a₁ • (a₀ • (s : Q) / s) / (a₀ • (s : Q) / s) ∈ orbSum A₂ S :=
      div_mem_orbSum_extendBy hu
    have hc := hcub a₀ ha₀ a₁ ha₁ a₂ ha₂ s (hSY hs)
    have hv1 := eq_one_of_smul_eq (hdisj A₂ hA₂A (hA₀A₁.trans hA₁A₂) a₂ ha₂ ha₂n) hv
      (div_eq_one.1 hc)
    exact Subtype.ext (peel2 a₀ ha₀ ha₀n a₁ ha₁ ha₁n s hs hv1)
  · intro he c hc s hs
    obtain ⟨a₀, ha₀, ha₀n⟩ := exists_not_mem_of_rk_lt hA₀A (by omega)
    set A₁ := extendBy hAc hA2 hA₀A ha₀ with hA₁
    have hrk₁ : rk ↥A₁ = rk ↥A₀ + 1 := rk_extendBy ha₀n
    have hA₁A : A₁ ≤ A := extendBy_le
    obtain ⟨a₁, ha₁, ha₁n⟩ := exists_not_mem_of_rk_lt hA₁A (by omega)
    have hcA : c ∈ A := hA₀A hc
    have hcS : c • s ∈ S := by
      rw [← (mem_stabIn.1 hc).2]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hs
    have hw : c • s / s ∈ S := Subgroup.div_mem _ hcS hs
    have e1 := hcub c hcA a₀ ha₀ a₁ ha₁ s (hSY hs)
    exact div_eq_one.1 (peel2 a₀ ha₀ ha₀n a₁ ha₁ ha₁n _ hw e1)

end Orbit

section Count

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem count_of_le_isoComp_of_conj [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {A : Subgroup Γ} (hA : IsPGroup 2 A)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) (hAI : ∀ a ∈ A, a • I = I) {Y : Subgroup Q}
    (hYΛ : XMod.IsInv ↥Λ Y) (hYA : ∀ a ∈ A, ∀ y ∈ Y, a • y ∈ Y)
    (hYI : Y ≤ isoComp ↥Λ I) :
    ∃ c : ℕ, rk ↥Y = c * rk ↥I ∧ c * nB A I ≤ nB A Y := by
  classical
  set H : Subgroup Γ := A ⊔ Λ with hH
  have hAImem : ∀ a ∈ A, ∀ v ∈ I, a • v ∈ I := by
    intro a ha v hv
    rw [← hAI a ha]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hv
  have hΛI : ∀ l ∈ Λ, ∀ v ∈ I, l • v ∈ I := fun l hl v hv => hI.1 ⟨l, hl⟩ v hv
  have hIH : ∀ g : ↥H, ∀ v ∈ I, g • v ∈ I := fun g => smul_mem_of_mem_sup hAImem hΛI g.2
  have hΛY : ∀ l ∈ Λ, ∀ y ∈ Y, l • y ∈ Y := fun l hl y hy => hYΛ ⟨l, hl⟩ y hy
  have hYH : ∀ g : ↥H, ∀ y ∈ Y, g • y ∈ Y := fun g => smul_mem_of_mem_sup hYA hΛY g.2
  let _iI := subAct (Γ := ↥H) I hIH
  let _iY := subAct (Γ := ↥H) Y hYH
  have hA' : IsPGroup 2 (A.subgroupOf H) := A4.isPGroup_subgroupOf_of_le le_sup_left hA
  have hAΛ' : ∀ a ∈ A.subgroupOf H, ∀ l ∈ Λ.subgroupOf H, a * l * a⁻¹ ∈ Λ.subgroupOf H :=
    fun a ha l hl => hAΛ a ha l hl
  have hgen : A.subgroupOf H ⊔ Λ.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hirr : ∀ J : Subgroup ↥I, (∀ l ∈ Λ.subgroupOf H, ∀ p ∈ J, l • p ∈ J) →
      J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    have hinv : XMod.IsInv ↥Λ (J.map I.subtype) := by
      rintro ⟨l, hl⟩ _ ⟨p, hp, rfl⟩
      have hlH : l ∈ H := (le_sup_right : Λ ≤ A ⊔ Λ) hl
      exact ⟨_, hJ ⟨l, hlH⟩ hl p hp, rfl⟩
    rcases hI.2.2 _ hinv bot_le (Subgroup.map_subtype_le J) with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective J I.subtype_injective).1 h
    · right
      rw [eq_top_iff]
      intro p _
      have : (p : Q) ∈ J.map I.subtype := by rw [h]; exact p.2
      obtain ⟨p', hp', he⟩ := this
      rwa [show p' = p from Subtype.ext he] at hp'
  have hYsq : ∀ y : ↥Y, y ^ 2 = 1 := fun y => Subtype.ext (by simpa using hQ y)
  have hgenQ : (⊤ : Subgroup ↥Y) ≤ ⨆ (φ : ↥I →* ↥Y)
      (_ : ∀ l ∈ Λ.subgroupOf H, ∀ p, φ (l • p) = l • φ p), φ.range := by
    have := isSemisimpleModule_toSubmod hI hYΛ hYI
    obtain ⟨c, ⟨e⟩⟩ := (isIsotypicOfType_toSubmod hI hYΛ hYI).linearEquiv_fun
    let f : Fin c → (↥(XMod.toSubmod hI.1) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥(XMod.toSubmod hYΛ)) :=
      fun i => e.symm.toLinearMap ∘ₗ
        LinearMap.single ↥(XMod.opRing ↥Λ Q) (fun _ => ↥(XMod.toSubmod hI.1)) i
    let φ : Fin c → (↥I →* ↥Y) := fun i =>
      { toFun := fun v => ⟨Additive.toMul (f i ⟨Additive.ofMul (v : Q), v.2⟩).1, (f i _).2⟩
        map_one' := by
          apply Subtype.ext
          show Additive.toMul (f i 0).1 = 1
          rw [map_zero]
          rfl
        map_mul' := fun v w => by
          apply Subtype.ext
          show Additive.toMul (f i (⟨Additive.ofMul (v : Q), v.2⟩ +
            ⟨Additive.ofMul (w : Q), w.2⟩)).1 = Additive.toMul (f i ⟨_, v.2⟩).1 *
              Additive.toMul (f i ⟨_, w.2⟩).1
          rw [map_add]
          rfl }
    have hφΛ : ∀ i, ∀ l ∈ Λ.subgroupOf H, ∀ p, φ i (l • p) = l • φ i p := by
      intro i l hl p
      apply Subtype.ext
      let ρ : ↥(XMod.opRing ↥Λ Q) :=
        ⟨XMod.actEnd ↥Λ Q ⟨((l : ↥H) : Γ), hl⟩, XMod.actEnd_mem_opRing _⟩
      have h1 : (⟨Additive.ofMul (((l • p : ↥I) : Q)), (l • p).2⟩ : ↥(XMod.toSubmod hI.1)) =
          ρ • ⟨Additive.ofMul (p : Q), p.2⟩ := Subtype.ext rfl
      have h2 : f i ⟨Additive.ofMul (((l • p : ↥I) : Q)), (l • p).2⟩ =
          ρ • f i ⟨Additive.ofMul (p : Q), p.2⟩ := by
        rw [h1, map_smul]
      exact congrArg (fun z : ↥(XMod.toSubmod hYΛ) => Additive.toMul z.1) h2
    intro y _
    set w := e ⟨Additive.ofMul (y : Q), y.2⟩ with hw
    have key : (⟨Additive.ofMul (y : Q), y.2⟩ : ↥(XMod.toSubmod hYΛ)) = ∑ i, f i (w i) := by
      rw [← e.symm_apply_apply ⟨Additive.ofMul (y : Q), y.2⟩, ← hw]
      conv_lhs => rw [← Finset.univ_sum_single w]
      exact _root_.map_sum e.symm.toLinearMap _ _
    have key2 : y = ∏ i, φ i ⟨Additive.toMul (w i).1, (w i).2⟩ := by
      apply Subtype.ext
      have h1 := congrArg (fun z : ↥(XMod.toSubmod hYΛ) => Additive.toMul (z : Additive Q)) key
      simp only [toMul_ofMul] at h1
      rw [h1, Submodule.coe_sum, toMul_sum, SubmonoidClass.coe_finsetProd]
      rfl
    rw [key2]
    exact Subgroup.prod_mem _ fun i _ =>
      (le_iSup₂_of_le (φ i) (hφΛ i) le_rfl : (φ i).range ≤ _) ⟨_, rfl⟩
  obtain ⟨c, hc1, hc2⟩ := count_of_homs hA' hAΛ' hgen hirr (Nat.card ↥Y) ↥Y rfl hYsq hgenQ
  refine ⟨c, hc1, ?_⟩
  rw [nB_top_subAct I hIH A le_sup_left, nB_top_subAct Y hYH A le_sup_left] at hc2
  exact hc2

end Count

section Decomp

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private def isoIn (X : Subgroup Γ) (Y L : Subgroup Q) : Subgroup Q :=
  ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J ∧ XMod.Iso ↥X J L), J

private def offOrb (P X : Subgroup Γ) (Y L : Subgroup Q) : Subgroup Q :=
  ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J ∧ ∀ a ∈ P, ¬ XMod.Iso ↥X J (a • L)), J

private theorem le_isoIn {X : Subgroup Γ} {Y L J : Subgroup Q} (hJY : J ≤ Y)
    (hJ : XMod.IsIrr ↥X J) (hJL : XMod.Iso ↥X J L) : J ≤ isoIn X Y L :=
  le_iSup₂_of_le J ⟨hJY, hJ, hJL⟩ le_rfl

private theorem isoIn_le (X : Subgroup Γ) (Y L : Subgroup Q) : isoIn X Y L ≤ Y :=
  iSup₂_le fun _ hJ => hJ.1

private theorem isoIn_le_isoComp (X : Subgroup Γ) (Y L : Subgroup Q) :
    isoIn X Y L ≤ isoComp ↥X L :=
  iSup₂_le fun _ hJ => le_isoComp hJ.2.1 hJ.2.2

private theorem isInv_isoIn (X : Subgroup Γ) (Y L : Subgroup Q) :
    XMod.IsInv ↥X (isoIn X Y L) :=
  XMod.isInv_iSup fun _ => XMod.isInv_iSup fun hJ => hJ.2.1.1

private theorem le_offOrb {P X : Subgroup Γ} {Y L J : Subgroup Q} (hJY : J ≤ Y)
    (hJ : XMod.IsIrr ↥X J) (hJL : ∀ a ∈ P, ¬ XMod.Iso ↥X J (a • L)) : J ≤ offOrb P X Y L :=
  le_iSup₂_of_le J ⟨hJY, hJ, hJL⟩ le_rfl

private theorem offOrb_le (P X : Subgroup Γ) (Y L : Subgroup Q) : offOrb P X Y L ≤ Y :=
  iSup₂_le fun _ hJ => hJ.1

private theorem isInv_offOrb (P X : Subgroup Γ) (Y L : Subgroup Q) :
    XMod.IsInv ↥X (offOrb P X Y L) :=
  XMod.isInv_iSup fun _ => XMod.isInv_iSup fun hJ => hJ.2.1.1

private theorem smul_eq_map (x : Γ) (T : Subgroup Q) :
    x • T = T.map (MulDistribMulAction.toMonoidHom Q x) :=
  rfl

private theorem smul_iSup' {ι : Sort*} (g : Γ) (T : ι → Subgroup Q) :
    g • (⨆ i, T i) = ⨆ i, g • T i := by
  rw [smul_eq_map, Subgroup.map_iSup]
  rfl

private theorem exists_iso_of_le_iSup_smul [Finite Q] {X : Subgroup Γ} {ι : Type*} (g : ι → Γ)
    (hg : ∀ i, g i ∈ Subgroup.normalizer (X : Set Γ)) {Y L J' : Subgroup Q}
    (hJ' : XMod.IsIrr ↥X J') (hle : J' ≤ ⨆ i, g i • isoIn X Y L) :
    ∃ i, XMod.Iso ↥X J' (g i • L) := by
  have hN := normalizes_normalizer (Q := Q) X
  let F := {J : Subgroup Q // J ≤ Y ∧ XMod.IsIrr ↥X J ∧ XMod.Iso ↥X J L}
  have e1 : isoIn X Y L = ⨆ J : F, (J : Subgroup Q) := by
    unfold isoIn
    exact iSup_subtype'
  have e : (⨆ i, g i • isoIn X Y L) = ⨆ p : ι × F, g p.1 • (p.2 : Subgroup Q) := by
    rw [iSup_prod]
    refine iSup_congr fun i => ?_
    rw [e1, smul_iSup']
  rw [e] at hle
  obtain ⟨p, hiso⟩ := exists_iso_of_le_iSup
    (S := fun p : ι × F => g p.1 • (p.2 : Subgroup Q))
    (fun p => isIrr_smul hN ⟨g p.1, hg p.1⟩ p.2.2.2.1) hJ' hle
  exact ⟨p.1, XMod.Iso.trans hiso (XMod.iso_smul hN ⟨g p.1, hg p.1⟩ p.2.2.2.2)⟩

variable [Finite Q] {P X : Subgroup Γ} (hPN : P ≤ Subgroup.normalizer (X : Set Γ))
  {Y L : Subgroup Q} (hYP : ∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y)

omit [Finite Q] in
include hYP in
private theorem smul_le_of_le {a : Γ} (ha : a ∈ P) {J : Subgroup Q} (hJY : J ≤ Y) : a • J ≤ Y := by
  intro q hq
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hq
  have h1 := hYP a ha _ (hJY hq)
  rwa [smul_inv_smul] at h1

include hPN hYP in
private theorem stabIn_isoIn (hL : XMod.IsIrr ↥X L) (hLY : L ≤ Y)
    (hhom : ∀ t ∈ P, XMod.Iso ↥X (t • L) L → t • L = L) :
    stabIn P (isoIn X Y L) = stabIn P L := by
  have hN := normalizes_normalizer (Q := Q) X
  ext a
  rw [mem_stabIn, mem_stabIn]
  constructor
  · rintro ⟨ha, haS⟩
    refine ⟨ha, hhom a ha ?_⟩
    have h1 : a • L ≤ isoIn X Y L := by
      rw [← haS]
      exact (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2
        (le_isoIn hLY hL (XMod.Iso.refl L))
    exact SmithD39Two.iso_of_le_isoComp (isIrr_smul hN ⟨a, hPN ha⟩ hL)
      (h1.trans (isoIn_le_isoComp X Y L))
  · rintro ⟨ha, haL⟩
    refine ⟨ha, ?_⟩
    have hle : a • isoIn X Y L ≤ isoIn X Y L := by
      unfold isoIn
      rw [smul_iSup']
      refine iSup_le fun J => ?_
      rw [smul_iSup']
      refine iSup_le fun hJ => ?_
      refine le_isoIn (smul_le_of_le hYP ha hJ.1) (isIrr_smul hN ⟨a, hPN ha⟩ hJ.2.1) ?_
      have h2 := XMod.iso_smul hN ⟨a, hPN ha⟩ hJ.2.2
      change XMod.Iso ↥X (a • J) (a • L) at h2
      rwa [haL] at h2
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_congr (XMod.smulEquiv a (isoIn X Y L)).toEquiv.symm]

include hPN in
private theorem orbSum_isoIn_inf_smul_eq_bot (hL : XMod.IsIrr ↥X L)
    (hhom : ∀ t ∈ P, XMod.Iso ↥X (t • L) L → t • L = L) {B : Subgroup Γ} (hBP : B ≤ P)
    (hstab : stabIn P L ≤ B) {a : Γ} (ha : a ∈ P) (haB : a ∉ B) :
    orbSum B (isoIn X Y L) ⊓ a • orbSum B (isoIn X Y L) = ⊥ := by
  have hN := normalizes_normalizer (Q := Q) X
  have hinv1 : XMod.IsInv ↥X (orbSum B (isoIn X Y L)) :=
    isInv_orbSum (hBP.trans hPN) (isInv_isoIn X Y L)
  have hinv2 : XMod.IsInv ↥X (a • orbSum B (isoIn X Y L)) := isModInv_smul (hPN ha) hinv1
  by_contra hne
  obtain ⟨J', hJ'X, hJ'⟩ := exists_isIrr_le (hinv1.inf hinv2) hne
  obtain ⟨⟨t, ht⟩, hiso1⟩ := exists_iso_of_le_iSup_smul (fun t : ↥B => (t : Γ))
    (fun t => hPN (hBP t.2)) hJ' (hJ'X.trans inf_le_left)
  have h2 : J' ≤ ⨆ t : ↥B, (a * (t : Γ)) • isoIn X Y L := by
    rw [← smul_orbSum]
    exact hJ'X.trans inf_le_right
  obtain ⟨⟨t', ht'⟩, hiso2⟩ := exists_iso_of_le_iSup_smul (fun t : ↥B => a * (t : Γ))
    (fun t => Subgroup.mul_mem _ (hPN ha) (hPN (hBP t.2))) hJ' h2
  have hiso : XMod.Iso ↥X (t • L) ((a * t') • L) :=
    (XMod.Iso.symm hJ'.1 hiso1).trans hiso2
  have hiso3 := XMod.iso_smul hN ⟨t⁻¹, hPN (P.inv_mem (hBP ht))⟩ hiso
  change XMod.Iso ↥X (t⁻¹ • t • L) (t⁻¹ • (a * t') • L) at hiso3
  rw [smul_smul, smul_smul, inv_mul_cancel, one_smul] at hiso3
  have hmem : t⁻¹ * (a * t') ∈ P := P.mul_mem (P.inv_mem (hBP ht)) (P.mul_mem ha (hBP ht'))
  have h4 := hhom _ hmem (XMod.Iso.symm hL.1 hiso3)
  have h5 : t⁻¹ * (a * t') ∈ B := hstab ⟨hmem, h4⟩
  apply haB
  have := B.mul_mem (B.mul_mem ht h5) (B.inv_mem ht')
  rwa [mul_inv_cancel_left, mul_inv_cancel_right] at this


omit [Finite Q] in
include hPN hYP in
private theorem le_orbSum_isoIn_sup_offOrb
    (hss : Y ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J), J) :
    Y ≤ orbSum P (isoIn X Y L) ⊔ offOrb P X Y L := by
  have hN := normalizes_normalizer (Q := Q) X
  refine hss.trans (iSup₂_le fun J hJ => ?_)
  by_cases h : ∃ a ∈ P, XMod.Iso ↥X J (a • L)
  · obtain ⟨a, ha, hiso⟩ := h
    refine le_sup_of_le_left ?_
    have h1 : a⁻¹ • J ≤ isoIn X Y L := by
      refine le_isoIn (smul_le_of_le hYP (P.inv_mem ha) hJ.1)
        (isIrr_smul hN ⟨a⁻¹, hPN (P.inv_mem ha)⟩ hJ.2) ?_
      have h2 := XMod.iso_smul hN ⟨a⁻¹, hPN (P.inv_mem ha)⟩ hiso
      change XMod.Iso ↥X (a⁻¹ • J) (a⁻¹ • a • L) at h2
      rwa [inv_smul_smul] at h2
    have h3 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2 h1
    rw [smul_inv_smul] at h3
    exact h3.trans (smul_le_orbSum _ ha)
  · push Not at h
    exact le_sup_of_le_right (le_offOrb hJ.1 hJ.2 h)

include hPN in
private theorem orbSum_isoIn_inf_offOrb :
    orbSum P (isoIn X Y L) ⊓ offOrb P X Y L = ⊥ := by
  have hinv1 : XMod.IsInv ↥X (orbSum P (isoIn X Y L)) := isInv_orbSum hPN (isInv_isoIn X Y L)
  have hinv2 := isInv_offOrb P X Y L
  by_contra hne
  obtain ⟨J', hJ'X, hJ'⟩ := exists_isIrr_le (hinv1.inf hinv2) hne
  obtain ⟨⟨t, ht⟩, hiso1⟩ := exists_iso_of_le_iSup_smul (fun t : ↥P => (t : Γ))
    (fun t => hPN t.2) hJ' (hJ'X.trans inf_le_left)
  let F := {J : Subgroup Q // J ≤ Y ∧ XMod.IsIrr ↥X J ∧ ∀ a ∈ P, ¬ XMod.Iso ↥X J (a • L)}
  have e1 : offOrb P X Y L = ⨆ J : F, (J : Subgroup Q) := by
    unfold offOrb
    exact iSup_subtype'
  have h2 : J' ≤ ⨆ J : F, (J : Subgroup Q) := e1 ▸ (hJ'X.trans inf_le_right)
  obtain ⟨⟨J'', hJ''Y, hJ'', hno⟩, hiso2⟩ := exists_iso_of_le_iSup
    (S := fun J : F => (J : Subgroup Q)) (fun J => J.2.2.1) hJ' h2
  exact hno t ht ((XMod.Iso.symm hJ'.1 hiso2).trans hiso1)

omit [Finite Q] in
include hPN hYP in
private theorem smul_mem_offOrb {b : Γ} (hb : b ∈ P) {y : Q} (hy : y ∈ offOrb P X Y L) :
    b • y ∈ offOrb P X Y L := by
  have hN := normalizes_normalizer (Q := Q) X
  have hle : b • offOrb P X Y L ≤ offOrb P X Y L := by
    unfold offOrb
    rw [smul_iSup']
    refine iSup_le fun J => ?_
    rw [smul_iSup']
    refine iSup_le fun hJ => ?_
    refine le_offOrb (smul_le_of_le hYP hb hJ.1) (isIrr_smul hN ⟨b, hPN hb⟩ hJ.2.1) ?_
    intro a ha hiso
    have h2 := XMod.iso_smul hN ⟨b⁻¹, hPN (P.inv_mem hb)⟩ hiso
    change XMod.Iso ↥X (b⁻¹ • b • J) (b⁻¹ • a • L) at h2
    rw [inv_smul_smul, smul_smul] at h2
    exact hJ.2.2 _ (P.mul_mem (P.inv_mem hb) ha) h2
  exact hle (Subgroup.smul_mem_pointwise_smul _ _ _ hy)

omit [Finite Q] in
include hYP in
private theorem orbSum_isoIn_le : orbSum P (isoIn X Y L) ≤ Y :=
  iSup_le fun t => smul_le_of_le hYP t.2 (isoIn_le X Y L)

end Decomp

section FL

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private theorem nB_eq_zero_of_fix {B : Subgroup Γ} {J : Subgroup Q}
    (h : ∀ b ∈ B, ∀ j ∈ J, b • j = j) : nB B J = 0 := by
  unfold nB
  have : J ⊓ XMod.fixed ↥B (⊤ : Subgroup Q) = J :=
    inf_eq_left.2 fun j hj => XMod.mem_fixed.2 ⟨trivial, fun b => h b b.2 j hj⟩
  rw [this, Nat.sub_self]

variable [Finite Γ] [Finite Q]

private theorem orbit_bound (hQ : ∀ q : Q, q ^ 2 = 1) {P X : Subgroup Γ}
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : ∀ a ∈ P, a ^ 2 = 1)
    (hPX : ∀ a ∈ P, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {Y : Subgroup Q}
    (hYP : ∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y) (hcub : IsCubicOn P Y)
    {d : ℕ} (hd3 : 3 ≤ d) (hd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → rk ↥J = d)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hrat : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J →
      q * (mRel (stabIn P J) X : ℚ) ≤ nB (stabIn P J) J)
    (htwo : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → stabIn P J ≠ P →
      q * ((mRel (stabIn P J) X : ℚ) + 2) ≤ d)
    {L : Subgroup Q} (hL : XMod.IsIrr ↥X L) (hLY : L ≤ Y)
    (hhom : ∀ t ∈ P, XMod.Iso ↥X (t • L) L → t • L = L) :
    q * (mRel P X : ℚ) * rk ↥(orbSum P (isoIn X Y L)) ≤ d * nB P (orbSum P (isoIn X Y L)) ∧
      ((∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → 0 < mRel (stabIn P J) X →
          q * (mRel (stabIn P J) X : ℚ) < nB (stabIn P J) J) → 0 < mRel P X →
        q * (mRel P X : ℚ) * rk ↥(orbSum P (isoIn X Y L)) <
          d * nB P (orbSum P (isoIn X Y L))) := by
  have hPN : P ≤ Subgroup.normalizer (X : Set Γ) := fun a ha => mem_normalizer_of_conj hPX ha
  set S := isoIn X Y L with hSdef
  set Pσ := stabIn P L with hPσ
  have hSst : stabIn P S = Pσ := stabIn_isoIn hPN hYP hL hLY hhom
  have hdisj : ∀ B : Subgroup Γ, B ≤ P → stabIn P S ≤ B → ∀ a ∈ P, a ∉ B →
      orbSum B S ⊓ a • orbSum B S = ⊥ := fun B hB h a ha haB =>
    orbSum_isoIn_inf_smul_eq_bot hPN hL hhom hB (by rw [hSst] at h; exact h) ha haB
  obtain ⟨hrkO, hnO⟩ := nB_orbit_gen hPc hP2 hdisj
  have hLS : L ≤ S := le_isoIn hLY hL (XMod.Iso.refl L)
  have hSne : S ≠ ⊥ := fun h => hL.2.1.ne' (le_bot_iff.1 (h ▸ hLS))
  obtain ⟨he2, htriv⟩ := orbit_cubic hPc hP2 (isoIn_le X Y L) hSne hcub hdisj
  rw [hSst] at hrkO hnO he2 htriv
  have hPσP : Pσ ≤ P := inf_le_left
  have hPσp : IsPGroup 2 ↥Pσ := fun x => ⟨1, Subtype.ext (by simpa using hP2 x (hPσP x.2))⟩
  have hPσX : ∀ a ∈ Pσ, ∀ x ∈ X, a * x * a⁻¹ ∈ X := fun a ha => hPX a (hPσP ha)
  have hPσL : ∀ a ∈ Pσ, a • L = L := fun a ha => (mem_stabIn.1 ha).2
  have hSPσ : ∀ a ∈ Pσ, ∀ y ∈ S, a • y ∈ S := by
    intro a ha y hy
    have ha' : a ∈ stabIn P S := by rw [hSst]; exact ha
    rw [← (mem_stabIn.1 ha').2]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hy
  obtain ⟨c, hc1, hc2⟩ := count_of_le_isoComp_of_conj hQ hL hPσp hPσX hPσL
    (isInv_isoIn X Y L) hSPσ (isoIn_le_isoComp X Y L)
  have hrkL : rk ↥L = d := hd L hLY hL
  rw [hrkL] at hc1
  have hrkS0 : rk ↥S ≠ 0 := fun h => hSne ((rk_eq_zero_iff hQ).1 h)
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hc1; exact absurd hc1 hrkS0
    · exact h
  have hCX : P ⊓ Subgroup.centralizer (X : Set Γ) ≤ Pσ := by
    rintro x ⟨hxP, hxC⟩
    refine ⟨hxP, hhom x hxP ?_⟩
    exact iso_smul_of_comm hL.1 fun l hl => ((Subgroup.mem_centralizer_iff.1 hxC) l hl).symm
  have hPσC : Pσ ⊓ Subgroup.centralizer (X : Set Γ) = P ⊓ Subgroup.centralizer (X : Set Γ) :=
    le_antisymm (inf_le_inf_right _ hPσP) (le_inf hCX inf_le_right)
  have hrk1 : rk ↥(P ⊓ Subgroup.centralizer (X : Set Γ)) ≤ rk ↥Pσ := rk_mono hCX
  have hrk2 : rk ↥Pσ ≤ rk ↥P := rk_mono hPσP
  have hmrel : mRel P X = (rk ↥P - rk ↥Pσ) + mRel Pσ X := by
    unfold mRel
    rw [hPσC]
    omega
  have hrL := hrat L hLY hL
  rw [← hPσ] at hrL
  set e := rk ↥P - rk ↥Pσ with he
  set m₀ := mRel Pσ X with hm₀
  have hd0 : (3 : ℚ) ≤ d := by exact_mod_cast hd3
  have hc0' : (1 : ℚ) ≤ c := by exact_mod_cast hc0
  have hm₀0 : (0 : ℚ) ≤ m₀ := by positivity
  have hn0 : (0 : ℚ) ≤ nB Pσ L := by positivity
  have hc2' : (c : ℚ) * nB Pσ L ≤ nB Pσ S := by exact_mod_cast hc2
  rw [hmrel, hrkO, hc1]
  rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2) with h0 | h1 | h2
  ·
    rw [h0] at hnO ⊢
    have hNP : nB P (orbSum P S) = nB Pσ S := by simp at hnO; omega
    rw [hNP]
    push_cast
    refine ⟨?_, fun hstrict hm => ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_right hrL (by positivity : (0 : ℚ) ≤ c * d)]
    · have hm₀' : 0 < m₀ := by simpa using hm
      have hs := hstrict L hLY hL (by rw [← hPσ]; exact hm₀')
      rw [← hPσ] at hs
      nlinarith [mul_lt_mul_of_pos_right hs (by positivity : (0 : ℚ) < c * d)]
  ·
    rw [h1] at hnO ⊢
    have hNP : nB P (orbSum P S) = c * d + nB Pσ S := by
      have : 2 ^ 1 * (c * d) = c * d + c * d := by ring
      rw [hc1, this] at hnO
      omega
    rw [hNP]
    have hne : Pσ ≠ P := fun h => by rw [h] at he; omega
    have ht := htwo L hLY hL hne
    rw [← hPσ] at ht
    push_cast
    refine ⟨?_, fun hstrict hm => ?_⟩
    · nlinarith [mul_le_mul_of_nonneg_right (add_le_add ht hrL) (by positivity : (0 : ℚ) ≤ c * d)]
    · rcases Nat.eq_zero_or_pos m₀ with hz | hpos
      · have hz' : (m₀ : ℚ) = 0 := by exact_mod_cast hz
        rw [hz']
        nlinarith [mul_pos (by positivity : (0 : ℚ) < c) (by positivity : (0 : ℚ) < d)]
      · have hs := hstrict L hLY hL (by rw [← hPσ]; exact hpos)
        rw [← hPσ] at hs
        nlinarith [mul_lt_mul_of_pos_right (add_lt_add_of_le_of_lt ht hs)
          (by positivity : (0 : ℚ) < c * d)]
  ·
    rw [h2] at hnO ⊢
    have hN0 : nB Pσ S = 0 := nB_eq_zero_of_fix (htriv h2)
    have hn0' : nB Pσ L = 0 :=
      nB_eq_zero_of_fix fun b hb j hj => htriv h2 b hb j (hLS hj)
    have hNP : nB P (orbSum P S) = 3 * (c * d) := by
      rw [hN0, hc1] at hnO
      omega
    rw [hNP]
    rw [hn0'] at hrL
    have hqm : q * m₀ = 0 := le_antisymm (by simpa using hrL) (by positivity)
    push_cast
    refine ⟨?_, fun _ _ => ?_⟩
    · nlinarith [mul_pos (by positivity : (0 : ℚ) < c) (by positivity : (0 : ℚ) < d)]
    · nlinarith [mul_pos (by positivity : (0 : ℚ) < c) (by positivity : (0 : ℚ) < d)]

private theorem fl_core (hQ : ∀ q : Q, q ^ 2 = 1) {P X : Subgroup Γ}
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : ∀ a ∈ P, a ^ 2 = 1)
    (hPX : ∀ a ∈ P, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {d : ℕ} (hd3 : 3 ≤ d) {q : ℚ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ∀ (n : ℕ) (Y : Subgroup Q), Nat.card ↥Y = n →
      (∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y) → (∀ x ∈ X, ∀ y ∈ Y, x • y ∈ Y) → IsCubicOn P Y →
      (Y ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J), J) →
      (∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → rk ↥J = d) →
      (∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J →
        q * (mRel (stabIn P J) X : ℚ) ≤ nB (stabIn P J) J) →
      (∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → stabIn P J ≠ P →
        q * ((mRel (stabIn P J) X : ℚ) + 2) ≤ d) →
      q * (mRel P X : ℚ) * rk ↥Y ≤ d * nB P Y ∧
        ((∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → 0 < mRel (stabIn P J) X →
            q * (mRel (stabIn P J) X : ℚ) < nB (stabIn P J) J) → 0 < mRel P X → Y ≠ ⊥ →
          q * (mRel P X : ℚ) * rk ↥Y < d * nB P Y) := by
  have hPN : P ≤ Subgroup.normalizer (X : Set Γ) := fun a ha => mem_normalizer_of_conj hPX ha
  have hNA := normalizes_of_conj (Q := Q) hPX
  have hPp : IsPGroup 2 ↥P := fun x => ⟨1, Subtype.ext (by simpa using hP2 x x.2)⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hn hYP hYX hcub hss hd hrat htwo
  have hYXi : XMod.IsInv ↥X Y := fun a y hy => hYX a a.2 y hy
  by_cases hY : Y = ⊥
  · subst hY
    have h0 : nB P (⊥ : Subgroup Q) = 0 :=
      nB_eq_zero_of_fix fun b _ j hj => by rw [Subgroup.mem_bot.1 hj, smul_one]
    rw [rk_bot, h0]
    exact ⟨by simp, fun _ _ h => absurd rfl h⟩
  obtain ⟨J₀, hJ₀Y, hJ₀⟩ := exists_isIrr_le hYXi hY
  obtain ⟨L, hLle, hL, -, hhc⟩ := XMod.exists_isHomComp_of_isIrr hQ hNA hPp hJ₀
  have hhom : ∀ t ∈ P, XMod.Iso ↥X (t • L) L → t • L = L := fun t ht hiso =>
    (XMod.forall_iso_smul_eq_iff_isHomComp hNA hL).2 hhc ⟨t, ht⟩ hiso
  have hLY : L ≤ Y := by
    refine hLle.trans (iSup_le fun t => ?_)
    intro y hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have h1 := hYP _ t.2 _ (hJ₀Y hy)
    change (t : Γ) • ((t : Γ)⁻¹ • y) ∈ Y at h1
    rwa [smul_inv_smul] at h1
  set Y₁ := orbSum P (isoIn X Y L) with hY₁
  set Y₂ := offOrb P X Y L with hY₂
  have hsup : Y₁ ⊔ Y₂ = Y :=
    le_antisymm (sup_le (orbSum_isoIn_le hYP) (offOrb_le P X Y L))
      (le_orbSum_isoIn_sup_offOrb hPN hYP hss)
  have hinf : Y₁ ⊓ Y₂ = ⊥ := orbSum_isoIn_inf_offOrb hPN
  have hLY₁ : L ≤ Y₁ := (le_isoIn hLY hL (XMod.Iso.refl L)).trans (le_orbSum P _)
  have hY₂Y : Y₂ ≤ Y := offOrb_le P X Y L
  have hY₂ne : Y₂ ≠ Y := by
    intro h
    have : L ≤ Y₁ ⊓ Y₂ := le_inf hLY₁ (h ▸ hLY)
    rw [hinf] at this
    exact hL.2.1.ne' (le_bot_iff.1 this)
  have hlt : Nat.card ↥Y₂ < n := by
    rw [← hn]
    refine lt_of_le_of_ne (Subgroup.card_le_of_le hY₂Y) fun h => hY₂ne ?_
    exact Subgroup.eq_of_le_of_card_ge hY₂Y h.ge
  have hY₂P : ∀ a ∈ P, ∀ y ∈ Y₂, a • y ∈ Y₂ := fun a ha y hy => smul_mem_offOrb hPN hYP ha hy
  have hY₂X : ∀ x ∈ X, ∀ y ∈ Y₂, x • y ∈ Y₂ := fun x hx y hy =>
    isInv_offOrb P X Y L ⟨x, hx⟩ y hy
  have hss₂ : Y₂ ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y₂ ∧ XMod.IsIrr ↥X J), J := by
    refine iSup₂_le fun J hJ => le_iSup₂_of_le J ⟨le_offOrb hJ.1 hJ.2.1 hJ.2.2, hJ.2.1⟩ le_rfl
  obtain ⟨h2a, -⟩ := ih _ hlt Y₂ rfl hY₂P hY₂X
    (fun a ha b hb c hc y hy => hcub a ha b hb c hc y (hY₂Y hy)) hss₂
    (fun J hJ => hd J (hJ.trans hY₂Y)) (fun J hJ => hrat J (hJ.trans hY₂Y))
    (fun J hJ => htwo J (hJ.trans hY₂Y))
  obtain ⟨h1a, h1b⟩ := orbit_bound hQ hPc hP2 hPX hYP hcub hd3 hd hq0 hq1 hrat htwo hL hLY hhom
  have hY₁P : ∀ a ∈ P, ∀ y ∈ Y₁, a • y ∈ Y₁ := fun a ha y hy => smul_mem_orbSum ha hy
  have hnB : nB P Y = nB P Y₁ + nB P Y₂ := by
    rw [← hsup]
    exact nB_sup_of_disjoint P (fun a y hy => hY₁P a a.2 y hy) (fun a y hy => hY₂P a a.2 y hy)
      hinf
  have hrk : rk ↥Y = rk ↥Y₁ + rk ↥Y₂ := by
    have h := rk_sup_add_rk_inf Y₁ Y₂
    rw [hinf, rk_bot, hsup] at h
    omega
  rw [hnB, hrk]
  push_cast
  refine ⟨by nlinarith, fun hstrict hm _ => ?_⟩
  have := h1b hstrict hm
  nlinarith

theorem nB_ge_of_constituents (hQ : ∀ q : Q, q ^ 2 = 1)
    {P X : Subgroup Γ} (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : ∀ a ∈ P, a ^ 2 = 1)
    (hPX : ∀ a ∈ P, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {Y : Subgroup Q}
    (hYP : ∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y) (hYX : ∀ x ∈ X, ∀ y ∈ Y, x • y ∈ Y)
    (hcub : IsCubicOn P Y) (hss : Y ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J), J)
    {d : ℕ} (hd3 : 3 ≤ d) (hd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → rk ↥J = d)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hrat : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J →
      q * (mRel (stabIn P J) X : ℚ) ≤ nB (stabIn P J) J)
    (htwo : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → stabIn P J ≠ P →
      q * ((mRel (stabIn P J) X : ℚ) + 2) ≤ d) :
    q * (mRel P X : ℚ) * rk ↥Y ≤ d * nB P Y :=
  (fl_core hQ hPc hP2 hPX hd3 hq0 hq1 _ Y rfl hYP hYX hcub hss hd hrat htwo).1

theorem nB_gt_of_constituents (hQ : ∀ q : Q, q ^ 2 = 1)
    {P X : Subgroup Γ} (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : ∀ a ∈ P, a ^ 2 = 1)
    (hPX : ∀ a ∈ P, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {Y : Subgroup Q}
    (hYP : ∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y) (hYX : ∀ x ∈ X, ∀ y ∈ Y, x • y ∈ Y)
    (hcub : IsCubicOn P Y) (hss : Y ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J), J)
    {d : ℕ} (hd3 : 3 ≤ d) (hd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → rk ↥J = d)
    {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hrat : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J →
      q * (mRel (stabIn P J) X : ℚ) ≤ nB (stabIn P J) J)
    (htwo : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → stabIn P J ≠ P →
      q * ((mRel (stabIn P J) X : ℚ) + 2) ≤ d)
    (hstrict : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → 0 < mRel (stabIn P J) X →
      q * (mRel (stabIn P J) X : ℚ) < nB (stabIn P J) J)
    (hm : 0 < mRel P X) (hY : Y ≠ ⊥) :
    q * (mRel P X : ℚ) * rk ↥Y < d * nB P Y :=
  (fl_core hQ hPc hP2 hPX hd3 hq0 hq1 _ Y rfl hYP hYX hcub hss hd hrat htwo).2 hstrict hm hY

end FL

section Hyp

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q] {X : Subgroup Γ}

theorem le_iSup_isIrr_of_iSup {ι : Sort*} {S : ι → Subgroup Q} (hS : ∀ i, XMod.IsIrr ↥X (S i)) :
    (⨆ i, S i) ≤ ⨆ (J : Subgroup Q) (_ : J ≤ ⨆ i, S i ∧ XMod.IsIrr ↥X J), J :=
  iSup_le fun i => le_iSup₂_of_le (S i) ⟨le_iSup S i, hS i⟩ le_rfl

theorem rk_eq_of_le_iSup [Finite Q] {ι : Type*} {S : ι → Subgroup Q}
    (hS : ∀ i, XMod.IsIrr ↥X (S i)) {d : ℕ} (hd : ∀ i, rk ↥(S i) = d) {J : Subgroup Q}
    (hJ : XMod.IsIrr ↥X J) (hJS : J ≤ ⨆ i, S i) : rk ↥J = d := by
  obtain ⟨i, hi⟩ := exists_iso_of_le_iSup hS hJ hJS
  unfold rk
  rw [card_eq_of_iso hi]
  exact hd i

theorem isCubicOn_qAct {W : Type} [CommGroup W] {M L : Subgroup (MulAut W)}
    (hML : M ≤ Subgroup.normalizer (L : Set (MulAut W))) {A : Subgroup (MulAut W)}
    (hA : commSeries A 3 = ⊥) (Y : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) :
    letI := qAct hML
    IsCubicOn (A.subgroupOf M) Y := by
  let _i := qAct hML
  intro a ha b hb c hc y _
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
  have key : ∀ (g : ↥M) (v : W), g • (QuotientGroup.mk v : W ⧸ modFix L (⊤ : Subgroup W)) =
      QuotientGroup.mk ((g : MulAut W) v) := fun _ _ => rfl
  simp only [key, ← QuotientGroup.mk_div]
  set u := (a : MulAut W) w / w with hu
  set v := (b : MulAut W) u / u with hv
  have hu' : u ∈ commSeries A 1 := by
    show u ∈ commSub ⊤ A
    exact Subgroup.subset_closure ⟨a, ha, w, trivial, by rw [hu, div_eq_mul_inv]⟩
  have hv' : v ∈ commSeries A 2 :=
    Subgroup.subset_closure ⟨b, hb, u, hu', by rw [hv, div_eq_mul_inv]⟩
  have hz : (c : MulAut W) v / v ∈ commSeries A 3 :=
    Subgroup.subset_closure ⟨c, hc, v, hv', by rw [div_eq_mul_inv]⟩
  rw [hA, Subgroup.mem_bot] at hz
  rw [hz]
  rfl

end Hyp

section NotFF

variable {Γ : Type*} [Group Γ] [Finite Γ] {Q : Type*} [CommGroup Q] [Finite Q]
  [MulDistribMulAction Γ Q]

omit [Finite Γ] in
private theorem rk_fixV_pos {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {E : Subgroup (MulAut V)} (hE : IsPGroup 2 E) (hrk : 0 < rk V) : 0 < rk (fixV E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_card_fixV hE
  rw [card_eq_two_pow_rk hV, card_eq_two_pow hV] at hmod
  by_contra h0
  have h0' : rk (fixV E) = 0 := by omega
  rw [h0'] at hmod
  have h1 : 2 ^ rk V ≡ 1 [MOD 2] := by simpa using hmod
  have h2 : 2 ∣ 2 ^ rk V := dvd_pow_self 2 (by omega)
  have h3 : (2 ^ rk V) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2
  have h4 : (2 ^ rk V) % 2 = 1 % 2 := h1
  omega

omit [Finite Γ] [Finite Q] in
theorem commute_of_fix_of_faithful {X : Subgroup Γ} {J : Subgroup Q}
    (hJX : ∀ x ∈ X, ∀ j ∈ J, x • j ∈ J) (hfaith : ∀ x ∈ X, (∀ j ∈ J, x • j = j) → x = 1)
    {a : Γ} (haX : ∀ x ∈ X, a * x * a⁻¹ ∈ X) (haJ : ∀ j ∈ J, a • j = j) :
    ∀ x ∈ X, x * a = a * x := by
  intro x hx
  have hmem : x * a * x⁻¹ * a⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem hx (by simpa [mul_assoc] using haX x⁻¹ (X.inv_mem hx))) (X.inv_mem hx)
      |> fun h => by
        have : x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) := by group
        rw [this]
        exact X.mul_mem hx (haX x⁻¹ (X.inv_mem hx))
  have haJ' : ∀ j ∈ J, a⁻¹ • j = j := fun j hj => by
    rw [inv_smul_eq_iff]
    exact (haJ j hj).symm
  have hfix : ∀ j ∈ J, (x * a * x⁻¹ * a⁻¹) • j = j := by
    intro j hj
    rw [mul_smul, mul_smul, mul_smul, haJ' j hj, haJ _ (hJX _ (X.inv_mem hx) j hj), smul_inv_smul]
  have h1 := hfaith _ hmem hfix
  have : x * a * x⁻¹ * a⁻¹ * (a * x) = x * a := by group
  rw [h1, one_mul] at this
  exact this.symm

theorem ratio_of_not_isFFModule (hQ : ∀ q : Q, q ^ 2 = 1) {X B : Subgroup Γ}
    (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB2 : ∀ a ∈ B, a ^ 2 = 1)
    (hBX : ∀ a ∈ B, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {J : Subgroup Q}
    (hJ : ∀ g ∈ X ⊔ B, ∀ j ∈ J, g • j ∈ J) (hJ2 : 2 ≤ rk ↥J)
    (hfaith : ∀ x ∈ X, (∀ j ∈ J, x • j = j) → x = 1)
    (hnot : ¬ IsFFModule (resJ (X ⊔ B) J hJ).range) :
    (mRel B X : ℚ) ≤ nB B J ∧ (0 < mRel B X → (mRel B X : ℚ) < nB B J) ∧
      (mRel B X : ℚ) + 2 ≤ rk ↥J := by
  have hBJ : ∀ b ∈ B, ∀ j ∈ J, b • j ∈ J := fun b hb => hJ b (le_sup_right (a := X) hb)
  have hXJ : ∀ x ∈ X, ∀ j ∈ J, x • j ∈ J := fun x hx => hJ x (le_sup_left (b := B) hx)
  have hJ2' : ∀ j : ↥J, j ^ 2 = 1 := fun j => Subtype.ext (by simpa using hQ j)
  set E := (resJ B J hBJ).range with hE
  have hEG : E ≤ (resJ (X ⊔ B) J hJ).range := range_resJ_mono le_sup_right
  have hEab : IsElemAbelian2 E := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBc a a.2 b b.2)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by simpa using hB2 a a.2)
      rw [this, map_one]
  have hrkE : rk ↥E + rk ↥(B ⊓ fixingSubgroup Γ (J : Set Q)) = rk ↥B :=
    rk_range_resJ (S := B) (J := J) (hS := hBJ)
  have hfixE : rk ↥(fixV E) = rk ↥(J ⊓ XMod.fixed ↥B (⊤ : Subgroup Q)) :=
    rk_fixV_range_resJ (S := B) (J := J) (hS := hBJ)
  have hidx := rk_add_rkIdx (fixV E)
  have hnB : nB B J = rk ↥J - rk ↥(fixV E) := by
    unfold nB
    rw [hfixE]
  have hfixle : rk ↥(fixV E) ≤ rk ↥J := by
    have := rk_mono (le_top : fixV E ≤ ⊤)
    rwa [rk_top] at this
  have hcent : B ⊓ fixingSubgroup Γ (J : Set Q) ≤ B ⊓ Subgroup.centralizer (X : Set Γ) := by
    rintro a ⟨haB, haF⟩
    refine ⟨haB, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact commute_of_fix_of_faithful hXJ hfaith (hBX a haB)
      (fun j hj => (mem_fixingSubgroup_iff Γ).1 haF j hj) x hx
  have hmle : mRel B X ≤ rk ↥E := by
    have := rk_mono hcent
    unfold mRel
    omega
  by_cases hE0 : E = ⊥
  · have h0 : rk ↥E = 0 := by rw [hE0]; exact rk_bot
    have hm0 : mRel B X = 0 := by omega
    rw [hm0]
    have : (2 : ℚ) ≤ rk ↥J := by exact_mod_cast hJ2
    refine ⟨by positivity, fun h => absurd h (lt_irrefl 0), ?_⟩
    push_cast
    linarith
  · have hEp : IsPGroup 2 ↥E := hEab.isPGroup
    have hlt : rk ↥E + rk ↥(fixV E) < rk ↥J := by
      by_contra hge
      push Not at hge
      apply hnot
      refine ⟨E, hEG, hE0, hEab, ?_⟩
      rw [card_eq_two_pow_rk hJ2', card_eq_two_pow_of_isPGroup hEp, card_eq_two_pow hJ2', ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) hge
    have hfpos : 0 < rk ↥(fixV E) :=
      rk_fixV_pos hJ2' hEp (by omega)
    have h1 : mRel B X < nB B J := by omega
    have h2 : mRel B X + 2 ≤ rk ↥J := by omega
    refine ⟨by exact_mod_cast h1.le, fun _ => by exact_mod_cast h1, by exact_mod_cast h2⟩

end NotFF

open CFSG.Open CFSG.Assembly.LowTwoRank

section A38

private theorem exists_mul_ne_of_isPerfect {X : Type*} [Group X] [Nontrivial X]
    [Group.IsPerfect X] : ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  exact Group.IsPerfect.not_isMulCommutative X ⟨⟨h⟩⟩

private theorem isPerfect_of_isPSL_two {X : Type} [Group X] {p f : ℕ} (h : IsPSL 2 p f X) :
    Group.IsPerfect X := by
  obtain ⟨⟨hp, hf, -, h22, h23⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  have hne2 : p ^ f ≠ 2 := fun h => h22 (by rw [h])
  have hne3 : p ^ f ≠ 3 := fun h => h23 (by rw [h])
  have : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three K (by rw [hK]; omega)
  let φ := CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K
  exact Group.IsPerfect.ofSurjective (f := (φ.trans e.symm).toMonoidHom)
    (MulEquiv.surjective _)

theorem exists_mul_ne_of_a38Types {X : Type} [Group X] [Nontrivial X] (hX : A38Types X) :
    ∃ a b : X, a * b ≠ b * a := by
  rcases hX with ⟨n, hn⟩ | ⟨n, hn⟩ | hJ | ⟨p, -, -, hn⟩
  · have := isPerfect_of_isPSL_two hn
    exact exists_mul_ne_of_isPerfect
  · obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hn
    obtain ⟨u, v, huv⟩ := CFSG.SectionRank.suzukiMatrixGroup_nonabelian a ha
    refine ⟨e.symm u, e.symm v, fun h => huv ?_⟩
    simpa using congrArg e h
  · obtain ⟨e⟩ := hJ
    have : Group.IsPerfect ↥CFSG.Open.walterJ1 := ⟨CFSG.Walter.J1Props.walterJ1_perfect⟩
    have : Group.IsPerfect X := Group.IsPerfect.ofSurjective
      (f := (e.trans CFSG.Walter.walterJ1EquivNative.symm).symm.toMonoidHom)
      (MulEquiv.surjective _)
    exact exists_mul_ne_of_isPerfect
  · have := isPerfect_of_isPSL_two hn
    exact exists_mul_ne_of_isPerfect

theorem isQuasisimple_of_a38Types {X : Type} [Group X] [IsSimpleGroup X] (hX : A38Types X) :
    CFSG.IsQuasisimple X :=
  (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (exists_mul_ne_of_a38Types hX)).1

end A38

section Constituent

variable {Γ : Type} [Group Γ] {Q : Type} [CommGroup Q] [MulDistribMulAction Γ Q]
  {X : Subgroup Γ} {J : Subgroup Q}

theorem resJ_injective_of_isSimpleGroup (hXs : IsSimpleGroup ↥X)
    (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J) (hnt : ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j) :
    Function.Injective (resJ X J hJX) := by
  have := hXs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (resJ X J hJX).ker with h | h
  · exact (MonoidHom.ker_eq_bot_iff _).1 h
  · exfalso
    obtain ⟨x, hx, j, hj, hxj⟩ := hnt
    have hmem : (⟨x, hx⟩ : ↥X) ∈ (resJ X J hJX).ker := by rw [h]; trivial
    rw [MonoidHom.mem_ker] at hmem
    exact hxj (congrArg (fun φ : MulAut ↥J => ((φ ⟨j, hj⟩ : ↥J) : Q)) hmem)

theorem eq_one_of_forall_smul_eq_of_isSimpleGroup (hXs : IsSimpleGroup ↥X)
    (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J) (hnt : ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j) :
    ∀ x ∈ X, (∀ j ∈ J, x • j = j) → x = 1 := by
  intro x hx hfix
  have h1 : resJ X J hJX ⟨x, hx⟩ = resJ X J hJX 1 := by
    rw [map_one]
    refine MulEquiv.ext fun j => Subtype.ext ?_
    show x • (j : Q) = j
    exact hfix j j.2
  exact congrArg Subtype.val (resJ_injective_of_isSimpleGroup hXs hJX hnt h1)

theorem mRel_le_rk_range [Finite Γ] (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J)
    (hfaith : ∀ x ∈ X, (∀ j ∈ J, x • j = j) → x = 1) {B : Subgroup Γ}
    (hBX : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hJB : ∀ b ∈ B, ∀ j ∈ J, b • j ∈ J) :
    mRel B X ≤ rk ↥(resJ B J hJB).range := by
  have hcent : B ⊓ fixingSubgroup Γ (J : Set Q) ≤ B ⊓ Subgroup.centralizer (X : Set Γ) := by
    rintro a ⟨haB, haF⟩
    refine ⟨haB, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact commute_of_fix_of_faithful hJX hfaith (hBX a haB)
      (fun j hj => (mem_fixingSubgroup_iff Γ).1 haF j hj) x hx
  have h1 := rk_range_resJ (S := B) (J := J) (hS := hJB)
  have h2 := rk_mono hcent
  unfold mRel
  omega

theorem nB_eq_rkIdx_fixV [Finite Q] {B : Subgroup Γ} (hJB : ∀ b ∈ B, ∀ j ∈ J, b • j ∈ J) :
    nB B J = rkIdx (fixV (resJ B J hJB).range) := by
  have h1 := rk_fixV_range_resJ (S := B) (J := J) (hS := hJB)
  have h2 := rk_add_rkIdx (fixV (resJ B J hJB).range)
  unfold nB
  omega

theorem isElemAbelian2_range_resJ {B : Subgroup Γ} (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hJB : ∀ b ∈ B, ∀ j ∈ J, b • j ∈ J) :
    IsElemAbelian2 (resJ B J hJB).range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc a a.2 b b.2)
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 2 = 1 := Subtype.ext (by simpa using hB2 a a.2)
    rw [this, map_one]

theorem commOf_eq_self_of_isIrr (hJ : XMod.IsIrr ↥X J) (hnt : ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j) :
    XMod.commOf ↥X J = J := by
  rcases hJ.2.2 _ (XMod.isInv_commOf J) bot_le (XMod.commOf_le_of_isInv hJ.1) with h | h
  · exfalso
    obtain ⟨x, hx, j, hj, hxj⟩ := hnt
    exact hxj ((XMod.mem_fixed.1 (XMod.commOf_eq_bot_iff.1 h hj)).2 ⟨x, hx⟩)
  · exact h

theorem three_le_rk_of_resJ_injective [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J) (hinj : Function.Injective (resJ X J hJX))
    [Group.IsPerfect ↥X] [Nontrivial ↥X] : 3 ≤ rk ↥J := by
  by_contra hlt
  have hcard : Nat.card ↥J ≤ 4 := by
    rw [card_eq_two_pow hQ J]
    calc 2 ^ rk ↥J ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  have : Group.IsSolvable (Equiv.Perm ↥J) := Equiv.Perm.isSolvable hcard
  have : Group.IsSolvable (MulAut ↥J) :=
    Group.isSolvable_of_isSolvable_injective (f := MulAut.toPerm _) fun a b hab =>
      MulEquiv.ext fun u => congrArg (fun e : Equiv.Perm _ => e u) hab
  have : Group.IsSolvable ↥X := Group.isSolvable_of_isSolvable_injective hinj
  exact Group.IsPerfect.not_isSolvable ↥X this

theorem three_le_rk_of_a38 [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) (hXs : IsSimpleGroup ↥X)
    (hXa : A38Types ↥X) (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J)
    (hnt : ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j) : 3 ≤ rk ↥J := by
  have := hXs
  have : Group.IsPerfect ↥X := (isQuasisimple_of_a38Types hXa).1
  exact three_le_rk_of_resJ_injective hQ hJX (resJ_injective_of_isSimpleGroup hXs hJX hnt)

theorem b4Hyp_of_a38 (hA21 : AsA21SQTKSection) (hΓ : IsQuotientOfSQTKTC Γ) [Finite Q]
    (hQ : ∀ q : Q, q ^ 2 = 1) {B : Subgroup Γ} (hXs : IsSimpleGroup ↥X) (hXa : A38Types ↥X)
    (hBX : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hJ : XMod.IsIrr ↥X J) (hnt : ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j)
    (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J) (hJXB : ∀ g ∈ X ⊔ B, ∀ j ∈ J, g • j ∈ J) :
    B4Hyp (resJ (X ⊔ B) J hJXB).range (resJ X J hJX).range ∧
      A38Types ↥(resJ X J hJX).range ∧ IsSimpleGroup ↥(resJ X J hJX).range ∧
      (IsPSL 3 2 1 ↥(resJ X J hJX).range → IsPSL 3 2 1 ↥X) := by
  have := hXs
  let e : ↥X ≃* ↥(resJ X J hJX).range :=
    MonoidHom.ofInjective (resJ_injective_of_isSimpleGroup hXs hJX hnt)
  have hXq : CFSG.IsQuasisimple ↥X := isQuasisimple_of_a38Types hXa
  exact ⟨b4Hyp_resJ hA21 hΓ hQ hXq hBX hB2 hJ (commOf_eq_self_of_isIrr hJ hnt) hJX hJXB,
    A38Types.of_mulEquiv e hXa, e.symm.isSimpleGroup, fun h => IsPSL.of_mulEquiv e.symm h⟩

end Constituent

section Module

variable {V : Type} [CommGroup V] [Finite V]

theorem rkIdx_fixV_lt_of_isPGroup (hV : ∀ v : V, v ^ 2 = 1) (h1 : 1 ≤ rk V)
    {E : Subgroup (MulAut V)} (hE : IsPGroup 2 ↥E) : rkIdx (fixV E) < rk V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := card_modEq_card_fixV (q := 2) hE
  have h2V : 2 ∣ Nat.card V := by
    rw [card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)]
    exact dvd_pow_self 2 (by omega)
  have h2F : 2 ∣ Nat.card ↥(fixV E) := (hmod.dvd_iff dvd_rfl).1 h2V
  have hpos : 0 < rk ↥(fixV E) := by
    rcases Nat.eq_zero_or_pos (rk ↥(fixV E)) with h | h
    · rw [card_eq_two_pow hV (fixV E), h, pow_zero] at h2F
      exact absurd h2F (by norm_num)
    · exact h
  have := rk_add_rkIdx (fixV E)
  omega

theorem exists_offender_of_ratio_lt (hV : ∀ v : V, v ^ 2 = 1) {X F : Subgroup (MulAut V)}
    (hFX : F ≤ X) (hF : IsElemAbelian2 F) {q : ℚ} (hq : q ≤ 1)
    (hr : (rkIdx (fixV F) : ℚ) < q * rk ↥F) :
    ∃ F' : Subgroup (MulAut V), IsFFStarOffender X F' ∧ IsQuadratic F' ∧ rAV F' < q := by
  have hFp : IsPGroup 2 ↥F := hF.isPGroup
  have hcard : ∀ C : Subgroup (MulAut V), C ≤ F →
      Nat.card ↥C * Nat.card ↥(fixV C) = 2 ^ (rk ↥C + rk ↥(fixV C)) := by
    intro C hC
    rw [card_eq_two_pow_of_isPGroup (hFp.to_le hC), card_eq_two_pow hV (fixV C), pow_add]
  have hidx : ∀ C : Subgroup (MulAut V), rk ↥(fixV C) + rkIdx (fixV C) = rk V :=
    fun C => rk_add_rkIdx (fixV C)
  have : Nonempty {C : Subgroup (MulAut V) // C ≤ F} := ⟨⟨⊥, bot_le⟩⟩
  obtain ⟨⟨E, hEF⟩, hEmax⟩ := Finite.exists_max
    (fun C : {C : Subgroup (MulAut V) // C ≤ F} => Nat.card ↥C.1 * Nat.card ↥(fixV C.1))
  have hEmax' : ∀ C : Subgroup (MulAut V), C ≤ F →
      rk ↥C + rk ↥(fixV C) ≤ rk ↥E + rk ↥(fixV E) := by
    intro C hC
    have h1 := hEmax ⟨C, hC⟩
    simp only at h1
    rw [hcard C hC, hcard E hEF] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have hFE := hEmax' F le_rfl
  have hFidx := hidx F
  have hEidx := hidx E
  have hrkE : rk ↥E ≤ rk ↥F := rk_mono hEF
  have hF0 : (0 : ℚ) ≤ rk ↥F := Nat.cast_nonneg _
  have hEne : E ≠ ⊥ := by
    intro hE
    rw [hE, rk_bot, B1.fixV_bot, rk_top] at hFE
    have h1 : (rk ↥F : ℚ) ≤ rkIdx (fixV F) := by exact_mod_cast (by omega)
    nlinarith
  have hEoff : IsFFStarOffender X E := by
    refine ⟨hEF.trans hFX, hEne, ⟨fun a ha b hb => hF.1 a (hEF ha) b (hEF hb),
      fun a ha => hF.2 a (hEF ha)⟩, fun C hC => ?_⟩
    exact hEmax ⟨C, hC.trans hEF⟩
  obtain ⟨F', hF'E, hF'off, hF'q, hF'card, -, -⟩ := exists_quadratic_offender_le hV hEoff
  have hF'F : F' ≤ F := hF'E.trans hEF
  have hF'rk : rk ↥F' + rk ↥(fixV F') = rk ↥E + rk ↥(fixV E) := by
    rw [hcard F' hF'F, hcard E hEF] at hF'card
    exact Nat.pow_right_injective le_rfl hF'card
  have hF'idx := hidx F'
  have hrkF' : rk ↥F' ≤ rk ↥E := rk_mono hF'E
  have hF'pos : (0 : ℚ) < rk ↥F' := by exact_mod_cast hF'off.isA2.rk_pos
  refine ⟨F', hF'off, hF'q, ?_⟩
  unfold rAV
  rw [div_lt_iff₀ hF'pos]
  have key : (rkIdx (fixV F') : ℚ) + rk ↥F ≤ rkIdx (fixV F) + rk ↥F' := by
    exact_mod_cast (by omega)
  have hFF' : (rk ↥F' : ℚ) ≤ rk ↥F := by exact_mod_cast hrkF'.trans hrkE
  nlinarith

private theorem q₀_nonneg_le_one {L : Type} [Group L] {q₀ : ℚ}
    (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 L)) : 0 ≤ q₀ ∧ q₀ ≤ 1 := by
  rcases hq₀ with rfl | ⟨rfl, -⟩ <;> norm_num

theorem q₀_mul_rk_le_rkIdx (hB42 : AsB42) (h9 : A38B42) (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hB4 : B4Hyp G L) (hL38 : A38Types ↥L) (hLs : IsSimpleGroup ↥L)
    {q₀ : ℚ} (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥L)) {F : Subgroup (MulAut V)}
    (hFG : F ≤ G) (hF : IsElemAbelian2 F) : q₀ * rk ↥F ≤ rkIdx (fixV F) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨F', hF'off, hF'q, hF'r⟩ :=
    exists_offender_of_ratio_lt hV hFG hF (q₀_nonneg_le_one hq₀).2 hlt
  have hq : qOf G < (q₀ : WithTop ℚ) :=
    kq_lt_iff.2 ⟨F', hF'off.isA2, (isQuadratic_iff_commSeries_two F').1 hF'q, hF'r⟩
  have key : ∀ c : ℚ, qOf G = (c : WithTop ℚ) → c < q₀ := fun c hc => by
    rw [hc] at hq
    exact WithTop.coe_lt_coe.1 hq
  rcases h9 V hV G L F' hB4 hL38 hLs hF'off (hB42 V hV G L hB4 F' hF'off) with
    ⟨⟨-, -, -, h1⟩, -⟩ | ⟨⟨-, -, h1⟩, -, hpsl, -⟩ | ⟨⟨-, h1⟩, -⟩
  · have := key _ h1
    rcases hq₀ with rfl | ⟨rfl, -⟩ <;> norm_num at this
  · have := key _ h1
    rcases hq₀ with rfl | ⟨rfl, hn⟩
    · norm_num at this
    · exact hn hpsl
  · have := key _ h1
    rcases hq₀ with rfl | ⟨rfl, -⟩ <;> norm_num at this

theorem q₀_mul_rk_add_two_le (hB42 : AsB42) (h9 : A38B42) (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hB4 : B4Hyp G L) (hL38 : A38Types ↥L) (hLs : IsSimpleGroup ↥L)
    (h3 : 3 ≤ rk V) {q₀ : ℚ} (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥L))
    {E : Subgroup (MulAut V)} (hEG : E ≤ G) (hE : IsElemAbelian2 E) :
    q₀ * ((rk ↥E : ℚ) + 2) ≤ rk V := by
  have hlt := rkIdx_fixV_lt_of_isPGroup hV (by omega) hE.isPGroup
  have hb := q₀_mul_rk_le_rkIdx hB42 h9 hV hB4 hL38 hLs hq₀ hEG hE
  have hlt' : (rkIdx (fixV E) : ℚ) + 1 ≤ rk V := by exact_mod_cast hlt
  rcases hq₀ with rfl | ⟨rfl, hpsl⟩
  · linarith
  by_contra hcon
  have hle : rk V ≤ rk ↥E + 1 := by
    have : (rk V : ℚ) < rk ↥E + 2 := by linarith
    have : rk V < rk ↥E + 2 := by exact_mod_cast this
    omega
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, rk_bot] at hle
    omega
  have hVc : Nat.card V = 2 ^ rk V :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hV)
  have hEc : Nat.card ↥E = 2 ^ rk ↥E := card_eq_two_pow_of_isPGroup hE.isPGroup
  have hoff : IsFFStarOffender G E := by
    refine ⟨hEG, hEne, hE, fun C hC => ?_⟩
    have hCa : IsElemAbelian2 C :=
      ⟨fun a ha b hb => hE.1 a (hC ha) b (hC hb), fun a ha => hE.2 a (hC ha)⟩
    have hbC := q₀_mul_rk_le_rkIdx hB42 h9 hV hB4 hL38 hLs (Or.inr ⟨rfl, hpsl⟩)
      (hC.trans hEG) hCa
    have hbC' : (rk ↥C : ℚ) ≤ rkIdx (fixV C) := by linarith
    have hbC'' : rk ↥C ≤ rkIdx (fixV C) := by exact_mod_cast hbC'
    have hb' : (rk ↥E : ℚ) ≤ rkIdx (fixV E) := by linarith
    have hb'' : rk ↥E ≤ rkIdx (fixV E) := by exact_mod_cast hb'
    have hiC := rk_add_rkIdx (fixV C)
    have hiE := rk_add_rkIdx (fixV E)
    rw [card_eq_two_pow_of_isPGroup (hE.isPGroup.to_le hC), card_eq_two_pow hV (fixV C), hEc,
      card_eq_two_pow hV (fixV E), ← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h9 V hV G L E hB4 hL38 hLs hoff (hB42 V hV G L hB4 E hoff) with
    ⟨-, n, hn, -, hV2, hE2⟩ | ⟨-, -, hpsl', -⟩ | ⟨-, -, hV4, hE4⟩
  · rw [hVc] at hV2
    rw [hEc] at hE2
    have h1 := Nat.pow_right_injective le_rfl hV2
    have h2 := Nat.pow_right_injective le_rfl hE2
    omega
  · exact hpsl hpsl'
  · rw [hVc] at hV4
    rw [hEc, show (4 : ℕ) = 2 ^ 2 by norm_num] at hE4
    have h1 := Nat.pow_right_injective le_rfl hV4
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hE4
    omega

end Module

section Bounds

variable {Γ : Type} [Group Γ] [Finite Γ] {Q : Type} [CommGroup Q] [Finite Q]
  [MulDistribMulAction Γ Q]

omit [Finite Γ] [Finite Q] in
theorem smul_mem_of_mem_stabIn {A : Subgroup Γ} {J : Subgroup Q} {b : Γ}
    (hb : b ∈ stabIn A J) {j : Q} (hj : j ∈ J) : b • j ∈ J := by
  rw [← (mem_stabIn.1 hb).2]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ hj

theorem constituent_bounds_of_a38 (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    (hΓ : IsQuotientOfSQTKTC Γ) (hQ : ∀ q : Q, q ^ 2 = 1) {X B : Subgroup Γ}
    (hXs : IsSimpleGroup ↥X) (hXa : A38Types ↥X) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) (hBX : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {J : Subgroup Q}
    (hJ : XMod.IsIrr ↥X J) (hnt : ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j)
    (hJB : ∀ b ∈ B, ∀ j ∈ J, b • j ∈ J) {q₀ : ℚ}
    (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥X)) :
    q₀ * (mRel B X : ℚ) ≤ nB B J ∧ q₀ * ((mRel B X : ℚ) + 2) ≤ rk ↥J := by
  have hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J := fun g hg j hj => hJ.1 ⟨g, hg⟩ j hj
  have hJXB : ∀ g ∈ X ⊔ B, ∀ j ∈ J, g • j ∈ J := fun g hg =>
    SmithD391.smul_mem_of_mem_sup hJX hJB hg
  obtain ⟨hB4, hL38, hLs, hpsl⟩ := b4Hyp_of_a38 hA21 hΓ hQ hXs hXa hBX hB2 hJ hnt hJX hJXB
  have h3 := three_le_rk_of_a38 hQ hXs hXa hJX hnt
  have hJ2 : ∀ j : ↥J, j ^ 2 = 1 := fun j => Subtype.ext (by simpa using hQ j)
  have hq : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥(resJ X J hJX).range) :=
    hq₀.imp_right fun h => ⟨h.1, fun h' => h.2 (hpsl h')⟩
  have hEG : (resJ B J hJB).range ≤ (resJ (X ⊔ B) J hJXB).range := range_resJ_mono le_sup_right
  have hE := isElemAbelian2_range_resJ hBc hB2 hJB
  have hm : (mRel B X : ℚ) ≤ rk ↥(resJ B J hJB).range := by
    exact_mod_cast mRel_le_rk_range hJX
      (eq_one_of_forall_smul_eq_of_isSimpleGroup hXs hJX hnt) hBX hJB
  have hq0 := (q₀_nonneg_le_one hq₀).1
  have h1 := q₀_mul_rk_le_rkIdx hB42 h9 hJ2 hB4 hL38 hLs hq hEG hE
  have h2 := q₀_mul_rk_add_two_le hB42 h9 hJ2 hB4 hL38 hLs h3 hq hEG hE
  rw [nB_eq_rkIdx_fixV hJB]
  exact ⟨(mul_le_mul_of_nonneg_left hm hq0).trans h1,
    (mul_le_mul_of_nonneg_left (by linarith) hq0).trans h2⟩

end Bounds

theorem nB_ge_of_a38 (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : IsQuotientOfSQTKTC Γ)
    {Q : Type} [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {P X : Subgroup Γ} (hXs : IsSimpleGroup ↥X) (hXa : A38Types ↥X)
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : ∀ a ∈ P, a ^ 2 = 1)
    (hPX : ∀ a ∈ P, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {Y : Subgroup Q}
    (hYP : ∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y) (hYX : ∀ x ∈ X, ∀ y ∈ Y, x • y ∈ Y)
    (hcub : IsCubicOn P Y) (hss : Y ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J), J)
    {d : ℕ} (hd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → rk ↥J = d)
    (hnt : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j)
    {q₀ : ℚ} (hq₀ : q₀ = 1 / 2 ∨ (q₀ = 1 ∧ ¬ IsPSL 3 2 1 ↥X)) :
    q₀ * (mRel P X : ℚ) * rk ↥Y ≤ d * nB P Y := by
  have hq := q₀_nonneg_le_one hq₀
  by_cases hY : Y = ⊥
  · subst hY
    rw [rk_bot, Nat.cast_zero, mul_zero]
    positivity
  have hbd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J →
      q₀ * (mRel (stabIn P J) X : ℚ) ≤ nB (stabIn P J) J ∧
        q₀ * ((mRel (stabIn P J) X : ℚ) + 2) ≤ rk ↥J := fun J hJY hJ =>
    constituent_bounds_of_a38 hA21 hB42 h9 hΓ hQ hXs hXa
      (fun a ha b hb => hPc a (mem_stabIn.1 ha).1 b (mem_stabIn.1 hb).1)
      (fun b hb => hP2 b (mem_stabIn.1 hb).1) (fun b hb => hPX b (mem_stabIn.1 hb).1) hJ
      (hnt J hJY hJ) (fun b hb j hj => smul_mem_of_mem_stabIn hb hj) hq₀
  obtain ⟨J₀, hJ₀Y, hJ₀⟩ :=
    SmithD391.exists_isIrr_le (Λ := X) (fun x y hy => hYX x x.2 y hy) hY
  have hd3 : 3 ≤ d := hd J₀ hJ₀Y hJ₀ ▸
    three_le_rk_of_a38 hQ hXs hXa (fun g hg j hj => hJ₀.1 ⟨g, hg⟩ j hj) (hnt J₀ hJ₀Y hJ₀)
  exact nB_ge_of_constituents hQ hPc hP2 hPX hYP hYX hcub hss hd3 hd hq.1 hq.2
    (fun J hJY hJ => (hbd J hJY hJ).1)
    (fun J hJY hJ _ => hd J hJY hJ ▸ (hbd J hJY hJ).2)

theorem ff_or_nB_gt_of_a38 (hA21 : AsA21SQTKSection) (hB42 : AsB42) (h9 : A38B42)
    {Γ : Type} [Group Γ] [Finite Γ] (hΓ : IsQuotientOfSQTKTC Γ)
    {Q : Type} [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {P X : Subgroup Γ} (hXs : IsSimpleGroup ↥X) (hXa : A38Types ↥X)
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP2 : ∀ a ∈ P, a ^ 2 = 1)
    (hPX : ∀ a ∈ P, ∀ x ∈ X, a * x * a⁻¹ ∈ X) {Y : Subgroup Q}
    (hYP : ∀ a ∈ P, ∀ y ∈ Y, a • y ∈ Y) (hYX : ∀ x ∈ X, ∀ y ∈ Y, x • y ∈ Y)
    (hcub : IsCubicOn P Y) (hss : Y ≤ ⨆ (J : Subgroup Q) (_ : J ≤ Y ∧ XMod.IsIrr ↥X J), J)
    {d : ℕ} (hd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → rk ↥J = d)
    (hnt : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → ∃ x ∈ X, ∃ j ∈ J, x • j ≠ j)
    (hm : 0 < mRel P X) (hY : Y ≠ ⊥) :
    (mRel P X : ℚ) * rk ↥Y < d * nB P Y ∨
      ∃ J : Subgroup Q, J ≤ Y ∧ XMod.IsIrr ↥X J ∧
        ∃ (hJ : ∀ g ∈ X ⊔ stabIn P J, ∀ j ∈ J, g • j ∈ J) (hJX : ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J)
          (F : Subgroup (MulAut ↥J)),
          B4Hyp (resJ (X ⊔ stabIn P J) J hJ).range (resJ X J hJX).range ∧
          IsFFStarOffender (resJ (X ⊔ stabIn P J) J hJ).range F ∧
          A38B42Concl (resJ (X ⊔ stabIn P J) J hJ).range (resJ X J hJX).range F := by
  have hBc : ∀ J : Subgroup Q, ∀ a ∈ stabIn P J, ∀ b ∈ stabIn P J, a * b = b * a :=
    fun J a ha b hb => hPc a (mem_stabIn.1 ha).1 b (mem_stabIn.1 hb).1
  have hB2 : ∀ J : Subgroup Q, ∀ b ∈ stabIn P J, b ^ 2 = 1 := fun J b hb =>
    hP2 b (mem_stabIn.1 hb).1
  have hBX : ∀ J : Subgroup Q, ∀ b ∈ stabIn P J, ∀ x ∈ X, b * x * b⁻¹ ∈ X := fun J b hb =>
    hPX b (mem_stabIn.1 hb).1
  have hJB : ∀ J : Subgroup Q, ∀ b ∈ stabIn P J, ∀ j ∈ J, b • j ∈ J := fun J b hb j hj =>
    smul_mem_of_mem_stabIn hb hj
  have hJX : ∀ J : Subgroup Q, XMod.IsIrr ↥X J → ∀ g ∈ X, ∀ j ∈ J, g • j ∈ J :=
    fun J hJ g hg j hj => hJ.1 ⟨g, hg⟩ j hj
  have hJXB : ∀ J : Subgroup Q, XMod.IsIrr ↥X J → ∀ g ∈ X ⊔ stabIn P J, ∀ j ∈ J, g • j ∈ J :=
    fun J hJ g hg => SmithD391.smul_mem_of_mem_sup (hJX J hJ) (hJB J) hg
  by_cases hff : ∃ J : Subgroup Q, ∃ (_ : J ≤ Y) (hJ : XMod.IsIrr ↥X J),
      IsFFModule (resJ (X ⊔ stabIn P J) J (hJXB J hJ)).range
  · right
    obtain ⟨J, hJY, hJ, hFF⟩ := hff
    have hJ2 : ∀ j : ↥J, j ^ 2 = 1 := fun j => Subtype.ext (by simpa using hQ j)
    obtain ⟨hB4, hL38, hLs, -⟩ := b4Hyp_of_a38 hA21 hΓ hQ hXs hXa (hBX J) (hB2 J) hJ
      (hnt J hJY hJ) (hJX J hJ) (hJXB J hJ)
    obtain ⟨F, hF⟩ := ((B1_4_5 hJ2 _).out 1 2).1 hFF
    exact ⟨J, hJY, hJ, hJXB J hJ, hJX J hJ, F, hB4, hF,
      h9 ↥J hJ2 _ _ F hB4 hL38 hLs hF (hB42 ↥J hJ2 _ _ hB4 F hF)⟩
  · left
    push Not at hff
    have h3 : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J → 3 ≤ rk ↥J := fun J hJY hJ =>
      three_le_rk_of_a38 hQ hXs hXa (hJX J hJ) (hnt J hJY hJ)
    have hbd : ∀ J : Subgroup Q, J ≤ Y → XMod.IsIrr ↥X J →
        (mRel (stabIn P J) X : ℚ) ≤ nB (stabIn P J) J ∧
          (0 < mRel (stabIn P J) X → (mRel (stabIn P J) X : ℚ) < nB (stabIn P J) J) ∧
          (mRel (stabIn P J) X : ℚ) + 2 ≤ rk ↥J := fun J hJY hJ =>
      ratio_of_not_isFFModule hQ (hBc J) (hB2 J) (hBX J) (hJXB J hJ)
        (by have := h3 J hJY hJ; omega)
        (eq_one_of_forall_smul_eq_of_isSimpleGroup hXs (hJX J hJ) (hnt J hJY hJ))
        (hff J hJY hJ)
    obtain ⟨J₀, hJ₀Y, hJ₀⟩ :=
      SmithD391.exists_isIrr_le (Λ := X) (fun x y hy => hYX x x.2 y hy) hY
    have hd3 : 3 ≤ d := hd J₀ hJ₀Y hJ₀ ▸ h3 J₀ hJ₀Y hJ₀
    have h := nB_gt_of_constituents (q := 1) hQ hPc hP2 hPX hYP hYX hcub hss hd3 hd
      zero_le_one le_rfl (fun J hJY hJ => by rw [one_mul]; exact (hbd J hJY hJ).1)
      (fun J hJY hJ _ => by rw [one_mul, ← hd J hJY hJ]; exact (hbd J hJY hJ).2.2)
      (fun J hJY hJ hpos => by rw [one_mul]; exact (hbd J hJY hJ).2.1 hpos) hm hY
    rwa [one_mul] at h

end CFSG.Quasithin.SmithD321
