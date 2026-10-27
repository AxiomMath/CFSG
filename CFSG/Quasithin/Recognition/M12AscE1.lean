module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Data.Fintype.CardEmbedding

public section

namespace CFSG.Quasithin

open Subgroup

private lemma pow_val_add_eq' {D : Type*} [Group D] [Finite D] {ρ : D} {n : ℕ}
    (hn : orderOf ρ = n) (i j : ZMod n) : ρ ^ ((i + j).val) = ρ ^ i.val * ρ ^ j.val := by
  have : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
  have hcong : (i.val + j.val) % n ≡ i.val + j.val [MOD n] :=
    Nat.mod_modEq (i.val + j.val) n
  have hx : ρ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one ρ
  calc
    ρ ^ ((i + j).val) = ρ ^ ((i.val + j.val) % n) := by
      rw [ZMod.val_add (n := n) i j]
    _ = ρ ^ (i.val + j.val) := pow_eq_pow_of_modEq hcong hx
    _ = ρ ^ i.val * ρ ^ j.val := by rw [pow_add]

private lemma pow_val_sub_zpow' {D : Type*} [Group D] [Finite D] {ρ : D} {n : ℕ}
    (hn : orderOf ρ = n) (i j : ZMod n) :
    ρ ^ ((j - i).val) = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
  have : NeZero n := ⟨by rw [← hn]; exact (orderOf_pos ρ).ne'⟩
  have hji : (i + (j - i) : ZMod n) = j := by
    simp [sub_eq_add_neg]
  have hval : j.val = (i.val + (j - i).val) % n := by
    calc
      j.val = (i + (j - i) : ZMod n).val := by rw [hji]
      _ = (i.val + (j - i).val) % n := ZMod.val_add (n := n) i (j - i)
  have hcong : j.val ≡ i.val + (j - i).val [MOD n] := by
    rw [hval]
    exact Nat.mod_modEq _ _
  have hx : ρ ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one ρ
  have hp : ρ ^ j.val = ρ ^ i.val * ρ ^ ((j - i).val) := by
    calc
      ρ ^ j.val = ρ ^ (i.val + (j - i).val) := pow_eq_pow_of_modEq hcong hx
      _ = ρ ^ i.val * ρ ^ ((j - i).val) := by rw [pow_add]
  calc
    ρ ^ ((j - i).val) = (ρ ^ i.val)⁻¹ * ρ ^ j.val := by rw [hp]; group
    _ = ρ ^ (-(i.val : ℤ)) * ρ ^ (j.val : ℤ) := by
      rw [← zpow_natCast (a := ρ) (n := i.val),
        ← zpow_neg (a := ρ) (n := (i.val : ℤ)),
        ← zpow_natCast (a := ρ) (n := j.val)]
    _ = ρ ^ ((j.val : ℤ) - (i.val : ℤ)) := by
      rw [← zpow_add]
      congr 1
      ring

private lemma pow_mul_rel' {D : Type*} [Group D] {ρ σ : D} (hrel : σ * ρ * σ⁻¹ = ρ⁻¹) (t : ℕ) :
    ρ ^ t * σ = σ * ρ ^ (-(t : ℤ)) := by
  have hconjInv : σ * ρ⁻¹ * σ⁻¹ = ρ := by
    have h := congrArg Inv.inv hrel
    simpa [mul_assoc] using h
  have hρσ : ρ * σ = σ * ρ⁻¹ := by
    calc
      ρ * σ = (σ * ρ⁻¹ * σ⁻¹) * σ := by rw [hconjInv]
      _ = σ * ρ⁻¹ := by group
  induction t with
  | zero => simp
  | succ t ih =>
      calc
        ρ ^ (t + 1) * σ = (ρ ^ t * ρ) * σ := by rw [pow_succ]
        _ = ρ ^ t * (ρ * σ) := by rw [mul_assoc]
        _ = ρ ^ t * (σ * ρ⁻¹) := by rw [hρσ]
        _ = (ρ ^ t * σ) * ρ⁻¹ := by rw [mul_assoc]
        _ = (σ * ρ ^ (-(t : ℤ))) * ρ⁻¹ := by rw [ih]
        _ = σ * ρ ^ (-((t + 1 : ℕ) : ℤ)) := by
          rw [mul_assoc, ← zpow_neg_one ρ, ← zpow_add]
          exact congrArg (fun e : ℤ => σ * ρ ^ e) (by omega)

private def quatHom {A : Type*} [Group A] [Finite A] (i j : A) (hn : orderOf i = 4)
    (hrel : j * i * j⁻¹ = i⁻¹) (hjj : j * j = i * i) : QuaternionGroup 2 →* A where
  toFun
    | QuaternionGroup.a k => i ^ k.val
    | QuaternionGroup.xa k => j * i ^ k.val
  map_one' := by
    change i ^ 0 = 1
    simp
  map_mul' := by
    rintro (k | k) (l | l)
    · change i ^ (k + l).val = i ^ k.val * i ^ l.val
      exact pow_val_add_eq' hn k l
    · change j * i ^ (l - k).val = i ^ k.val * (j * i ^ l.val)
      symm
      calc
        i ^ k.val * (j * i ^ l.val) = (i ^ k.val * j) * i ^ l.val := by rw [mul_assoc]
        _ = (j * i ^ (-(k.val : ℤ))) * i ^ l.val := by rw [pow_mul_rel' hrel k.val]
        _ = j * (i ^ (-(k.val : ℤ)) * i ^ (l.val : ℤ)) := by rw [mul_assoc, zpow_natCast]
        _ = j * i ^ ((l.val : ℤ) - (k.val : ℤ)) := by
          rw [← zpow_add]
          congr 2
          ring
        _ = j * i ^ (l - k).val := by rw [pow_val_sub_zpow' hn k l]
    · change j * i ^ (k + l).val = (j * i ^ k.val) * i ^ l.val
      rw [pow_val_add_eq' hn]
      simp [mul_assoc]
    · change i ^ (((2 : ZMod 4) + l - k).val) = (j * i ^ k.val) * (j * i ^ l.val)
      symm
      calc
        (j * i ^ k.val) * (j * i ^ l.val) = j * (i ^ k.val * j) * i ^ l.val := by group
        _ = j * (j * i ^ (-(k.val : ℤ))) * i ^ l.val := by rw [pow_mul_rel' hrel k.val]
        _ = (j * j) * (i ^ (-(k.val : ℤ)) * i ^ (l.val : ℤ)) := by
          rw [zpow_natCast]
          group
        _ = i ^ 2 * (i ^ (-(k.val : ℤ)) * i ^ (l.val : ℤ)) := by rw [hjj, pow_two]
        _ = i ^ 2 * i ^ ((l.val : ℤ) - (k.val : ℤ)) := by
          rw [← zpow_add]
          congr 2
          ring
        _ = i ^ 2 * i ^ (l - k).val := by rw [pow_val_sub_zpow' hn k l]
        _ = i ^ ((2 : ZMod 4) + (l - k)).val := by
          simpa only [show (2 : ZMod 4).val = 2 by decide] using
            (pow_val_add_eq' hn (2 : ZMod 4) (l - k)).symm
        _ = i ^ ((2 : ZMod 4) + l - k).val := by
          congr 2
          ring

private lemma quatHom_injective {A : Type*} [Group A] [Finite A] (i j : A) (hn : orderOf i = 4)
    (hrel : j * i * j⁻¹ = i⁻¹) (hjj : j * j = i * i) (hj : j ∉ zpowers i) :
    Function.Injective (quatHom i j hn hrel hjj) := by
  have hpows {k l : ZMod 4} (h : i ^ k.val = i ^ l.val) : k = l := by
    apply ZMod.val_injective
    exact pow_injOn_Iio_orderOf (x := i)
      (by simpa [hn] using k.val_lt)
      (by simpa [hn] using l.val_lt) h
  rintro (k | k) (l | l) h
  · change i ^ k.val = i ^ l.val at h
    congr 1
    exact hpows h
  · exfalso
    change i ^ k.val = j * i ^ l.val at h
    apply hj
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(k.val : ℤ) - (l.val : ℤ), ?_⟩
    calc
      i ^ ((k.val : ℤ) - (l.val : ℤ)) = i ^ (k.val : ℤ) * i ^ (-(l.val : ℤ)) := by
        rw [sub_eq_add_neg, zpow_add]
      _ = i ^ k.val * (i ^ l.val)⁻¹ := by
        rw [zpow_natCast, zpow_neg, zpow_natCast]
      _ = (j * i ^ l.val) * (i ^ l.val)⁻¹ := by rw [h]
      _ = j := by group
  · exfalso
    change j * i ^ k.val = i ^ l.val at h
    apply hj
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(l.val : ℤ) - (k.val : ℤ), ?_⟩
    calc
      i ^ ((l.val : ℤ) - (k.val : ℤ)) = i ^ (l.val : ℤ) * i ^ (-(k.val : ℤ)) := by
        rw [sub_eq_add_neg, zpow_add]
      _ = i ^ l.val * (i ^ k.val)⁻¹ := by
        rw [zpow_natCast, zpow_neg, zpow_natCast]
      _ = (j * i ^ k.val) * (i ^ k.val)⁻¹ := by rw [h]
      _ = j := by group
  · change j * i ^ k.val = j * i ^ l.val at h
    congr 1
    apply hpows
    exact mul_left_cancel h

theorem exists_mulEquiv_quaternion {A : Type*} [Group A] [Finite A] (i j : A)
    (hcard : Nat.card A = 8) (hn : orderOf i = 4) (hrel : j * i * j⁻¹ = i⁻¹)
    (hjj : j * j = i * i) (hj : j ∉ zpowers i) : Nonempty (A ≃* QuaternionGroup 2) := by
  have hinj := quatHom_injective i j hn hrel hjj hj
  have hQ : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hbij : Function.Bijective (quatHom i j hn hrel hjj) :=
    hinj.bijective_of_nat_card_le (by rw [hcard, hQ])
  exact ⟨(MulEquiv.ofBijective (quatHom i j hn hrel hjj) hbij).symm⟩

theorem sharp3_of_free {Γ Ω : Type*} [Group Γ] [Finite Γ] [Finite Ω] [MulAction Γ Ω]
    (hΓ : Nat.card Γ = 720) (hΩ : Nat.card Ω = 10) (p : Fin 3 → Ω) (hp : Function.Injective p)
    (hfree : ∀ g : Γ, (∀ i, g • p i = p i) → g = 1) :
    ∀ a b : Fin 3 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : Γ, ∀ i, g • a i = b i := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  let F : Γ → (Fin 3 ↪ Ω) := fun g => ⟨fun i => g • p i, fun i j h => hp (MulAction.injective g h)⟩
  have hF : Function.Injective F := by
    intro g g' h
    have h' : ∀ i, g • p i = g' • p i := fun i => congrArg (fun e : Fin 3 ↪ Ω => e i) h
    have : g⁻¹ * g' = 1 := hfree _ (fun i => by
      rw [mul_smul, ← h' i, inv_smul_smul])
    exact inv_mul_eq_one.1 this
  have hE : Nat.card (Fin 3 ↪ Ω) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
      ← Nat.card_eq_fintype_card, hΩ]
    decide
  have hbij : Function.Bijective F := hF.bijective_of_nat_card_le (by rw [hE, hΓ])
  have hsurj : ∀ e : Fin 3 ↪ Ω, ∃ g : Γ, ∀ i, g • p i = e i := by
    intro e
    obtain ⟨g, hg⟩ := hbij.2 e
    exact ⟨g, fun i => congrArg (fun e : Fin 3 ↪ Ω => e i) hg⟩
  intro a b ha hb
  obtain ⟨ga, hga⟩ := hsurj ⟨a, ha⟩
  obtain ⟨gb, hgb⟩ := hsurj ⟨b, hb⟩
  have hga' : ∀ i, ga • p i = a i := fun i => hga i
  have hgb' : ∀ i, gb • p i = b i := fun i => hgb i
  refine ⟨gb * ga⁻¹, fun i => ?_, ?_⟩
  · calc (gb * ga⁻¹) • a i = (gb * ga⁻¹) • (ga • p i) := by rw [hga' i]
      _ = gb • p i := by rw [smul_smul, inv_mul_cancel_right]
      _ = b i := hgb' i
  · intro g hg
    have h1 : F (g * ga) = F gb := by
      apply DFunLike.ext
      intro i
      show (g * ga) • p i = gb • p i
      rw [mul_smul, hga' i, hg i, hgb' i]
    have := hF h1
    calc g = g * ga * ga⁻¹ := by group
      _ = gb * ga⁻¹ := by rw [this]

end CFSG.Quasithin
