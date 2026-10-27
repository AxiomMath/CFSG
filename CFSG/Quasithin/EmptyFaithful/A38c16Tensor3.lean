module

public import CFSG.Quasithin.EmptyFaithful.A38c16Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.A38c16.Tensor

open scoped MatrixGroups Matrix BigOperators

section Bridge

variable {W : Type} [CommGroup W]

theorem isKSub_inf {X : Subgroup (MulAut W)} {A B : Subgroup W} (hA : IsKSub X A)
    (hB : IsKSub X B) : IsKSub X (A ⊓ B) :=
  fun k hk v hv => ⟨hA k hk v hv.1, hB k hk v hv.2⟩

theorem isKSub_sup {X : Subgroup (MulAut W)} {A B : Subgroup W} (hA : IsKSub X A)
    (hB : IsKSub X B) : IsKSub X (A ⊔ B) := by
  intro k hk v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hA k hk a ha) (hB k hk b hb)

theorem isKSub_bot {X : Subgroup (MulAut W)} : IsKSub X (⊥ : Subgroup W) := by
  intro k _ v hv
  rw [Subgroup.mem_bot] at hv ⊢
  rw [hv, map_one]

theorem isKSub_finset_sup {X : Subgroup (MulAut W)} (s : Finset (Subgroup W))
    (hs : ∀ M ∈ s, IsKSub X M) : IsKSub X (s.sup id) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty]; exact isKSub_bot
  | insert M s hM ih =>
    rw [Finset.sup_insert]
    exact isKSub_sup (hs M (Finset.mem_insert_self _ _))
      (ih fun M' hM' => hs M' (Finset.mem_insert_of_mem hM'))

theorem card_eq_of_le_sup_simple8 [Finite W] (X : Subgroup (MulAut W)) {N : Subgroup W}
    (hN1 : N ≠ ⊥) (hNX : IsKSub X N)
    (hmin : ∀ N' : Subgroup W, N' ≤ N → IsKSub X N' → N' = ⊥ ∨ N' = N)
    (s : Finset (Subgroup W)) (hs : ∀ M ∈ s, IsSimple8 X M) (hNs : N ≤ s.sup id) :
    ∃ M ∈ s, Nat.card N = Nat.card M := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    rw [Finset.sup_empty] at hNs
    exact hN1 (le_bot_iff.mp hNs)
  | insert M₀ s' hM₀ ih =>
    have hs' : ∀ M ∈ s', IsSimple8 X M := fun M hM => hs M (Finset.mem_insert_of_mem hM)
    have hM₀s : IsSimple8 X M₀ := hs M₀ (Finset.mem_insert_self _ _)
    have hYinv : IsKSub X (s'.sup id) := isKSub_finset_sup s' fun M hM => (hs' M hM).1
    have hNs' : N ≤ M₀ ⊔ s'.sup id := by
      rw [Finset.sup_insert] at hNs
      exact hNs
    by_cases hNY : N ≤ s'.sup id
    · obtain ⟨M, hM, hc⟩ := ih hs' hNY
      exact ⟨M, Finset.mem_insert_of_mem hM, hc⟩
    · have hNYbot : N ⊓ s'.sup id = ⊥ := by
        rcases hmin (N ⊓ s'.sup id) inf_le_left (isKSub_inf hNX hYinv) with h | h
        · exact h
        · exact absurd (h ▸ inf_le_right) hNY
      have hM₀Y : M₀ ⊓ s'.sup id = ⊥ := by
        rcases hM₀s.2.2 (M₀ ⊓ s'.sup id) inf_le_left (isKSub_inf hM₀s.1 hYinv) with h | h
        · exact h
        · exfalso
          have hle : M₀ ≤ s'.sup id := by rw [← h]; exact inf_le_right
          exact hNY (hNs'.trans (sup_le hle le_rfl))
      have hZinv : IsKSub X (N ⊔ s'.sup id) := isKSub_sup hNX hYinv
      rcases hM₀s.2.2 (M₀ ⊓ (N ⊔ s'.sup id)) inf_le_left (isKSub_inf hM₀s.1 hZinv) with h | h
      · exfalso
        apply hN1
        rw [eq_bot_iff]
        intro n hn
        obtain ⟨m, hm, y, hy, hmy⟩ := Subgroup.mem_sup.mp (hNs' hn)
        have hmZ : m ∈ M₀ ⊓ (N ⊔ s'.sup id) := by
          refine ⟨hm, ?_⟩
          have : m = n * y⁻¹ := by rw [eq_mul_inv_iff_mul_eq]; exact hmy
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hn)
            (Subgroup.inv_mem _ (Subgroup.mem_sup_right hy))
        rw [h, Subgroup.mem_bot] at hmZ
        have hny : n = y := by rw [← hmy, hmZ, one_mul]
        have hnY : n ∈ N ⊓ s'.sup id := ⟨hn, hny ▸ hy⟩
        rw [hNYbot, Subgroup.mem_bot] at hnY
        rw [hnY]
        exact Subgroup.one_mem _
      · have hM₀le : M₀ ≤ N ⊔ s'.sup id := by rw [← h]; exact inf_le_right
        have hEq : M₀ ⊔ s'.sup id = N ⊔ s'.sup id :=
          le_antisymm (sup_le hM₀le le_sup_right) (sup_le hNs' le_sup_right)
        have c1 := card_sup_mul_card_inf M₀ (s'.sup id)
        have c2 := card_sup_mul_card_inf N (s'.sup id)
        rw [hM₀Y, Subgroup.card_bot, mul_one, hEq] at c1
        rw [hNYbot, Subgroup.card_bot, mul_one] at c2
        have hYpos : 0 < Nat.card ↥(s'.sup id) := Nat.card_pos
        exact ⟨M₀, Finset.mem_insert_self _ _,
          Nat.eq_of_mul_eq_mul_right hYpos (c2.symm.trans c1)⟩

theorem card_eq_eight_of_minimal [Finite W] (X : Subgroup (MulAut W)) {S : Subgroup W}
    (hS : S ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 X M), M) {N : Subgroup W} (hNS : N ≤ S)
    (hN1 : N ≠ ⊥) (hNX : IsKSub X N)
    (hmin : ∀ N' : Subgroup W, N' ≤ N → IsKSub X N' → N' = ⊥ ∨ N' = N) :
    Nat.card N = 8 := by
  classical
  have : Fintype (Subgroup W) := Fintype.ofFinite _
  let s : Finset (Subgroup W) := Finset.univ.filter fun M => IsSimple8 X M
  have hsup : (⨆ (M : Subgroup W) (_ : IsSimple8 X M), M) ≤ s.sup id := by
    refine iSup₂_le fun M hM => ?_
    exact Finset.le_sup (f := id) (by simp [s, hM])
  obtain ⟨M, hM, hc⟩ := card_eq_of_le_sup_simple8 X hN1 hNX hmin s
    (fun M hM => (Finset.mem_filter.mp hM).2) (hNS.trans (hS.trans hsup))
  rw [hc]
  exact ((Finset.mem_filter.mp hM).2).2.1

end Bridge

section Linear

variable {W : Type} [CommGroup W]

@[expose, instance_reducible] def z2Module (hW : ∀ w : W, w ^ 2 = 1) :
    Module (ZMod 2) (Additive W) :=
  AddCommGroup.zmodModule (fun v => by
    have h : Additive.ofMul (Additive.toMul v ^ 2) = Additive.ofMul 1 := by rw [hW]
    rw [ofMul_pow] at h
    simpa using h)

variable [Module (ZMod 2) (Additive W)]

@[expose] noncomputable def linAut : MulAut W →* Module.End (ZMod 2) (Additive W) where
  toFun k := AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun v : Additive W => Additive.ofMul (k (Additive.toMul v)))
      (fun a b => by simp [map_mul]))
  map_one' := by
    ext v
    rfl
  map_mul' k l := by
    ext v
    rfl

@[expose] def toSub (H : Subgroup W) : Submodule (ZMod 2) (Additive W) where
  carrier := {v | Additive.toMul v ∈ H}
  add_mem' := fun {_ _} ha hb => H.mul_mem ha hb
  zero_mem' := H.one_mem
  smul_mem' := by
    intro c v hv
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · simp
    · simpa using hv

@[expose] def ofSub (N : Submodule (ZMod 2) (Additive W)) : Subgroup W where
  carrier := {w | Additive.ofMul w ∈ N}
  mul_mem' := fun {_ _} ha hb => N.add_mem ha hb
  one_mem' := N.zero_mem
  inv_mem' := fun {_} ha => N.neg_mem ha

theorem mem_toSub {H : Subgroup W} {v : Additive W} : v ∈ toSub H ↔ Additive.toMul v ∈ H := Iff.rfl

theorem mem_ofSub {N : Submodule (ZMod 2) (Additive W)} {w : W} :
    w ∈ ofSub N ↔ Additive.ofMul w ∈ N := Iff.rfl

theorem toSub_ofSub (N : Submodule (ZMod 2) (Additive W)) : toSub (ofSub N) = N :=
  Submodule.ext fun _ => Iff.rfl

theorem ofSub_toSub (H : Subgroup W) : ofSub (toSub H) = H :=
  Subgroup.ext fun _ => Iff.rfl

theorem toSub_bot : toSub (⊥ : Subgroup W) = ⊥ := by
  ext v
  simp [mem_toSub, Submodule.mem_bot]

theorem ofSub_bot : ofSub (⊥ : Submodule (ZMod 2) (Additive W)) = ⊥ := by
  ext w
  simp [mem_ofSub, Subgroup.mem_bot]

theorem card_ofSub (N : Submodule (ZMod 2) (Additive W)) :
    Nat.card ↥(ofSub N) = Nat.card ↥N :=
  Nat.card_congr
    { toFun := fun w => ⟨Additive.ofMul w.1, w.2⟩
      invFun := fun v => ⟨Additive.toMul v.1, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Linear

section Main

variable {W : Type} [CommGroup W] [Finite W] [Module (ZMod 2) (Additive W)]

theorem card_eight_of_toSub_minimal (X : Subgroup (MulAut W)) {S : Subgroup W}
    (hS : S ≤ ⨆ (M : Subgroup W) (_ : IsSimple8 X M), M)
    {N : Submodule (ZMod 2) (Additive W)} (hNS : N ≤ toSub S) (hN1 : N ≠ ⊥)
    (hNX : ∀ g : ↥X, ∀ v ∈ N,
      (linAut.comp X.subtype : ↥X →* Module.End (ZMod 2) (Additive W)) g v ∈ N)
    (hmin : ∀ N' : Submodule (ZMod 2) (Additive W), N' ≤ N →
      (∀ g : ↥X, ∀ v ∈ N',
        (linAut.comp X.subtype : ↥X →* Module.End (ZMod 2) (Additive W)) g v ∈ N') →
      N' = ⊥ ∨ N' = N) :
    Nat.card N = 8 := by
  have h1 : IsKSub X (ofSub N) := fun k hk w hw => hNX ⟨k, hk⟩ (Additive.ofMul w) hw
  have h2 : ofSub N ≤ S := fun w hw => hNS hw
  have h3 : ofSub N ≠ ⊥ := by
    intro h
    apply hN1
    rw [← toSub_ofSub N, h, toSub_bot]
  have h4 : ∀ N' : Subgroup W, N' ≤ ofSub N → IsKSub X N' → N' = ⊥ ∨ N' = ofSub N := by
    intro N' hN'le hN'X
    have hle : toSub N' ≤ N := fun v hv => hN'le hv
    rcases hmin (toSub N') hle (fun g v hv => hN'X g g.2 _ hv) with h | h
    · left
      rw [← ofSub_toSub N', h, ofSub_bot]
    · right
      rw [← ofSub_toSub N', h]
  rw [← card_ofSub N]
  exact card_eq_eight_of_minimal X hS h2 h3 h1 h4

end Main

end CFSG.Quasithin.A38c16.Tensor
