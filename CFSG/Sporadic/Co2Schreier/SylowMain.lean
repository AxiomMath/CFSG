module

public import CFSG.Sporadic.Co2Schreier.SylowNode
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.RuSchreier
open scoped IsMulCommutative

theorem profTable_rows : ∀ w < 32, (profTable.getD w []).length = 12 := by
  decide

theorem unique_spec
    {k : ℕ} (hk : k < 5) {w : ℕ} (hw : w < 32) (hne : w ≠ 2 ^ k) :
    profTable.getD w [] ≠ profTable.getD (2 ^ k) [] := by
  have h := allLt_spec (allLt_spec unique_check hk) hw
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at h
  rcases h with h | h
  · exact absurd h hne
  · exact h

theorem rows_eq_of_getD {l₁ l₂ : List ℕ} (h₁ : l₁.length = 12) (h₂ : l₂.length = 12)
    (h : ∀ i < 12, l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  refine List.ext_getElem (h₁.trans h₂.symm) fun n hn₁ hn₂ => ?_
  have := h n (h₁ ▸ hn₁)
  rwa [List.getD_eq_getElem _ _ hn₁, List.getD_eq_getElem _ _ hn₂] at this

theorem bits5_two_pow {k : ℕ} (hk : k < 5) : bits5 (2 ^ k) = [k] := by
  interval_cases k <;> rfl

theorem getD_one_mem {H : Subgroup (Equiv.Perm (Fin 2300))} {l : List (Equiv.Perm (Fin 2300))}
    (hl : ∀ g ∈ l, g ∈ H) (k : ℕ) : l.getD k 1 ∈ H := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[k]? with
  | none => exact H.one_mem
  | some g => exact hl g (List.mem_of_getElem? h)

@[expose] def yBasisSub (k : ℕ) : locS := ⟨yBasisTuple.getD k 1, getD_one_mem yBasisTuple_mem_S k⟩

theorem ySub_eq_prod (w : ℕ) : ySub w = ((bits5 w).map yBasisSub).prod := by
  apply Subtype.ext
  rw [ySub]
  change prodList yBasisTuple (bits5 w) = _
  rw [prodList, Subgroup.val_list_prod, List.map_map]
  rfl

theorem cosetY_two_pow
    {k : ℕ} (hk : k < 5) :
    cosetY (2 ^ k) = (QuotientGroup.mk (yBasisSub k) : locS ⧸ frattini locS) := by
  rw [cosetY, ySub_eq_prod, bits5_two_pow hk]
  simp

theorem cosetY_eq_prod
    (w : ℕ) : cosetY w = ((bits5 w).map fun k =>
    (QuotientGroup.mk (yBasisSub k) : locS ⧸ frattini locS)).prod := by
  rw [cosetY, ySub_eq_prod, ← QuotientGroup.mk'_apply, map_list_prod, List.map_map]
  rfl

theorem profile_stabilizer_trivial :
    letI : CFSG.IsElementaryAbelian 2 (locS ⧸ frattini locS) :=
      (CFSG.GroupTheory.frattini_elementary_quotient isPGroup_locS).2.2.2.1
    ∀ T : Additive (locS ⧸ frattini locS) ≃ₗ[ZMod 2] Additive (locS ⧸ frattini locS),
      (∀ (v : Additive (locS ⧸ frattini locS)) (k : ℕ), 0 < k →
        Nat.card {x : locS // (x : locS ⧸ frattini locS) = (T v).toMul ∧ orderOf x = k} =
            Nat.card {x : locS // (x : locS ⧸ frattini locS) = v.toMul ∧ orderOf x = k} ∧
          Nat.card {x : locS // (x : locS ⧸ frattini locS) = (T v).toMul ∧
              orderOf (x : locS ⧸ Subgroup.center locS) = k} =
            Nat.card {x : locS // (x : locS ⧸ frattini locS) = v.toMul ∧
              orderOf (x : locS ⧸ Subgroup.center locS) = k}) →
      T = LinearEquiv.refl (ZMod 2) (Additive (locS ⧸ frattini locS)) := by
  let _inst : CFSG.IsElementaryAbelian 2 (locS ⧸ frattini locS) :=
    (CFSG.GroupTheory.frattini_elementary_quotient isPGroup_locS).2.2.2.1
  intro T hT
  have hfix : ∀ k < 5, T (Additive.ofMul (cosetY (2 ^ k))) = Additive.ofMul (cosetY (2 ^ k)) := by
    intro k hk
    set v := Additive.ofMul (cosetY (2 ^ k)) with hv
    obtain ⟨w, hw, hwe⟩ := exists_cosetY (T v).toMul
    have h2k : 2 ^ k < 32 := by
      calc 2 ^ k < 2 ^ 5 := Nat.pow_lt_pow_right (by norm_num) hk
        _ = 32 := by norm_num
    have hrow : profTable.getD w [] = profTable.getD (2 ^ k) [] := by
      refine rows_eq_of_getD (profTable_rows w hw) (profTable_rows _ h2k) fun i hi => ?_
      by_cases hi6 : i < 6
      · have h := (hT v (2 ^ i) (pow_pos (by norm_num) i)).2
        rw [← hwe, hv, toMul_ofMul, card_coset_orderOf_quot hw hi6,
          card_coset_orderOf_quot h2k hi6] at h
        exact h
      · have hi' : i - 6 < 6 := by omega
        have h := (hT v (2 ^ (i - 6)) (pow_pos (by norm_num) _)).1
        rw [← hwe, hv, toMul_ofMul, card_coset_orderOf hw hi', card_coset_orderOf h2k hi',
          show 6 + (i - 6) = i by omega] at h
        exact h
    have hw' : w = 2 ^ k := by
      by_contra hne
      exact unique_spec hk hw hne hrow
    calc T v = Additive.ofMul (Additive.toMul (T v)) := rfl
      _ = Additive.ofMul (cosetY w) := by rw [hwe]
      _ = v := by rw [hw', hv]
  let H : Subgroup (locS ⧸ frattini locS) :=
    { carrier := {q | T (Additive.ofMul q) = Additive.ofMul q}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [ofMul_mul, map_add, ha, hb]
      one_mem' := by
        simp only [Set.mem_ofPred_eq, ofMul_one, map_zero]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [ofMul_inv, map_neg, ha] }
  have hgen : ∀ k < 5, (QuotientGroup.mk (yBasisSub k) : locS ⧸ frattini locS) ∈ H := by
    intro k hk
    rw [← cosetY_two_pow hk]
    exact hfix k hk
  have hall : ∀ q, q ∈ H := by
    intro q
    obtain ⟨w, -, rfl⟩ := exists_cosetY q
    rw [cosetY_eq_prod]
    refine H.list_prod_mem fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hgen k (List.mem_range.1 (List.mem_filter.1 hk).1)
  refine LinearEquiv.ext fun v => ?_
  exact hall v.toMul

theorem AT_Co2_Sylow_Frattini_profiles :
    (Subgroup.center locS).map locS.subtype = Subgroup.zpowers locZ ∧
    Nat.card (locS ⧸ frattini locS) = 2 ^ 5 ∧
    Nonempty (Additive (locS ⧸ frattini locS) ≃+ (Fin 5 → ZMod 2)) ∧
    IsPGroup 2 (MulAut locS) ∧
    (letI : CFSG.IsElementaryAbelian 2 (locS ⧸ frattini locS) :=
        (CFSG.GroupTheory.frattini_elementary_quotient isPGroup_locS).2.2.2.1
      ∀ T : Additive (locS ⧸ frattini locS) ≃ₗ[ZMod 2] Additive (locS ⧸ frattini locS),
        (∀ (v : Additive (locS ⧸ frattini locS)) (k : ℕ), 0 < k →
          Nat.card {x : locS // (x : locS ⧸ frattini locS) = (T v).toMul ∧ orderOf x = k} =
              Nat.card {x : locS // (x : locS ⧸ frattini locS) = v.toMul ∧ orderOf x = k} ∧
            Nat.card {x : locS // (x : locS ⧸ frattini locS) = (T v).toMul ∧
                orderOf (x : locS ⧸ Subgroup.center locS) = k} =
              Nat.card {x : locS // (x : locS ⧸ frattini locS) = v.toMul ∧
                orderOf (x : locS ⧸ Subgroup.center locS) = k}) →
        T = LinearEquiv.refl (ZMod 2) (Additive (locS ⧸ frattini locS))) := by
  obtain ⟨-, -, -, -, d, hd, he⟩ := CFSG.GroupTheory.frattini_elementary_quotient isPGroup_locS
  have hd5 : d = 5 := by
    rw [card_quot_frattini] at hd
    exact (Nat.pow_right_injective le_rfl (hd.symm.trans (by norm_num : (32 : ℕ) = 2 ^ 5)))
  subst hd5
  exact ⟨center_locS, by rw [card_quot_frattini]; norm_num, he,
    CFSG.Sporadic.SchreierLemmas.Frattini_profile_automorphisms isPGroup_locS
      profile_stabilizer_trivial, profile_stabilizer_trivial⟩

end CFSG.Sporadic.Co2Schreier
