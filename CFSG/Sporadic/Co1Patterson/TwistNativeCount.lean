module

public import CFSG.Sporadic.Co1Patterson.TwistNativePCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

@[expose] def countPred (k t c : ℕ) (p : ℕ × ℕ) : Bool :=
  let s := eqA 240 (liftSq k c) negArr
  let x := Native.mul (hprodRow c) (aRowOf p)
  if t = 0 then (Native.mul x x == iotaARows && !s) || (Native.mul x x == Native.one && s)
  else (Native.mul x x == yRow 0 && !s) || (Native.mul x x == Native.mul (yRow 0) iotaARows && s)

theorem countTw_eq (k t : ℕ) :
    countTw k t = ((List.range 64).map fun c => (aList.filter (countPred k t c)).length).sum := by
  unfold countTw
  exact congrArg (fun f => ((List.range 64).map f).sum) (funext fun c => rfl)

theorem sum_range_eq_list (f : ℕ → ℕ) (n : ℕ) :
    ∑ c ∈ Finset.range n, f c = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem card_pairs_filter (l : List (ℕ × ℕ)) (hl : l.Nodup) (B : ℕ → ℕ × ℕ → Bool) :
    Nat.card {q : {q : ℕ × (ℕ × ℕ) // q.1 < 64 ∧ q.2 ∈ l} // B q.1.1 q.1.2 = true} =
      ((List.range 64).map fun c => (l.filter (B c)).length).sum := by
  have e : {q : {q : ℕ × (ℕ × ℕ) // q.1 < 64 ∧ q.2 ∈ l} // B q.1.1 q.1.2 = true} ≃
      Σ c : Fin 64, {p // p ∈ l.filter (B c)} :=
    { toFun := fun q => ⟨⟨q.1.1.1, q.1.2.1⟩, ⟨q.1.1.2, List.mem_filter.2 ⟨q.1.2.2, q.2⟩⟩⟩
      invFun := fun q => ⟨⟨(q.1, q.2.1), q.1.2, (List.mem_filter.1 q.2.2).1⟩,
        (List.mem_filter.1 q.2.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc : ∀ c : ℕ, Nat.card {p // p ∈ l.filter (B c)} = (l.filter (B c)).length := fun c => by
    rw [← Nat.card_congr (List.Nodup.getEquiv _ (hl.filter _)), Nat.card_eq_fintype_card,
      Fintype.card_fin]
  rw [Nat.card_congr e, Nat.card_sigma]
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range (fun c => (l.filter (B c)).length) 64]
  exact sum_range_eq_list _ 64

theorem card_Idx_filter (B : ℕ → ℕ × ℕ → Bool) :
    Nat.card {q : Idx // B q.1.1 q.1.2 = true} =
      ((List.range 64).map fun c => (aList.filter (B c)).length).sum :=
  card_pairs_filter aList aList_nodup B

theorem countOK_parts :
    countTw 1 0 = 3136 ∧ countTw 1 1 = 4032 ∧ countTw 2 0 = 3136 ∧ countTw 2 1 = 4032 := by
  have h := tw_count_check
  simp only [countOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

variable
  (k : Fin 3)

theorem liftRoots_lt (c : ℕ) : ∀ r ∈ liftRoots k c, r < 240 := by
  rw [liftRoots_eq]
  intro r hr
  obtain ⟨j, hj, hr⟩ := List.mem_flatMap.1 hr
  exact omWords_lt (liftLetter_lt (cword_lt c j hj)) r hr

theorem rep_liftSq (c : ℕ) :
    Rep 240 (liftSq k c) ((eHat k c * eHat k c : wPlus) : Equiv.Perm (Fin 240)) := by
  have h := rep_wordArr _ (liftRoots_lt k c)
  rw [liftSq, Subgroup.coe_mul, eHat, coe_liftWord k _ (cword_lt c), ← liftRoots_eq]
  exact rep_compA h h

theorem liftSq_neg_iff (c : ℕ) :
    eqA 240 (liftSq k c) negArr = true ↔ eHat k c * eHat k c = zPlus := by
  rw [eqA_iff (rep_liftSq k c) rep_negArr]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

@[expose] def IsGenuine (k : Fin 3) : Prop := (k : ℕ) = 1 ∨ (k : ℕ) = 2

theorem signOK_parts : ∀ k ∈ [1, 2], ∀ c < 64,
    (eqA 240 (liftSq k c) negArr || eqA 240 (liftSq k c) (idA 240)) = true := by
  have h := tw_sign_check
  simp only [signOK, List.all_eq_true, List.mem_range] at h
  exact h

theorem eHat_sq (hk : IsGenuine k) {c : ℕ} (hc : c < 64) :
    eHat k c * eHat k c = zPlus ∨ eHat k c * eHat k c = 1 := by
  have h := signOK_parts (k : ℕ) (by rcases hk with h | h <;> simp [h]) c hc
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl ((liftSq_neg_iff k c).1 h)
  · right
    exact Subtype.ext ((eqA_iff (rep_liftSq k c) rep_idA).1 h)

theorem rep_sqRow (c : ℕ) (p : ℕ × ℕ) :
    MRep (Native.mul (Native.mul (hprodRow c) (aRowOf p)) (Native.mul (hprodRow c) (aRowOf p)))
      (centEmb ((hcH c * aElt p) * (hcH c * aElt p))) := by
  rw [map_mul, map_mul]
  exact ((rep_hcH c).mul (rep_aElt p)).mul ((rep_hcH c).mul (rep_aElt p))

theorem valid_sqRow (c : ℕ) {p : ℕ × ℕ} (hp : p.1 < 256) :
    CFSG.Sporadic.Co1.InvNative.validRows
      (Native.mul (Native.mul (hprodRow c) (aRowOf p))
        (Native.mul (hprodRow c) (aRowOf p))) = true :=
  valid_mul (valid_mul (valid_hprodRow c) (valid_aRowOf hp))
    (valid_mul (valid_hprodRow c) (valid_aRowOf hp))

theorem sqRow_beq_iff (c : ℕ) {p : ℕ × ℕ} (hp : p.1 < 256) {Y : Native.Rows}
    {y : centralizer ({aNC} : Set NativeSporadic.Co1)} (hY : MRep Y (centEmb y))
    (vY : CFSG.Sporadic.Co1.InvNative.validRows Y = true) :
    (Native.mul (Native.mul (hprodRow c) (aRowOf p)) (Native.mul (hprodRow c) (aRowOf p)) ==
      Y) = true ↔ (hcH c * aElt p) * (hcH c * aElt p) = y := by
  rw [rows_beq_iff (rep_sqRow c p) hY (valid_sqRow c hp) vY, centEmb_injective.eq_iff]

theorem rep_z_row : MRep iotaARows (centEmb typeSystemC.z) := by
  rw [show centEmb typeSystemC.z = aG from centEmb_zM]
  exact rep_iotaA

theorem rep_one_row : MRep Native.one (centEmb 1) := by
  rw [map_one]
  exact MRep.one

theorem rep_w_row : MRep (yRow 0) (centEmb (yH 0)) := by
  rw [centEmb_yH]
  exact rep_yG 0

theorem rep_wz_row : MRep (Native.mul (yRow 0) iotaARows) (centEmb (yH 0 * typeSystemC.z)) := by
  rw [map_mul]
  exact rep_w_row.mul rep_z_row

theorem tw_eq_zT_iff (g : FP k) : tw k g = zT k ↔
    (g.val.1 = typeSystemC.z ∧ g.val.2 = 1) ∨ (g.val.1 = 1 ∧ g.val.2 = zPlus) := by
  rw [zT, twZ, tw_eq_tw_iff]
  constructor
  · rintro (h | h)
    · have h1 : (z1Fib typeSystemC : FP k).val.1 = g.val.1 := by rw [h]
      have h2 : (z1Fib typeSystemC : FP k).val.2 = g.val.2 := by rw [h]
      exact Or.inl ⟨h1.symm, h2.symm⟩
    · have h1 : (z1Fib typeSystemC : FP k).val.1 = (g * zζ typeSystemC (wPlusMap iotaC k) zPlus
          (wPlusMap_zPlus iotaC k) : FP k).val.1 := by rw [h]
      have h2 : (z1Fib typeSystemC : FP k).val.2 = (g * zζ typeSystemC (wPlusMap iotaC k) zPlus
          (wPlusMap_zPlus iotaC k) : FP k).val.2 := by rw [h]
      rw [fst_mul_zζ, fst_z1Fib] at h1
      rw [snd_mul_zζ, snd_z1Fib] at h2
      refine Or.inr ⟨?_, ?_⟩
      · calc g.val.1 = g.val.1 * typeSystemC.z * typeSystemC.z := by
              rw [mul_assoc, typeSystemC.z_mul_self, mul_one]
          _ = 1 := by rw [← h1, typeSystemC.z_mul_self]
      · calc g.val.2 = g.val.2 * zPlus * zPlus := by rw [mul_assoc, zPlus_mul_self, mul_one]
          _ = zPlus := by rw [← h2, one_mul]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      exact Subtype.ext (Prod.ext h1.symm h2.symm)
    · right
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change typeSystemC.z = g.val.1 * typeSystemC.z
        rw [h1, one_mul]
      · change (1 : wPlus) = g.val.2 * zPlus
        rw [h2, zPlus_mul_self]

theorem tw_eq_wT_iff (g : FP k) : tw k g = wT k ↔
    (g.val.1 = yH 0 ∧ g.val.2 = 1) ∨ (g.val.1 = yH 0 * typeSystemC.z ∧ g.val.2 = zPlus) := by
  rw [wT, tw_eq_tw_iff]
  constructor
  · rintro (h | h)
    · have h1 : (wFib k : FP k).val.1 = g.val.1 := by rw [h]
      have h2 : (wFib k : FP k).val.2 = g.val.2 := by rw [h]
      exact Or.inl ⟨h1.symm, h2.symm⟩
    · have h1 : (wFib k : FP k).val.1 = (g * zζ typeSystemC (wPlusMap iotaC k) zPlus
          (wPlusMap_zPlus iotaC k) : FP k).val.1 := by rw [h]
      have h2 : (wFib k : FP k).val.2 = (g * zζ typeSystemC (wPlusMap iotaC k) zPlus
          (wPlusMap_zPlus iotaC k) : FP k).val.2 := by rw [h]
      rw [fst_mul_zζ, fst_wFib] at h1
      rw [snd_mul_zζ, snd_wFib] at h2
      refine Or.inr ⟨?_, ?_⟩
      · rw [h1, mul_assoc, typeSystemC.z_mul_self, mul_one]
      · calc g.val.2 = g.val.2 * zPlus * zPlus := by rw [mul_assoc, zPlus_mul_self, mul_one]
          _ = zPlus := by rw [← h2, one_mul]
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · left
      exact Subtype.ext (Prod.ext h1.symm h2.symm)
    · right
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change yH 0 = g.val.1 * typeSystemC.z
        rw [h1, mul_assoc, typeSystemC.z_mul_self, mul_one]
      · change (1 : wPlus) = g.val.2 * zPlus
        rw [h2, zPlus_mul_self]

theorem sq_Ψ (c : ℕ) (p : ℕ × ℕ) : Ψ k c p ^ 2 = tw k (ψFib k c p * ψFib k c p) := by
  rw [sq]
  rfl

theorem fst_ψsq (c : ℕ) (p : ℕ × ℕ) :
    (ψFib k c p * ψFib k c p : FP k).val.1 = (hcH c * aElt p) * (hcH c * aElt p) := rfl

theorem snd_ψsq (c : ℕ) (p : ℕ × ℕ) :
    (ψFib k c p * ψFib k c p : FP k).val.2 = eHat k c * eHat k c := rfl

theorem not_iff_one {e : wPlus} (he : e = zPlus ∨ e = 1) : ¬ e = zPlus ↔ e = 1 := by
  rcases he with h | h
  · rw [h]
    exact ⟨fun h1 => absurd rfl h1, fun h1 => absurd h1 zPlus_ne_one⟩
  · rw [h]
    exact ⟨fun _ => rfl, fun _ h2 => zPlus_ne_one h2.symm⟩

theorem sq_Ψ_eq_zT_iff (hk : IsGenuine k) {c : ℕ} (hc : c < 64) {p : ℕ × ℕ} (hp : p ∈ aList) :
    Ψ k c p ^ 2 = zT k ↔ countPred k 0 c p = true := by
  have hp1 := (mem_aList.1 hp).1
  rw [sq_Ψ, tw_eq_zT_iff, fst_ψsq, snd_ψsq]
  simp only [countPred, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true']
  rw [sqRow_beq_iff c hp1 rep_z_row dagOK_parts.2.1, sqRow_beq_iff c hp1 rep_one_row validRows_one,
    ← Bool.not_eq_true, liftSq_neg_iff, not_iff_one (eHat_sq k hk hc)]

theorem sq_Ψ_eq_wT_iff (hk : IsGenuine k) {c : ℕ} (hc : c < 64) {p : ℕ × ℕ} (hp : p ∈ aList) :
    Ψ k c p ^ 2 = wT k ↔ countPred k 1 c p = true := by
  have hp1 := (mem_aList.1 hp).1
  rw [sq_Ψ, tw_eq_wT_iff, fst_ψsq, snd_ψsq]
  simp only [countPred, one_ne_zero, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true']
  rw [sqRow_beq_iff c hp1 rep_w_row (dagOK_parts.2.2.1 0 (by norm_num)),
    sqRow_beq_iff c hp1 rep_wz_row (valid_mul (dagOK_parts.2.2.1 0 (by norm_num))
      dagOK_parts.2.1), ← Bool.not_eq_true, liftSq_neg_iff, not_iff_one (eHat_sq k hk hc)]

theorem card_sq_zT (hk : IsGenuine k) :
    Nat.card {x : CFSG.pCore 2 (Kc k) // ((x : Kc k) : TM k) ^ 2 = zT k} = 3136 := by
  rw [card_sq_pCore_eq k (zT k),
    Nat.card_congr (Equiv.subtypeEquivRight fun q : Idx => sq_Ψ_eq_zT_iff k hk q.2.1 q.2.2),
    card_Idx_filter, ← countTw_eq]
  rcases hk with hk | hk <;> rw [hk]
  · exact countOK_parts.1
  · exact countOK_parts.2.2.1

theorem card_sq_wT (hk : IsGenuine k) :
    Nat.card {x : CFSG.pCore 2 (Kc k) // ((x : Kc k) : TM k) ^ 2 = wT k} = 4032 := by
  rw [card_sq_pCore_eq k (wT k),
    Nat.card_congr (Equiv.subtypeEquivRight fun q : Idx => sq_Ψ_eq_wT_iff k hk q.2.1 q.2.2),
    card_Idx_filter, ← countTw_eq]
  rcases hk with hk | hk <;> rw [hk]
  · exact countOK_parts.2.1
  · exact countOK_parts.2.2.2

end CFSG.Sporadic.Co1Patterson.TwistNative
