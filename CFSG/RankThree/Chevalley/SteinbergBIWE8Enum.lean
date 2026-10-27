module

public import CFSG.RankThree.Chevalley.SteinbergBIWE8Code

public noncomputable section

namespace CFSG.RankThree.Chevalley.WeylE8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley.WE8.Native

theorem pairT_getD {a : ℕ} (ha : a < 240) (k : Fin Tag.E8.rank) :
    (pairT.getD a #[]).getD k 0 = pair k (rootsL.getD a []) := by
  rw [pairT, getD_roots_map _ _ ha, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  have hk : (k : ℕ) < 8 := k.2
  simp only [hk, dite_true, Option.getD_some]

theorem ipT_getD {a b : ℕ} (ha : a < 240) (hb : b < 240) :
    (ipT.getD b #[]).getD a 0 = ip (rootsL.getD b []) (rootsL.getD a []) := by
  rw [ipT, getD_roots_map _ _ hb, getD_roots_map _ _ ha]

theorem okFrom_of_forall (sgn : ℤ) (a n : ℕ) (pa : Array ℤ) :
    ∀ (bs : List ℕ) (j₀ : ℕ), (∀ k (hk : k < bs.length),
      (ipT.getD bs[k] #[]).getD a 0 = cart (j₀ + k) n ∧
        pa.getD (j₀ + k) 0 = sgn * (pairT.getD bs[k] #[]).getD n 0) →
      okFrom sgn a n pa j₀ bs = true
  | [], _, _ => rfl
  | b :: bs, j₀, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero, add_zero] at h0
    simp only [okFrom, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨h0.1, h0.2⟩, okFrom_of_forall sgn a n pa bs (j₀ + 1) fun k hk => ?_⟩
    have := h (k + 1) (by simp only [List.length_cons]; omega)
    simp only [List.getElem_cons_succ] at this
    rwa [show j₀ + (k + 1) = j₀ + 1 + k by ring] at this

@[expose] def SgnSym (sgn : ℤ) (w : W8) : Prop :=
  ∀ i j : Fin Tag.E8.rank, iform (w • eb i) (eb j) = sgn * iform (eb i) (w • eb j)

theorem sym_of_sq_eq_one {t : W8} (ht : t * t = 1) : SgnSym 1 t := by
  intro i j
  rw [one_mul]
  conv_lhs => rw [← iform_smul t]
  rw [← mul_smul, ht, one_smul]

theorem iform_neg_right (u v : L8) : iform u (-v) = -iform u v := by
  simp [iform, Finset.sum_neg_distrib]

theorem skew_of_sq_eq_neg {y : W8} (hy : ∀ v : L8, (y * y) • v = -v) : SgnSym (-1) y := by
  intro i j
  have e1 : eb j = -(y • y • eb j) := by rw [← mul_smul, hy, neg_neg]
  rw [neg_one_mul]
  conv_lhs => rw [e1]
  rw [iform_neg_right, iform_smul]

theorem take_code_mem_enum {sgn : ℤ} {w : W8} (hw : SgnSym sgn w) :
    ∀ n ≤ 8, (code w).take n ∈ enum sgn n := by
  intro n
  induction n with
  | zero => intro _; simp [enum]
  | succ n ih =>
    intro hn
    have hn8 : n < Tag.E8.rank := by change n < 8; omega
    have hlen : n < (code w).length := by rw [length_code]; omega
    rw [enum, List.mem_flatMap]
    refine ⟨(code w).take n, ih (by omega), ?_⟩
    rw [extend, List.mem_map]
    refine ⟨(code w)[n], List.mem_filter.2 ⟨?_, ?_⟩, ?_⟩
    · rw [List.mem_range, ← List.getD_eq_getElem _ 0 hlen]
      exact getD_code_lt w ⟨n, hn8⟩
    · have hlt : (code w)[n] < 240 := by
        rw [← List.getD_eq_getElem _ 0 hlen]
        exact getD_code_lt w ⟨n, hn8⟩
      have hcol : rootsL.getD (code w)[n] [] = toL (w • eb ⟨n, hn8⟩) := by
        rw [← List.getD_eq_getElem _ 0 hlen]
        exact col_code w ⟨n, hn8⟩
      have htake : ((code w).take n).length = n := by
        rw [List.length_take]; omega
      simp only [okNew, Bool.and_eq_true, beq_iff_eq, htake]
      refine ⟨?_, okFrom_of_forall sgn _ n _ _ 0 fun k hk => ?_⟩
      · rw [pairT_getD hlt ⟨n, hn8⟩, hcol, pair_toL_eq_iform]
        have h := hw ⟨n, hn8⟩ ⟨n, hn8⟩
        rwa [iform_comm (w • eb _)] at h
      · rw [htake] at hk
        have hk8 : k < Tag.E8.rank := by change k < 8; omega
        have hk' : k < (code w).length := by rw [length_code]; omega
        rw [List.getElem_take, zero_add]
        have hltk : (code w)[k] < 240 := by
          rw [← List.getD_eq_getElem _ 0 hk']
          exact getD_code_lt w ⟨k, hk8⟩
        have hcolk : rootsL.getD (code w)[k] [] = toL (w • eb ⟨k, hk8⟩) := by
          rw [← List.getD_eq_getElem _ 0 hk']
          exact col_code w ⟨k, hk8⟩
        refine ⟨?_, ?_⟩
        · rw [ipT_getD hlt hltk, hcolk, hcol, ip_toL, iform_smul, iform_eb]
          exact (cart_eq ⟨k, hk8⟩ ⟨n, hn8⟩).symm
        · rw [pairT_getD hlt ⟨k, hk8⟩, hcol, pair_toL_eq_iform, pairT_getD hltk ⟨n, hn8⟩, hcolk,
            pair_toL_eq_iform, iform_comm]
          exact hw ⟨n, hn8⟩ ⟨k, hk8⟩
    · rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some]

theorem code_mem_enum {sgn : ℤ} {w : W8} (hw : SgnSym sgn w) : code w ∈ enum sgn 8 := by
  have h := take_code_mem_enum hw 8 le_rfl
  rwa [List.take_of_length_le (by rw [length_code])] at h

theorem card_le_enum (sgn : ℤ) : Nat.card {w : W8 // SgnSym sgn w} ≤ (enum sgn 8).length := by
  classical
  let f : {w : W8 // SgnSym sgn w} → (enum sgn 8).toFinset := fun w =>
    ⟨code w, List.mem_toFinset.2 (code_mem_enum w.2)⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (code_injective (congrArg Subtype.val hab))
  calc Nat.card {w : W8 // SgnSym sgn w} ≤ Nat.card (enum sgn 8).toFinset :=
        Nat.card_le_card_of_injective f hf
    _ = (enum sgn 8).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (enum sgn 8).length := List.toFinset_card_le _

end CFSG.RankThree.Chevalley.WeylE8
