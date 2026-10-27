module

public import Certificates.Data.SUSmallCheck
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Sporadic.Suz.Simple

public section

namespace Certificates.SUSmall

open CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def hdRo7SmKeysAux_fiberCard {m : ℕ} (p : Pair m) (k : Fin 9) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => pairCode (p.1 i) (p.2 i) = k)).card

lemma hdRo7SmKeysAux_key_eq_map {m : ℕ} (p : Pair m) :
    key p = (List.finRange 9).map (hdRo7SmKeysAux_fiberCard p) := rfl

lemma hdRo7SmKeysAux_pairCode_inj {x y x' y' : ZMod 3}
    (h : pairCode x y = pairCode x' y') : x = x' ∧ y = y' := by
  have hv : x.val * 3 + y.val = x'.val * 3 + y'.val := by
    have := congrArg Fin.val h
    simpa [pairCode] using this
  have hx := ZMod.val_lt x; have hy := ZMod.val_lt y
  have hx' := ZMod.val_lt x'; have hy' := ZMod.val_lt y'
  have hxv : x.val = x'.val := by omega
  have hyv : y.val = y'.val := by omega
  exact ⟨(ZMod.val_injective 3) hxv, (ZMod.val_injective 3) hyv⟩

lemma hdRo7SmKeysAux_uOf_pairCode (x y : ZMod 3) : uOf (pairCode x y) = x := by
  have h1 : (pairCode x y).val / 3 = x.val := by
    simp only [pairCode, Fin.val_mk]
    exact Nat.div_eq_of_lt_le (by omega) (by have := ZMod.val_lt y; omega)
  rw [uOf, h1]
  exact ZMod.natCast_zmod_val x

lemma hdRo7SmKeysAux_phiOf_pairCode (x y : ZMod 3) : phiOf (pairCode x y) = y := by
  have h1 : (pairCode x y).val % 3 = y.val := by
    simp only [pairCode, Fin.val_mk]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt (ZMod.val_lt y)
  rw [phiOf, h1]
  exact ZMod.natCast_zmod_val y

lemma hdRo7SmKeysAux_pairCode_uOf_phiOf (k : Fin 9) : pairCode (uOf k) (phiOf k) = k := by
  apply Fin.ext
  have hu : (uOf k).val = k.val / 3 := by
    rw [uOf]; exact ZMod.val_cast_of_lt (by have := k.isLt; omega)
  have hp : (phiOf k).val = k.val % 3 := by
    rw [phiOf]; exact ZMod.val_cast_of_lt (by have := k.isLt; omega)
  simp only [pairCode, Fin.val_mk, hu, hp]
  have := k.isLt
  omega

lemma hdRo7SmKeysAux_negCode_involutive (k : Fin 9) : negCode (negCode k) = k := by
  unfold negCode
  rw [hdRo7SmKeysAux_uOf_pairCode, hdRo7SmKeysAux_phiOf_pairCode]
  simp only [neg_neg]
  exact hdRo7SmKeysAux_pairCode_uOf_phiOf k

lemma hdRo7SmKeysAux_pairCode_neg (x y : ZMod 3) :
    pairCode (-x) (-y) = negCode (pairCode x y) := by
  unfold negCode
  rw [hdRo7SmKeysAux_uOf_pairCode, hdRo7SmKeysAux_phiOf_pairCode]

lemma hdRo7SmKeysAux_key_length {m : ℕ} (p : Pair m) : (key p).length = 9 := by
  rw [hdRo7SmKeysAux_key_eq_map, List.length_map, List.length_finRange]

lemma hdRo7SmKeysAux_finRange_getElem (n : ℕ) (i : Fin n) :
    (List.finRange n)[i.val] = i := by
  rw [List.getElem_finRange]
  exact Fin.ext rfl

lemma hdRo7SmKeysAux_key_getD {m : ℕ} (p : Pair m) (k : Fin 9) :
    (key p).getD k 0 = hdRo7SmKeysAux_fiberCard p k := by
  rw [hdRo7SmKeysAux_key_eq_map, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_map, List.length_finRange]; exact k.isLt),
    Option.getD_some]
  simp only [List.getElem_map]
  rw [hdRo7SmKeysAux_finRange_getElem]

lemma hdRo7SmKeysAux_negKey_getD (c : List ℕ) (k : Fin 9) :
    (negKey c).getD k 0 = c.getD (negCode k) 0 := by
  rw [negKey, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by rw [List.length_map, List.length_finRange]; exact k.isLt),
    Option.getD_some]
  simp only [List.getElem_map]
  rw [hdRo7SmKeysAux_finRange_getElem]

lemma hdRo7SmKeysAux_negKey_length (c : List ℕ) : (negKey c).length = 9 := by
  rw [negKey, List.length_map, List.length_finRange]

lemma hdRo7SmKeysAux_key_ext {c d : List ℕ} (hc : c.length = 9) (hd : d.length = 9)
    (h : ∀ k : Fin 9, c.getD k 0 = d.getD k 0) : c = d := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 9
  · rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    congr 1
    rw [← List.getD_eq_getElem c 0 (by omega), ← List.getD_eq_getElem d 0 (by omega)]
    exact h ⟨i, hi⟩
  · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]

lemma hdRo7SmKeysAux_negKey_involutive {c : List ℕ} (hc : c.length = 9) :
    negKey (negKey c) = c := by
  apply hdRo7SmKeysAux_key_ext (hdRo7SmKeysAux_negKey_length (negKey c)) hc
  intro k
  rw [hdRo7SmKeysAux_negKey_getD, hdRo7SmKeysAux_negKey_getD, hdRo7SmKeysAux_negCode_involutive]

lemma hdRo7SmKeysAux_negKey_injective {c d : List ℕ} (hc : c.length = 9) (hd : d.length = 9)
    (h : negKey c = negKey d) : c = d := by
  have := congrArg negKey h
  rwa [hdRo7SmKeysAux_negKey_involutive hc, hdRo7SmKeysAux_negKey_involutive hd] at this

lemma hdRo7SmKeysAux_sum_map_finRange {α : Type*} [AddCommMonoid α] :
    ∀ (n : ℕ) (f : Fin n → α), ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  intro n
  induction n with
  | zero => intro f; simp
  | succ n ih =>
    intro f
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, ih (f ∘ Fin.succ),
      Fin.sum_univ_succ]
    rfl

lemma hdRo7SmKeysAux_key_sum {m : ℕ} (p : Pair m) : (key p).sum = m := by
  rw [hdRo7SmKeysAux_key_eq_map, hdRo7SmKeysAux_sum_map_finRange]
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin m)))
      (t := (Finset.univ : Finset (Fin 9)))
      (f := fun i : Fin m => pairCode (p.1 i) (p.2 i)) (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  exact (Finset.sum_congr rfl (fun k _ => by rw [hdRo7SmKeysAux_fiberCard])).trans h.symm

@[expose] def hdRo7SmKeysAux_encAux (n : ℕ) (c : List ℕ) : ℕ :=
  ((List.finRange n).map Fin.val).foldl (fun acc k => acc * 10 + c.getD k 0) 0

lemma hdRo7SmKeysAux_enc_eq_encAux (c : List ℕ) : enc c = hdRo7SmKeysAux_encAux 9 c :=
  rfl

lemma hdRo7SmKeysAux_encAux_succ (n : ℕ) (c : List ℕ) :
    hdRo7SmKeysAux_encAux (n + 1) c = hdRo7SmKeysAux_encAux n c * 10 + c.getD n 0 := by
  unfold hdRo7SmKeysAux_encAux
  rw [List.finRange_succ_last, List.map_append, List.map_map]
  simp only [Function.comp_apply, Fin.val_castSucc, List.map_singleton, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  congr 1

lemma hdRo7SmKeysAux_encAux_inj (n : ℕ) {c d : List ℕ}
    (hc : ∀ k, c.getD k 0 < 10) (hd : ∀ k, d.getD k 0 < 10)
    (h : hdRo7SmKeysAux_encAux n c = hdRo7SmKeysAux_encAux n d) :
    ∀ k < n, c.getD k 0 = d.getD k 0 := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    intro k hk
    rw [hdRo7SmKeysAux_encAux_succ, hdRo7SmKeysAux_encAux_succ] at h
    have hmod : c.getD n 0 = d.getD n 0 := by
      have hcong := congrArg (· % 10) h
      have h1 : (hdRo7SmKeysAux_encAux n c * 10 + c.getD n 0) % 10 = c.getD n 0 % 10 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      have h2 : (hdRo7SmKeysAux_encAux n d * 10 + d.getD n 0) % 10 = d.getD n 0 % 10 := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right]
      rw [h1, h2, Nat.mod_eq_of_lt (hc n), Nat.mod_eq_of_lt (hd n)] at hcong
      exact hcong
    have hcancel : hdRo7SmKeysAux_encAux n c * 10 = hdRo7SmKeysAux_encAux n d * 10 := by
      rw [hmod] at h
      exact Nat.add_right_cancel h
    have hX : hdRo7SmKeysAux_encAux n c = hdRo7SmKeysAux_encAux n d :=
      Nat.mul_right_cancel (by norm_num) hcancel
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | heq
    · exact ih hX k hlt
    · rw [heq]; exact hmod

lemma hdRo7SmKeysAux_enc_inj {c d : List ℕ} (hc : c.length = 9) (hd : d.length = 9)
    (hc' : ∀ k, c.getD k 0 < 10) (hd' : ∀ k, d.getD k 0 < 10) (h : enc c = enc d) : c = d := by
  rw [hdRo7SmKeysAux_enc_eq_encAux, hdRo7SmKeysAux_enc_eq_encAux] at h
  have hk := hdRo7SmKeysAux_encAux_inj 9 hc' hd' h
  apply List.ext_getElem?
  intro i
  by_cases hi : i < 9
  · rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    congr 1
    rw [← List.getD_eq_getElem c 0 (by omega), ← List.getD_eq_getElem d 0 (by omega)]
    exact hk i hi
  · rw [List.getElem?_eq_none_iff.mpr (by omega), List.getElem?_eq_none_iff.mpr (by omega)]

lemma hdRo7SmKeysAux_key_digits {m : ℕ} (hm : m ≤ 9) (p : Pair m) :
    ∀ k : ℕ, (key p).getD k 0 < 10 := by
  intro k
  by_cases hk : k < 9
  · rw [hdRo7SmKeysAux_key_getD p ⟨k, hk⟩, hdRo7SmKeysAux_fiberCard]
    have h1 : (Finset.univ.filter
        (fun i : Fin m => pairCode (p.1 i) (p.2 i) = (⟨k, hk⟩ : Fin 9))).card ≤ m := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_filter_le (Finset.univ : Finset (Fin m))
          (fun i => pairCode (p.1 i) (p.2 i) = (⟨k, hk⟩ : Fin 9)))
    omega
  · rw [List.getD_eq_default _ _ (by rw [hdRo7SmKeysAux_key_length]; omega)]
    norm_num

lemma hdRo7SmKeysAux_negKey_digits {m : ℕ} (hm : m ≤ 9) (p : Pair m) :
    ∀ k : ℕ, (negKey (key p)).getD k 0 < 10 := by
  intro k
  by_cases hk : k < 9
  · rw [hdRo7SmKeysAux_negKey_getD (key p) ⟨k, hk⟩]
    exact hdRo7SmKeysAux_key_digits hm p ((negCode ⟨k, hk⟩ : Fin 9) : ℕ)
  · rw [List.getD_eq_default _ _ (by rw [hdRo7SmKeysAux_negKey_length]; omega)]
    norm_num

lemma hdRo7SmKeysAux_exists_perm_of_fiber_card_eq {m : ℕ} {f g : Fin m → Fin 9}
    (h : ∀ k, (Finset.univ.filter (fun i => f i = k)).card =
      (Finset.univ.filter (fun i => g i = k)).card) :
    ∃ σ : Equiv.Perm (Fin m), ∀ i, f i = g (σ i) := by
  classical
  refine ⟨Equiv.ofFiberEquiv (f := f) (g := g) (fun k => Fintype.equivOfCardEq ?_), ?_⟩
  · rw [Fintype.card_subtype, Fintype.card_subtype]; exact h k
  · intro i
    exact (Equiv.ofFiberEquiv_map (f := f) (g := g) _ i).symm

lemma hdRo7SmKeysAux_fiber_card_eq_of_perm {m : ℕ} {f g : Fin m → Fin 9}
    (σ : Equiv.Perm (Fin m)) (h : ∀ i, f i = g (σ i)) (k : Fin 9) :
    (Finset.univ.filter (fun i => f i = k)).card =
      (Finset.univ.filter (fun i => g i = k)).card := by
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [← h i]; exact hi
  · intro i₁ _ i₂ _ heq
    exact σ.injective heq
  · intro j hj
    refine ⟨σ.symm j, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    have := h (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [this]; exact hj

lemma hdRo7SmKeysAux_key_eq_of_fiber_eq {m : ℕ} {p q : Pair m}
    (h : hdRo7SmKeysAux_fiberCard p = hdRo7SmKeysAux_fiberCard q) : key p = key q := by
  rw [hdRo7SmKeysAux_key_eq_map, hdRo7SmKeysAux_key_eq_map, h]

lemma hdRo7SmKeysAux_key_eq_of_perm {m : ℕ} {p q : Pair m} (σ : Equiv.Perm (Fin m))
    (h : ∀ i, pairCode (p.1 i) (p.2 i) = pairCode (q.1 (σ i)) (q.2 (σ i))) : key p = key q := by
  apply hdRo7SmKeysAux_key_eq_of_fiber_eq
  funext k
  rw [hdRo7SmKeysAux_fiberCard, hdRo7SmKeysAux_fiberCard]
  exact hdRo7SmKeysAux_fiber_card_eq_of_perm σ h k

lemma hdRo7SmKeysAux_key_eq_negKey_of_perm {m : ℕ} {p q : Pair m} (σ : Equiv.Perm (Fin m))
    (h : ∀ i, pairCode (p.1 i) (p.2 i) = negCode (pairCode (q.1 (σ i)) (q.2 (σ i)))) :
    key p = negKey (key q) := by
  apply hdRo7SmKeysAux_key_ext (hdRo7SmKeysAux_key_length p)
    (hdRo7SmKeysAux_negKey_length (key q))
  intro k
  rw [hdRo7SmKeysAux_key_getD, hdRo7SmKeysAux_negKey_getD, hdRo7SmKeysAux_key_getD]
  rw [hdRo7SmKeysAux_fiberCard, hdRo7SmKeysAux_fiberCard]
  have h1 : (Finset.univ.filter (fun i : Fin m => pairCode (p.1 i) (p.2 i) = k)) =
      (Finset.univ.filter (fun i : Fin m => pairCode (q.1 (σ i)) (q.2 (σ i)) = negCode k)) := by
    apply Finset.filter_congr
    intro i _
    rw [h i]
    constructor
    · intro hh; rw [← hh, hdRo7SmKeysAux_negCode_involutive]
    · intro hh; rw [hh, hdRo7SmKeysAux_negCode_involutive]
  rw [h1]
  exact hdRo7SmKeysAux_fiber_card_eq_of_perm
    (f := fun i => pairCode (q.1 (σ i)) (q.2 (σ i)))
    (g := fun i => pairCode (q.1 i) (q.2 i)) σ (fun i => rfl) (negCode k)

lemma hdRo7SmKeysAux_smClass_key_rel {m : ℕ} {p q : Pair m} (h : SMClass p q) :
    key p = key q ∨ key p = negKey (key q) := by
  obtain ⟨π, s, hs, hpq⟩ := h
  rcases hs with rfl | rfl
  · left
    apply hdRo7SmKeysAux_key_eq_of_perm π
    intro i
    rw [(hpq i).1, (hpq i).2, one_mul, one_mul]
  · right
    apply hdRo7SmKeysAux_key_eq_negKey_of_perm π
    intro i
    rw [(hpq i).1, (hpq i).2, neg_one_mul, neg_one_mul, hdRo7SmKeysAux_pairCode_neg]

lemma hdRo7SmKeysAux_ckey_eq_of_key_rel {m : ℕ} (hm : m ≤ 9) {p q : Pair m}
    (h : key p = key q ∨ key p = negKey (key q)) : ckey p = ckey q := by
  rcases h with h | h
  · unfold ckey; rw [h]
  · unfold ckey
    rw [h, hdRo7SmKeysAux_negKey_involutive (hdRo7SmKeysAux_key_length q)]
    by_cases hc : enc (key q) = enc (negKey (key q))
    · have heq : key q = negKey (key q) :=
        hdRo7SmKeysAux_enc_inj (hdRo7SmKeysAux_key_length q)
          (hdRo7SmKeysAux_negKey_length (key q)) (hdRo7SmKeysAux_key_digits hm q)
          (hdRo7SmKeysAux_negKey_digits hm q) hc
      rw [if_pos (le_of_eq hc.symm), if_pos (le_of_eq hc)]
      exact heq.symm
    · rcases lt_or_gt_of_ne hc with hlt | hlt
      · rw [if_neg (not_le.mpr hlt), if_pos (le_of_lt hlt)]
      · rw [if_pos (le_of_lt hlt), if_neg (not_le.mpr hlt)]

lemma hdRo7SmKeysAux_key_rel_of_ckey_eq {m : ℕ} {p q : Pair m} (h : ckey p = ckey q) :
    key p = key q ∨ key p = negKey (key q) := by
  by_cases h1 : enc (key p) ≤ enc (negKey (key p)) <;>
    by_cases h2 : enc (key q) ≤ enc (negKey (key q))
  · left
    have : key p = key q := by
      have := h; unfold ckey at this; rw [if_pos h1, if_pos h2] at this; exact this
    exact this
  · right
    have : key p = negKey (key q) := by
      have := h; unfold ckey at this; rw [if_pos h1, if_neg h2] at this; exact this
    exact this
  · right
    have : negKey (key p) = key q := by
      have := h; unfold ckey at this; rw [if_neg h1, if_pos h2] at this; exact this
    rw [← hdRo7SmKeysAux_negKey_involutive (hdRo7SmKeysAux_key_length p), this]
  · left
    have : negKey (key p) = negKey (key q) := by
      have := h; unfold ckey at this; rw [if_neg h1, if_neg h2] at this; exact this
    exact hdRo7SmKeysAux_negKey_injective (hdRo7SmKeysAux_key_length p)
      (hdRo7SmKeysAux_key_length q) this

lemma hdRo7SmKeysAux_smClass_of_key_rel {m : ℕ} {p q : Pair m}
    (h : key p = key q ∨ key p = negKey (key q)) : SMClass p q := by
  rcases h with h | h
  · have hfiber : ∀ k : Fin 9, hdRo7SmKeysAux_fiberCard p k = hdRo7SmKeysAux_fiberCard q k := by
      intro k
      have := congrArg (fun l => l.getD k 0) h
      rwa [hdRo7SmKeysAux_key_getD, hdRo7SmKeysAux_key_getD] at this
    obtain ⟨σ, hσ⟩ := hdRo7SmKeysAux_exists_perm_of_fiber_card_eq
      (f := fun i => pairCode (p.1 i) (p.2 i))
      (g := fun i => pairCode (q.1 i) (q.2 i))
      (by simpa [hdRo7SmKeysAux_fiberCard] using hfiber)
    refine ⟨σ, 1, Or.inl rfl, fun i => ?_⟩
    obtain ⟨h1, h2⟩ := hdRo7SmKeysAux_pairCode_inj (hσ i)
    exact ⟨by rw [h1, one_mul], by rw [h2, one_mul]⟩
  · have hfiber : ∀ k : Fin 9,
        hdRo7SmKeysAux_fiberCard p (negCode k) = hdRo7SmKeysAux_fiberCard q k := by
      intro k
      have := congrArg (fun l => l.getD (negCode k) 0) h
      rw [hdRo7SmKeysAux_key_getD, hdRo7SmKeysAux_negKey_getD, hdRo7SmKeysAux_key_getD,
        hdRo7SmKeysAux_negCode_involutive] at this
      exact this
    obtain ⟨σ, hσ⟩ := hdRo7SmKeysAux_exists_perm_of_fiber_card_eq
      (f := fun i => negCode (pairCode (p.1 i) (p.2 i)))
      (g := fun i => pairCode (q.1 i) (q.2 i)) (by
        intro k
        show (Finset.univ.filter
            (fun i : Fin m => negCode (pairCode (p.1 i) (p.2 i)) = k)).card =
          hdRo7SmKeysAux_fiberCard q k
        have e : (Finset.univ.filter
            (fun i : Fin m => negCode (pairCode (p.1 i) (p.2 i)) = k)).card =
            hdRo7SmKeysAux_fiberCard p (negCode k) := by
          rw [hdRo7SmKeysAux_fiberCard]
          congr 1
          apply Finset.filter_congr
          intro i _
          constructor
          · intro hh; rw [← hh, hdRo7SmKeysAux_negCode_involutive]
          · intro hh; rw [hh, hdRo7SmKeysAux_negCode_involutive]
        rw [e, hfiber k])
    refine ⟨σ, -1, Or.inr rfl, fun i => ?_⟩
    have hσ' : pairCode (p.1 i) (p.2 i) = pairCode (-(q.1 (σ i))) (-(q.2 (σ i))) := by
      rw [hdRo7SmKeysAux_pairCode_neg]
      rw [← hdRo7SmKeysAux_negCode_involutive (pairCode (p.1 i) (p.2 i)), hσ i]
    obtain ⟨h1, h2⟩ := hdRo7SmKeysAux_pairCode_inj hσ'
    exact ⟨by rw [h1, neg_one_mul], by rw [h2, neg_one_mul]⟩

end Certificates.SUSmall

end
