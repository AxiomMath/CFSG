module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents
public import CFSG.LocalAnalysis.StandardType.PhanEFlagBuilding

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open Module CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} [Field K] {n m : ℕ} {d : List ℕ}

structure IsCut (n : ℕ) (d : List ℕ) : Prop where
  head : d.getD 0 0 = 0
  last : d.getD (d.length - 1) 0 = n
  strict : ∀ i, i + 1 < d.length → d.getD i 0 < d.getD (i + 1) 0

@[expose] def blockSize (d : List ℕ) (b : ℕ) : ℕ := d.getD (b + 1) 0 - d.getD b 0

@[expose] def cutTypes (m : ℕ) (d : List ℕ) : Set (Fin m) :=
  {j | ∀ i, i < d.length → d.getD i 0 ≠ j.val + 1}

@[expose] def refSet (K : Type) [Field K] (n : ℕ) (d : List ℕ) : Set (FlagK K n) :=
  {x | ∀ i, i < d.length → x.E (d.getD i 0) = Vsub n (d.getD i 0)}

lemma q2cFPt_getD_le {n : ℕ} {d : List ℕ} (hd : IsCut n d) {i j : ℕ}
    (hij : i ≤ j) (hj : j < d.length) : d.getD i 0 ≤ d.getD j 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  clear hij
  have key : ∀ k, i + k < d.length → d.getD i 0 ≤ d.getD (i + k) 0 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      exact le_trans (ih (by omega)) (le_of_lt (hd.strict (i + k) (by omega)))
  exact key k (by omega)

lemma q2cFPt_le_last {n : ℕ} {d : List ℕ} (hd : IsCut n d) {b : ℕ}
    (hb : b < d.length) : d.getD b 0 ≤ n := by
  have h := q2cFPt_getD_le hd (i := b) (j := d.length - 1) (by omega) (by omega)
  rwa [hd.last] at h

lemma q2cFPt_card_fin_lt {N c : ℕ} (hc : c ≤ N) :
    (Finset.univ.filter fun k : Fin N => k.val < c).card = c := by
  rcases eq_or_lt_of_le hc with rfl | hc'
  · rw [Finset.filter_true_of_mem (fun x _ => x.isLt), Finset.card_univ, Fintype.card_fin]
  · have h : (Finset.univ.filter fun k : Fin N => k.val < c) = Finset.Iio (⟨c, hc'⟩ : Fin N) := by
      ext x; simp [Finset.mem_Iio, Fin.lt_def]
    rw [h, Fin.card_Iio]

private lemma q2cFPt_nextCut_exists {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    ∃ b, k.val < d.getD b 0 :=
  ⟨d.length - 1, by rw [hd.last]; exact k.isLt⟩

noncomputable def q2cFPt_nextCut {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) : ℕ :=
  Nat.find (q2cFPt_nextCut_exists hd k)

lemma q2cFPt_nextCut_spec {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    k.val < d.getD (q2cFPt_nextCut hd k) 0 :=
  Nat.find_spec (q2cFPt_nextCut_exists hd k)

lemma q2cFPt_nextCut_min {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) {b : ℕ}
    (hb : b < q2cFPt_nextCut hd k) : d.getD b 0 ≤ k.val := by
  by_contra h
  rw [not_le] at h
  exact Nat.find_min (q2cFPt_nextCut_exists hd k) hb h

private lemma q2cFPt_nextCut_le {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    q2cFPt_nextCut hd k ≤ d.length - 1 :=
  Nat.find_min' (q2cFPt_nextCut_exists hd k) (by rw [hd.last]; exact k.isLt)

lemma q2cFPt_nextCut_pos {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    1 ≤ q2cFPt_nextCut hd k := by
  rcases Nat.eq_zero_or_pos (q2cFPt_nextCut hd k) with h | h
  · exfalso
    have h' := q2cFPt_nextCut_spec hd k
    rw [h, hd.head] at h'
    exact absurd h' (Nat.not_lt_zero _)
  · exact h

lemma q2cFPt_nextCut_lt_length {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    q2cFPt_nextCut hd k < d.length := by
  have h1 := q2cFPt_nextCut_pos hd k
  have h2 := q2cFPt_nextCut_le hd k
  omega

private lemma q2cFPt_nextCut_le_iff {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) {b : ℕ}
    (hb : b < d.length) : k.val < d.getD b 0 ↔ q2cFPt_nextCut hd k ≤ b := by
  constructor
  · intro h; exact Nat.find_min' (q2cFPt_nextCut_exists hd k) h
  · intro h
    exact lt_of_lt_of_le (q2cFPt_nextCut_spec hd k) (q2cFPt_getD_le hd h hb)

lemma q2cFPt_nextCut_eq_iff {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) {c : ℕ}
    (hc1 : 1 ≤ c) (hc : c < d.length) :
    q2cFPt_nextCut hd k = c ↔ d.getD (c - 1) 0 ≤ k.val ∧ k.val < d.getD c 0 := by
  constructor
  · intro h
    constructor
    · have hlt : c - 1 < q2cFPt_nextCut hd k := by rw [h]; omega
      exact q2cFPt_nextCut_min hd k hlt
    · rw [← h]; exact q2cFPt_nextCut_spec hd k
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact (q2cFPt_nextCut_le_iff hd k hc).mp h2
    · by_contra hlt
      rw [not_le] at hlt
      have hspec := q2cFPt_nextCut_spec hd k
      have hmono : d.getD (q2cFPt_nextCut hd k) 0 ≤ d.getD (c - 1) 0 :=
        q2cFPt_getD_le hd (by omega) (by omega)
      omega

noncomputable def q2cFPt_blockRev {n : ℕ} {d : List ℕ} (hd : IsCut n d)
    (k : Fin n) : Fin n :=
  ⟨d.getD (q2cFPt_nextCut hd k - 1) 0 + d.getD (q2cFPt_nextCut hd k) 0 - 1 - k.val, by
    have hpos := q2cFPt_nextCut_pos hd k
    have hb1 : d.getD (q2cFPt_nextCut hd k - 1) 0 ≤ k.val := q2cFPt_nextCut_min hd k (by omega)
    have hb2 : k.val < d.getD (q2cFPt_nextCut hd k) 0 := q2cFPt_nextCut_spec hd k
    have hcn : d.getD (q2cFPt_nextCut hd k) 0 ≤ n :=
      q2cFPt_le_last hd (q2cFPt_nextCut_lt_length hd k)
    omega⟩

private lemma q2cFPt_blockRev_val {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    (q2cFPt_blockRev hd k).val =
      d.getD (q2cFPt_nextCut hd k - 1) 0 + d.getD (q2cFPt_nextCut hd k) 0 - 1 - k.val := rfl

private lemma q2cFPt_blockRev_nextCut {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    q2cFPt_nextCut hd (q2cFPt_blockRev hd k) = q2cFPt_nextCut hd k := by
  have hc1 := q2cFPt_nextCut_pos hd k
  have hc := q2cFPt_nextCut_lt_length hd k
  rw [q2cFPt_nextCut_eq_iff hd (q2cFPt_blockRev hd k) hc1 hc]
  constructor
  · rw [q2cFPt_blockRev_val]
    have hb1 : d.getD (q2cFPt_nextCut hd k - 1) 0 ≤ k.val := q2cFPt_nextCut_min hd k (by omega)
    have hb2 : k.val < d.getD (q2cFPt_nextCut hd k) 0 := q2cFPt_nextCut_spec hd k
    omega
  · rw [q2cFPt_blockRev_val]
    have hb1 : d.getD (q2cFPt_nextCut hd k - 1) 0 ≤ k.val := q2cFPt_nextCut_min hd k (by omega)
    have hb2 : k.val < d.getD (q2cFPt_nextCut hd k) 0 := q2cFPt_nextCut_spec hd k
    omega

lemma q2cFPt_blockRev_involutive {n : ℕ} {d : List ℕ} (hd : IsCut n d) :
    Function.Involutive (q2cFPt_blockRev hd) := by
  intro k
  apply Fin.ext
  rw [q2cFPt_blockRev_val hd (q2cFPt_blockRev hd k), q2cFPt_blockRev_nextCut hd k,
    q2cFPt_blockRev_val hd k]
  have hb2 : k.val < d.getD (q2cFPt_nextCut hd k) 0 := q2cFPt_nextCut_spec hd k
  omega

lemma q2cFPt_blockRev_mem {n : ℕ} {d : List ℕ} (hd : IsCut n d) {b : ℕ}
    (hb : b < d.length) {k : Fin n} (hk : k.val < d.getD b 0) :
    (q2cFPt_blockRev hd k).val < d.getD b 0 := by
  have hcb : q2cFPt_nextCut hd k ≤ b := (q2cFPt_nextCut_le_iff hd k hb).mp hk
  have hb1 : d.getD (q2cFPt_nextCut hd k - 1) 0 ≤ k.val :=
    q2cFPt_nextCut_min hd k (by have := q2cFPt_nextCut_pos hd k; omega)
  have hb2 : k.val < d.getD (q2cFPt_nextCut hd k) 0 := q2cFPt_nextCut_spec hd k
  have hle : d.getD (q2cFPt_nextCut hd k) 0 ≤ d.getD b 0 := q2cFPt_getD_le hd hcb hb
  rw [q2cFPt_blockRev_val]
  omega

lemma q2cFPt_blockRev_prefix {n : ℕ} {d : List ℕ} (hd : IsCut n d) {b : ℕ}
    (hb : b < d.length) (k : Fin n) :
    (q2cFPt_blockRev hd k).val < d.getD b 0 ↔ k.val < d.getD b 0 := by
  constructor
  · intro h
    have h' := q2cFPt_blockRev_mem hd hb h
    rwa [q2cFPt_blockRev_involutive hd k] at h'
  · exact q2cFPt_blockRev_mem hd hb

lemma q2cFPt_blockRev_val_of_block {n : ℕ} {d : List ℕ} (hd : IsCut n d) {b : ℕ}
    {k : Fin n} (hb : b + 1 < d.length) (hk1 : d.getD b 0 ≤ k.val)
    (hk2 : k.val < d.getD (b + 1) 0) :
    (q2cFPt_blockRev hd k).val = d.getD b 0 + d.getD (b + 1) 0 - 1 - k.val := by
  have h : q2cFPt_nextCut hd k = b + 1 :=
    (q2cFPt_nextCut_eq_iff hd k (by omega) hb).mpr ⟨hk1, hk2⟩
  rw [q2cFPt_blockRev_val, h, Nat.add_sub_cancel]

@[expose] noncomputable def q2cFPt_blockRevI {n : ℕ} {d : List ℕ} (hd : IsCut n d) :
    Equiv.Perm (Fin n) :=
  (q2cFPt_blockRev_involutive hd).toPerm (q2cFPt_blockRev hd)

lemma q2cFPt_blockRevI_apply {n : ℕ} {d : List ℕ} (hd : IsCut n d) (k : Fin n) :
    q2cFPt_blockRevI hd k = q2cFPt_blockRev hd k := rfl

lemma q2cFPt_blockRevI_inv {n : ℕ} {d : List ℕ} (hd : IsCut n d) :
    (q2cFPt_blockRevI hd)⁻¹ = q2cFPt_blockRevI hd :=
  Function.Involutive.toPerm_symm (q2cFPt_blockRev_involutive hd)

@[expose] def q2cFPt_prefixSub (n : ℕ) (d : List ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ b, b < d.length →
    ∀ k : Fin n, (σ k).val < d.getD b 0 ↔ k.val < d.getD b 0}
  one_mem' := by intro b hb k; simp
  mul_mem' := by
    intro σ τ hσ hτ b hb k
    rw [Equiv.Perm.mul_apply, hσ b hb (τ k), hτ b hb k]
  inv_mem' := by
    intro σ hσ b hb k
    have h := hσ b hb (σ⁻¹ k)
    simpa using h.symm

private lemma q2cFPt_swap_prefix {N : ℕ} {a b : Fin N} {c : ℕ}
    (h : a.val < c ↔ b.val < c) (k : Fin N) : (Equiv.swap a b k).val < c ↔ k.val < c := by
  rcases eq_or_ne k a with rfl | hka
  · rw [Equiv.swap_apply_left]; exact h.symm
  · rcases eq_or_ne k b with rfl | hkb
    · rw [Equiv.swap_apply_right]; exact h
    · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

private lemma q2cFPt_adjSwap_mem {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {i : Fin m} (hi : i ∈ cutTypes m d) : adjSwap i ∈ q2cFPt_prefixSub (m + 1) d := by
  intro b hb k
  have hne : d.getD b 0 ≠ i.val + 1 := hi b hb
  have hiff : i.castSucc.val < d.getD b 0 ↔ i.succ.val < d.getD b 0 := by
    simp only [Fin.val_castSucc, Fin.val_succ]; omega
  have h' := q2cFPt_swap_prefix (a := i.castSucc) (b := i.succ) (c := d.getD b 0) hiff k
  simpa [adjSwap] using h'

private lemma q2cFPt_exists_adjacent_descent {m : ℕ} {σ : Equiv.Perm (Fin (m + 1))}
    (hσ : σ ≠ 1) : ∃ i : Fin m, σ i.succ < σ i.castSucc := by
  have hσ' : σ⁻¹ ≠ 1 := fun h => hσ (inv_eq_one.mp h)
  obtain ⟨i, hi1, hin, hdesc⟩ := LinearFlag.exists_descent (w := σ⁻¹) hσ'
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  have h1 : (⟨i - 1, by omega⟩ : Fin m).succ = ⟨i, hin⟩ := Fin.ext (by simp; omega)
  rw [h1]
  simpa using hdesc

private lemma q2cFPt_prefixSub_le_parabolic {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d) :
    q2cFPt_prefixSub (m + 1) d ≤ (symCox m).parabolic (cutTypes m d) := by
  have key : ∀ t (σ : Equiv.Perm (Fin (m + 1))), invCount σ = t →
      σ ∈ q2cFPt_prefixSub (m + 1) d → σ ∈ (symCox m).parabolic (cutTypes m d) := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro σ ht hσ
      rcases eq_or_ne σ 1 with rfl | hne
      · exact Subgroup.one_mem _
      · obtain ⟨i, hdesc⟩ := q2cFPt_exists_adjacent_descent hne
        have hcut : i ∈ cutTypes m d := by
          intro b hb hdb
          have hc : (σ i.castSucc).val < d.getD b 0 :=
            (hσ b hb i.castSucc).mpr (by simp only [Fin.val_castSucc]; omega)
          have hge : d.getD b 0 ≤ (σ i.succ).val := by
            by_contra hlt
            rw [not_le] at hlt
            have h' := (hσ b hb i.succ).mp hlt
            simp only [Fin.val_succ] at h'
            omega
          have hfin : (σ i.castSucc).val < (σ i.succ).val := lt_of_lt_of_le hc hge
          exact absurd hdesc (not_lt.mpr (le_of_lt hfin))
        have hτ : σ * adjSwap i ∈ q2cFPt_prefixSub (m + 1) d :=
          (q2cFPt_prefixSub (m + 1) d).mul_mem hσ (q2cFPt_adjSwap_mem hd hcut)
        have hcount : invCount (σ * adjSwap i) + 1 = invCount σ :=
          invCount_mul_adjSwap_of_gt σ i hdesc
        have heq : σ = (σ * adjSwap i) * adjSwap i := by
          rw [mul_assoc, adjSwap_mul_self, mul_one]
        rw [heq]
        refine Subgroup.mul_mem _ (ih _ ?_ (σ * adjSwap i) rfl hτ) ?_
        · omega
        · rw [← symCox_simple i]
          exact (symCox m).simple_mem_parabolic hcut
  intro σ hσ
  exact key (invCount σ) σ rfl hσ

lemma q2cFPt_parabolic_eq_prefixSub {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d) :
    (symCox m).parabolic (cutTypes m d) = q2cFPt_prefixSub (m + 1) d := by
  apply le_antisymm
  · rw [CoxeterSystem.parabolic_le_iff]
    intro i hi
    rw [symCox_simple]
    exact q2cFPt_adjSwap_mem hd hi
  · exact q2cFPt_prefixSub_le_parabolic hd

theorem stdFlag_mem_refSet (hd : IsCut n d) : stdFlag K n ∈ refSet K n d := by
  intro i _
  rfl

private lemma q2cFPt_prefix_forward_of_hasPos {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {x y : FlagK K (m + 1)} {σ : Equiv.Perm (Fin (m + 1))} (hpos : HasPos x y σ)
    (hx : x ∈ refSet K (m + 1) d) (hy : y ∈ refSet K (m + 1) d) {b : ℕ} (hb : b < d.length)
    {k : Fin (m + 1)} (hk : k.val < d.getD b 0) : (σ k).val < d.getD b 0 := by
  have hc : d.getD b 0 ≤ m + 1 := q2cFPt_le_last hd hb
  have h1 : rk x y (d.getD b 0) (d.getD b 0) =
      permRk σ (d.getD b 0) (d.getD b 0) := hpos _ _ hc hc
  unfold rk at h1
  rw [hx b hb, hy b hb, inf_idem, finrank_Vsub hc] at h1
  unfold permRk at h1
  have hsub : (Finset.univ.filter fun k : Fin (m + 1) =>
        k.val < d.getD b 0 ∧ (σ k).val < d.getD b 0) ⊆
      (Finset.univ.filter fun k : Fin (m + 1) => k.val < d.getD b 0) := by
    intro k hk'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk').2.1⟩
  have hcardT : (Finset.univ.filter fun k : Fin (m + 1) =>
      k.val < d.getD b 0).card = d.getD b 0 := q2cFPt_card_fin_lt hc
  have hcardS : (Finset.univ.filter fun k : Fin (m + 1) =>
      k.val < d.getD b 0 ∧ (σ k).val < d.getD b 0).card = d.getD b 0 := h1.symm
  have heq := Finset.eq_of_subset_of_card_le hsub (le_of_eq (hcardT.trans hcardS.symm))
  have hkS : k ∈ Finset.univ.filter (fun k : Fin (m + 1) =>
      k.val < d.getD b 0 ∧ (σ k).val < d.getD b 0) := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
  exact (Finset.mem_filter.mp hkS).2.2

private lemma q2cFPt_permRk_self_of_mem_prefixSub {m : ℕ} {d : List ℕ} (hd : IsCut (m + 1) d)
    {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ∈ q2cFPt_prefixSub (m + 1) d) {b : ℕ}
    (hb : b < d.length) : permRk σ (d.getD b 0) (d.getD b 0) = d.getD b 0 := by
  unfold permRk
  have hset : (Finset.univ.filter fun k : Fin (m + 1) =>
        k.val < d.getD b 0 ∧ (σ k).val < d.getD b 0) =
      (Finset.univ.filter fun k : Fin (m + 1) => k.val < d.getD b 0) := by
    apply Finset.filter_congr
    intro k _
    exact ⟨fun h => h.1, fun h => ⟨h, (hσ b hb k).mpr h⟩⟩
  rw [hset, q2cFPt_card_fin_lt (q2cFPt_le_last hd hb)]

theorem flagδ_mem_parabolic_of_mem_refSet (hd : IsCut (m + 1) d) {x y : FlagK K (m + 1)}
    (hx : x ∈ refSet K (m + 1) d) (hy : y ∈ refSet K (m + 1) d) :
    flagδ m x y ∈ (symCox m).parabolic (cutTypes m d) := by
  rw [q2cFPt_parabolic_eq_prefixSub hd]
  have hpre : relPos x y ∈ q2cFPt_prefixSub (m + 1) d := by
    intro b hb k
    constructor
    · intro h
      have h' := q2cFPt_prefix_forward_of_hasPos hd (hasPos_relPos y x) hy hx hb h
      rw [relPos_symm] at h'
      simpa using h'
    · intro hk
      exact q2cFPt_prefix_forward_of_hasPos hd (hasPos_relPos x y) hx hy hb hk
  simpa [flagδ] using (q2cFPt_prefixSub (m + 1) d).inv_mem hpre

theorem residue_cutTypes_eq (hd : IsCut (m + 1) d) {x : FlagK K (m + 1)}
    (hx : x ∈ refSet K (m + 1) d) :
    residue (symCox m) (flagδ (K := K) m) (cutTypes m d) x = refSet K (m + 1) d := by
  ext y
  rw [mem_residue_iff_mem_parabolic isWeylDistanceBuilding_flag]
  constructor
  · intro hy
    intro b hb
    have hpar : relPos x y ∈ (symCox m).parabolic (cutTypes m d) := by
      simpa [flagδ] using ((symCox m).parabolic (cutTypes m d)).inv_mem hy
    have hσ : relPos x y ∈ q2cFPt_prefixSub (m + 1) d := by
      rwa [q2cFPt_parabolic_eq_prefixSub hd] at hpar
    have hc : d.getD b 0 ≤ m + 1 := q2cFPt_le_last hd hb
    have h1 : rk x y (d.getD b 0) (d.getD b 0) =
        permRk (relPos x y) (d.getD b 0) (d.getD b 0) := hasPos_relPos x y _ _ hc hc
    unfold rk at h1
    rw [hx b hb, q2cFPt_permRk_self_of_mem_prefixSub hd hσ hb] at h1
    have hle : Vsub (K := K) (m + 1) (d.getD b 0) ≤ y.E (d.getD b 0) := by
      have hEq : Vsub (K := K) (m + 1) (d.getD b 0) ⊓ y.E (d.getD b 0) =
          Vsub (K := K) (m + 1) (d.getD b 0) :=
        Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, finrank_Vsub hc])
      exact inf_eq_left.mp hEq
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_Vsub hc, y.dim _ hc])).symm
  · intro hy
    exact flagδ_mem_parabolic_of_mem_refSet hd hx hy

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
