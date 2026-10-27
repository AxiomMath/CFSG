module

public import CFSG.Sporadic.Co2Smith.CCNative
public import CFSG.Sporadic.Co2Smith.CRep

public section

namespace CFSG.Sporadic.Co2Smith


open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

abbrev genSub (u : ℕ → Cz) (m : ℕ) : Subgroup Cz := Subgroup.closure (u '' {l | l < m})

variable {Gs : Array (Array ℕ)} {u : ℕ → Cz}

theorem treeM_spec (hG : ∀ l < Gs.size, RepC (u l) Gs[l]!) {n : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ} (ht : Native.treeM Gs n rec_ = true) :
    rec_.1.size = n ∧ rec_.1[0]! = idRows 22 ∧
      (∀ i < n, ∃ w : Cz, RepC w rec_.1[i]! ∧ w ∈ genSub u Gs.size) ∧
      (∀ i < n, ∀ l < Gs.size, ∃ p < n, rec_.1[p]! = Native.mulRowsF rec_.1[i]! Gs[l]!) ∧
      (∀ i < n, ∀ j < n, rec_.1[i]! = rec_.1[j]! → i = j) := by
  simp only [Native.treeM, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨hsz, -⟩, -⟩, h0⟩, hall⟩ := ht
  refine ⟨hsz, h0, fun i => ?_, fun i hi l hl => ⟨_, (hall i hi).2 l hl |>.1,
    ((hall i hi).2 l hl).2⟩, fun i hi j hj e => ?_⟩
  · induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases (hall i hi).1.2 with hi0 | ⟨⟨hp, hl⟩, hpt⟩
      · subst hi0
        exact ⟨1, h0 ▸ repC_one, Subgroup.one_mem _⟩
      · obtain ⟨w, hw, hwm⟩ := ih _ hp (hp.trans hi)
        refine ⟨w * u rec_.2.2[i]!, ?_, Subgroup.mul_mem _ hwm
          (Subgroup.subset_closure ⟨_, hl, rfl⟩)⟩
        rw [hpt]
        exact hw.mul (hG _ hl)
  · rw [← (hall i hi).1.1, ← (hall j hj).1.1, e]

theorem mem_genSub_iff (hG : ∀ l < Gs.size, RepC (u l) Gs[l]!) {n : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ} (ht : Native.treeM Gs n rec_ = true)
    (w : Cz) : w ∈ genSub u Gs.size ↔ ∃ i < n, RepC w rec_.1[i]! := by
  obtain ⟨hsz, h0, hpts, hcl, -⟩ := treeM_spec hG ht
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [getElem!_neg rec_.1 0 (by omega)] at h0
      exact absurd (congrArg Array.size h0) (by simp only [idRows, Array.size_ofFn]; decide)
    · exact h
  constructor
  · intro hw
    have hright : ∀ x : Cz, (∃ i < n, RepC x rec_.1[i]!) → ∀ l < Gs.size,
        ∃ i < n, RepC (x * u l) rec_.1[i]! := by
      rintro x ⟨i, hi, hx⟩ l hl
      obtain ⟨p, hp, hpr⟩ := hcl i hi l hl
      exact ⟨p, hp, hpr ▸ hx.mul (hG l hl)⟩
    have hpow : ∀ x : Cz, (∃ i < n, RepC x rec_.1[i]!) → ∀ l < Gs.size, ∀ k : ℕ,
        ∃ i < n, RepC (x * u l ^ k) rec_.1[i]! := by
      intro x hx l hl k
      induction k with
      | zero => simpa using hx
      | succ k ih =>
        obtain ⟨i, hi, hxi⟩ := hright _ ih l hl
        exact ⟨i, hi, by rw [pow_succ, ← mul_assoc]; exact hxi⟩
    refine Subgroup.closure_induction_right
      (p := fun x _ => ∃ i < n, RepC x rec_.1[i]!) ⟨0, hn, h0 ▸ repC_one⟩ ?_ ?_ hw
    · rintro x - _ ⟨l, hl, rfl⟩ hx
      exact hright x hx l hl
    · rintro x - _ ⟨l, hl, rfl⟩ hx
      obtain ⟨i, hi, hxi⟩ := hpow x hx l hl (orderOf (u l) - 1)
      refine ⟨i, hi, ?_⟩
      have e : u l ^ (orderOf (u l) - 1) = (u l)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos (u l)),
          pow_orderOf_eq_one]
      rwa [e] at hxi
  · rintro ⟨i, hi, hw⟩
    obtain ⟨w', hw', hwm⟩ := hpts i hi
    rwa [hw.eq hw']

theorem natCard_genSub (hG : ∀ l < Gs.size, RepC (u l) Gs[l]!) {n : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ} (ht : Native.treeM Gs n rec_ = true) :
    Nat.card (genSub u Gs.size) = n := by
  obtain ⟨-, -, hpts, -, hdist⟩ := treeM_spec hG ht
  choose w hw hwm using hpts
  have hbij : Function.Bijective (fun i : Fin n => (⟨w i i.2, hwm i i.2⟩ : genSub u Gs.size)) := by
    refine ⟨fun i j hij => Fin.ext (hdist i i.2 j j.2 ?_), fun x => ?_⟩
    · exact (hw i i.2).unique (by
        have : w i i.2 = w j j.2 := congrArg Subtype.val hij
        rw [this]
        exact hw j j.2)
    · obtain ⟨i, hi, hxi⟩ := (mem_genSub_iff hG ht x.1).mp x.2
      exact ⟨⟨i, hi⟩, Subtype.ext ((hw i hi).eq hxi)⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fin]

end CFSG.Sporadic.Co2Smith
