module

public import CFSG.Sporadic.Co2Smith.HPRep

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem mulRowsF_z0_z0
    {R : Array ℕ} (hR : Native.validM R = true) :
    Native.mulRowsF (Native.mulRowsF R seedRowsArr[0]!) seedRowsArr[0]! = R := by
  rw [mulRowsF_eq, mulRowsF_eq]
  refine eq_of_rowsMatrix_eq (validM_mulRows (validM_mulRows hR validM_z0R) validM_z0R) hR ?_
  rw [rowsMatrix_mulRows, rowsMatrix_mulRows, ← rows_z0, mul_assoc, ← val_val_mul,
    seedA_mul_self, val_val_one, mul_one]

theorem keyP_eq_of_eqvP
    {a b : Array ℕ × Array ℤ} (hb : Native.validM b.1 = true)
    (h : Native.eqvP seedRowsArr[0]! a b = true) :
    Native.keyP seedRowsArr[0]! a = Native.keyP seedRowsArr[0]! b := by
  simp only [Native.eqvP, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨h2, h1⟩ | ⟨h2, h1⟩
  · rw [show a = b from Prod.ext h1 h2]
  · have ha : a = (Native.mulRowsF b.1 seedRowsArr[0]!, Native.negZ b.2) := Prod.ext h1 h2
    rw [ha, Native.keyP, Native.keyP, mulRowsF_z0_z0 hb, negZ_negZ, min_comm]

theorem exists_conj_injective
    {G Gi : Array (Array ℕ × Array ℤ)} {u ui : ℕ → FibP}
    (hG : ∀ l < G.size, RepOK (u l) G[l]!) (hGi : ∀ l < G.size, RepOK (ui l) Gi[l]!)
    (hinv : ∀ l < G.size,
      (QuotientGroup.mk (ui l) : Hprime) = (QuotientGroup.mk (u l) : Hprime)⁻¹)
    {y₀ : FibP} {start : Array ℕ × Array ℤ} (hs : RepOK y₀ start) {m : ℕ}
    {rec_ : Array (Array ℕ × Array ℤ) × Array ℕ × Array ℕ}
    (ht : Native.treeP seedRowsArr[0]! G Gi start m rec_ = true) :
    ∃ f : Fin m → Hprime, Function.Injective f ∧
      ∀ i, ∃ h : Hprime, f i = h * QuotientGroup.mk y₀ * h⁻¹ := by
  simp only [Native.treeP, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨hsz, -⟩, -⟩, h0⟩, hall⟩ := ht
  set pts := rec_.1
  have key : ∀ i < m, ∃ w : FibP, RepOK w pts[i]! ∧
      ∃ h : Hprime, (QuotientGroup.mk w : Hprime) = h * QuotientGroup.mk y₀ * h⁻¹ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      obtain ⟨-, hrec⟩ := hall i hi
      rcases hrec with hi0 | ⟨⟨⟨hp, hl⟩, hpt⟩⟩
      · have : i = 0 := by simpa using hi0
        subst this
        exact ⟨y₀, h0 ▸ hs, 1, by group⟩
      · obtain ⟨w, hw, h, hh⟩ := ih _ hp (hp.trans hi)
        set l := rec_.2.2[i]!
        refine ⟨u l * w * ui l, hpt ▸ ((hG l hl).mul hw).mul (hGi l hl), QuotientGroup.mk (u l) * h,
          ?_⟩
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hh, hinv l hl]
        group
  choose w hw hconj using key
  refine ⟨fun i => QuotientGroup.mk (w i i.2), fun i j hij => ?_, fun i => hconj i i.2⟩
  have e := ((hw i i.2).mk_eq_iff (hw j j.2)).mp hij
  have hk := keyP_eq_of_eqvP (hw j j.2).1 e
  have hi := (hall i i.2).1
  have hj := (hall j j.2).1
  apply Fin.ext
  rw [← hi, ← hj, hk]

theorem le_ncard_conj
    {G Gi : Array (Array ℕ × Array ℤ)} {u ui : ℕ → FibP}
    (hG : ∀ l < G.size, RepOK (u l) G[l]!) (hGi : ∀ l < G.size, RepOK (ui l) Gi[l]!)
    (hinv : ∀ l < G.size,
      (QuotientGroup.mk (ui l) : Hprime) = (QuotientGroup.mk (u l) : Hprime)⁻¹)
    {y₀ : FibP} {start : Array ℕ × Array ℤ} (hs : RepOK y₀ start) {m : ℕ}
    {rec_ : Array (Array ℕ × Array ℤ) × Array ℕ × Array ℕ}
    (ht : Native.treeP seedRowsArr[0]! G Gi start m rec_ = true) :
    m ≤ {y : Hprime | ∃ h : Hprime, y = h * QuotientGroup.mk y₀ * h⁻¹}.ncard := by
  obtain ⟨f, hf, hc⟩ := exists_conj_injective hG hGi hinv hs ht
  calc m = (Set.range f).ncard := by rw [Set.ncard_range_of_injective hf, Nat.card_fin]
    _ ≤ _ := Set.ncard_le_ncard (fun _ ⟨i, hi⟩ => hi ▸ hc i) (Set.toFinite _)

end CFSG.Sporadic.Co2Smith
