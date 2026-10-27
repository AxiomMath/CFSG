module

public import CFSG.Sporadic.Co2Smith.CRep
public import CFSG.Sporadic.Co2Smith.ClassCount
public import CFSG.Sporadic.Co2Smith.CCNative

public section

namespace CFSG.Sporadic.Co2Smith


open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G Gi : Array (Array ℕ)} {u ui : ℕ → Cz}

theorem treeC_points (hG : ∀ l < G.size, RepC (u l) G[l]!)
    (hGi : ∀ l < G.size, RepC (ui l) Gi[l]!) (hinv : ∀ l < G.size, ui l = (u l)⁻¹)
    {y₀ : Cz} {start : Array ℕ} (hs : RepC y₀ start) {m : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ}
    (ht : Native.treeC G Gi start m rec_ = true) :
    rec_.1.size = m ∧ ∀ i < m, ∃ w : Cz, RepC w rec_.1[i]! ∧ ∃ h : Cz, w = h * y₀ * h⁻¹ := by
  simp only [Native.treeC, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at ht
  obtain ⟨⟨⟨⟨hsz, -⟩, -⟩, h0⟩, hall⟩ := ht
  refine ⟨hsz, fun i => ?_⟩
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
      refine ⟨u l * w * ui l, ?_, u l * h, ?_⟩
      · rw [hpt]
        exact ((hG l hl).mul hw).mul (hGi l hl)
      · rw [hh, hinv l hl]
        group

theorem exists_conj_injective_C (hG : ∀ l < G.size, RepC (u l) G[l]!)
    (hGi : ∀ l < G.size, RepC (ui l) Gi[l]!) (hinv : ∀ l < G.size, ui l = (u l)⁻¹)
    {y₀ : Cz} {start : Array ℕ} (hs : RepC y₀ start) {m : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ}
    (ht : Native.treeC G Gi start m rec_ = true) :
    ∃ f : Fin m → Cz, Function.Injective f ∧ ∀ i, ∃ h : Cz, f i = h * y₀ * h⁻¹ := by
  have key := (treeC_points hG hGi hinv hs ht).2
  simp only [Native.treeC, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at ht
  obtain ⟨-, hall⟩ := ht
  choose w hw hconj using key
  refine ⟨fun i => w i i.2, fun i j hij => ?_, fun i => hconj i i.2⟩
  have hij' : w i i.2 = w j j.2 := hij
  have e : rec_.1[(i : ℕ)]! = rec_.1[(j : ℕ)]! :=
    (hw i i.2).unique (by rw [hij']; exact hw j j.2)
  have hi := (hall i i.2).1
  have hj := (hall j j.2).1
  apply Fin.ext
  rw [← hi, ← hj, e]

theorem le_ncard_conjC (hG : ∀ l < G.size, RepC (u l) G[l]!)
    (hGi : ∀ l < G.size, RepC (ui l) Gi[l]!) (hinv : ∀ l < G.size, ui l = (u l)⁻¹)
    {y₀ : Cz} {start : Array ℕ} (hs : RepC y₀ start) {m : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ}
    (ht : Native.treeC G Gi start m rec_ = true) : m ≤ (conjSet y₀).ncard := by
  obtain ⟨f, hf, hc⟩ := exists_conj_injective_C hG hGi hinv hs ht
  calc m = (Set.range f).ncard := by rw [Set.ncard_range_of_injective hf, Nat.card_fin]
    _ ≤ _ := Set.ncard_le_ncard (fun _ ⟨i, hi⟩ => hi ▸ hc i) (Set.toFinite _)

theorem conj_of_any (hG : ∀ l < G.size, RepC (u l) G[l]!)
    (hGi : ∀ l < G.size, RepC (ui l) Gi[l]!) (hinv : ∀ l < G.size, ui l = (u l)⁻¹)
    {y₀ : Cz} {start : Array ℕ} (hs : RepC y₀ start) {m : ℕ}
    {rec_ : Array (Array ℕ) × Array ℕ × Array ℕ}
    (ht : Native.treeC G Gi start m rec_ = true) {y : Cz} {R : Array ℕ} (hy : RepC y R)
    (hR : rec_.1.any (· == R) = true) : ∃ h : Cz, h * y₀ * h⁻¹ = y := by
  obtain ⟨hsz, hpts⟩ := treeC_points hG hGi hinv hs ht
  rw [Array.any_eq_true] at hR
  obtain ⟨i, hi, he⟩ := hR
  rw [beq_iff_eq] at he
  obtain ⟨w, hw, h, rfl⟩ := hpts i (hsz ▸ hi)
  refine ⟨h, (hw.eq_iff hy).mpr ?_⟩
  rw [getElem!_pos rec_.1 i hi]
  exact he

end CFSG.Sporadic.Co2Smith
