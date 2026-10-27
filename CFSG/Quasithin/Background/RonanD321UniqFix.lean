module

public import CFSG.Quasithin.Background.SmithD321Kplus

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD39Two CFSG.Quasithin.Z391
open scoped Pointwise

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem smul_eq_of_two_pow_of_isIrr [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {J : Subgroup Q} (hJ : XMod.IsIrr ↥Λ J) {y : Γ} (hyΛ : ∀ l ∈ Λ, l * y = y * l)
    (hyJ : ∀ q ∈ J, y • q ∈ J) {k : ℕ} (hk : ∀ q ∈ J, y ^ (2 ^ k) • q = q) :
    ∀ q ∈ J, y • q = q := by
  classical
  set F := J ⊓ XMod.fixed ↥(Subgroup.zpowers y) (⊤ : Subgroup Q)
  have hFinv : XMod.IsInv ↥Λ F := by
    intro l q hq
    refine ⟨hJ.1 l q hq.1, mem_fixed_zpowers_iff.2 ?_⟩
    have h1 : y • q = q := mem_fixed_zpowers_iff.1 hq.2
    show y • (l : Γ) • q = (l : Γ) • q
    rw [smul_smul, ← hyΛ l l.2, mul_smul, h1]
  rcases hJ.2.2 F hFinv bot_le inf_le_left with h | h
  · exfalso
    let f : Function.End ↥J := fun j => ⟨y • (j : Q), hyJ j j.2⟩
    have hfk : ∀ (m : ℕ) (j : ↥J), (((f ^ m) j : ↥J) : Q) = y ^ m • (j : Q) := by
      intro m
      induction m with
      | zero => intro j; rw [pow_zero, pow_zero, one_smul]; rfl
      | succ m ih =>
        intro j
        rw [pow_succ', pow_succ', mul_smul]
        show y • (((f ^ m) j : ↥J) : Q) = _
        rw [ih]
    have hf : f ^ 2 ^ k = 1 := by
      funext j
      apply Subtype.ext
      rw [hfk]
      exact hk j j.2
    have := Fact.mk Nat.prime_two
    have := Fintype.ofFinite ↥J
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := k) hf
    have hone : Fintype.card ↑(Function.fixedPoints f) = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨⟨1, ?_⟩, fun j => ?_⟩
      · show f 1 = 1
        apply Subtype.ext
        show y • (1 : Q) = 1
        exact smul_one y
      · apply Subtype.ext
        apply Subtype.ext
        have hj : y • ((j : ↥J) : Q) = ((j : ↥J) : Q) := congrArg Subtype.val j.2
        have hmem : ((j : ↥J) : Q) ∈ F := ⟨(j : ↥J).2, mem_fixed_zpowers_iff.2 hj⟩
        rw [h] at hmem
        exact Subgroup.mem_bot.1 hmem
    have hJcard : Fintype.card ↥J = 2 ^ rk ↥J := by
      rw [← Nat.card_eq_fintype_card]
      exact card_eq_two_pow hQ J
    have hrk : rk ↥J ≠ 0 := fun h0 => hJ.2.1.ne' ((rk_eq_zero_iff hQ).1 h0)
    obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hrk
    rw [hone, hJcard, hr, pow_succ] at hmod
    unfold Nat.ModEq at hmod
    omega
  · intro q hq
    have hq' : q ∈ F := by rw [h]; exact hq
    exact mem_fixed_zpowers_iff.1 hq'.2

theorem isIrr_of_isotypicOfLength_one [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I J : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) (hJ : IsotypicOfLength ↥Λ J I 1) :
    XMod.IsIrr ↥Λ J := by
  have hrkI : rk ↥I ≠ 0 := fun h0 => hI.2.1.ne' ((rk_eq_zero_iff hQ).1 h0)
  refine ⟨hJ.1, bot_lt_iff_ne_bot.2 fun h0 => ?_, fun K hK _ hKJ => ?_⟩
  · have h1 := hJ.2.2
    rw [h0, (rk_eq_zero_iff hQ).2 rfl, one_mul] at h1
    exact hrkI h1.symm
  · obtain ⟨c, hc⟩ := exists_rk_eq_mul hQ hI hK (hKJ.trans hJ.2.1)
    have hle := rk_mono hKJ
    rw [hc, hJ.2.2, one_mul] at hle
    rcases Nat.lt_or_ge c 1 with h | h
    · left
      have hc0 : c = 0 := by omega
      rw [hc0, zero_mul] at hc
      exact (rk_eq_zero_iff hQ).1 hc
    · right
      refine eq_of_le_of_rk_le hQ hKJ ?_
      rw [hc, hJ.2.2, one_mul]
      exact Nat.le_mul_of_pos_left _ h

theorem isotypicOfLength_one_of_isIrr [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y J : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) (hIY : I ≤ Y) (hY : IsotypicOfLength ↥Λ Y I 2)
    (hJ : XMod.IsIrr ↥Λ J) (hJY : J ≤ Y) : IsotypicOfLength ↥Λ J I 1 := by
  refine ⟨hJ.1, hJY.trans hY.2.1, ?_⟩
  obtain ⟨c, hc⟩ := exists_rk_eq_mul hQ hI hJ.1 (hJY.trans hY.2.1)
  have hrkI : rk ↥I ≠ 0 := fun h0 => hI.2.1.ne' ((rk_eq_zero_iff hQ).1 h0)
  have hrkJ : rk ↥J ≠ 0 := fun h0 => hJ.2.1.ne' ((rk_eq_zero_iff hQ).1 h0)
  have hle := rk_mono hJY
  rw [hY.2.2, hc] at hle
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hc
    exact hrkJ hc
  have hc2 : c ≤ 2 := Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero hrkI)
  rcases (by omega : c = 1 ∨ c = 2) with h | h
  · rw [hc, h]
  · exfalso
    have hJeq : J = Y := eq_of_le_of_rk_le hQ hJY (by rw [hY.2.2, hc, h])
    rcases hJ.2.2 I hI.1 bot_le (hJeq ▸ hIY) with h0 | h0
    · exact hI.2.1.ne' h0
    · have h1 := hY.2.2
      rw [← hJeq, ← h0] at h1
      omega

theorem smul_eq_of_ne_of_isotypicOfLength_two [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Λ : Subgroup Γ} {I Y J₁ J₂ : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) (hIY : I ≤ Y)
    (hY : IsotypicOfLength ↥Λ Y I 2) (hJ₁ : XMod.IsIrr ↥Λ J₁) (hJ₁Y : J₁ ≤ Y)
    (hJ₂ : XMod.IsIrr ↥Λ J₂) (hJ₂Y : J₂ ≤ Y) (hne : J₁ ≠ J₂) {y : Γ}
    (hyΛ : ∀ l ∈ Λ, l * y = y * l) (hy₁ : ∀ q ∈ J₁, y • q ∈ J₁) (hy₂ : ∀ q ∈ J₂, y • q ∈ J₂)
    {k : ℕ} (hk : ∀ q ∈ Y, y ^ (2 ^ k) • q = q) :
    ∀ q ∈ Y, y • q = q := by
  have hinf : J₁ ⊓ J₂ = ⊥ := by
    rcases hJ₁.2.2 (J₁ ⊓ J₂) (hJ₁.1.inf hJ₂.1) bot_le inf_le_left with h | h
    · exact h
    · exfalso
      have hle : J₁ ≤ J₂ := h ▸ inf_le_right
      rcases hJ₂.2.2 J₁ hJ₁.1 bot_le hle with h0 | h0
      · exact hJ₁.2.1.ne' h0
      · exact hne h0
  have hsup : J₁ ⊔ J₂ = Y := by
    refine eq_of_le_of_rk_le hQ (sup_le hJ₁Y hJ₂Y) ?_
    have h1 := rk_sup_add_rk_inf J₁ J₂
    rw [hinf, (rk_eq_zero_iff hQ).2 rfl, add_zero,
      (isotypicOfLength_one_of_isIrr hQ hI hIY hY hJ₁ hJ₁Y).2.2,
      (isotypicOfLength_one_of_isIrr hQ hI hIY hY hJ₂ hJ₂Y).2.2] at h1
    rw [h1, hY.2.2]
    omega
  have e₁ := smul_eq_of_two_pow_of_isIrr hQ hJ₁ hyΛ hy₁ fun q hq => hk q (hJ₁Y hq)
  have e₂ := smul_eq_of_two_pow_of_isIrr hQ hJ₂ hyΛ hy₂ fun q hq => hk q (hJ₂Y hq)
  intro q hq
  rw [← hsup] at hq
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hq
  rw [smul_mul', e₁ a ha, e₂ b hb]

theorem exists_max_fixed_of_two_pow [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ : Subgroup Γ}
    {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {c : ℕ} (hY : IsotypicOfLength ↥Λ Y I c)
    (hc : 1 ≤ c) {A : Subgroup Γ} (hA2 : ∀ a ∈ A, ∃ k : ℕ, ∀ q ∈ Y, a ^ (2 ^ k) • q = q)
    (hAΛ : ∀ a ∈ A, ∀ l ∈ Λ, a * l * a⁻¹ ∈ Λ) (hAY : ∀ a ∈ A, ∀ q ∈ Y, a • q ∈ Y) :
    ∃ J : Subgroup Q, J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y ∧
      ∀ a ∈ A, ∀ q ∈ J, a • q ∈ J := by
  classical
  have hN : XMod.Normalizes ↥Λ ↥A Q := normalizes_of_conj Λ A hAΛ
  have hle : ∀ b : ↥A, b • Y ≤ Y := by
    rintro b _ ⟨y, hy, rfl⟩
    exact hAY b b.2 y hy
  have hYeq : ∀ b : ↥A, b • Y = Y := by
    intro b
    have h1 := Subgroup.pointwise_smul_subset_iff.1 (hle b⁻¹)
    rw [inv_inv] at h1
    exact le_antisymm (hle b) h1
  let Ω := {J : Subgroup Q // J ≤ Y ∧ XMod.IsInv ↥Λ J ∧ XMod.IsIrrSec ↥Λ J Y}
  have hsm : ∀ (b : ↥A) (J : Ω),
      b • J.1 ≤ Y ∧ XMod.IsInv ↥Λ (b • J.1) ∧ XMod.IsIrrSec ↥Λ (b • J.1) Y := by
    intro b J
    refine ⟨(Subgroup.pointwise_smul_le_pointwise_smul_iff.2 J.2.1).trans_eq (hYeq b),
      XMod.isInv_smul_of_normalizes hN b J.2.2.1, ?_⟩
    have h1 : XMod.IsIrrSec ↥Λ (b • J.1) (b • Y) := isIrrSec_smul hN b J.2.2.2
    rwa [hYeq b] at h1
  let act : MulAction ↥A Ω :=
    { smul := fun b J => ⟨b • J.1, hsm b J⟩
      one_smul := fun J => Subtype.ext (one_smul ↥A J.1)
      mul_smul := fun b b' J => Subtype.ext (mul_smul b b' J.1) }
  have hΩodd : Odd (Nat.card Ω) := odd_card_max hQ hI hY hc
  let φ : ↥A →* Equiv.Perm Ω := @MulAction.toPermHom ↥A Ω _ act
  have hφ : ∀ (b : ↥A) (J : Ω), ((φ b J : Ω) : Subgroup Q) = b • J.1 := fun _ _ => rfl
  have hfixY : ∀ b : ↥A, (∀ q ∈ Y, b • q = q) → ∀ J : Ω, b • J.1 = J.1 := by
    intro b hb J
    refine le_antisymm ?_ fun q hq => ?_
    · rintro _ ⟨q, hq, rfl⟩
      show b • q ∈ J.1
      rw [hb q (J.2.1 hq)]
      exact hq
    · have h1 : b • q ∈ b • J.1 := Subgroup.smul_mem_pointwise_smul _ _ _ hq
      rwa [hb q (J.2.1 hq)] at h1
  have hH : IsPGroup 2 ↥φ.range := by
    rintro ⟨_, b, rfl⟩
    obtain ⟨k, hk⟩ := hA2 b b.2
    refine ⟨k, Subtype.ext ?_⟩
    show φ b ^ 2 ^ k = 1
    rw [← map_pow]
    refine Equiv.ext fun J => Subtype.ext ?_
    rw [hφ]
    exact hfixY (b ^ 2 ^ k) (fun q hq => by
      rw [Subgroup.smul_def, Subgroup.coe_pow]
      exact hk q hq) J
  have := Fact.mk Nat.prime_two
  have hmod := IsPGroup.card_modEq_card_fixedPoints hH Ω
  have hfixodd : Nat.card ↑(MulAction.fixedPoints ↥φ.range Ω) % 2 = 1 := by
    have h1 : Nat.card Ω % 2 = 1 := Nat.odd_iff.1 hΩodd
    have h2 : Nat.card Ω % 2 = Nat.card ↑(MulAction.fixedPoints ↥φ.range Ω) % 2 := hmod
    omega
  have hnonempty : Nonempty ↑(MulAction.fixedPoints ↥φ.range Ω) := by
    rw [← Finite.card_pos_iff]
    omega
  obtain ⟨⟨J, hJ⟩⟩ := hnonempty
  have hJfix : ∀ b : ↥A, b • J.1 = J.1 := fun b => by
    rw [← hφ]
    exact congrArg Subtype.val (hJ ⟨φ b, b, rfl⟩)
  refine ⟨J.1, J.2.1, J.2.2.1, J.2.2.2, fun a ha q hq => ?_⟩
  have h1 : (⟨a, ha⟩ : ↥A) • q ∈ (⟨a, ha⟩ : ↥A) • J.1 :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hq
  rw [hJfix] at h1
  exact h1

end CFSG.Quasithin.RonanD321
