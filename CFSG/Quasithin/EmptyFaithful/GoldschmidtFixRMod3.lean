module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRMod2

public section

namespace CFSG.Quasithin.FixR

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

theorem exists_inverted {P : Subgroup (MulAut W)} (hP5 : ∀ κ ∈ P, κ ^ 5 = 1) {a : MulAut W}
    (haa : a * a = 1) (haN : a ∈ Subgroup.normalizer (P : Set (MulAut W)))
    (hf : ¬ ∀ κ ∈ P, a * κ = κ * a) :
    ∃ q ∈ P, q ≠ 1 ∧ q ^ 5 = 1 ∧ a * q = q ^ 4 * a := by
  push Not at hf
  obtain ⟨κ, hκ, hne⟩ := hf
  have hκ' : a * κ * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp haN κ).mp hκ
  have ha1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  rw [ha1] at hκ'
  have hq : κ * (a * κ * a)⁻¹ ∈ P := P.mul_mem hκ (P.inv_mem hκ')
  have hq5 : (κ * (a * κ * a)⁻¹) ^ 5 = 1 := hP5 _ hq
  have hq1 : κ * (a * κ * a)⁻¹ ≠ 1 := by
    intro h
    have h1 : κ = a * κ * a := mul_inv_eq_one.mp h
    apply hne
    calc a * κ = a * κ * (a * a) := by rw [haa, mul_one]
      _ = (a * κ * a) * a := by group
      _ = κ * a := by rw [← h1]
  have hinv : a * (κ * (a * κ * a)⁻¹) * a = (κ * (a * κ * a)⁻¹)⁻¹ := by
    calc a * (κ * (a * κ * a)⁻¹) * a = a * κ * a⁻¹ * κ⁻¹ * a⁻¹ * a := by group
      _ = a * κ * a⁻¹ * κ⁻¹ := by group
      _ = (κ * (a * κ * a)⁻¹)⁻¹ := by rw [ha1]; group
  refine ⟨κ * (a * κ * a)⁻¹, hq, hq1, hq5, ?_⟩
  set q := κ * (a * κ * a)⁻¹ with hqdef
  have hq4 : q ^ 4 = q⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hq5)
  rw [hq4]
  calc a * q = a * q * (a * a) := by rw [haa, mul_one]
    _ = (a * q * a) * a := by group
    _ = q⁻¹ * a := by rw [hinv]

theorem card_ge_of_three [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)}
    [Fintype ↥P] (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 25)
    {a q : MulAut W} (haa : a * a = 1) (hq : q ∈ P) (hq5 : q ^ 5 = 1) (hq1 : q ≠ 1)
    (hqa : a * q = q ^ 4 * a) {L₁ L₂ L₃ : Subgroup (MulAut W)} (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P)
    (h₃ : L₃ ≤ P) (c₁ : Nat.card L₁ = 5) (c₂ : Nat.card L₂ = 5) (c₃ : Nat.card L₃ = 5)
    (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₂₃ : L₂ ≠ L₃) (m₁ : Subgroup.zpowers q ≠ L₁)
    (m₂ : Subgroup.zpowers q ≠ L₂) (m₃ : Subgroup.zpowers q ≠ L₃) (t₁ : tp P L₁ ≠ ⊥)
    (t₂ : tp P L₂ ≠ ⊥) (t₃ : tp P L₃ ≠ ⊥) :
    64 * Nat.card (phiHom a).ker ≤ Nat.card W := by
  have s₁ := sixteen_le_card_tp hW hPc hP h₁ t₁
  have s₂ := sixteen_le_card_tp hW hPc hP h₂ t₂
  have s₃ := sixteen_le_card_tp hW hPc hP h₃ t₃
  have hb12 : tp P L₁ ⊓ tp P L₂ = ⊥ := tp_inf_tp hW P L₁ L₂ hP (sup_eq_of_ne hP h₁ h₂ c₁ c₂ n₁₂)
  have hb3 : tp P L₃ ⊓ (tp P L₁ ⊔ tp P L₂) = ⊥ := tp_sup_inf hW hPc hP h₁ h₂ h₃ c₁ c₂ c₃ n₁₂ n₁₃ n₂₃
  have e12 : Nat.card ↥(tp P L₁ ⊔ tp P L₂) = Nat.card (tp P L₁) * Nat.card (tp P L₂) := by
    have := card_sup_mul_card_inf (tp P L₁) (tp P L₂)
    rwa [hb12, Subgroup.card_bot, mul_one] at this
  have e123 : Nat.card ↥((tp P L₁ ⊔ tp P L₂) ⊔ tp P L₃) =
      Nat.card ↥(tp P L₁ ⊔ tp P L₂) * Nat.card (tp P L₃) := by
    have := card_sup_mul_card_inf (tp P L₁ ⊔ tp P L₂) (tp P L₃)
    rwa [inf_comm, hb3, Subgroup.card_bot, mul_one] at this
  have hY : (tp P L₁ ⊔ tp P L₂) ⊔ tp P L₃ ≤ (nuHom q).ker :=
    sup_le (sup_le (tp_le_ker_nuHom hW hPc hP hq hq5 hq1 h₁ c₁ m₁)
      (tp_le_ker_nuHom hW hPc hP hq hq5 hq1 h₂ c₂ m₂))
      (tp_le_ker_nuHom hW hPc hP hq hq5 hq1 h₃ c₃ m₃)
  have hY4096 : 4096 ≤ Nat.card (nuHom q).ker := by
    have h1 : Nat.card ↥((tp P L₁ ⊔ tp P L₂) ⊔ tp P L₃) ≤ Nat.card (nuHom q).ker :=
      Subgroup.card_le_of_le hY
    rw [e123, e12] at h1
    calc 4096 = 16 * 16 * 16 := by norm_num
      _ ≤ Nat.card (tp P L₁) * Nat.card (tp P L₂) * Nat.card (tp P L₃) :=
        Nat.mul_le_mul (Nat.mul_le_mul s₁ s₂) s₃
      _ ≤ _ := h1
  have hm := card_ker_nuHom hW a q haa hq5 hqa
  have hm64 : 64 ≤ Nat.card ((nuHom q).ker.map (phiHom a)) := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ((nuHom q).ker.map (phiHom a)) * Nat.card ((nuHom q).ker.map (phiHom a)) <
        64 * 64 := Nat.mul_self_lt_mul_self hlt
    omega
  calc 64 * Nat.card (phiHom a).ker ≤ Nat.card ((nuHom q).ker.map (phiHom a)) *
        Nat.card (phiHom a).ker := Nat.mul_le_mul_right _ hm64
    _ = Nat.card (phiHom a).ker * Nat.card ((nuHom q).ker.map (phiHom a)) := mul_comm _ _
    _ ≤ Nat.card W := card_fixV_mul_ge a _

theorem final_contra [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)} [Fintype ↥P]
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Fintype.card ↥P = 25)
    (hP5 : ∀ κ ∈ P, κ ^ 5 = 1) {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) (hA0 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (P : Set (MulAut W)))
    (hAf : ∀ a ∈ A, (∀ κ ∈ P, a * κ = κ * a) → a = 1) (hAc : Nat.card A ≤ 4)
    (hAr : Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A))
    {L₁ L₂ L₃ L₄ : Subgroup (MulAut W)} (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P) (h₃ : L₃ ≤ P) (h₄ : L₄ ≤ P)
    (c₁ : Nat.card L₁ = 5) (c₂ : Nat.card L₂ = 5) (c₃ : Nat.card L₃ = 5) (c₄ : Nat.card L₄ = 5)
    (n₁₂ : L₁ ≠ L₂) (n₁₃ : L₁ ≠ L₃) (n₁₄ : L₁ ≠ L₄) (n₂₃ : L₂ ≠ L₃) (n₂₄ : L₂ ≠ L₄)
    (n₃₄ : L₃ ≠ L₄) (t₁ : tp P L₁ ≠ ⊥) (t₂ : tp P L₂ ≠ ⊥) (t₃ : tp P L₃ ≠ ⊥)
    (t₄ : tp P L₄ ≠ ⊥) : False := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA0
  have haA : (a : MulAut W) ∈ A := a.2
  have haa : (a : MulAut W) * a = 1 := by
    have := hA.2 a a.2
    rwa [pow_two] at this
  have hf : ¬ ∀ κ ∈ P, (a : MulAut W) * κ = κ * a := fun h =>
    ha1 (Subtype.ext (hAf a a.2 h))
  obtain ⟨q, hq, hq1, hq5, hqa⟩ := exists_inverted hP5 haa (hAN a.2) hf
  have hmain : 64 * Nat.card (phiHom (a : MulAut W)).ker ≤ Nat.card W := by
    by_cases e1 : Subgroup.zpowers q = L₁
    · exact card_ge_of_three hW hPc hP haa hq hq5 hq1 hqa h₂ h₃ h₄ c₂ c₃ c₄ n₂₃ n₂₄ n₃₄
        (fun h => n₁₂ (e1.symm.trans h)) (fun h => n₁₃ (e1.symm.trans h))
        (fun h => n₁₄ (e1.symm.trans h)) t₂ t₃ t₄
    by_cases e2 : Subgroup.zpowers q = L₂
    · exact card_ge_of_three hW hPc hP haa hq hq5 hq1 hqa h₁ h₃ h₄ c₁ c₃ c₄ n₁₃ n₁₄ n₃₄
        (fun h => n₁₂ (h.symm.trans e2)) (fun h => n₂₃ (e2.symm.trans h))
        (fun h => n₂₄ (e2.symm.trans h)) t₁ t₃ t₄
    by_cases e3 : Subgroup.zpowers q = L₃
    · exact card_ge_of_three hW hPc hP haa hq hq5 hq1 hqa h₁ h₂ h₄ c₁ c₂ c₄ n₁₂ n₁₄ n₂₄
        (fun h => n₁₃ (h.symm.trans e3)) (fun h => n₂₃ (h.symm.trans e3))
        (fun h => n₃₄ (e3.symm.trans h)) t₁ t₂ t₄
    exact card_ge_of_three hW hPc hP haa hq hq5 hq1 hqa h₁ h₂ h₃ c₁ c₂ c₃ n₁₂ n₁₃ n₂₃ e1 e2 e3
      t₁ t₂ t₃
  have hker : Nat.card (fixV A) ≤ Nat.card (phiHom (a : MulAut W)).ker :=
    Subgroup.card_le_of_le fun w hw => (mem_ker_phiHom hW _).mpr (hw _ haA)
  have hA2 : Nat.card A ^ 2 ≤ 16 := by
    calc Nat.card A ^ 2 ≤ 4 ^ 2 := Nat.pow_le_pow_left hAc 2
      _ = 16 := by norm_num
  have hpos : 0 < Nat.card (phiHom (a : MulAut W)).ker := Nat.card_pos
  have h3 : Nat.card W ≤ 16 * Nat.card (phiHom (a : MulAut W)).ker :=
    hAr.trans (Nat.mul_le_mul hA2 hker)
  omega

end CFSG.Quasithin.FixR
