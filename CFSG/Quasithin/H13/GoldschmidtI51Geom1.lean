module

public import CFSG.Quasithin.H13.GoldschmidtI51Local
public import CFSG.Quasithin.H13.GoldschmidtI51Act

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

theorem Q0_core12 (hD : IsDSystem D Gs) :
    ∀ n ∈ QQ Gs 0, ∀ g ∈ Gs 1, g⁻¹ * n * g ∈ Gs 1 ⊓ Gs 2 := by
  intro n hn g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := loc1_prod2 hD g hg
  have h1 : a⁻¹ * n * a ∈ QQ Gs 0 := by
    have := normalizes_pCoreOf (Gs 0) (Gs 0 |>.inv_mem ha.1) hn
    simpa using this
  have h2 : a⁻¹ * n * a ∈ Gs 1 ⊓ Gs 2 := TT_le_inf 1 2 (QQ_le_TT hD 0 h1)
  have : (a * b)⁻¹ * n * (a * b) = b⁻¹ * (a⁻¹ * n * a) * b := by group
  rw [this]
  exact (Gs 1 ⊓ Gs 2).mul_mem ((Gs 1 ⊓ Gs 2).mul_mem ((Gs 1 ⊓ Gs 2).inv_mem hb) h2) hb

theorem Q2_core10 (hD : IsDSystem D Gs) :
    ∀ n ∈ QQ Gs 2, ∀ g ∈ Gs 1, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 1 := by
  intro n hn g hg
  obtain ⟨b, hb, a, ha, rfl⟩ := loc1_prod2' hD g hg
  have h1 : b⁻¹ * n * b ∈ QQ Gs 2 := by
    have := normalizes_pCoreOf (Gs 2) (Gs 2 |>.inv_mem hb.2) hn
    simpa using this
  have h2 : b⁻¹ * n * b ∈ Gs 0 ⊓ Gs 1 := TT_le_inf 0 1 (QQ_le_TT hD 2 h1)
  have : (b * a)⁻¹ * n * (b * a) = a⁻¹ * (b⁻¹ * n * b) * a := by group
  rw [this]
  exact (Gs 0 ⊓ Gs 1).mul_mem ((Gs 0 ⊓ Gs 1).mul_mem ((Gs 0 ⊓ Gs 1).inv_mem ha) h2) ha

theorem Q2_cases (hD : IsDSystem D Gs) :
    ∀ q₁ ∈ QQ Gs 2, ∀ q₂ ∈ QQ Gs 2, q₁ ∈ QQ Gs 1 ∨ q₂ ∈ QQ Gs 1 ∨ q₁ * q₂⁻¹ ∈ QQ Gs 1 := by
  intro q₁ h₁ q₂ h₂
  have hcases := core_cases_of_relIndex_three (H := Gs 1) (P := Gs 1 ⊓ Gs 2) (S := QQ Gs 2)
    inf_le_left (Q2_le_P12 hD) (loc1_index_12 hD) q₁ h₁ q₂ h₂
  have key : ∀ q ∈ QQ Gs 2, (∀ h ∈ Gs 1, h⁻¹ * q * h ∈ Gs 1 ⊓ Gs 2) → q ∈ QQ Gs 1 := by
    intro q hq hc
    exact loc1_core hD q (QQ_le_TT hD 2 hq |> TT_le 1) (Q2_core10 hD q hq) hc
  rcases hcases with h | h | h
  · exact Or.inl (key q₁ h₁ h)
  · exact Or.inr (Or.inl (key q₂ h₂ h))
  · exact Or.inr (Or.inr (key _ ((QQ Gs 2).mul_mem h₁ ((QQ Gs 2).inv_mem h₂)) h))

omit [Finite G] in
theorem gen_two (hD : IsDSystem D Gs) (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : Gs i ⊓ Gs j ⊔ Gs i ⊓ Gs k = Gs i := by
  obtain ⟨hne, hmax⟩ := hD.d3max i j k hij hik hjk
  obtain ⟨-, hlta, hma⟩ := (hmax _).2 (Or.inl rfl)
  obtain ⟨-, hltb, hmb⟩ := (hmax _).2 (Or.inr rfl)
  have hW : Gs i ⊓ Gs j ⊔ Gs i ⊓ Gs k ≤ Gs i := sup_le inf_le_left inf_le_left
  rcases hma _ le_sup_left hW with h | h
  · exfalso
    have hba : Gs i ⊓ Gs k ≤ Gs i ⊓ Gs j := h ▸ le_sup_right
    rcases hmb _ hba inf_le_left with h' | h'
    · exact hne h'
    · exact hlta.ne h'
  · exact h

omit [Finite G] in
theorem gen_top (hD : IsDSystem D Gs) : Gs 0 ⊔ Gs 1 ⊓ Gs 2 = ⊤ := by
  have h1 := gen_two hD 1 0 2 (by decide) (by decide) (by decide)
  have h2 := gen_two hD 2 0 1 (by decide) (by decide) (by decide)
  rw [inf_comm (Gs 1) (Gs 0)] at h1
  rw [inf_comm (Gs 2) (Gs 0), inf_comm (Gs 2) (Gs 1)] at h2
  have hG1 : Gs 1 ≤ Gs 0 ⊔ Gs 1 ⊓ Gs 2 :=
    calc Gs 1 = Gs 0 ⊓ Gs 1 ⊔ Gs 1 ⊓ Gs 2 := h1.symm
      _ ≤ Gs 0 ⊔ Gs 1 ⊓ Gs 2 := sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hG2 : Gs 2 ≤ Gs 0 ⊔ Gs 1 ⊓ Gs 2 :=
    calc Gs 2 = Gs 0 ⊓ Gs 2 ⊔ Gs 1 ⊓ Gs 2 := h2.symm
      _ ≤ Gs 0 ⊔ Gs 1 ⊓ Gs 2 := sup_le (inf_le_left.trans le_sup_left) le_sup_right
  refine eq_top_iff.2 ?_
  calc (⊤ : Subgroup G) = Gs 0 ⊔ Gs 1 ⊔ Gs 2 := hD.d4gen.symm
    _ ≤ Gs 0 ⊔ Gs 1 ⊓ Gs 2 := sup_le (sup_le le_sup_left hG1) hG2

omit [Finite G] in
theorem normal_of_gen (hD : IsDSystem D Gs) {N : Subgroup G}
    (h0 : ∀ a ∈ Gs 0, ∀ n ∈ N, a * n * a⁻¹ ∈ N)
    (h12 : ∀ a ∈ Gs 1 ⊓ Gs 2, ∀ n ∈ N, a * n * a⁻¹ ∈ N) : N.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← gen_top hD]
  have key : ∀ S : Subgroup G, (∀ a ∈ S, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      S ≤ Subgroup.normalizer (N : Set G) := by
    intro S hS a ha
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn; exact hS a ha n hn
    · intro hn
      have := hS a⁻¹ (S.inv_mem ha) _ hn
      have e : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
      rwa [e] at this
  exact sup_le (key _ h0) (key _ h12)

theorem Q2_not_le_Q1 (hD : IsDSystem D Gs) : ¬ QQ Gs 2 ≤ QQ Gs 1 := by
  intro h
  have hrel : (QQ Gs 2).relIndex (QQ Gs 1) = 2 := by
    have := Subgroup.relIndex_mul_relIndex (QQ Gs 2) (QQ Gs 1) (TT Gs) h (QQ_le_TT hD 1)
    rw [loc1_relIndex hD, loc2_relIndex hD] at this
    omega
  have hle : QQ Gs 1 ≤ QQ Gs 2 := loc2_noNormal_21 hD (Q1_le_P12 hD)
    (fun a ha m hm => normalizes_pCoreOf (Gs 1) ha.1 hm)
    (hord_of_relIndex_le_two (le_of_eq hrel))
  have h1 := Subgroup.relIndex_eq_one.2 hle
  omega

theorem Q1Q2_relIndex (hD : IsDSystem D Gs) :
    (QQ Gs 1 ⊓ QQ Gs 2).relIndex (QQ Gs 2) = 2 := by
  have hle2 : (QQ Gs 1 ⊓ QQ Gs 2).relIndex (QQ Gs 2) ≤ 2 := by
    apply relIndex_le_two_of_hord
    intro m₁ h₁ m₂ h₂
    rcases Q2_cases hD m₁ h₁ m₂ h₂ with h | h | h
    · exact Or.inl ⟨h, h₁⟩
    · exact Or.inr (Or.inl ⟨h, h₂⟩)
    · exact Or.inr (Or.inr ⟨h, (QQ Gs 2).mul_mem h₁ ((QQ Gs 2).inv_mem h₂)⟩)
  have hne1 : (QQ Gs 1 ⊓ QQ Gs 2).relIndex (QQ Gs 2) ≠ 1 := fun h1 =>
    Q2_not_le_Q1 hD (fun x hx => (Subgroup.relIndex_eq_one.1 h1 hx).1)
  have hne0 : (QQ Gs 1 ⊓ QQ Gs 2).relIndex (QQ Gs 2) ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem relIndex_Q1Q2_T (hD : IsDSystem D Gs) :
    (QQ Gs 1 ⊓ QQ Gs 2).relIndex (TT Gs) = 16 := by
  have := Subgroup.relIndex_mul_relIndex (QQ Gs 1 ⊓ QQ Gs 2) (QQ Gs 2) (TT Gs) inf_le_right
    (QQ_le_TT hD 2)
  rw [Q1Q2_relIndex hD, loc2_relIndex hD] at this
  omega

theorem not_Q0_le_Q1_C3 (hD : IsDSystem .C3 Gs) : ¬ QQ Gs 0 ≤ QQ Gs 1 := by
  intro h01
  have hcore : ∀ n ∈ QQ Gs 0, ∀ g ∈ Gs 2, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 2 := by
    intro n hn g hg
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := loc2_fano hD g hg
    have h1 : a⁻¹ * n * a ∈ QQ Gs 0 := by
      simpa using normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem ha.1) hn
    have h2 : b⁻¹ * (a⁻¹ * n * a) * b ∈ QQ Gs 1 := by
      simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hb.1) (h01 h1)
    have h3 : b⁻¹ * (a⁻¹ * n * a) * b ∈ Gs 0 ⊓ Gs 2 := TT_le_inf 0 2 (QQ_le_TT hD 1 h2)
    have e : (a * b * c)⁻¹ * n * (a * b * c) = c⁻¹ * (b⁻¹ * (a⁻¹ * n * a) * b) * c := by group
    rw [e]
    exact (Gs 0 ⊓ Gs 2).mul_mem ((Gs 0 ⊓ Gs 2).mul_mem ((Gs 0 ⊓ Gs 2).inv_mem hc) h3) hc
  have hQ02 : QQ Gs 0 ≤ QQ Gs 2 := fun n hn =>
    loc2_core hD n (TT_le 2 (QQ_le_TT hD 0 hn)) (hcore n hn)
  have hle : QQ Gs 0 ≤ QQ Gs 1 ⊓ QQ Gs 2 := le_inf h01 hQ02
  have hT := Subgroup.relIndex_mul_relIndex (QQ Gs 0) (QQ Gs 1 ⊓ QQ Gs 2) (TT Gs) hle
    (inf_le_left.trans (QQ_le_TT hD 1))
  rw [relIndex_Q1Q2_T hD] at hT
  have hQ0 : QQ Gs 0 = QQ Gs 1 ⊓ QQ Gs 2 := by
    rcases loc0_relIndex hD with h8 | h16
    · omega
    · have h1 : (QQ Gs 0).relIndex (QQ Gs 1 ⊓ QQ Gs 2) = 1 := by omega
      exact le_antisymm hle (Subgroup.relIndex_eq_one.1 h1)
  have hnorm12 : ∀ a ∈ Gs 1 ⊓ Gs 2, ∀ n ∈ QQ Gs 0, a * n * a⁻¹ ∈ QQ Gs 0 := fun a ha n hn => by
    rw [hQ0] at hn ⊢
    exact ⟨normalizes_pCoreOf (Gs 1) ha.1 hn.1, normalizes_pCoreOf (Gs 2) ha.2 hn.2⟩
  have hN : (QQ Gs 0).Normal := normal_of_gen hD (fun a ha n hn => normalizes_pCoreOf (Gs 0) ha hn)
    hnorm12
  have hbot : QQ Gs 0 = ⊥ := hD.d4core _ hN (QQ_le_TT hD 0)
  rcases hD.d5 rfl with hz | hbig
  · apply hz
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz'
    have hzc : (z : G) ∈ QQ Gs 0 := loc0_center hD z z.2 (fun g hg => by
      have := Subgroup.mem_center_iff.1 hz' ⟨g, hg⟩
      exact congrArg Subtype.val this)
    rw [hbot, Subgroup.mem_bot] at hzc
    exact Subtype.ext hzc
  · have : Nat.card ↥(pCoreOf 2 (Gs 0)) = 1 := by
      have h' : pCoreOf 2 (Gs 0) = ⊥ := hbot
      rw [h']; exact Subgroup.card_bot
    omega

theorem not_Q0_le_Q1_A3 (hD : IsDSystem .A3 Gs) : ¬ QQ Gs 0 ≤ QQ Gs 1 := by
  intro h01
  have hcore : ∀ n ∈ QQ Gs 0, ∀ g ∈ Gs 2, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 2 := by
    intro n hn g hg
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := loc2_fano hD g hg
    have h1 : a⁻¹ * n * a ∈ QQ Gs 0 := by
      simpa using normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem ha.1) hn
    have h2 : b⁻¹ * (a⁻¹ * n * a) * b ∈ QQ Gs 1 := by
      simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hb.1) (h01 h1)
    have h3 : b⁻¹ * (a⁻¹ * n * a) * b ∈ Gs 0 ⊓ Gs 2 := TT_le_inf 0 2 (QQ_le_TT hD 1 h2)
    have e : (a * b * c)⁻¹ * n * (a * b * c) = c⁻¹ * (b⁻¹ * (a⁻¹ * n * a) * b) * c := by group
    rw [e]
    exact (Gs 0 ⊓ Gs 2).mul_mem ((Gs 0 ⊓ Gs 2).mul_mem ((Gs 0 ⊓ Gs 2).inv_mem hc) h3) hc
  have hQ02 : QQ Gs 0 ≤ QQ Gs 2 := fun n hn =>
    loc2_core hD n (TT_le 2 (QQ_le_TT hD 0 hn)) (hcore n hn)
  have hle : QQ Gs 0 ≤ QQ Gs 1 ⊓ QQ Gs 2 := le_inf h01 hQ02
  have hT := Subgroup.relIndex_mul_relIndex (QQ Gs 0) (QQ Gs 1 ⊓ QQ Gs 2) (TT Gs) hle
    (inf_le_left.trans (QQ_le_TT hD 1))
  rw [relIndex_Q1Q2_T hD, loc0A_relIndex hD] at hT
  omega

theorem not_Q0_le_Q1 (hD : IsDSystem D Gs) : ¬ QQ Gs 0 ≤ QQ Gs 1 := by
  cases D
  · exact not_Q0_le_Q1_A3 hD
  · exact not_Q0_le_Q1_C3 hD

end CFSG.Quasithin.H13.I51
