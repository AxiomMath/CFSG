module

public import CFSG.Quasithin.H13.GoldschmidtI51Geom1

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {D : DType} {Gs : Fin 3 → Subgroup G}

theorem Q0_cases (hD : IsDSystem D Gs) :
    ∀ q₁ ∈ QQ Gs 0, ∀ q₂ ∈ QQ Gs 0, q₁ ∈ QQ Gs 1 ∨ q₂ ∈ QQ Gs 1 ∨ q₁ * q₂⁻¹ ∈ QQ Gs 1 := by
  intro q₁ h₁ q₂ h₂
  have hcases := core_cases_of_relIndex_three (H := Gs 1) (P := Gs 0 ⊓ Gs 1) (S := QQ Gs 0)
    inf_le_right (Q0_le_P01 hD) (loc1_index_10 hD) q₁ h₁ q₂ h₂
  have key : ∀ q ∈ QQ Gs 0, (∀ h ∈ Gs 1, h⁻¹ * q * h ∈ Gs 0 ⊓ Gs 1) → q ∈ QQ Gs 1 := by
    intro q hq hc
    exact loc1_core hD q (TT_le 1 (QQ_le_TT hD 0 hq)) hc (Q0_core12 hD q hq)
  rcases hcases with h | h | h
  · exact Or.inl (key q₁ h₁ h)
  · exact Or.inr (Or.inl (key q₂ h₂ h))
  · exact Or.inr (Or.inr (key _ ((QQ Gs 0).mul_mem h₁ ((QQ Gs 0).inv_mem h₂)) h))

theorem Q0_relIndex (hD : IsDSystem D Gs) : (QQ Gs 0 ⊓ QQ Gs 1).relIndex (QQ Gs 0) = 2 := by
  have hle2 : (QQ Gs 0 ⊓ QQ Gs 1).relIndex (QQ Gs 0) ≤ 2 := by
    apply relIndex_le_two_of_hord
    intro m₁ h₁ m₂ h₂
    rcases Q0_cases hD m₁ h₁ m₂ h₂ with h | h | h
    · exact Or.inl ⟨h₁, h⟩
    · exact Or.inr (Or.inl ⟨h₂, h⟩)
    · exact Or.inr (Or.inr ⟨(QQ Gs 0).mul_mem h₁ ((QQ Gs 0).inv_mem h₂), h⟩)
  have hne1 : (QQ Gs 0 ⊓ QQ Gs 1).relIndex (QQ Gs 0) ≠ 1 := fun h1 =>
    not_Q0_le_Q1 hD (fun x hx => (Subgroup.relIndex_eq_one.1 h1 hx).2)
  have hne0 : (QQ Gs 0 ⊓ QQ Gs 1).relIndex (QQ Gs 0) ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

theorem core_of_conj_mem_Q1 (hD : IsDSystem D Gs) {n : G}
    (hn : ∀ a ∈ Gs 0 ⊓ Gs 2, a⁻¹ * n * a ∈ QQ Gs 1) :
    ∀ g ∈ Gs 2, g⁻¹ * n * g ∈ Gs 0 ⊓ Gs 2 := by
  intro g hg
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := loc2_fano hD g hg
  have h2 : b⁻¹ * (a⁻¹ * n * a) * b ∈ QQ Gs 1 := by
    simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hb.1) (hn a ha)
  have h3 : b⁻¹ * (a⁻¹ * n * a) * b ∈ Gs 0 ⊓ Gs 2 := TT_le_inf 0 2 (QQ_le_TT hD 1 h2)
  have e : (a * b * c)⁻¹ * n * (a * b * c) = c⁻¹ * (b⁻¹ * (a⁻¹ * n * a) * b) * c := by group
  rw [e]
  exact (Gs 0 ⊓ Gs 2).mul_mem ((Gs 0 ⊓ Gs 2).mul_mem ((Gs 0 ⊓ Gs 2).inv_mem hc) h3) hc

theorem fix_iff (hD : IsDSystem D Gs) {s : G} (hs : s ∈ Gs 1) (hs0 : s ∉ Gs 0) {q : G}
    (hq : q ∈ QQ Gs 0) : s⁻¹ * q * s ∈ Gs 0 ↔ q ∈ QQ Gs 1 := by
  constructor
  · intro h
    have hsP : s ∉ Gs 0 ⊓ Gs 1 := fun h' => hs0 h'.1
    have hq1 : q ∈ Gs 1 := TT_le 1 (QQ_le_TT hD 0 hq)
    have hconj : s⁻¹ * q * s ∈ Gs 0 ⊓ Gs 1 :=
      ⟨h, (Gs 1).mul_mem ((Gs 1).mul_mem ((Gs 1).inv_mem hs) hq1) hs⟩
    have hall := core_of_fix_point (H := Gs 1) (P := Gs 0 ⊓ Gs 1) (S := QQ Gs 0) inf_le_right
      (Q0_le_P01 hD) (loc1_index_10 hD) hs hsP q hq hconj
    exact loc1_core hD q hq1 hall (Q0_core12 hD q hq)
  · intro h
    have : s⁻¹ * q * s ∈ QQ Gs 1 := by
      simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hs) h
    exact (TT_le 0 (QQ_le_TT hD 1 this))

omit [Finite G] in
theorem le_normalizer_of_conj {S N : Subgroup G} (hS : ∀ a ∈ S, ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    S ≤ Subgroup.normalizer (N : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn; exact hS a ha n hn
  · intro hn
    have := hS a⁻¹ (S.inv_mem ha) _ hn
    have e : a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n := by group
    rwa [e] at this

theorem uniq_line (hD : IsDSystem D Gs) {s v h : G} (hs : s ∈ Gs 1) (hs0 : s ∉ Gs 0)
    (hv : v ∈ Gs 1) (hh : h ∈ Gs 0) (hrel : s⁻¹ * h * v ∈ Gs 0) : h ∈ Gs 1 := by
  by_contra hh1
  have hquot : ∀ q ∈ QQ Gs 0, h⁻¹ * q * h ∈ QQ Gs 1 → q ∈ QQ Gs 1 := by
    intro q hq hqh
    rw [← fix_iff hD hs hs0 hq]
    have h1 : v⁻¹ * (h⁻¹ * q * h) * v ∈ Gs 0 :=
      TT_le 0 (QQ_le_TT hD 1 (by simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hv) hqh))
    have e : s⁻¹ * q * s =
        (s⁻¹ * h * v) * (v⁻¹ * (h⁻¹ * q * h) * v) * (s⁻¹ * h * v)⁻¹ := by group
    rw [e]
    exact (Gs 0).mul_mem ((Gs 0).mul_mem hrel h1) ((Gs 0).inv_mem hrel)
  have hv0 : v ∉ Gs 0 := fun hv0 => hs0 (by
    have h1 : s⁻¹ * h ∈ Gs 0 := by
      have := (Gs 0).mul_mem hrel ((Gs 0).inv_mem hv0)
      simpa [mul_assoc] using this
    have := (Gs 0).inv_mem ((Gs 0).mul_mem h1 ((Gs 0).inv_mem hh))
    simpa [mul_assoc] using this)
  have hquot2 : ∀ n ∈ QQ Gs 0, h * n * h⁻¹ ∈ QQ Gs 1 → n ∈ QQ Gs 1 := by
    intro n hn hnh
    rw [← fix_iff hD hv hv0 hn]
    have h1 : s⁻¹ * (h * n * h⁻¹) * s ∈ Gs 0 :=
      TT_le 0 (QQ_le_TT hD 1 (by simpa using normalizes_pCoreOf (Gs 1) ((Gs 1).inv_mem hs) hnh))
    have e : v⁻¹ * n * v = (s⁻¹ * h * v)⁻¹ * (s⁻¹ * (h * n * h⁻¹) * s) * (s⁻¹ * h * v) := by group
    rw [e]
    exact (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).inv_mem hrel) h1) hrel
  have hP : ∀ a ∈ Gs 0 ⊓ Gs 1, ∀ n ∈ QQ Gs 0 ⊓ QQ Gs 1, a * n * a⁻¹ ∈ QQ Gs 0 ⊓ QQ Gs 1 :=
    fun a ha n hn => ⟨normalizes_pCoreOf (Gs 0) ha.1 hn.1, normalizes_pCoreOf (Gs 1) ha.2 hn.2⟩
  have hhN : ∀ n ∈ QQ Gs 0 ⊓ QQ Gs 1, h * n * h⁻¹ ∈ QQ Gs 0 ⊓ QQ Gs 1 := by
    intro n hn
    have h0 : h * n * h⁻¹ ∈ QQ Gs 0 := normalizes_pCoreOf (Gs 0) hh hn.1
    refine ⟨h0, hquot _ h0 ?_⟩
    have e : h⁻¹ * (h * n * h⁻¹) * h = n := by group
    rw [e]; exact hn.2
  obtain ⟨-, -, hmax0⟩ :
      Gs 0 ⊓ Gs 1 ⊓ Gs 2 ≤ Gs 0 ⊓ Gs 1 ∧ A6.IsMaxSubgroupIn (Gs 0 ⊓ Gs 1) (Gs 0) :=
    ((hD.d3max 0 1 2 (by decide) (by decide) (by decide)).2 (Gs 0 ⊓ Gs 1)).2 (Or.inl rfl)
  have hP' : Gs 0 ⊓ Gs 1 ≤ Subgroup.normalizer ((QQ Gs 0 ⊓ QQ Gs 1 : Subgroup G) : Set G) ⊓ Gs 0 :=
    le_inf (le_normalizer_of_conj hP) inf_le_left
  have hG0 : ∀ a ∈ Gs 0, ∀ n ∈ QQ Gs 0 ⊓ QQ Gs 1, a * n * a⁻¹ ∈ QQ Gs 0 ⊓ QQ Gs 1 := by
    rcases hmax0 _ hP' inf_le_right with hW | hW
    · exfalso
      have hhW : h ∈ Subgroup.normalizer ((QQ Gs 0 ⊓ QQ Gs 1 : Subgroup G) : Set G) ⊓ Gs 0 := by
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_normalizer_iff.2 (fun n =>
          ⟨fun hn => hhN n hn, fun hn => ?_⟩), hh⟩
        have hn0 : n ∈ QQ Gs 0 := by
          have := normalizes_pCoreOf (Gs 0) ((Gs 0).inv_mem hh) hn.1
          have e : h⁻¹ * (h * n * h⁻¹) * h⁻¹⁻¹ = n := by group
          rwa [e] at this
        exact ⟨hn0, hquot2 n hn0 hn.2⟩
      rw [hW] at hhW
      exact hh1 hhW.2
    · intro a ha n hn
      have : a ∈ Subgroup.normalizer ((QQ Gs 0 ⊓ QQ Gs 1 : Subgroup G) : Set G) ⊓ Gs 0 := by
        rw [hW]; exact ha
      exact (Subgroup.mem_normalizer_iff.1 this.1 n).1 hn
  have hNQ2 : QQ Gs 0 ⊓ QQ Gs 1 ≤ QQ Gs 2 := fun n hn =>
    loc2_core hD n (TT_le 2 (QQ_le_TT hD 0 hn.1)) (core_of_conj_mem_Q1 hD (fun a ha => by
      have := (hG0 a⁻¹ ((Gs 0).inv_mem ha.1) n hn).2
      simpa using this))
  have hQ0Q2 : QQ Gs 0 ≤ QQ Gs 2 := loc2_noNormal_20 hD (Q0_le_P02 hD)
    (fun a ha m hm => normalizes_pCoreOf (Gs 0) ha.1 hm) (fun m₁ h₁ m₂ h₂ => by
      rcases Q0_cases hD m₁ h₁ m₂ h₂ with h | h | h
      · exact Or.inl (hNQ2 ⟨h₁, h⟩)
      · exact Or.inr (Or.inl (hNQ2 ⟨h₂, h⟩))
      · exact Or.inr (Or.inr (hNQ2 ⟨(QQ Gs 0).mul_mem h₁ ((QQ Gs 0).inv_mem h₂), h⟩)))
  exact not_Q0_le_Q1 hD (fun n hn => loc1_core hD n (TT_le 1 (QQ_le_TT hD 0 hn))
    (Q2_core10 hD n (hQ0Q2 hn)) (Q0_core12 hD n hn))

end CFSG.Quasithin.H13.I51
