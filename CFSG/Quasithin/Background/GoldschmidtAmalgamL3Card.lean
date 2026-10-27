module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Mod

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem mem_normalizer_zpowers_of_mul_comm {y w : D} (hc : y * w = w * y) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers w : Set D) :=
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers_of_mul_comm hc)

omit [Finite D] in
theorem card_zpowers_le_two {w : D} (hw : w ^ 2 = 1) : Nat.card (Subgroup.zpowers w) ≤ 2 := by
  rw [Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hw)

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem exists_conj_gens :
    ∃ w₁ w₂ : D, w₁ ∈ conjClosure V B ∧ w₂ ∈ conjClosure V B ∧
      conjClosure V B ≤ V ⊔ Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂ := by
  obtain ⟨x, hxB, hx3⟩ := h.gold.vertex_right.exists_order_three
  obtain ⟨a, -, -, hVset⟩ := h.natural.basis
  have hxT : x ∉ A ⊓ B := h.gold.vertex_right.not_mem_of_orderOf hx3
  have hx2T : x * x ∉ A ⊓ B := h.gold.vertex_right.sq_not_mem_of_orderOf hx3
  have hxxB : x * x ∈ B := B.mul_mem hxB hxB
  have hzV : z ∈ V := h.natural.z_mem_V
  have haV : a ∈ V := by
    have : a ∈ (V : Set D) := by rw [hVset]; simp
    exact this
  have hmemV : ∀ v' ∈ V, v' = 1 ∨ v' = z ∨ v' = a ∨ v' = z * a := by
    intro v' hv'
    have : v' ∈ (V : Set D) := hv'
    rw [hVset] at this
    simpa using this
  have hz₁ : x * z * x⁻¹ = z := h.central x hxB
  have hz₂ : x * x * z * (x * x)⁻¹ = z := h.central (x * x) hxxB
  have hS₁ : ∀ v' ∈ V, x * v' * x⁻¹ ∈
      V ⊔ Subgroup.zpowers (x * a * x⁻¹) ⊔ Subgroup.zpowers (x * x * a * (x * x)⁻¹) := by
    intro v' hv'
    rcases hmemV v' hv' with e | e | e | e
    · simp [e]
    · rw [e, hz₁]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV)
    · rw [e]
      exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · have e' : x * (z * a) * x⁻¹ = (x * z * x⁻¹) * (x * a * x⁻¹) := by group
      rw [e, e', hz₁]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
  have hS₂ : ∀ v' ∈ V, x * x * v' * (x * x)⁻¹ ∈
      V ⊔ Subgroup.zpowers (x * a * x⁻¹) ⊔ Subgroup.zpowers (x * x * a * (x * x)⁻¹) := by
    intro v' hv'
    rcases hmemV v' hv' with e | e | e | e
    · simp [e]
    · rw [e, hz₂]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV)
    · rw [e]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · have e' : x * x * (z * a) * (x * x)⁻¹ =
          (x * x * z * (x * x)⁻¹) * (x * x * a * (x * x)⁻¹) := by group
      rw [e, e', hz₂]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hzV))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  refine ⟨x * a * x⁻¹, x * x * a * (x * x)⁻¹,
    HypF91.conjSub_le_conjClosure hxB (mul_mem_conjSub haV),
    HypF91.conjSub_le_conjClosure hxxB (mul_mem_conjSub haV), ?_⟩
  refine conjClosure_le fun k hk v hv => ?_
  rcases coset_decomp h.gold.relIndex_right hxB hxT hx2T hk with hkT | ⟨t, htT, rfl⟩ |
      ⟨t, htT, rfl⟩
  · have : k * v * k⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 hkT.1) v).mp hv
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left this)
  · have htv : t * v * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 htT.1) v).mp hv
    have e : x * t * v * (x * t)⁻¹ = x * (t * v * t⁻¹) * x⁻¹ := by group
    rw [e]; exact hS₁ _ htv
  · have htv : t * v * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.natural.reduced.2.1 htT.1) v).mp hv
    have e : x * x * t * v * (x * x * t)⁻¹ = x * x * (t * v * t⁻¹) * (x * x)⁻¹ := by group
    rw [e]; exact hS₂ _ htv

theorem card_conjClosure_le : Nat.card (conjClosure V B) ≤ 16 := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hle⟩ := h.exists_conj_gens
  have hw₁2 : w₁ ^ 2 = 1 := h.abelian.2 w₁ hw₁
  have hw₂2 : w₂ ^ 2 = 1 := h.abelian.2 w₂ hw₂
  have hV₁ : V ≤ Subgroup.normalizer (Subgroup.zpowers w₁ : Set D) := fun v hv =>
    mem_normalizer_zpowers_of_mul_comm (isElemAbelian_comm h.abelian (le_conjClosure V B hv) hw₁)
  have hV₂ : V ⊔ Subgroup.zpowers w₁ ≤ Subgroup.normalizer (Subgroup.zpowers w₂ : Set D) := by
    refine sup_le (fun v hv => mem_normalizer_zpowers_of_mul_comm
      (isElemAbelian_comm h.abelian (le_conjClosure V B hv) hw₂)) ?_
    refine Subgroup.zpowers_le.mpr ?_
    exact mem_normalizer_zpowers_of_mul_comm (isElemAbelian_comm h.abelian hw₁ hw₂)
  have c1 := GoldAmN.card_sup_le_of_le_normalizer V (Subgroup.zpowers w₁) hV₁
  have c2 := GoldAmN.card_sup_le_of_le_normalizer (V ⊔ Subgroup.zpowers w₁)
    (Subgroup.zpowers w₂) hV₂
  have c3 := Subgroup.card_le_of_le hle
  rw [h.natural.card_eq] at c1
  calc Nat.card (conjClosure V B)
      ≤ Nat.card ↥(V ⊔ Subgroup.zpowers w₁ ⊔ Subgroup.zpowers w₂) := c3
    _ ≤ Nat.card ↥(V ⊔ Subgroup.zpowers w₁) * Nat.card (Subgroup.zpowers w₂) := c2
    _ ≤ (4 * 2) * 2 :=
      Nat.mul_le_mul (c1.trans (Nat.mul_le_mul_left 4 (card_zpowers_le_two hw₁2)))
        (card_zpowers_le_two hw₂2)

theorem exists_not_mem_normalizer : ∃ b ∈ B, b ∉ Subgroup.normalizer (V : Set D) := by
  by_contra hcon
  push Not at hcon
  have hBV : B ≤ Subgroup.normalizer (V : Set D) := fun b hb => hcon b hb
  have hVT : V ≤ A ⊓ B := h.natural.le_pCoreOf.trans h.gold.pCoreOf_left_le
  exact h.natural.natural.ne_bot (h.gold.eq_bot_of_normalizes h.natural.reduced.2.1 hBV hVT)

theorem not_conjClosure_le : ¬ conjClosure V B ≤ V := by
  obtain ⟨b, hb, hbN⟩ := h.exists_not_mem_normalizer
  intro hle
  have h1 : conjSub b V ≤ V := (HypF91.conjSub_le_conjClosure hb).trans hle
  have h2 : conjSub b V = V := Subgroup.eq_of_le_of_card_ge h1 (by rw [card_conjSub])
  exact hbN (mem_normalizer_of_conjSub_eq h2)

theorem eight_le_card_conjClosure : 8 ≤ Nat.card (conjClosure V B) := by
  have hgt : 4 < Nat.card (conjClosure V B) := by
    have hle := Subgroup.card_le_of_le (le_conjClosure V B)
    have h4 := h.natural.card_eq
    by_contra hcon
    have heq : V = conjClosure V B :=
      Subgroup.eq_of_le_of_card_ge (le_conjClosure V B) (by omega)
    exact h.not_conjClosure_le heq.symm.le
  obtain ⟨n, hn⟩ := h.hypF91V.isPGroup_conjClosure.exists_card_eq
  rw [hn] at hgt ⊢
  have hn3 : 3 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n <;> simp at hgt
  calc 8 = 2 ^ 3 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3

theorem card_conjClosure_eq :
    Nat.card (conjClosure V B) = 8 ∨ Nat.card (conjClosure V B) = 16 := by
  have h8 := h.eight_le_card_conjClosure
  have h16 := h.card_conjClosure_le
  obtain ⟨n, hn⟩ := h.hypF91V.isPGroup_conjClosure.exists_card_eq
  rw [hn] at h8 h16 ⊢
  have hn3 : 3 ≤ n := by
    by_contra hlt
    push Not at hlt
    interval_cases n <;> simp at h8
  have hn4 : n ≤ 4 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  interval_cases n <;> simp

theorem eight_le_card_coreIn : 8 ≤ Nat.card ↥(coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B) :=
  h.eight_le_card_conjClosure.trans (Subgroup.card_le_of_le h.conjClosure_le_coreIn)

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
