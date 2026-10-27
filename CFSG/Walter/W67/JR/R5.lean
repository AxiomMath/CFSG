module

public import CFSG.Walter.W67.JR.Ree

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups

namespace JRGroup

variable {L : Type} [Group L] [Finite L] (h : JRGroup L)

theorem J_mem_centralizer {X : Subgroup L} (hX : X ≤ h.K) :
    h.J ∈ Subgroup.centralizer (X : Set L) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hy => h.commute_J_of_mem_K (hX hy)

theorem J_mem_normalizer {X : Subgroup L} (hX : X ≤ h.K) :
    h.J ∈ Subgroup.normalizer (X : Set L) :=
  Subgroup.centralizer_le_normalizer _ (h.J_mem_centralizer hX)

theorem mem_K_or_of_mem_H (hq : 5 < h.q) {x : L}
    (hx : x ∈ Subgroup.centralizer ({h.J} : Set L)) : x ∈ h.K ∨ h.J * x ∈ h.K :=
  (h.toJTHyp hq).mem_centralizer_t.mp hx

theorem eq_J_mul_J_mul (x : L) : x = h.J * (h.J * x) := by
  rw [← mul_assoc, h.J_mul_J, one_mul]

omit [Finite L] in
theorem inv_ne_self_of_odd {b : L} (hb : Odd (orderOf b)) (hb1 : b ≠ 1) : b⁻¹ ≠ b := by
  intro hinv
  have h2 : b ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 1 [← hinv]
    exact inv_mul_cancel b
  have hd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
  · exact hb1 (orderOf_eq_one_iff.mp h1)
  · rw [h1] at hb
    exact absurd hb (by decide)

theorem r5
    (hJT : JTThreeHyp) (hq5 : h.q ≠ 5) : h.R5 := by
  intro hq3 B hBK hBc hBcard
  have hq := h.five_lt_q hq5 hq3
  have hp3 := h.p_eq_three hJT hq
  set h' := h.toJTHyp hq with hh'
  have hq8 : h.q % 8 = 3 := h'.q_mod_eight_of_eq_three hp3
  have hq4 : h.p ^ h.f % 4 = 3 := by
    change h.q % 4 = 3
    omega
  have hBcard' : 2 * Nat.card B + 1 = h.q := by omega
  obtain ⟨w, hU⟩ := JT.exists_torusData_of_isCyclic h.K h.iso h.p_ne_two hq hq4 hBK hBc
    hBcard'
  have hBodd : Odd (Nat.card B) := ⟨(Nat.card B - 1) / 2, by omega⟩
  have hB1 : 1 < Nat.card B := by omega
  have hbodd : ∀ b ∈ B, Odd (orderOf b) := fun b hb =>
    Odd.of_dvd_nat hBodd (Subgroup.orderOf_dvd_natCard B hb)
  have hBne : B ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hB1
    omega
  have hwK := hU.w_mem
  have hJw : Commute h.J w := (h.commute_J_of_mem_K hwK).symm
  have hww := hU.w_mul_self
  have hw1 : w ≠ 1 := fun h0 => hU.w_not_mem (h0 ▸ B.one_mem)
  have hJw' : h.J ≠ w := fun h0 => h.J_not_mem (h0 ▸ hwK)
  set W := GorensteinWalter.kleinFourOfCommutingInvolutions h.J w h.J_mul_J hww hJw with hWdef
  have hW4 : IsKleinFour W := GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions
    _ _ _ _ h.J_ne_one hw1 hJw' hJw
  have hmemW : ∀ x, x ∈ W ↔ x = h.J * w ∨ x = h.J ∨ x = w ∨ x = 1 := fun x => Iff.rfl
  have hJW : h.J ∈ W := (hmemW _).mpr (Or.inr (Or.inl rfl))
  have hwW : w ∈ W := (hmemW _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hKN : ∀ R : Subgroup L, R ≤ B → R ≠ ⊥ →
      h.K ⊓ Subgroup.normalizer (R : Set L) = B ⊔ Subgroup.zpowers w := hU.normalizer
  have hwN : w ∈ Subgroup.normalizer (B : Set L) := by
    have : w ∈ B ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    rw [← hKN B le_rfl hBne] at this
    exact this.2
  obtain ⟨⟨b₀, hb₀⟩, hgen⟩ := hBc.exists_generator
  have hb₀B : B = Subgroup.zpowers b₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := hgen ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact hb₀
  have hb₀ord : orderOf b₀ = Nat.card B := by
    rw [hb₀B, Nat.card_zpowers]
  have hb₀1 : b₀ ≠ 1 := by
    intro h0
    rw [h0, orderOf_one] at hb₀ord
    omega
  have hNB : Subgroup.normalizer (B : Set L) ≤ Subgroup.centralizer ({h.J} : Set L) := by
    have := h'.normalizer_le_of_lemma716 hp3 (h'.lemma_7_16 hp3) (hBK hb₀)
      (by rw [hb₀ord]; exact hBcard') (Subgroup.mem_zpowers b₀) hb₀1
    rw [hb₀B]
    exact this
  have hCK : ∀ b ∈ B, b ≠ 1 → ∀ y ∈ h.K, y * b = b * y → y ∈ B := by
    intro b hb hb1 y hyK hyb
    have hR : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hb
    have hRne : Subgroup.zpowers b ≠ ⊥ := by
      rw [Ne, Subgroup.zpowers_eq_bot]
      exact hb1
    have hy : y ∈ B ⊔ Subgroup.zpowers w := by
      rw [← hKN _ hR hRne]
      exact ⟨hyK, JT.mem_normalizer_zpowers_of_commute hyb⟩
    rcases hU.conj_eq hy hb with ⟨hyB, -⟩ | ⟨-, hyinv⟩
    · exact hyB
    · exfalso
      rw [hyb, mul_inv_cancel_right] at hyinv
      exact inv_ne_self_of_odd (hbodd b hb) hb1 hyinv.symm
  refine ⟨W, hW4.card_four, fun x hx => JT.mul_self_of_isKleinFour' hW4 hx, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    · intro x hx
      have hkey : ∀ y ∈ h.K, y ∈ Subgroup.normalizer (B : Set L) → y ∈ W ⊔ B := by
        intro y hyK hyN
        have hy : y ∈ B ⊔ Subgroup.zpowers w := by
          rw [← hKN B le_rfl hBne]
          exact ⟨hyK, hyN⟩
        exact (sup_le le_sup_right ((Subgroup.zpowers_le.mpr hwW).trans le_sup_left)) hy
      have hJN := h.J_mem_normalizer hBK
      rcases h.mem_K_or_of_mem_H hq (hNB hx) with hxK | hxK
      · exact hkey x hxK hx
      · rw [h.eq_J_mul_J_mul x]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hJW)
          (hkey _ hxK (Subgroup.mul_mem _ hJN hx))
    · refine sup_le ?_ Subgroup.le_normalizer
      intro x hx
      rcases (hmemW x).mp hx with rfl | rfl | rfl | rfl
      · exact Subgroup.mul_mem _ (h.J_mem_normalizer hBK) hwN
      · exact h.J_mem_normalizer hBK
      · exact hwN
      · exact Subgroup.one_mem _
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxB⟩ := hx
    have hx2 : x * x = 1 := JT.mul_self_of_isKleinFour' hW4 hxW
    by_contra hx1
    exact inv_ne_self_of_odd (hbodd x hxB) hx1 (inv_eq_of_mul_eq_one_right hx2)
  ·
    intro b hb hb1
    refine ⟨h.J, hJW, h.orderOf_J, ?_, ?_⟩
    · apply le_antisymm
      · intro x hx
        have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp hx
        have hxJ := h'.lemma_7_16 hp3 B hBK hBc hBcard' b hb hb1 hx
        have hJb : h.J * b = b * h.J := (h.commute_J_of_mem_K (hBK hb)).symm
        rcases h.mem_K_or_of_mem_H hq hxJ with hxK | hxK
        · exact Subgroup.mem_sup_right (hCK b hb hb1 x hxK hxb)
        · rw [h.eq_J_mul_J_mul x]
          refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
            (Subgroup.mem_sup_right (hCK b hb hb1 _ hxK ?_))
          rw [mul_assoc, hxb, ← mul_assoc, hJb, mul_assoc]
      · refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact (h.commute_J_of_mem_K (hBK hb)).symm
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          have := hBc
          exact congrArg Subtype.val
            ((IsCyclic.commGroup (α := B)).mul_comm ⟨y, hy⟩ ⟨b, hb⟩)
    · apply le_antisymm
      · intro x hx
        obtain ⟨hxW, hxC⟩ := hx
        rcases (hmemW x).mp hxW with rfl | rfl | rfl | rfl
        · exfalso
          have hc := Subgroup.mem_centralizer_iff.mp hxC b hb
          have hinv := hU.inv b hb
          have hJb' : h.J * b * h.J⁻¹ = b := by
            rw [← h.commute_J_of_mem_K (hBK hb), mul_inv_cancel_right]
          have : h.J * w * b * (h.J * w)⁻¹ = b⁻¹ := by
            rw [show h.J * w * b * (h.J * w)⁻¹ = h.J * (w * b * w⁻¹) * h.J⁻¹ by group, hinv,
              show h.J * b⁻¹ * h.J⁻¹ = (h.J * b * h.J⁻¹)⁻¹ by group, hJb']
          rw [← hc, mul_inv_cancel_right] at this
          exact inv_ne_self_of_odd (hbodd b hb) hb1 this.symm
        · exact Subgroup.mem_zpowers _
        · exfalso
          have hc := Subgroup.mem_centralizer_iff.mp hxC b hb
          have hinv := hU.inv b hb
          rw [← hc, mul_inv_cancel_right] at hinv
          exact inv_ne_self_of_odd (hbodd b hb) hb1 hinv.symm
        · exact Subgroup.one_mem _
      · rw [Subgroup.zpowers_le]
        exact ⟨hJW, h.J_mem_centralizer hBK⟩

end JRGroup

end CFSG.Walter.W67
