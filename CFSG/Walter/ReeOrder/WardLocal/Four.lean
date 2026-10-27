module

public import CFSG.Walter.ReeOrder.WardLocal.Hall4

public section

open scoped BigOperators Classical MatrixGroups Pointwise

namespace CFSG.Walter.WardLocal

open CFSG CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect

variable {G : Type} [Group G] [Finite G]

theorem exists_hall
    (h : ReeTypeHyp G) {k : ℕ} (hq : h.q = 3 ^ (2 * k + 1)) (s : Bool) :
    ∃ M W : Subgroup G,
      (∀ x ∈ M, ∀ y ∈ M, x * y = y * x) ∧
      Nat.card M = (if s then h.q + 1 + 3 * 3 ^ k else h.q + 1 - 3 * 3 ^ k) ∧
      Nat.Coprime (Nat.card M) M.index ∧
      (∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) ∧
      M.relIndex (Subgroup.normalizer (M : Set G)) = 6 ∧
      IsCyclic W ∧ Nat.card W = 6 ∧ M ⊓ W = ⊥ ∧
      Subgroup.normalizer (M : Set G) = M ⊔ W ∧
      ∀ w ∈ W, w ≠ 1 → M ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨⟨k', -, hq'⟩, hG⟩ := ward_order h
  have hkk : k' = k := by
    have h1 : 3 ^ (2 * k' + 1) = 3 ^ (2 * k + 1) := hq'.symm.trans hq
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1
    omega
  subst hkk
  have : CharP h.F 3 := ree_charP_three h hq
  obtain ⟨S, D, B, P₀, hP1P, hPc, hPn, hN1c⟩ := exists_data h hq hG
  have hK := h.card_F
  have hm : h.q = 3 * (3 ^ k') ^ 2 := by rw [hq, ← pow_mul, ← pow_succ']; ring_nf
  obtain ⟨M₁, hc₁, hcomm₁, hcen₁⟩ := B.exists_minus hq hK hG hP1P hPc hPn hN1c hm
  obtain ⟨M₂, hc₂, hcomm₂, hcen₂⟩ := B.exists_plus hq hK hG hP1P hPc hPn hN1c hm
  obtain ⟨h6₁, h6₂⟩ :=
    B.relIndex_eq_six hq hK hG hP1P hPc hPn hN1c hm hc₁ hcomm₁ hcen₁ hc₂ hcomm₂ hcen₂
  cases s
  · obtain ⟨W, hWc, hW6, hMW, hN, hfpf⟩ :=
      Block.exists_complement (S := S) hq hm (Or.inl rfl) hc₁ hcomm₁ hcen₁ h6₁
    exact ⟨M₁, W, hcomm₁, by simpa using hc₁, (Block.coprime_index_minus hq hG hm hc₁).1,
      hcen₁, h6₁, hWc, hW6, hMW, hN, hfpf⟩
  · obtain ⟨W, hWc, hW6, hMW, hN, hfpf⟩ :=
      Block.exists_complement (S := S) hq hm (Or.inr rfl) hc₂ hcomm₂ hcen₂ h6₂
    exact ⟨M₂, W, hcomm₂, by simpa using hc₂, (Block.coprime_index_plus hq hG hm hc₂).1,
      hcen₂, h6₂, hWc, hW6, hMW, hN, hfpf⟩

theorem ward_four
    (h : ReeTypeHyp G) {k : ℕ} (hq : h.q = 3 ^ (2 * k + 1)) :
    h.q ^ 2 - h.q + 1 = (h.q + 1 + 3 * 3 ^ k) * (h.q + 1 - 3 * 3 ^ k) ∧
    ∀ s : Bool, ∃ M W : Subgroup G,
      IsMulCommutative M ∧
      Nat.card M = (if s then h.q + 1 + 3 * 3 ^ k else h.q + 1 - 3 * 3 ^ k) ∧
      Nat.Coprime (Nat.card M) M.index ∧
      (∀ x ∈ M, x ≠ 1 → Subgroup.centralizer ({x} : Set G) = M) ∧
      (∀ g : G, M ⊓ (MulAut.conj g • M) = ⊥ ∨ M ⊓ (MulAut.conj g • M) = M) ∧
      IsCyclic W ∧ Nat.card W = 6 ∧ M ⊓ W = ⊥ ∧
      Subgroup.normalizer (M : Set G) = M ⊔ W ∧
      ∀ w ∈ W, w ≠ 1 → M ⊓ Subgroup.centralizer ({w} : Set G) = ⊥ := by
  refine ⟨hall_mul (by rw [hq, ← pow_mul, ← pow_succ']; ring_nf), fun s => ?_⟩
  obtain ⟨M, W, hcomm, hc, hcop, hcen, -, hWc, hW6, hMW, hN, hfpf⟩ := exists_hall h hq s
  exact ⟨M, W, ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hc, hcop, hcen,
    ti_of_centralizer hcen, hWc, hW6, hMW, hN, hfpf⟩

theorem ward_four_hall
    (h : ReeTypeHyp G) (m' : ℕ) (hm' : m' ^ 2 = 3 * h.q) (s : Bool) :
    ∃ M : Subgroup G, IsMulCommutative M ∧
      Nat.card M = (if s then h.q + 1 + m' else h.q + 1 - m') ∧
      Nat.Coprime (Nat.card M) M.index ∧
      (∃ g ∈ Subgroup.normalizer (M : Set G),
        Subgroup.zpowers g ⊔ Subgroup.centralizer (M : Set G) =
          Subgroup.normalizer (M : Set G)) ∧
      ((Subgroup.centralizer (M : Set G)).subgroupOf
        (Subgroup.normalizer (M : Set G))).index = 6 ∧
      ∀ c ∈ M, c ≠ 1 → Subgroup.centralizer ({c} : Set G) = M := by
  obtain ⟨⟨k, hk, hq⟩, -⟩ := ward_order h
  have hm'k : m' = 3 * 3 ^ k := by
    have h1 : m' ^ 2 = (3 * 3 ^ k) ^ 2 := by
      rw [hm', hq]; ring
    exact Nat.pow_left_injective (by norm_num) h1
  subst hm'k
  obtain ⟨M, W, hcomm, hcard, hcop, hcen, h6, hWc, hW6, hMW, hN, -⟩ := exists_hall h hq s
  have hCM : Subgroup.centralizer (M : Set G) = M := by
    have hne : ∃ x ∈ M, x ≠ 1 := by
      by_contra hne
      push Not at hne
      have : M = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hne
      rw [this, Subgroup.card_bot] at hcard
      have h9 : 3 ≤ 3 ^ k := Nat.le_self_pow (by omega) 3
      have hq' : h.q = 3 * (3 ^ k) ^ 2 := by rw [hq, ← pow_mul, ← pow_succ']; ring_nf
      have : 3 * 3 ^ k + 3 ≤ h.q + 1 := by rw [hq']; nlinarith
      cases s <;> simp at hcard <;> omega
    obtain ⟨x₀, hx₀, hx₀1⟩ := hne
    apply le_antisymm
    · intro z hz
      rw [← hcen x₀ hx₀ hx₀1, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hz x₀ hx₀).symm
    · intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcomm y hy z hz
  obtain ⟨⟨g, hg⟩, hgen⟩ := hWc.exists_generator
  have hWz : W = Subgroup.zpowers g := by
    apply le_antisymm
    · intro w hw
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨w, hw⟩)
      have := congrArg Subtype.val hi
      rw [Subgroup.coe_zpow] at this
      exact Subgroup.mem_zpowers_iff.mpr ⟨i, this⟩
    · rw [Subgroup.zpowers_le]; exact hg
  refine ⟨M, ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hcard, hcop, ⟨g, ?_, ?_⟩, ?_,
    fun c hc hc1 => hcen c hc hc1⟩
  · rw [hN]; exact Subgroup.mem_sup_right hg
  · rw [hCM, ← hWz, sup_comm, hN]
  · rw [hCM]; exact h6

end CFSG.Walter.WardLocal
