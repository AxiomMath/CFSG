module

public import CFSG.Quasithin.Vol2.Ch3E215MC
public import CFSG.Quasithin.Vol2.Ch3E215MD

public section

namespace CFSG.Quasithin.Ch3E215M

open CFSG.Open CFSG.QuasithinUnique B6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

omit [Finite G] in
theorem le_of_mem_normalizer (h : E2.Pair X T M V g)
    (hg : g ∈ Subgroup.normalizer (M : Set G)) : X ≤ M := by
  have hVM : V ≤ M := h.le_pCoreOf.trans (pCoreOf_le 2 M)
  rw [h.gen]
  refine sup_le hVM ?_
  rw [← conjSub_eq_self hg]
  exact (conjSub g).monotone hVM

theorem exists_orderOf_of_surjective {H : Subgroup G} {I : Subgroup H} {L : Type*} [Group L]
    {ψ : I →* L} (hψ : Function.Surjective ψ) {c : L} {d : ℕ} (hc : orderOf c = d) :
    ∃ x ∈ I.map H.subtype, orderOf x = d := by
  obtain ⟨y, rfl⟩ := hψ c
  have hdvd : d ∣ orderOf y := hc ▸ orderOf_map_dvd ψ y
  have hz : orderOf (y ^ (orderOf y / d)) = d := orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
  refine ⟨((y ^ (orderOf y / d) : I) : H), ⟨_, (y ^ (orderOf y / d)).2, rfl⟩, ?_⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]

theorem eq_three_of_dvd {a m : ℕ} (ha : 2 ≤ a) (hm : 0 < m) (hm2 : m ≤ 2)
    (hdvd : a ∣ 2 ^ m - 1) : a = 3 := by
  interval_cases m
  · have h1 : a ∣ 1 := by simpa using hdvd
    have := Nat.le_of_dvd one_pos h1
    omega
  · have h3 : a ∣ 3 := by simpa using hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h1 | h1
    · omega
    · exact h1

omit [Finite G] in
theorem relIndex_eq_three (h : E2.Pair X T M V g) (h6 : (kerIn M X).relIndex X = 6) :
    M.relIndex X = 3 := by
  have hdvd6 : M.relIndex X ∣ 6 := h6 ▸ Subgroup.relIndex_dvd_of_le_left X kerIn_le
  have hTM : T ≤ M := fun t ht => h.normalizer_le ⟨h.sylow.1 ht, h.normal_T ht⟩
  have hodd : ¬ 2 ∣ M.relIndex X := fun h2 =>
    h.sylow.2.2 (h2.trans (Subgroup.relIndex_dvd_of_le_left X hTM))
  have hne1 : M.relIndex X ≠ 1 := fun h1 => by
    have hXM : X ≤ M := Subgroup.relIndex_eq_one.1 h1
    have hXJ : X ≤ kerIn M X := fun x hx => mem_kerIn.2 fun b hb =>
      hXM (X.mul_mem (X.mul_mem hb hx) (X.inv_mem hb))
    rw [Subgroup.relIndex_eq_one.2 hXJ] at h6
    omega
  have hle6 : M.relIndex X ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
  obtain ⟨r, hr⟩ : ∃ r, M.relIndex X = r := ⟨_, rfl⟩
  rw [hr] at hdvd6 hodd hne1 hle6 ⊢
  interval_cases r <;> omega

theorem exists_not_mem_conj (h : E2.Pair X T M V g) (hMX : ¬ X ≤ M) :
    g ∉ M ∧ ∃ n ∈ M, g⁻¹ * n * g ∉ M := by
  refine ⟨fun hgM => hMX (le_of_mem_normalizer h (Subgroup.le_normalizer hgM)), ?_⟩
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have h1 : conjSub g⁻¹ M ≤ M := fun x hx => by
    rw [mem_conjSub, inv_inv] at hx
    simpa [mul_assoc] using hcon _ hx
  have h2 : conjSub g⁻¹ M = M := Subgroup.eq_of_le_of_card_ge h1
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).ge
  have h3 : conjSub g M = M := by
    conv_lhs => rw [← h2]
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
  exact hMX (le_of_mem_normalizer h (mem_normalizer_of_conjSub_le h3.le h2.le))

theorem bruhat_of_relIndex_eq_three (h : E2.Pair X T M V g) (h3 : M.relIndex X = 3) :
    ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂ := by
  have hMX : ¬ X ≤ M := fun hXM => by
    rw [Subgroup.relIndex_eq_one.2 hXM] at h3
    omega
  obtain ⟨hgM, n, hnM, hn⟩ := exists_not_mem_conj h hMX
  have hy : (⟨g, h.mem⟩ : X) ∉ M.subgroupOf X := hgM
  have hn1 : (1 : X) ≠ ⟨n, h.le_X hnM⟩ := fun h1 => hn (by
    rw [show n = 1 from (congrArg Subtype.val h1).symm, mul_one, inv_mul_cancel]
    exact M.one_mem)
  have key : (((⟨g, h.mem⟩ : X) : X) : X ⧸ M.subgroupOf X) ≠
      ((⟨n, h.le_X hnM⟩ * ⟨g, h.mem⟩ : X) : X ⧸ M.subgroupOf X) := fun h' => hn (by
    have h2 := QuotientGroup.eq.mp h'
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [mul_assoc] using h2)
  have hinj : Set.InjOn (fun s => ((s * ⟨g, h.mem⟩ : X) : X ⧸ M.subgroupOf X))
      {1, ⟨n, h.le_X hnM⟩} := by
    intro s hs s' hs' hss'
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hs'
    rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
    · rfl
    · exact absurd (by simpa only [one_mul] using hss') key
    · exact absurd (by simpa only [one_mul] using hss'.symm) key
    · rfl
  have hSN : ({1, ⟨n, h.le_X hnM⟩} : Set X) ⊆ M.subgroupOf X := by
    intro s hs
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact (M.subgroupOf X).one_mem
    · exact hnM
  have hcard : (M.subgroupOf X).index ≤ ({1, ⟨n, h.le_X hnM⟩} : Set X).ncard + 1 := by
    rw [Set.ncard_pair hn1]
    exact (show M.relIndex X = 3 from h3).le
  intro x hx
  rcases bruhat_of_injOn hy hSN hinj hcard ⟨x, hx⟩ with h1 | ⟨n₁, hn₁, n₂, hn₂, h1⟩
  · exact Or.inl h1
  · refine Or.inr ⟨n₁, hn₁, n₂, hn₂, ?_⟩
    simpa using congrArg Subtype.val h1

theorem e215DataOf_of_dihedral (h : E2.Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V)
    {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hcard : (kerIn M X).relIndex X = 2 * ℓ ^ e) (hc : ∃ c ∈ X, orderOf c = ℓ ^ e) :
    E215DataOf X M V g := by
  have hV2 : (kerIn M X ⊓ V).relIndex V ≤ 2 := by
    have h1 := Ch3E213M.relIndex_le_two_pow h (n := 1) (hℓ.odd_of_ne_two hℓ2).pow
      (by rw [hcard, pow_one])
    rwa [pow_one] at h1
  rcases (two_le_relIndex h hchar hXV).lt_or_eq with hlt | heq
  · exact Or.inl (hV2.trans_lt hlt)
  obtain ⟨c, hcX, hco⟩ := hc
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨m, hm, hdvd, hle⟩ := exists_two_pow_le_of_orderOf h hchar hcX hℓ hℓ2 hco
  rw [← heq] at hle
  have hm2 : m ≤ 2 := by
    by_contra hm3
    have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right two_pos (by omega)
    have e8 : (2 : ℕ) ^ 3 = 8 := by norm_num
    have e4 : (2 : ℕ) ^ 2 = 4 := by norm_num
    omega
  have hℓe : 2 ≤ ℓ ^ (e' + 1) := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
  have h3 := relIndex_eq_three h (by rw [hcard, eq_three_of_dvd hℓe hm hm2 hdvd])
  exact e215DataOf_of_bruhat h (bruhat_of_relIndex_eq_three h h3) (by rw [h3, ← heq])

end CFSG.Quasithin.Ch3E215M
