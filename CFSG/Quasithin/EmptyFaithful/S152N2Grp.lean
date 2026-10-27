module

public import CFSG.Quasithin.EmptyFaithful.S152N2Lin
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ConfinedInvolution

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ]

theorem oddCoreIn_eq_of_normal [Finite Γ] {X N : Subgroup Γ} (hNX : N ≤ X)
    (hnorm : (N.subgroupOf X).Normal) (hodd : Odd (Nat.card N))
    (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N) : oddCoreIn X = N := by
  apply le_antisymm
  · intro z hz
    have hzX : z ∈ X := oddCoreIn_le X hz
    obtain ⟨k, hk⟩ := hpow z hzX
    have hodd' : Odd (orderOf z) := by
      have h1 : orderOf z ∣ Nat.card (oddCoreIn X) := by
        have := orderOf_dvd_natCard (⟨z, hz⟩ : oddCoreIn X)
        rwa [Subgroup.orderOf_mk] at this
      exact (odd_card_oddCoreIn X).of_dvd_nat h1
    have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd')
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact N.pow_mem hk m
  · have hodd' : Odd (Nat.card (N.subgroupOf X)) := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
    have hle : N.subgroupOf X ≤ fusionOddCore X := le_sSup ⟨hnorm, hodd'⟩
    intro k hk
    exact ⟨⟨k, hNX hk⟩, hle hk, rfl⟩

theorem prime_normal_facts [Finite Γ] {X N : Subgroup Γ} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hNX : N ≤ X) (hnorm : (N.subgroupOf X).Normal) (hcard : Nat.card N = p)
    (hC : ∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → x ∈ N)
    (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N) :
    oddCoreIn X = N ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      (∀ b ∈ X, b ^ 2 = 1 → b ≠ 1 → ∀ n ∈ N, b⁻¹ * n * b = n⁻¹) := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  refine ⟨oddCoreIn_eq_of_normal hNX hnorm (hcard ▸ hpodd) hpow, ?_, ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hcyc : IsCyclic N := isCyclic_of_prime_card hcard
    intro a ha b hb
    let _ : CommGroup N := IsCyclic.commGroup
    have := mul_comm (⟨a, ha⟩ : N) ⟨b, hb⟩
    exact congrArg Subtype.val this
  · intro b hbX hb2 hb1 n hn
    have hbN : b ∈ Subgroup.normalizer (N : Set Γ) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mp hnorm) hbX
    have hfix : N ⊓ Subgroup.centralizer ({b} : Set Γ) = ⊥ := by
      by_contra hne
      have hdvd : Nat.card (N ⊓ Subgroup.centralizer ({b} : Set Γ) : Subgroup Γ) ∣ p := by
        rw [← hcard]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact hne (Subgroup.card_eq_one.mp h1)
      · have hK : N ⊓ Subgroup.centralizer ({b} : Set Γ) = N :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hcard])
        have hcomm : ∀ m ∈ N, b * m = m * b := by
          intro m hm
          have : m ∈ N ⊓ Subgroup.centralizer ({b} : Set Γ) := by rw [hK]; exact hm
          have h2 := Subgroup.mem_centralizer_singleton_iff.mp this.2
          exact h2.symm
        have hbmem : b ∈ N := hC b hbX hcomm
        have hord : orderOf b ∣ p := by
          have := orderOf_dvd_natCard (⟨b, hbmem⟩ : N)
          rwa [Subgroup.orderOf_mk, hcard] at this
        have hord2 : orderOf b = 2 := orderOf_eq_prime hb2 hb1
        rw [hord2] at hord
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hord).symm
    exact (inverts_and_commute_of_inf_centralizer_eq_bot hb2 hbN hfix).1 n hn

theorem exists_normal_prime_of_card_two_mul [Finite Γ] {X : Subgroup Γ}
    {p : ℕ} (hp : p.Prime)
    (hX : Nat.card X = 2 * p) (hnc : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) :
    ∃ N : Subgroup Γ, N ≤ X ∧ (N.subgroupOf X).Normal ∧ Nat.card N = p ∧
      (∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → x ∈ N) ∧ (∀ x ∈ X, x ^ 2 ∈ N) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card X := ⟨2, by rw [hX]; ring⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hordc : orderOf (c : Γ) = p := by rw [Subgroup.orderOf_coe]; exact hc
  set N : Subgroup Γ := Subgroup.zpowers (c : Γ) with hN
  have hNX : N ≤ X := (Subgroup.zpowers_le).mpr c.2
  have hcardN : Nat.card N = p := by rw [hN, Nat.card_zpowers, hordc]
  have hidx : (N.subgroupOf X).index = 2 := by
    have h1 := (N.subgroupOf X).card_mul_index
    have h2 : Nat.card (N.subgroupOf X) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, hcardN]
    rw [h2, hX] at h1
    have hp0 : 0 < p := hp.pos
    nlinarith
  have hnorm : (N.subgroupOf X).Normal := Subgroup.normal_of_index_eq_two hidx
  have hNcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    have hcyc : IsCyclic N := isCyclic_of_prime_card hcardN
    intro a ha b hb
    let _ : CommGroup N := IsCyclic.commGroup
    have := mul_comm (⟨a, ha⟩ : N) ⟨b, hb⟩
    exact congrArg Subtype.val this
  refine ⟨N, hNX, hnorm, hcardN, ?_, ?_⟩
  · intro x hxX hxc
    by_contra hxN
    obtain ⟨a, haX, b, hbX, hab⟩ := hnc
    apply hab
    have hxK : (⟨x, hxX⟩ : X) ∉ N.subgroupOf X := fun h => hxN h
    have hdecomp : ∀ u ∈ X, ∃ m ∈ N, ∃ e : ℕ, e < 2 ∧ u = m * x ^ e := by
      intro u hu
      by_cases huN : u ∈ N
      · exact ⟨u, huN, 0, by norm_num, by simp⟩
      · have huK : (⟨u, hu⟩ : X) ∉ N.subgroupOf X := fun h => huN h
        have hmem : (⟨u, hu⟩ : X) * (⟨x, hxX⟩ : X)⁻¹ ∈ N.subgroupOf X := by
          rw [Subgroup.mul_mem_iff_of_index_two hidx]
          constructor
          · intro h; exact absurd h huK
          · intro h; exact absurd ((N.subgroupOf X).inv_mem_iff.mp h) hxK
        have hm : u * x⁻¹ ∈ N := hmem
        exact ⟨u * x⁻¹, hm, 1, by norm_num, by simp⟩
    obtain ⟨m₁, hm₁, e₁, -, rfl⟩ := hdecomp a haX
    obtain ⟨m₂, hm₂, e₂, -, rfl⟩ := hdecomp b hbX
    have hx1 : ∀ m ∈ N, ∀ e : ℕ, x ^ e * m = m * x ^ e := fun m hm e =>
      ((Commute.pow_left (show Commute x m from hxc m hm) e)).eq
    calc m₁ * x ^ e₁ * (m₂ * x ^ e₂) = m₁ * (x ^ e₁ * m₂) * x ^ e₂ := by group
      _ = m₁ * (m₂ * x ^ e₁) * x ^ e₂ := by rw [hx1 m₂ hm₂]
      _ = (m₁ * m₂) * (x ^ e₁ * x ^ e₂) := by group
      _ = (m₂ * m₁) * (x ^ e₂ * x ^ e₁) := by
          rw [hNcomm m₁ hm₁ m₂ hm₂, ← pow_add, ← pow_add, add_comm]
      _ = m₂ * x ^ e₂ * (m₁ * x ^ e₁) := by
          calc (m₂ * m₁) * (x ^ e₂ * x ^ e₁) = m₂ * (m₁ * x ^ e₂) * x ^ e₁ := by group
            _ = m₂ * (x ^ e₂ * m₁) * x ^ e₁ := by rw [hx1 m₁ hm₁]
            _ = m₂ * x ^ e₂ * (m₁ * x ^ e₁) := by group
  · intro x hx
    have := Subgroup.pow_index_mem (N.subgroupOf X) (⟨x, hx⟩ : X)
    rw [hidx] at this
    exact this

theorem zpow_eq_one_or_self' {b : Γ} (hb2 : b * b = 1) (k : ℤ) : b ^ k = 1 ∨ b ^ k = b := by
  have h2 : b ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hb2
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    have : k = 2 * (k / 2) := by omega
    rw [this, zpow_mul, h2, one_zpow]
  · right
    have : k = 2 * (k / 2) + 1 := by omega
    rw [this, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem inverts_of_comm_eq {O : Subgroup Γ} {b : Γ} (hb2 : b * b = 1)
    (hO : ∀ a ∈ O, ∀ c ∈ O, a * c = c * a) (hN : b ∈ Subgroup.normalizer (O : Set Γ))
    (h : O ≤ ⁅O, Subgroup.zpowers b⁆) : ∀ x ∈ O, b * x * b⁻¹ = x⁻¹ := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hconj : ∀ x ∈ O, b * x * b⁻¹ ∈ O := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have key : ∀ x ∈ ⁅O, Subgroup.zpowers b⁆, x ∈ O ∧ b * x * b⁻¹ = x⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨o, ho, g, hg, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      rcases zpow_eq_one_or_self' hb2 k with hk | hk
      · rw [hk, commutatorElement_def]
        refine ⟨by simp, by simp⟩
      · rw [hk, commutatorElement_def]
        have ho' : b * o⁻¹ * b⁻¹ ∈ O := hconj _ (O.inv_mem ho)
        have hmem : o * b * o⁻¹ * b⁻¹ ∈ O := by
          have : o * b * o⁻¹ * b⁻¹ = o * (b * o⁻¹ * b⁻¹) := by group
          rw [this]; exact O.mul_mem ho ho'
        refine ⟨hmem, ?_⟩
        set o' := b * o * b⁻¹ with ho'def
        have hbo' : b * o' * b⁻¹ = o := by
          rw [ho'def]
          calc b * (b * o * b⁻¹) * b⁻¹ = (b * b) * o * (b⁻¹ * b⁻¹) := by group
            _ = o := by rw [hb2, hbinv, hb2]; simp
        have hc : o * b * o⁻¹ * b⁻¹ = o * o'⁻¹ := by
          rw [ho'def]; group
        rw [hc]
        have h1 : b * (o * o'⁻¹) * b⁻¹ = o' * o⁻¹ := by
          calc b * (o * o'⁻¹) * b⁻¹ = (b * o * b⁻¹) * (b * o' * b⁻¹)⁻¹ := by group
            _ = o' * o⁻¹ := by rw [← ho'def, hbo']
        rw [h1, mul_inv_rev, inv_inv]
    | one => exact ⟨O.one_mem, by simp⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨O.mul_mem ihx.1 ihy.1, ?_⟩
      calc b * (x * y) * b⁻¹ = (b * x * b⁻¹) * (b * y * b⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [ihx.2, ihy.2]
        _ = (x * y)⁻¹ := by rw [mul_inv_rev]; exact hO _ (O.inv_mem ihx.1) _ (O.inv_mem ihy.1)
    | inv x hx ih =>
      refine ⟨O.inv_mem ih.1, ?_⟩
      calc b * x⁻¹ * b⁻¹ = (b * x * b⁻¹)⁻¹ := by group
        _ = x⁻¹⁻¹ := by rw [ih.2]
  intro x hx
  exact (key x (h hx)).2

theorem comm_eq_of_inverts [Finite Γ] {O : Subgroup Γ} {b : Γ}
    (hodd : Odd (Nat.card O)) (hN : b ∈ Subgroup.normalizer (O : Set Γ))
    (hinv : ∀ x ∈ O, b * x * b⁻¹ = x⁻¹) : O = ⁅O, Subgroup.zpowers b⁆ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨m, hm⟩ := hodd
    have hxpow : (⟨x, hx⟩ : O) ^ (Nat.card O) = 1 := pow_card_eq_one'
    have hy : x = (x ^ (m + 1)) ^ 2 := by
      have h1 : x ^ Nat.card O = 1 := congrArg Subtype.val hxpow
      rw [← pow_mul]
      have : x ^ ((m + 1) * 2) = x ^ (Nat.card O) * x := by
        rw [hm, ← pow_succ]; congr 1; ring
      rw [this, h1, one_mul]
    set y := x ^ (m + 1) with hydef
    have hyO : y ∈ O := O.pow_mem hx _
    have hc : y * b * y⁻¹ * b⁻¹ = x := by
      have e1 : b * y⁻¹ * b⁻¹ = y := by
        have := hinv y⁻¹ (O.inv_mem hyO)
        rw [this, inv_inv]
      calc y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
        _ = y * y := by rw [e1]
        _ = x := by rw [← sq]; exact hy.symm
    rw [← hc]
    exact Subgroup.commutator_mem_commutator hyO (Subgroup.mem_zpowers b)
  · rw [Subgroup.commutator_le]
    intro o ho g hg
    have hgN : g ∈ Subgroup.normalizer (O : Set Γ) :=
      (Subgroup.zpowers_le).mpr hN hg
    have h1 : g * o⁻¹ * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hgN o⁻¹).mp (O.inv_mem ho)
    rw [commutatorElement_def]
    have : o * g * o⁻¹ * g⁻¹ = o * (g * o⁻¹ * g⁻¹) := by group
    rw [this]
    exact O.mul_mem ho h1

theorem eq_of_inverts {O T X : Subgroup Γ} (hT : IsPGroup 2 T) (hTX : T ≤ X)
    (hodd : Odd (Nat.card O))
    (hSC : ∀ x ∈ X, (∀ n ∈ O, x * n = n * x) → x ∈ O)
    {b₁ b₂ : Γ} (h1 : b₁ ∈ T) (h2 : b₂ ∈ T) (hb₂ : b₂ * b₂ = 1)
    (hi₁ : ∀ x ∈ O, b₁ * x * b₁⁻¹ = x⁻¹) (hi₂ : ∀ x ∈ O, b₂ * x * b₂⁻¹ = x⁻¹) : b₁ = b₂ := by
  have hb₂inv : b₂⁻¹ = b₂ := inv_eq_of_mul_eq_one_right hb₂
  have hcX : b₁ * b₂ ∈ X := X.mul_mem (hTX h1) (hTX h2)
  have hcomm : ∀ n ∈ O, (b₁ * b₂) * n = n * (b₁ * b₂) := by
    intro n hn
    have e2 := hi₂ n hn
    have e1 := hi₁ n⁻¹ (O.inv_mem hn)
    have hnn : b₂ * n * b₂⁻¹ = n⁻¹ := e2
    calc (b₁ * b₂) * n = (b₁ * (b₂ * n * b₂⁻¹)) * b₂ := by group
      _ = (b₁ * n⁻¹) * b₂ := by rw [hnn]
      _ = (b₁ * n⁻¹ * b₁⁻¹) * (b₁ * b₂) := by group
      _ = n * (b₁ * b₂) := by rw [e1, inv_inv]
  have hcO : b₁ * b₂ ∈ O := hSC _ hcX hcomm
  have hcT : b₁ * b₂ ∈ T := T.mul_mem h1 h2
  have hord : orderOf (b₁ * b₂) = 1 := by
    have hdvd : orderOf (b₁ * b₂) ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨b₁ * b₂, hcO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨k, hk⟩ := (hT ⟨b₁ * b₂, hcT⟩)
    have hk' : orderOf (b₁ * b₂) ∣ 2 ^ k := by
      have : orderOf (⟨b₁ * b₂, hcT⟩ : T) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (orderOf (b₁ * b₂)) 2 := by
      rcases hodd with ⟨m, hm⟩
      have : Odd (orderOf (b₁ * b₂)) := Odd.of_dvd_nat ⟨m, hm⟩ hdvd
      exact Nat.coprime_two_right.mpr this
    exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hk'
  have h1' : b₁ * b₂ = 1 := orderOf_eq_one_iff.mp hord
  calc b₁ = b₁ * b₂ * b₂⁻¹ := by group
    _ = b₂ := by rw [h1', one_mul, hb₂inv]

structure ShapeConcl (X Tb : Subgroup Γ) (Bs : Set (Subgroup Γ)) : Prop where
  isB0 : ∀ B ∈ Bs, oddCoreIn X = ⁅oddCoreIn X, B⁆
  uniq : ∀ B₁ B₂ : Subgroup Γ, B₁ ≤ Tb → B₂ ≤ Tb → Nat.card B₁ = 2 → Nat.card B₂ = 2 →
    oddCoreIn X = ⁅oddCoreIn X, B₁⁆ → oddCoreIn X = ⁅oddCoreIn X, B₂⁆ → B₁ = B₂

theorem shapeConcl_of_oddCore [Finite Γ] {X Tb : Subgroup Γ} (hTb : IsSylowTwoOf Tb X)
    {N : Subgroup Γ} (hN : oddCoreIn X = N) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hSC : ∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → x ∈ N) (Bs : Set (Subgroup Γ))
    (hBs : ∀ B ∈ Bs, B ≤ Tb ∧ Nat.card B = 2 ∧
      ∀ b ∈ B, b ≠ 1 → ∀ n ∈ N, b * n * b⁻¹ = n⁻¹) : ShapeConcl X Tb Bs := by
  have hodd : Odd (Nat.card N) := hN ▸ odd_card_oddCoreIn X
  have hnorm : ∀ b ∈ X, b ∈ Subgroup.normalizer (N : Set Γ) := fun b hb => by
    have := le_normalizer_oddCoreIn X hb
    rwa [hN] at this
  refine ⟨fun B hB => ?_, fun B₁ B₂ hB₁ hB₂ c₁ c₂ h₁ h₂ => ?_⟩
  · obtain ⟨hBT, hBc, hBinv⟩ := hBs B hB
    obtain ⟨b, hb1, hb2, hBeq⟩ := exists_zpowers_eq_of_card_two hBc
    have hbB : b ∈ B := by rw [hBeq]; exact Subgroup.mem_zpowers b
    rw [hN, hBeq]
    exact comm_eq_of_inverts hodd (hnorm b (hTb.1 (hBT hbB))) (hBinv b hbB hb1)
  · obtain ⟨b₁, hb₁1, hb₁2, hB₁eq⟩ := exists_zpowers_eq_of_card_two c₁
    obtain ⟨b₂, hb₂1, hb₂2, hB₂eq⟩ := exists_zpowers_eq_of_card_two c₂
    have hb₁B : b₁ ∈ B₁ := by rw [hB₁eq]; exact Subgroup.mem_zpowers b₁
    have hb₂B : b₂ ∈ B₂ := by rw [hB₂eq]; exact Subgroup.mem_zpowers b₂
    have hi₁ : ∀ x ∈ N, b₁ * x * b₁⁻¹ = x⁻¹ := by
      refine inverts_of_comm_eq hb₁2 hcomm (hnorm b₁ (hTb.1 (hB₁ hb₁B))) ?_
      rw [hN] at h₁
      rw [hB₁eq] at h₁
      exact h₁.le
    have hi₂ : ∀ x ∈ N, b₂ * x * b₂⁻¹ = x⁻¹ := by
      refine inverts_of_comm_eq hb₂2 hcomm (hnorm b₂ (hTb.1 (hB₂ hb₂B))) ?_
      rw [hN] at h₂
      rw [hB₂eq] at h₂
      exact h₂.le
    have := eq_of_inverts hTb.2.1 hTb.1 hodd hSC (hB₁ hb₁B) (hB₂ hb₂B) hb₂2 hi₁ hi₂
    rw [hB₁eq, hB₂eq, this]

theorem shapeConcl_of_dihedralLike [Finite Γ] {X Tb : Subgroup Γ} (hTb : IsSylowTwoOf Tb X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hX : Nat.card X = 2 * p)
    (hnc : ∃ a ∈ X, ∃ b ∈ X, a * b ≠ b * a) (Bs : Set (Subgroup Γ))
    (hBs : ∀ B ∈ Bs, B ≤ Tb ∧ Nat.card B = 2) : ShapeConcl X Tb Bs := by
  obtain ⟨N, hNX, hnorm, hcard, hC, hpow⟩ := exists_normal_prime_of_card_two_mul hp hX hnc
  obtain ⟨hON, hcomm, hinv⟩ := prime_normal_facts hp hp2 hNX hnorm hcard hC
    (fun x hx => ⟨1, by simpa using hpow x hx⟩)
  refine shapeConcl_of_oddCore hTb hON hcomm hC Bs fun B hB => ?_
  obtain ⟨hBT, hBc⟩ := hBs B hB
  refine ⟨hBT, hBc, fun b hbB hb1 n hn => ?_⟩
  have hb2 : b ^ 2 = 1 := by
    have hpow' : (⟨b, hbB⟩ : B) ^ (Nat.card B) = 1 := pow_card_eq_one'
    rw [hBc] at hpow'
    exact congrArg Subtype.val hpow'
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hb2)
  have := hinv b (hTb.1 (hBT hbB)) hb2 hb1 n hn
  rw [hbinv] at this ⊢
  exact this

end S152N2

end CFSG.Quasithin
