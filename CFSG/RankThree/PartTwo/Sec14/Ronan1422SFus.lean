module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422STransfer
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422S

theorem fus_mem_zpowers_eq_or_inv {G : Type} [Group G] {d x : G} (hd : d ^ 3 = 1)
    (hx : x ∈ Subgroup.zpowers d) (hx1 : x ≠ 1) : x = d ∨ x = d⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h3 : d ^ (3 : ℤ) = 1 := by exact_mod_cast hd
  have hk : d ^ k = d ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, mul_one]
  rw [hk] at hx1 ⊢
  have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hr with h | h | h
  · rw [h, zpow_zero] at hx1
    exact absurd rfl hx1
  · rw [h, zpow_one]
    exact Or.inl rfl
  · rw [h]
    refine Or.inr ?_
    have h2 : d ^ (2 : ℤ) = d ^ (2 : ℕ) := by norm_cast
    rw [h2]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hd)

theorem fus_conj_pow_three_eq_one {G : Type} [Group G] {c a : G} (hc : c ^ 3 = 1) :
    (a * c * a⁻¹) ^ 3 = 1 := by
  rw [conj_pow, hc, mul_one, mul_inv_cancel]

theorem fus_conj_ne_one {G : Type} [Group G] {c g : G} (hc : c ≠ 1) : g⁻¹ * c * g ≠ 1 :=
  fun h => hc ((conj_eq_one_iff (a := g⁻¹) (b := c)).mp (by rwa [inv_inv]))

theorem fus_inv_mul_eq_of_comm {G : Type} [Group G] {c y : G} (hy : y * c = c * y) :
    y⁻¹ * c * y = c := by
  rw [mul_assoc, ← hy, inv_mul_cancel_left]

theorem fus_mem_normalizer_of_conj_mem {G : Type} [Group G] [Finite G] {c y : G}
    (h : y⁻¹ * c * y ∈ Subgroup.zpowers c) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  rw [← Subgroup.inv_mem_iff]
  apply Subgroup.mem_normalizer_fintype
  intro n hn
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have e : y⁻¹ * c ^ k * y⁻¹⁻¹ = (y⁻¹ * c * y⁻¹⁻¹) ^ k := conj_zpow.symm
  have h' : y⁻¹ * c * y⁻¹⁻¹ ∈ Subgroup.zpowers c := by
    rw [inv_inv]
    exact h
  rw [e]
  exact (Subgroup.zpowers c).zpow_mem h' k

theorem fus_card_le_of_not_dvd_index {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {A Q : Subgroup K} (hQ : IsPGroup p Q) (hA : ¬ p ∣ A.index) :
    Nat.card Q ≤ Nat.card A := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hQ
  have hdvd : Nat.card Q ∣ Nat.card A * A.index := by
    rw [Subgroup.card_mul_index]
    exact Subgroup.card_subgroup_dvd_card Q
  have hcop : Nat.Coprime (Nat.card Q) A.index := by
    rw [hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hA)
  exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right hdvd)

theorem fus_not_dvd_index_of_maximal {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    {A : Subgroup K} (hA : IsPGroup p A)
    (hmax : ∀ T : Subgroup K, IsPGroup p T → A ≤ T → T = A) : ¬ p ∣ A.index := by
  intro hdvd
  obtain ⟨T, hAT⟩ := IsPGroup.exists_le_sylow hA
  have hTA : (T : Subgroup K) = A := hmax _ T.isPGroup' hAT
  exact Sylow.not_dvd_index T (by rw [hTA]; exact hdvd)

theorem fus_card_le_of_normalizer {G : Type} [Group G] [Finite G] {c : G} {A : Subgroup G}
    (hA3 : IsPGroup 3 A) (hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hsyl : ∀ Q : Subgroup G, IsPGroup 3 Q → A ≤ Q →
      Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) → Q = A)
    {Q : Subgroup G} (hQ3 : IsPGroup 3 Q)
    (hQN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Nat.card Q ≤ Nat.card A := by
  set H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G)
  have hA' : IsPGroup 3 (A.subgroupOf H) :=
    hA3.of_equiv (Subgroup.subgroupOfEquivOfLe hAN).symm
  have hQ' : IsPGroup 3 (Q.subgroupOf H) :=
    hQ3.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hmap : (A.subgroupOf H).map H.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN]
  have hsylH : ¬ 3 ∣ (A.subgroupOf H).index := by
    apply fus_not_dvd_index_of_maximal hA'
    intro T hT hAT
    have hS : T.map H.subtype = A :=
      hsyl _ (hT.map H.subtype) (le_trans (le_of_eq hmap.symm) (Subgroup.map_mono hAT))
        (Subgroup.map_subtype_le T)
    apply Subgroup.map_injective (f := H.subtype) (fun a b hab => Subtype.ext hab)
    rw [hS, hmap]
  have hbound := fus_card_le_of_not_dvd_index hQ' hsylH
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv] at hbound
  exact hbound

theorem fus_sup_zpowers_eq {G : Type} [Group G] [Finite G] {P N : Subgroup G} {c : G}
    (hNP : N ≤ P) (hidx : Nat.card P = 3 * Nat.card N) (hcP : c ∈ P) (hcN : c ∉ N) :
    N ⊔ Subgroup.zpowers c = P := by
  have hNM : N ≤ N ⊔ Subgroup.zpowers c := le_sup_left
  have hMP : N ⊔ Subgroup.zpowers c ≤ P := sup_le hNP (Subgroup.zpowers_le.mpr hcP)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hNM
  obtain ⟨l, hl⟩ := Subgroup.card_dvd_of_le hMP
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hkl : k * l = 3 := by
    apply Nat.eq_of_mul_eq_mul_left hNpos
    rw [mul_comm (Nat.card N) 3, ← hidx, hl, hk]
    ring
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hMeq : N = N ⊔ Subgroup.zpowers c := by
      apply Subgroup.eq_of_le_of_card_ge hNM
      apply le_of_eq
      rw [hk, mul_one]
    apply hcN
    rw [hMeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hk3 : k = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro l hkl) with h | h
    · exact absurd h hk1
    · exact h
  have hl1 : l = 1 := by
    rw [hk3] at hkl
    omega
  apply Subgroup.eq_of_le_of_card_ge hMP
  rw [hl, hl1, mul_one]

theorem fus_sup_zpowers_le_centralizer {G : Type} [Group G] {N : Subgroup G} {c b : G}
    (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x) (hbN : b ∈ N) (hcb : c * b = b * c) :
    N ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer ({b} : Set G) := by
  refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
  · intro n hn
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hNc n hn b hbN
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcb

theorem exists_inverting_of_fusion {G : Type} [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnc : ∃ a b : G, a * b ≠ b * a) {A B P N : Subgroup G} {c : G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) (hcA : c ∈ A)
    (hc1 : c ≠ 1) (hBA : B ≤ A) (hcB : c ∉ B) (hAP : A ≤ P) (hP3 : IsPGroup 3 P)
    (hNP : N ≤ P) (hNn : (N.subgroupOf P).Normal) (hidx : Nat.card P = 3 * Nat.card N)
    (hcN : c ∉ N) (hBN : B ≤ N) (hNc : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x)
    (hP243 : 27 < Nat.card P)
    (hΩ : ∀ x ∈ P, x ^ 3 = 1 → x ∈ A)
    (htr : ∀ x ∈ A, x ∉ B → ∀ y ∈ A, y ∉ B →
      ∃ p ∈ N, Subgroup.zpowers (p * x * p⁻¹) = Subgroup.zpowers y)
    (hsyl : ∀ Q : Subgroup G, IsPGroup 3 Q → A ≤ Q →
      Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) → Q = A) :
    ∃ g : G, g * c * g⁻¹ = c⁻¹ := by
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hcP : c ∈ P := hAP hcA
  have hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
    intro a ha
    apply fus_mem_normalizer_of_conj_mem
    have e : a⁻¹ * c * a = c := fus_inv_mul_eq_of_comm (hAc a ha c hcA)
    rw [e]
    exact Subgroup.mem_zpowers c
  have hA3' : IsPGroup 3 A := hP3.to_le hAP
  have hbound : ∀ Q : Subgroup G, IsPGroup 3 Q →
      Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) → Nat.card Q ≤ Nat.card A :=
    fun Q hQ3 hQN => fus_card_le_of_normalizer hA3' hAN hsyl hQ3 hQN
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    have hNbot : N ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hidx
      omega
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
    exact ⟨a.1, a.2, fun h => ha (Subtype.ext h)⟩
  have hAP_ne : A ≠ P := by
    intro hAeq
    have hPA : P ≤ A := le_of_eq hAeq.symm
    have hcn_mem : c * n ∈ A := hPA (P.mul_mem hcP (hNP hnN))
    have hcnB : c * n ∉ B := by
      intro hB
      apply hcN
      have h1 : c * n ∈ N := hBN hB
      have h2 : c = (c * n) * n⁻¹ := by group
      rw [h2]
      exact N.mul_mem h1 (N.inv_mem hnN)
    obtain ⟨p, hpN, hp⟩ := htr c hcA hcB (c * n) hcn_mem hcnB
    have hpc : p * c * p⁻¹ = c := by
      rw [hAc p (hPA (hNP hpN)) c hcA, mul_inv_cancel_right]
    rw [hpc] at hp
    have hmem : c * n ∈ Subgroup.zpowers c := by
      rw [hp]
      exact Subgroup.mem_zpowers _
    have hnz : n ∈ Subgroup.zpowers c := by
      have h2 : n = c⁻¹ * (c * n) := by group
      rw [h2]
      exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c))
        hmem
    rcases fus_mem_zpowers_eq_or_inv hc3 hnz hn1 with h | h
    · apply hcN
      rw [h] at hnN
      exact hnN
    · apply hcN
      have h2 : c = n⁻¹ := by rw [h, inv_inv]
      rw [h2]
      exact N.inv_mem hnN
  have hAlt : Nat.card A < Nat.card P :=
    Subgroup.card_lt_of_lt (lt_of_le_of_ne hAP hAP_ne)
  have hno_b : ∀ b ∈ B, b ≠ 1 → ∀ g : G, g⁻¹ * c * g ≠ b := by
    intro b hbB hb1 g hgb
    have hbN : b ∈ N := hBN hbB
    have hcent : P ≤ Subgroup.centralizer ({b} : Set G) := by
      rw [← fus_sup_zpowers_eq hNP hidx hcP hcN]
      exact fus_sup_zpowers_le_centralizer hNc hbN (hAc c hcA b (hBA hbB))
    let Q : Subgroup G := P.map (MulAut.conj g).toMonoidHom
    have hQ3 : IsPGroup 3 Q := hP3.map _
    have hQcard : Nat.card Q = Nat.card P :=
      Subgroup.card_map_of_injective (fun x y hxy => (MulAut.conj g).injective hxy)
    have hQN : Q ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      rintro _ ⟨x, hxP, rfl⟩
      have hxb : x * b = b * x := Subgroup.mem_centralizer_singleton_iff.mp (hcent hxP)
      have hxb' : x * (g⁻¹ * c * g) = (g⁻¹ * c * g) * x := by
        rw [hgb]
        exact hxb
      have hcomm : g * x * g⁻¹ * c = c * (g * x * g⁻¹) := by
        calc g * x * g⁻¹ * c = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by rw [hxb']
          _ = c * (g * x * g⁻¹) := by group
      show g * x * g⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)
      apply fus_mem_normalizer_of_conj_mem
      rw [fus_inv_mul_eq_of_comm hcomm]
      exact Subgroup.mem_zpowers c
    have hbQ := hbound Q hQ3 hQN
    omega
  have hfuse : ∀ g : G, g⁻¹ * c * g ∈ P →
      ∃ p ∈ N, Subgroup.zpowers (p * c * p⁻¹) = Subgroup.zpowers (g⁻¹ * c * g) := by
    intro g hg
    have hx3 : (g⁻¹ * c * g) ^ 3 = 1 := by
      have e := fus_conj_pow_three_eq_one (a := g⁻¹) hc3
      rwa [inv_inv] at e
    have hxA : g⁻¹ * c * g ∈ A := hΩ _ hg hx3
    have hxB : g⁻¹ * c * g ∉ B := fun hB => hno_b _ hB (fus_conj_ne_one hc1) g rfl
    exact htr c hcA hcB _ hxA hxB
  have hPsyl : ¬ 3 ∣ P.index := by
    intro hdvd
    obtain ⟨T, hPT⟩ := IsPGroup.exists_le_sylow hP3
    have hPT_ne : P ≠ (T : Subgroup G) := by
      intro h
      apply Sylow.not_dvd_index T
      rw [← h]
      exact hdvd
    have hlt : P.subgroupOf (T : Subgroup G) < ⊤ := by
      refine lt_of_le_of_ne le_top ?_
      intro htop
      apply hPT_ne
      apply le_antisymm hPT
      intro t ht
      have hmem : (⟨t, ht⟩ : (T : Subgroup G)) ∈ P.subgroupOf (T : Subgroup G) := by
        rw [htop]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hmem
    haveI : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
    obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hxP : (x : G) ∉ P := fun h => hxH (Subgroup.mem_subgroupOf.mpr h)
    have hcT : c ∈ (T : Subgroup G) := hPT hcP
    have hcH : (⟨c, hcT⟩ : (T : Subgroup G)) ∈ P.subgroupOf (T : Subgroup G) :=
      Subgroup.mem_subgroupOf.mpr hcP
    have hxinv := Subgroup.inv_mem _ hxN
    have hconj0 := (Subgroup.mem_normalizer_iff.mp hxinv ⟨c, hcT⟩).mp hcH
    have hconjP : (x : G)⁻¹ * c * (x : G) ∈ P := by
      have h2 := Subgroup.mem_subgroupOf.mp hconj0
      simpa using h2
    obtain ⟨p, hpN, hp⟩ := hfuse (x : G) hconjP
    have hpP : p ∈ P := hNP hpN
    have hd3 : (p * c * p⁻¹) ^ 3 = 1 := fus_conj_pow_three_eq_one hc3
    have hxd : (x : G)⁻¹ * c * (x : G) ∈ Subgroup.zpowers (p * c * p⁻¹) := by
      rw [hp]
      exact Subgroup.mem_zpowers _
    have hyc : ((x : G) * p)⁻¹ * c * ((x : G) * p) ∈ Subgroup.zpowers c := by
      have e : ((x : G) * p)⁻¹ * c * ((x : G) * p) =
          p⁻¹ * ((x : G)⁻¹ * c * (x : G)) * p := by
        group
      rw [e]
      rcases fus_mem_zpowers_eq_or_inv hd3 hxd (fus_conj_ne_one hc1) with h | h
      · rw [h]
        have e2 : p⁻¹ * (p * c * p⁻¹) * p = c := by group
        rw [e2]
        exact Subgroup.mem_zpowers c
      · rw [h]
        have e2 : p⁻¹ * (p * c * p⁻¹)⁻¹ * p = c⁻¹ := by group
        rw [e2]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers c)
    obtain ⟨y, hy⟩ : ∃ y : G, y = (x : G) * p := ⟨_, rfl⟩
    rw [← hy] at hyc
    have hy_norm : y ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      fus_mem_normalizer_of_conj_mem hyc
    have hyT : y ∈ (T : Subgroup G) := by
      rw [hy]
      exact (T : Subgroup G).mul_mem x.2 (hPT hpP)
    have hQT : A ⊔ Subgroup.zpowers y ≤ (T : Subgroup G) :=
      sup_le (le_trans hAP hPT) (Subgroup.zpowers_le.mpr hyT)
    have hQ3 : IsPGroup 3 (↥(A ⊔ Subgroup.zpowers y)) := T.isPGroup'.to_le hQT
    have hQN : A ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      sup_le hAN (Subgroup.zpowers_le.mpr hy_norm)
    have hQeq : A ⊔ Subgroup.zpowers y = A := hsyl _ hQ3 le_sup_left hQN
    have hyA : y ∈ A := by
      have h1 : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      rw [hQeq] at h1
      exact h1
    apply hxP
    have e3 : (x : G) = y * p⁻¹ := by
      rw [hy]
      group
    rw [e3]
    exact P.mul_mem (hAP hyA) (P.inv_mem hpP)
  by_contra hno
  have hconj : ∀ g : G, g⁻¹ * c * g ∈ P → c⁻¹ * (g⁻¹ * c * g) ∈ N := by
    intro g hg
    obtain ⟨p, hpN, hp⟩ := hfuse g hg
    have hpP : p ∈ P := hNP hpN
    have hd3 : (p * c * p⁻¹) ^ 3 = 1 := fus_conj_pow_three_eq_one hc3
    have hxd : g⁻¹ * c * g ∈ Subgroup.zpowers (p * c * p⁻¹) := by
      rw [hp]
      exact Subgroup.mem_zpowers _
    rcases fus_mem_zpowers_eq_or_inv hd3 hxd (fus_conj_ne_one hc1) with h | h
    · rw [h]
      have hcp : c⁻¹ * p * c ∈ N := by
        have h2 := Subgroup.mem_subgroupOf.mp
          (hNn.conj_mem ⟨p, hpP⟩ (Subgroup.mem_subgroupOf.mpr hpN) ⟨c⁻¹, P.inv_mem hcP⟩)
        simpa using h2
      have e : c⁻¹ * (p * c * p⁻¹) = (c⁻¹ * p * c) * p⁻¹ := by group
      rw [e]
      exact N.mul_mem hcp (N.inv_mem hpN)
    · exfalso
      apply hno
      refine ⟨p⁻¹ * g⁻¹, ?_⟩
      have e : p⁻¹ * g⁻¹ * c * (p⁻¹ * g⁻¹)⁻¹ = p⁻¹ * (g⁻¹ * c * g) * p := by group
      rw [e, h]
      group
  exact false_of_conj_mem_coset hG hnc hPsyl hNP hNn hidx hcP hcN hc3 hconj

end CFSG.RankThree.PartTwo.Sec14.Ronan1422S
