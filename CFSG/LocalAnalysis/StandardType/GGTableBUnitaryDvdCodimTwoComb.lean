module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndDvdComb

public section

namespace CFSG.StandardType.TableBUDT

open CFSG.StandardType.TypeA

variable {d p : ℕ} {K : Type} [Field K]

@[expose] def HasNode (Y : Subgroup (Fin d → Kˣ)) : Prop :=
  ∃ y ∈ Y, y ≠ 1 ∧ ∃ T : Finset (Fin d), T.Nonempty ∧ T.card ≤ 2 ∧
    (∀ i ∈ T, ∀ j, j ≠ i → y j ≠ y i) ∧ (∀ k l, k ∉ T → l ∉ T → y k = y l) ∧
    ∀ y' ∈ Y, (∀ k l, k ∉ T → l ∉ T → y' k = y' l) → y' ∈ Subgroup.zpowers y

variable [Finite K] {Y : Subgroup (Fin d → Kˣ)}

theorem card_four {i j l k₀ : Fin d} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hik : i ≠ k₀)
    (hjk : j ≠ k₀) (hlk : l ≠ k₀) : ({i, j, l, k₀} : Finset (Fin d)).card = 4 := by
  classical
  rw [Finset.card_insert_of_notMem (by simp [hij, hil, hik]),
    Finset.card_insert_of_notMem (by simp [hjl, hjk]),
    Finset.card_insert_of_notMem (by simp [hlk]), Finset.card_singleton]

theorem exists_triple_elem (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {k₀ : Fin d}
    (hY0 : ∀ y ∈ Y, y k₀ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K)
    (hcard : p ^ (d - 3) ≤ Nat.card Y) {i j l : Fin d} (hij : i ≠ j) (hil : i ≠ l)
    (hjl : j ≠ l) (hik : i ≠ k₀) (hjk : j ≠ k₀) (hlk : l ≠ k₀) :
    ∃ u ∈ Y, u ≠ 1 ∧ ∀ k, k ≠ i → k ≠ j → k ≠ l → u k = 1 := by
  classical
  set S : Finset (Fin d) := ({i, j, l, k₀} : Finset (Fin d))ᶜ with hS
  have hS4 := card_four hij hil hjl hik hjk hlk
  have hd4 : 4 ≤ d := by
    have := Finset.card_le_univ ({i, j, l, k₀} : Finset (Fin d))
    rw [hS4, Fintype.card_fin] at this
    exact this
  have hScard : S.card = d - 4 := by
    rw [hS, Finset.card_compl, hS4, Fintype.card_fin]
  let f : Y →* (S → rootsOfUnity p K) :=
    { toFun := fun y k => ⟨(y : Fin d → Kˣ) k, hYp _ y.2 k⟩
      map_one' := by
        funext k
        rfl
      map_mul' := fun y y' => by
        funext k
        rfl }
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ≤ p ^ (d - 4) := by
    calc Nat.card f.range ≤ Nat.card (S → rootsOfUnity p K) := Subgroup.card_le_card_group _
      _ = p ^ (d - 4) := by
        rw [Nat.card_fun, card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_fintype_card,
          Fintype.card_coe, hScard]
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at h1
    have h3 : p ^ (d - 3) ≤ p ^ (d - 4) := hcard.trans (h1 ▸ h2)
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  refine ⟨u, u.2, fun h => hu1 (Subtype.ext (Subtype.ext h)), fun k hki hkj hkl => ?_⟩
  by_cases hkk : k = k₀
  · rw [hkk]
    exact hY0 _ u.2
  · have hkS : k ∈ S := by simp [hS, hki, hkj, hkl, hkk]
    have := congrArg (fun g : S → rootsOfUnity p K => ((g ⟨k, hkS⟩ : rootsOfUnity p K) : Kˣ))
      (MonoidHom.mem_ker.mp hu)
    simpa [f] using this

theorem hasNode_of_pair (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {k₀ : Fin d}
    (hY0 : ∀ y ∈ Y, y k₀ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K) {i j : Fin d}
    (hij : i ≠ j) (hik : i ≠ k₀) (hjk : j ≠ k₀) {u : Fin d → Kˣ} (huY : u ∈ Y) (hu1 : u ≠ 1)
    (hus : ∀ k, k ≠ i → k ≠ j → u k = 1) (huij : u i ≠ u j) : HasNode Y := by
  classical
  by_cases hA : ∃ m : Fin d, ∃ y ∈ Y, y ≠ 1 ∧ ∀ k l, k ≠ m → l ≠ m → y k = y l
  · obtain ⟨m, y, hyY, hy1, hyc⟩ := hA
    obtain ⟨m', hm'⟩ : ∃ m' : Fin d, m' ≠ m := by
      by_cases h : m = i
      · exact ⟨j, by rw [h]; exact Ne.symm hij⟩
      · exact ⟨i, Ne.symm h⟩
    obtain ⟨h1, h2⟩ := node_of_single hp hpK hY0 hYp hm' hyY hy1 hyc
    refine ⟨y, hyY, hy1, {m}, Finset.singleton_nonempty m, by simp, ?_, ?_, ?_⟩
    · intro i' hi' j' hj'
      rw [Finset.mem_singleton] at hi'
      subst hi'
      exact h1 j' hj'
    · intro k l hk hl
      exact hyc k l (by simpa using hk) (by simpa using hl)
    · intro y' hy' hc'
      exact h2 y' hy' fun k l hk hl => hc' k l (by simpa using hk) (by simpa using hl)
  · have hB : ∀ (m : Fin d), ∀ y ∈ Y, (∀ k l, k ≠ m → l ≠ m → y k = y l) → y = 1 := by
      intro m y hy hc
      by_contra h1
      exact hA ⟨m, y, hy, h1, hc⟩
    obtain ⟨hui, huj, hpow⟩ := pair_props hp hpK hY0 hYp hB hik hjk huY hu1 hus
    refine ⟨u, huY, hu1, {i, j}, Finset.insert_nonempty _ _, Finset.card_le_two, ?_, ?_, ?_⟩
    · intro i' hi' j' hj'
      rw [Finset.mem_insert, Finset.mem_singleton] at hi'
      rcases hi' with rfl | rfl
      · by_cases hj'j : j' = j
        · rw [hj'j]
          exact Ne.symm huij
        · rw [hus j' hj' hj'j]
          exact Ne.symm hui
      · by_cases hj'i : j' = i
        · rw [hj'i]
          exact huij
        · rw [hus j' hj'i hj']
          exact Ne.symm huj
    · intro k l hk hl
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
      rw [hus k hk.1 hk.2, hus l hl.1 hl.2]
    · intro y' hy' hc'
      exact hpow y' hy' fun k l hki hkj hli hlj =>
        hc' k l (by simp [hki, hkj]) (by simp [hli, hlj])

theorem exists_three_ne (hd : 5 ≤ d) {s t : Fin d} (hst : s ≠ t) :
    ∃ a b c : Fin d, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a ≠ s ∧ a ≠ t ∧ b ≠ s ∧ b ≠ t ∧ c ≠ s ∧ c ≠ t := by
  classical
  have hc : 2 < (({s, t} : Finset (Fin d))ᶜ).card := by
    rw [Finset.card_compl, Finset.card_pair_eq_two_iff.mpr hst, Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc'
  exact ⟨a, b, c, hab, hac, hbc, ha.1, ha.2, hb.1, hb.2, hc'.1, hc'.2⟩

theorem hasNode_of_eq (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    {s t : Fin d} (hst : s ≠ t) (hYs : ∀ y ∈ Y, y s = 1) (hYt : ∀ y ∈ Y, y t = 1)
    (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K) (hcard : p ^ (d - 3) ≤ Nat.card Y) :
    HasNode Y := by
  classical
  by_cases hA : ∃ m : Fin d, ∃ y ∈ Y, y ≠ 1 ∧ ∀ k l, k ≠ m → l ≠ m → y k = y l
  · obtain ⟨m, y, hyY, hy1, hyc⟩ := hA
    obtain ⟨m', hm'⟩ : ∃ m' : Fin d, m' ≠ m := by
      by_cases h : m = s
      · exact ⟨t, by rw [h]; exact Ne.symm hst⟩
      · exact ⟨s, Ne.symm h⟩
    obtain ⟨h1, h2⟩ := node_of_single hp hpK hYs hYp hm' hyY hy1 hyc
    refine ⟨y, hyY, hy1, {m}, Finset.singleton_nonempty m, by simp, ?_, ?_, ?_⟩
    · intro i' hi' j' hj'
      rw [Finset.mem_singleton] at hi'
      subst hi'
      exact h1 j' hj'
    · intro k l hk hl
      exact hyc k l (by simpa using hk) (by simpa using hl)
    · intro y' hy' hc'
      exact h2 y' hy' fun k l hk hl => hc' k l (by simpa using hk) (by simpa using hl)
  have hB : ∀ (m : Fin d), ∀ y ∈ Y, (∀ k l, k ≠ m → l ≠ m → y k = y l) → y = 1 := by
    intro m y hy hc
    by_contra h1
    exact hA ⟨m, y, hy, h1, hc⟩
  have hpair : ∀ a b : Fin d, a ≠ b → a ≠ s → b ≠ s → a ≠ t → b ≠ t →
      ∃ u ∈ Y, u ≠ 1 ∧ ∀ k, k ≠ a → k ≠ b → u k = 1 := by
    intro a b hab has hbs hat hbt
    obtain ⟨u, huY, hu1, hu⟩ :=
      exists_triple_elem hp hpK hYs hYp hcard hab hat hbt has hbs (Ne.symm hst)
    refine ⟨u, huY, hu1, fun k hka hkb => ?_⟩
    by_cases hkt : k = t
    · rw [hkt]
      exact hYt u huY
    · exact hu k hka hkb hkt
  obtain ⟨i₀, i₁, i₂, h01, h02, h12, h0k, h0t, h1k, h1t, h2k, h2t⟩ := exists_three_ne hd hst
  obtain ⟨u01, hu01Y, hu01, hu01s⟩ := hpair i₀ i₁ h01 h0k h1k h0t h1t
  obtain ⟨u02, hu02Y, hu02, hu02s⟩ := hpair i₀ i₂ h02 h0k h2k h0t h2t
  obtain ⟨u12, hu12Y, hu12, hu12s⟩ := hpair i₁ i₂ h12 h1k h2k h1t h2t
  by_cases g01 : u01 i₀ ≠ u01 i₁
  · exact hasNode_of_pair hp hpK hYs hYp h01 h0k h1k hu01Y hu01 hu01s g01
  by_cases g02 : u02 i₀ ≠ u02 i₂
  · exact hasNode_of_pair hp hpK hYs hYp h02 h0k h2k hu02Y hu02 hu02s g02
  by_cases g12 : u12 i₁ ≠ u12 i₂
  · exact hasNode_of_pair hp hpK hYs hYp h12 h1k h2k hu12Y hu12 hu12s g12
  exfalso
  rw [not_not] at g01 g02 g12
  obtain ⟨hx1, -, -⟩ := pair_props hp hpK hYs hYp hB h0k h1k hu01Y hu01 hu01s
  obtain ⟨hy1, -, -⟩ := pair_props hp hpK hYs hYp hB h0k h2k hu02Y hu02 hu02s
  obtain ⟨hz1, -, -⟩ := pair_props hp hpK hYs hYp hB h1k h2k hu12Y hu12 hu12s
  have := Fact.mk hp
  set R := rootsOfUnity p K with hR
  have hRcard : Nat.card R = p := card_rootsOfUnity_of_dvd hp hpK
  set x : R := ⟨u01 i₀, hYp _ hu01Y i₀⟩ with hx
  set yv : R := ⟨u02 i₀, hYp _ hu02Y i₀⟩ with hyv
  set z : R := ⟨u12 i₁, hYp _ hu12Y i₁⟩ with hz
  have hx1' : x ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hy1' : yv ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := mem_powers_of_prime_card hRcard hx1' (g' := z⁻¹)
  obtain ⟨b, hb⟩ := mem_powers_of_prime_card hRcard hy1' (g' := z⁻¹)
  have ha' : u01 i₀ ^ a = (u12 i₁)⁻¹ := congrArg Subtype.val ha
  have hb' : u02 i₀ ^ b = (u12 i₁)⁻¹ := congrArg Subtype.val hb
  set w := u01 ^ a * u02 ^ b * u12 with hw
  have hwY : w ∈ Y := Y.mul_mem (Y.mul_mem (Y.pow_mem hu01Y a) (Y.pow_mem hu02Y b)) hu12Y
  have hwk : ∀ k, k ≠ i₀ → w k = 1 := by
    intro k hk
    show u01 k ^ a * u02 k ^ b * u12 k = 1
    by_cases hk1 : k = i₁
    · rw [hk1, ← g01, ha', hu02s i₁ (Ne.symm h01) h12, one_pow, mul_one, inv_mul_cancel]
    · by_cases hk2 : k = i₂
      · rw [hk2, hu01s i₂ (Ne.symm h02) (Ne.symm h12), one_pow, one_mul, ← g02, hb', ← g12,
          inv_mul_cancel]
      · rw [hu01s k hk hk1, hu02s k hk hk2, hu12s k hk1 hk2, one_pow, one_pow, one_mul,
          one_mul]
  have hw1 : w = 1 := hB i₀ w hwY fun k l hk hl => by rw [hwk k hk, hwk l hl]
  have hw0 : w i₀ = (u12 i₁)⁻¹ * (u12 i₁)⁻¹ := by
    show u01 i₀ ^ a * u02 i₀ ^ b * u12 i₀ = _
    rw [ha', hb', hu12s i₀ h01 h02, mul_one]
  rw [hw1] at hw0
  have hzz : (u12 i₁) ^ 2 = 1 := by
    have h3 : (1 : Kˣ) = (u12 i₁)⁻¹ * (u12 i₁)⁻¹ := hw0
    rw [sq]
    calc u12 i₁ * u12 i₁ = ((u12 i₁)⁻¹ * (u12 i₁)⁻¹)⁻¹ := by rw [← mul_inv_rev, inv_inv]
      _ = 1 := by rw [← h3, inv_one]
  have hzp : (u12 i₁) ^ p = 1 := (mem_rootsOfUnity _ _).mp (hYp _ hu12Y i₁)
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  exact hz1 ((pow_eq_one_iff_of_coprime hcop).mp ⟨hzz, hzp⟩)

theorem exists_ne_of_five (hd : 6 ≤ d) (a b c e f : Fin d) :
    ∃ x : Fin d, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ e ∧ x ≠ f := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {a, b, c, e, f} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have := h x
    tauto
  have := (Finset.card_le_card hsub).trans Finset.card_le_five
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

theorem exists_ne_of_six (hd : 7 ≤ d) (a b c e f g : Fin d) :
    ∃ x : Fin d, x ≠ a ∧ x ≠ b ∧ x ≠ c ∧ x ≠ e ∧ x ≠ f ∧ x ≠ g := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin d)) ⊆ {a, b, c, e, f, g} := by
    intro x _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have := h x
    tauto
  have := (Finset.card_le_card hsub).trans Finset.card_le_six
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

omit [Finite K] in
theorem eq_one_of_sq_eq_one (hp : p.Prime) (hp2 : p ≠ 2) {x : Kˣ} (hx : x ∈ rootsOfUnity p K)
    (h2 : x ^ 2 = 1) : x = 1 := by
  have hxp : x ^ p = 1 := (mem_rootsOfUnity _ _).mp hx
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h2, hxp⟩

theorem outer_comb (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 6 ≤ d)
    {k₀ : Fin d} (hY0 : ∀ y ∈ Y, y k₀ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K)
    (hcard : p ^ (d - 3) ≤ Nat.card Y) (hdist : ∀ i j : Fin d, i ≠ j → ∃ y ∈ Y, y i ≠ y j)
    {σ : Fin d → Fin d} (hσ : ∀ y ∈ Y, ∃ z : Kˣ, ∀ i, y (σ i) * y i = z) :
    d = 6 ∧ HasNode Y := by
  classical
  have hσσ : ∀ i, σ (σ i) = i := by
    intro i
    by_contra hne
    obtain ⟨y, hyY, hy⟩ := hdist _ _ hne
    obtain ⟨z, hz⟩ := hσ y hyY
    have e : y (σ (σ i)) * y (σ i) = y i * y (σ i) := by rw [hz (σ i), mul_comm, hz i]
    exact hy (mul_right_cancel e)
  have hsupp : ∀ y ∈ Y, ∀ z : Kˣ, (∀ i, y (σ i) * y i = z) → ∀ i, y i ≠ 1 → z = 1 →
      y (σ i) ≠ 1 ∧ σ i ≠ i := by
    intro y hyY z hz i hi hz1
    have h1 : y (σ i) = (y i)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [hz i, hz1])
    refine ⟨by rw [h1]; exact inv_ne_one.mpr hi, fun he => hi ?_⟩
    refine eq_one_of_sq_eq_one hp hp2 (hYp y hyY i) ?_
    rw [sq]
    have h2 := hz i
    rw [he, hz1] at h2
    exact h2
  have hd6 : d = 6 := by
    by_contra hd6
    have hd7 : 7 ≤ d := by omega
    obtain ⟨i₁, h1k, -, -, -, -⟩ := exists_ne_of_five hd k₀ k₀ k₀ k₀ k₀
    obtain ⟨i₂, h2k, h21, h2σ, -, -⟩ := exists_ne_of_five hd k₀ i₁ (σ i₁) k₀ k₀
    obtain ⟨i₃, h3k, h31, h3σ1, h32, h3σ2⟩ := exists_ne_of_five hd k₀ i₁ (σ i₁) i₂ (σ i₂)
    obtain ⟨y, hyY, hy1, hys⟩ :=
      exists_triple_elem hp hpK hY0 hYp hcard (Ne.symm h21) (Ne.symm h31) (Ne.symm h32) h1k h2k
        h3k
    obtain ⟨z, hz⟩ := hσ y hyY
    obtain ⟨a, ha1, ha2, ha3, haσ1, haσ2, haσ3⟩ :=
      exists_ne_of_six hd7 i₁ i₂ i₃ (σ i₁) (σ i₂) (σ i₃)
    have hσa : ∀ b, σ a = σ b → a = b := fun b h => by rw [← hσσ a, h, hσσ b]
    have hz1 : z = 1 := by
      rw [← hz a, hys a ha1 ha2 ha3,
        hys (σ a) (fun h => haσ1 (hσa _ (by rw [h, hσσ])))
          (fun h => haσ2 (hσa _ (by rw [h, hσσ]))) (fun h => haσ3 (hσa _ (by rw [h, hσσ]))),
        mul_one]
    have hex : ∃ i, (i = i₁ ∨ i = i₂ ∨ i = i₃) ∧ y i ≠ 1 := by
      by_contra hne
      push Not at hne
      apply hy1
      funext k
      by_cases hk1 : k = i₁
      · rw [hk1]; exact hne i₁ (Or.inl rfl)
      by_cases hk2 : k = i₂
      · rw [hk2]; exact hne i₂ (Or.inr (Or.inl rfl))
      by_cases hk3 : k = i₃
      · rw [hk3]; exact hne i₃ (Or.inr (Or.inr rfl))
      exact hys k hk1 hk2 hk3
    obtain ⟨i, hiI, hi1⟩ := hex
    obtain ⟨hσi1, hσii⟩ := hsupp y hyY z hz i hi1 hz1
    have hσiI : σ i = i₁ ∨ σ i = i₂ ∨ σ i = i₃ := by
      by_contra hne
      push Not at hne
      exact hσi1 (hys _ hne.1 hne.2.1 hne.2.2)
    rcases hiI with rfl | rfl | rfl
    · rcases hσiI with h | h | h
      · exact hσii h
      · exact h2σ h.symm
      · exact h3σ1 h.symm
    · rcases hσiI with h | h | h
      · exact h2σ (by rw [← h, hσσ])
      · exact hσii h
      · exact h3σ2 h.symm
    · rcases hσiI with h | h | h
      · exact h3σ1 (by rw [← h, hσσ])
      · exact h3σ2 (by rw [← h, hσσ])
      · exact hσii h
  refine ⟨hd6, ?_⟩
  have hfix : ∀ a b, σ a = a → σ b = b → a = b := by
    intro a b ha hb
    by_contra hab
    obtain ⟨y, hyY, hy⟩ := hdist a b hab
    obtain ⟨z, hz⟩ := hσ y hyY
    apply hy
    have e : (y a * (y b)⁻¹) ^ 2 = 1 := by
      have h1 := hz a
      have h2 := hz b
      rw [ha] at h1
      rw [hb] at h2
      rw [mul_pow, inv_pow, sq, sq, h1, h2, mul_inv_cancel]
    have hm : y a * (y b)⁻¹ ∈ rootsOfUnity p K :=
      Subgroup.mul_mem _ (hYp y hyY a) (Subgroup.inv_mem _ (hYp y hyY b))
    exact mul_inv_eq_one.mp (eq_one_of_sq_eq_one hp hp2 hm e)
  have hmove : ∀ x x' : Fin d, x ≠ x' → ∃ w, (w = x ∨ w = x') ∧ σ w ≠ w := by
    intro x x' hxx'
    by_cases hx : σ x = x
    · exact ⟨x', Or.inr rfl, fun hx' => hxx' (hfix x x' hx hx')⟩
    · exact ⟨x, Or.inl rfl, hx⟩
  obtain ⟨x₁, hx1k, hx1σ, -, -, -⟩ := exists_ne_of_five hd k₀ (σ k₀) k₀ k₀ k₀
  obtain ⟨x₂, hx2k, hx2σ, hx21, -, -⟩ := exists_ne_of_five hd k₀ (σ k₀) x₁ k₀ k₀
  obtain ⟨i, hiw, hσi⟩ := hmove x₂ x₁ hx21
  have hik : i ≠ k₀ := by rcases hiw with rfl | rfl <;> assumption
  have hiσk : i ≠ σ k₀ := by rcases hiw with rfl | rfl <;> assumption
  obtain ⟨x₃, hx3k, hx3σ, hx3i, hx3σi, -⟩ := exists_ne_of_five hd k₀ (σ k₀) i (σ i) k₀
  obtain ⟨x₄, hx4k, hx4σ, hx4i, hx4σi, hx43⟩ := exists_ne_of_five hd k₀ (σ k₀) i (σ i) x₃
  obtain ⟨j, hjw, hσj⟩ := hmove x₄ x₃ hx43
  have hjk : j ≠ k₀ := by rcases hjw with rfl | rfl <;> assumption
  have hjσk : j ≠ σ k₀ := by rcases hjw with rfl | rfl <;> assumption
  have hji : j ≠ i := by rcases hjw with rfl | rfl <;> assumption
  have hjσi : j ≠ σ i := by rcases hjw with rfl | rfl <;> assumption
  have hσik : σ i ≠ k₀ := fun h => hiσk (by rw [← h, hσσ])
  obtain ⟨y, hyY, hy1, hys⟩ :=
    exists_triple_elem hp hpK hY0 hYp hcard (Ne.symm hσi) (Ne.symm hji) (Ne.symm hjσi) hik hσik
      hjk
  obtain ⟨z, hz⟩ := hσ y hyY
  have hz1 : z = 1 := by
    rw [← hz k₀, hY0 y hyY, mul_one]
    exact hys _ (Ne.symm hiσk) (fun h => hik (by rw [← hσσ k₀, h, hσσ]))
      (Ne.symm hjσk)
  have hyj : y j = 1 := by
    have h1 : y (σ j) = 1 := hys _ (fun h => hjσi (by rw [← h, hσσ]))
      (fun h => hji (by rw [← hσσ j, h, hσσ])) hσj
    have h2 := hz j
    rw [h1, one_mul, hz1] at h2
    exact h2
  have hys' : ∀ k, k ≠ i → k ≠ σ i → y k = 1 := by
    intro k hki hkσ
    by_cases hkj : k = j
    · rw [hkj]; exact hyj
    · exact hys k hki hkσ hkj
  have hyi : y i ≠ 1 := by
    intro hyi
    apply hy1
    funext k
    by_cases hki : k = i
    · rw [hki]; exact hyi
    by_cases hkσ : k = σ i
    · have h2 := hz i
      rw [hyi, mul_one, hz1, ← hkσ] at h2
      exact h2
    exact hys' k hki hkσ
  have hne : y i ≠ y (σ i) := by
    intro he
    apply hyi
    refine eq_one_of_sq_eq_one hp hp2 (hYp y hyY i) ?_
    rw [sq]
    have h2 := hz i
    rw [← he, hz1] at h2
    exact h2
  exact hasNode_of_pair hp hpK hY0 hYp (Ne.symm hσi) hik hσik hyY hy1 hys' hne

end CFSG.StandardType.TableBUDT
