module

public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus

public section

namespace CFSG.StandardType.TypeA

variable {d p : ℕ} {K : Type} [Field K]

@[expose] def constSub (S : Finset (Fin d)) : Subgroup (Fin d → Kˣ) where
  carrier := {y | ∀ k ∈ S, ∀ l ∈ S, y k = y l}
  mul_mem' := by
    intro a b ha hb k hk l hl
    simp only [Pi.mul_apply]
    rw [ha k hk l hl, hb k hk l hl]
  one_mem' := fun _ _ _ _ => rfl
  inv_mem' := by
    intro a ha k hk l hl
    simp only [Pi.inv_apply]
    rw [ha k hk l hl]

theorem mem_constSub {S : Finset (Fin d)} {y : Fin d → Kˣ} :
    y ∈ constSub (K := K) S ↔ ∀ k ∈ S, ∀ l ∈ S, y k = y l :=
  Iff.rfl

theorem le_zpowers_of_card_le {G : Type*} [Group G] (hp : p.Prime) {W : Subgroup G}
    [Finite W] (hW : Nat.card W ≤ p) {y : G} (hyW : y ∈ W) (hy1 : y ≠ 1) (hyp : y ^ p = 1) :
    W ≤ Subgroup.zpowers y := by
  have := Fact.mk hp
  have h1 : Subgroup.zpowers y ≤ W := Subgroup.zpowers_le.mpr hyW
  have h2 : Nat.card (Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
  exact (Subgroup.eq_of_le_of_card_ge h1 (h2 ▸ hW)).ge

theorem card_le_of_injective_roots [Finite K] (hp : p.Prime) (hpK : p ∣ Nat.card K - 1)
    {W : Subgroup (Fin d → Kˣ)} (f : W → rootsOfUnity p K) (hf : Function.Injective f) :
    Nat.card W ≤ p :=
  (card_rootsOfUnity_of_dvd hp hpK) ▸ Nat.card_le_card_of_injective f hf

theorem pow_eq_one_of_mem_roots {Y : Subgroup (Fin d → Kˣ)}
    (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K) {y : Fin d → Kˣ} (hy : y ∈ Y) : y ^ p = 1 :=
  funext fun k => by simpa [mem_rootsOfUnity] using hYp y hy k

section Node

variable [Finite K] {Y : Subgroup (Fin d → Kˣ)}

theorem node_of_single (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {k₀ : Fin d}
    (hY0 : ∀ y ∈ Y, y k₀ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K) {i m : Fin d}
    (hm : m ≠ i) {y : Fin d → Kˣ} (hyY : y ∈ Y) (hy1 : y ≠ 1)
    (hyc : ∀ k l, k ≠ i → l ≠ i → y k = y l) :
    (∀ j, j ≠ i → y j ≠ y i) ∧
      ∀ y' ∈ Y, (∀ k l, k ≠ i → l ≠ i → y' k = y' l) → y' ∈ Subgroup.zpowers y := by
  have hyi : y i ≠ y m := by
    intro h
    apply hy1
    have hall : ∀ k, y k = y m := fun k => by
      by_cases hk : k = i
      · rw [hk, h]
      · exact hyc k m hk hm
    have hm1 : y m = 1 := (hall k₀).symm.trans (hY0 y hyY)
    funext k
    rw [hall k, hm1]
    rfl
  refine ⟨fun j hj => by rw [hyc j m hj hm]; exact hyi.symm, fun y' hy' hc' => ?_⟩
  set W := Y ⊓ constSub ({i}ᶜ : Finset (Fin d)) with hW
  have hmemW : ∀ w : Fin d → Kˣ, w ∈ Y → (∀ k l, k ≠ i → l ≠ i → w k = w l) → w ∈ W :=
    fun w hw hc => ⟨hw, fun k hk l hl => hc k l (by simpa using hk) (by simpa using hl)⟩
  have hWc : ∀ w ∈ W, ∀ k l, k ≠ i → l ≠ i → w k = w l := fun w hw k l hk hl =>
    hw.2 k (by simpa using hk) l (by simpa using hl)
  have hWcard : Nat.card W ≤ p := by
    refine card_le_of_injective_roots hp hpK
      (fun w => ⟨(w : Fin d → Kˣ) i * ((w : Fin d → Kˣ) m)⁻¹,
        Subgroup.mul_mem _ (hYp _ w.2.1 i) (Subgroup.inv_mem _ (hYp _ w.2.1 m))⟩) ?_
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ hww'
    have h1 : w i * (w m)⁻¹ = w' i * (w' m)⁻¹ := congrArg Subtype.val hww'
    have hwk : ∀ k, k ≠ i → w k = w m := fun k hk => hWc w hw k m hk hm
    have hw'k : ∀ k, k ≠ i → w' k = w' m := fun k hk => hWc w' hw' k m hk hm
    have hmm : w m = w' m ∧ w i = w' i := by
      by_cases hki : k₀ = i
      · have h2 : w i = 1 := hki ▸ hY0 w hw.1
        have h3 : w' i = 1 := hki ▸ hY0 w' hw'.1
        rw [h2, h3, one_mul, one_mul, inv_inj] at h1
        exact ⟨h1, h2.trans h3.symm⟩
      · have h2 : w m = 1 := (hwk k₀ hki).symm.trans (hY0 w hw.1)
        have h3 : w' m = 1 := (hw'k k₀ hki).symm.trans (hY0 w' hw'.1)
        rw [h2, h3, inv_one, mul_one, mul_one] at h1
        exact ⟨h2.trans h3.symm, h1⟩
    apply Subtype.ext
    funext k
    show w k = w' k
    by_cases hk : k = i
    · rw [hk]
      exact hmm.2
    · rw [hwk k hk, hw'k k hk]
      exact hmm.1
  exact le_zpowers_of_card_le hp hWcard (hmemW y hyY hyc) hy1
    (pow_eq_one_of_mem_roots hYp hyY) (hmemW y' hy' hc')

theorem exists_pair_elem (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {k₀ : Fin d}
    (hY0 : ∀ y ∈ Y, y k₀ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K)
    (hcard : p ^ (d - 2) ≤ Nat.card Y) {i j : Fin d} (hij : i ≠ j) (hik : i ≠ k₀)
    (hjk : j ≠ k₀) : ∃ u ∈ Y, u ≠ 1 ∧ ∀ k, k ≠ i → k ≠ j → u k = 1 := by
  classical
  set S : Finset (Fin d) := ({i, j, k₀} : Finset (Fin d))ᶜ with hS
  have hS3 : ({i, j, k₀} : Finset (Fin d)).card = 3 :=
    Finset.card_eq_three.mpr ⟨i, j, k₀, hij, hik, hjk, rfl⟩
  have hd3 : 3 ≤ d := by
    have := Finset.card_le_univ ({i, j, k₀} : Finset (Fin d))
    rw [hS3, Fintype.card_fin] at this
    exact this
  have hScard : S.card = d - 3 := by
    rw [hS, Finset.card_compl, hS3, Fintype.card_fin]
  let f : Y →* (S → rootsOfUnity p K) :=
    { toFun := fun y k => ⟨(y : Fin d → Kˣ) k, hYp _ y.2 k⟩
      map_one' := by
        funext k
        rfl
      map_mul' := fun y y' => by
        funext k
        rfl }
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ≤ p ^ (d - 3) := by
    calc Nat.card f.range ≤ Nat.card (S → rootsOfUnity p K) := Subgroup.card_le_card_group _
      _ = p ^ (d - 3) := by
        rw [Nat.card_fun, card_rootsOfUnity_of_dvd hp hpK, Nat.card_eq_fintype_card,
          Fintype.card_coe, hScard]
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at h1
    have h3 : p ^ (d - 2) ≤ p ^ (d - 3) := hcard.trans (h1 ▸ h2)
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
    omega
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker
  refine ⟨u, u.2, fun h => hu1 (Subtype.ext (Subtype.ext h)), fun k hki hkj => ?_⟩
  by_cases hkk : k = k₀
  · rw [hkk]
    exact hY0 _ u.2
  · have hkS : k ∈ S := by simp [hS, hki, hkj, hkk]
    have := congrArg (fun g : S → rootsOfUnity p K => ((g ⟨k, hkS⟩ : rootsOfUnity p K) : Kˣ))
      (MonoidHom.mem_ker.mp hu)
    simpa [f] using this

theorem pair_props (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) {k₀ : Fin d}
    (hY0 : ∀ y ∈ Y, y k₀ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K)
    (hB : ∀ (i : Fin d), ∀ y ∈ Y, (∀ k l, k ≠ i → l ≠ i → y k = y l) → y = 1)
    {i j : Fin d} (hik : i ≠ k₀) (hjk : j ≠ k₀) {u : Fin d → Kˣ} (huY : u ∈ Y)
    (hu1 : u ≠ 1) (hu : ∀ k, k ≠ i → k ≠ j → u k = 1) :
    u i ≠ 1 ∧ u j ≠ 1 ∧
      ∀ y' ∈ Y, (∀ k l, k ≠ i → k ≠ j → l ≠ i → l ≠ j → y' k = y' l) →
        y' ∈ Subgroup.zpowers u := by
  have htriv : ∀ w ∈ Y, (∀ k, k ≠ i → k ≠ j → w k = 1) → (w i = 1 ∨ w j = 1) → w = 1 := by
    intro w hw hw1 hor
    rcases hor with h | h
    · refine hB j w hw fun k l hk hl => ?_
      have hk1 : w k = 1 := by
        by_cases hki : k = i
        · rw [hki, h]
        · exact hw1 k hki hk
      have hl1 : w l = 1 := by
        by_cases hli : l = i
        · rw [hli, h]
        · exact hw1 l hli hl
      rw [hk1, hl1]
    · refine hB i w hw fun k l hk hl => ?_
      have hk1 : w k = 1 := by
        by_cases hkj : k = j
        · rw [hkj, h]
        · exact hw1 k hk hkj
      have hl1 : w l = 1 := by
        by_cases hlj : l = j
        · rw [hlj, h]
        · exact hw1 l hl hlj
      rw [hk1, hl1]
  refine ⟨fun h => hu1 (htriv u huY hu (Or.inl h)), fun h => hu1 (htriv u huY hu (Or.inr h)),
    fun y' hy' hc' => ?_⟩
  have hconst : ∀ w ∈ Y, (∀ k l, k ≠ i → k ≠ j → l ≠ i → l ≠ j → w k = w l) →
      ∀ k, k ≠ i → k ≠ j → w k = 1 := fun w hw hc k hki hkj =>
    (hc k k₀ hki hkj hik.symm hjk.symm).trans (hY0 w hw)
  set W := Y ⊓ constSub (({i, j} : Finset (Fin d))ᶜ) with hW
  have hmemW : ∀ w ∈ Y, (∀ k l, k ≠ i → k ≠ j → l ≠ i → l ≠ j → w k = w l) → w ∈ W :=
    fun w hw hc => ⟨hw, fun k hk l hl => hc k l (by simp at hk; exact hk.1)
      (by simp at hk; exact hk.2) (by simp at hl; exact hl.1) (by simp at hl; exact hl.2)⟩
  have hWc : ∀ w ∈ W, ∀ k, k ≠ i → k ≠ j → w k = 1 := fun w hw =>
    hconst w hw.1 fun k l hki hkj hli hlj => hw.2 k (by simp [hki, hkj]) l (by simp [hli, hlj])
  have hWcard : Nat.card W ≤ p := by
    refine card_le_of_injective_roots hp hpK
      (fun w => ⟨(w : Fin d → Kˣ) i, hYp _ w.2.1 i⟩) ?_
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ hww'
    have h1 : w i = w' i := congrArg Subtype.val hww'
    have h2 : w⁻¹ * w' ∈ W := W.mul_mem (W.inv_mem hw) hw'
    have h3 : w⁻¹ * w' = 1 := by
      refine htriv _ h2.1 (hWc _ h2) (Or.inl ?_)
      show (w i)⁻¹ * w' i = 1
      rw [h1, inv_mul_cancel]
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  have huW : u ∈ W := hmemW u huY fun k l hki hkj hli hlj => by
    rw [hu k hki hkj, hu l hli hlj]
  exact le_zpowers_of_card_le hp hWcard huW hu1 (pow_eq_one_of_mem_roots hYp huY)
    (hmemW y' hy' hc')

theorem exists_node (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    (hY0 : ∀ y ∈ Y, y ⟨3, by omega⟩ = 1) (hYp : ∀ y ∈ Y, ∀ k, y k ∈ rootsOfUnity p K)
    (hcard : p ^ (d - 2) ≤ Nat.card Y) :
    ∃ y ∈ Y, y ≠ 1 ∧ ∃ T : Finset (Fin d), T.Nonempty ∧ T.card ≤ 2 ∧
      (∀ i ∈ T, ∀ j, j ≠ i → y j ≠ y i) ∧ (∀ k l, k ∉ T → l ∉ T → y k = y l) ∧
      ∀ y' ∈ Y, (∀ k l, k ∉ T → l ∉ T → y' k = y' l) → y' ∈ Subgroup.zpowers y := by
  classical
  set k₀ : Fin d := ⟨3, by omega⟩ with hk₀
  by_cases hA : ∃ i : Fin d, ∃ y ∈ Y, y ≠ 1 ∧ ∀ k l, k ≠ i → l ≠ i → y k = y l
  · obtain ⟨i, y, hyY, hy1, hyc⟩ := hA
    obtain ⟨m, hm⟩ : ∃ m : Fin d, m ≠ i := by
      by_cases h : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [h]; simp⟩
      · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
    obtain ⟨h1, h2⟩ := node_of_single hp hpK hY0 hYp hm hyY hy1 hyc
    refine ⟨y, hyY, hy1, {i}, Finset.singleton_nonempty i, by simp, ?_, ?_, ?_⟩
    · intro i' hi' j hj
      rw [Finset.mem_singleton] at hi'
      subst hi'
      exact h1 j hj
    · intro k l hk hl
      exact hyc k l (by simpa using hk) (by simpa using hl)
    · intro y' hy' hc'
      exact h2 y' hy' fun k l hk hl => hc' k l (by simpa using hk) (by simpa using hl)
  · have hB : ∀ (i : Fin d), ∀ y ∈ Y, (∀ k l, k ≠ i → l ≠ i → y k = y l) → y = 1 := by
      intro i y hy hc
      by_contra h1
      exact hA ⟨i, y, hy, h1, hc⟩
    set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
    set i₁ : Fin d := ⟨1, by omega⟩ with hi₁
    set i₂ : Fin d := ⟨2, by omega⟩ with hi₂
    have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁]
    have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂]
    have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂]
    have h0k : i₀ ≠ k₀ := by simp [hi₀, hk₀]
    have h1k : i₁ ≠ k₀ := by simp [hi₁, hk₀]
    have h2k : i₂ ≠ k₀ := by simp [hi₂, hk₀]
    obtain ⟨u01, hu01Y, hu01, hu01s⟩ := exists_pair_elem hp hpK hY0 hYp hcard h01 h0k h1k
    obtain ⟨u02, hu02Y, hu02, hu02s⟩ := exists_pair_elem hp hpK hY0 hYp hcard h02 h0k h2k
    obtain ⟨u12, hu12Y, hu12, hu12s⟩ := exists_pair_elem hp hpK hY0 hYp hcard h12 h1k h2k
    have hgood : ∀ i j : Fin d, i ≠ j → i ≠ k₀ → j ≠ k₀ → ∀ u ∈ Y, u ≠ 1 →
        (∀ k, k ≠ i → k ≠ j → u k = 1) → u i ≠ u j →
        ∃ y ∈ Y, y ≠ 1 ∧ ∃ T : Finset (Fin d), T.Nonempty ∧ T.card ≤ 2 ∧
          (∀ i ∈ T, ∀ j, j ≠ i → y j ≠ y i) ∧ (∀ k l, k ∉ T → l ∉ T → y k = y l) ∧
          ∀ y' ∈ Y, (∀ k l, k ∉ T → l ∉ T → y' k = y' l) → y' ∈ Subgroup.zpowers y := by
      intro i j hij hik hjk u huY hu1 hus huij
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
        · by_cases hj'i : j' = i'
          · exact absurd hj'i hj'
          · by_cases hj'i' : j' = i
            · rw [hj'i']
              exact huij
            · rw [hus j' hj'i' hj']
              exact Ne.symm huj
      · intro k l hk hl
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk hl
        rw [hus k hk.1 hk.2, hus l hl.1 hl.2]
      · intro y' hy' hc'
        exact hpow y' hy' fun k l hki hkj hli hlj =>
          hc' k l (by simp [hki, hkj]) (by simp [hli, hlj])
    by_cases g01 : u01 i₀ ≠ u01 i₁
    · exact hgood i₀ i₁ h01 h0k h1k u01 hu01Y hu01 hu01s g01
    by_cases g02 : u02 i₀ ≠ u02 i₂
    · exact hgood i₀ i₂ h02 h0k h2k u02 hu02Y hu02 hu02s g02
    by_cases g12 : u12 i₁ ≠ u12 i₂
    · exact hgood i₁ i₂ h12 h1k h2k u12 hu12Y hu12 hu12s g12
    exfalso
    rw [not_not] at g01 g02 g12
    obtain ⟨hx1, -, -⟩ := pair_props hp hpK hY0 hYp hB h0k h1k hu01Y hu01 hu01s
    obtain ⟨hy1, -, -⟩ := pair_props hp hpK hY0 hYp hB h0k h2k hu02Y hu02 hu02s
    obtain ⟨hz1, -, -⟩ := pair_props hp hpK hY0 hYp hB h1k h2k hu12Y hu12 hu12s
    have := Fact.mk hp
    set R := rootsOfUnity p K with hR
    have hRcard : Nat.card R = p := card_rootsOfUnity_of_dvd hp hpK
    set x : R := ⟨u01 i₀, hYp _ hu01Y i₀⟩ with hx
    set yv : R := ⟨u02 i₀, hYp _ hu02Y i₀⟩ with hyv
    set z : R := ⟨u12 i₁, hYp _ hu12Y i₁⟩ with hz
    have hx1' : x ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    have hy1' : yv ≠ 1 := fun h => hy1 (congrArg Subtype.val h)
    have hz1' : z ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
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

end Node

end CFSG.StandardType.TypeA
