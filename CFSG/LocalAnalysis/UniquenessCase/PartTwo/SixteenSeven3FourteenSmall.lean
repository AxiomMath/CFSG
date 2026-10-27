module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s16c1614_false_of_two_summands {W : Type*} [CommGroup W] {A : Subgroup (MulAut W)}
    {x : MulAut W} (hxA : x ∈ A)
    (hne : commSub (⊤ : Subgroup W) (Subgroup.zpowers x) ≠ ⊥)
    (hreg : ∀ w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x),
      ∀ w' ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x), w ≠ 1 → w' ≠ 1 →
        ∃ g ∈ Subgroup.zpowers x, g w = w')
    {I₁ I₂ : Subgroup W} (hinf : I₁ ⊓ I₂ = ⊥)
    (h₁ : ∀ a ∈ A, ∀ u ∈ I₁, a u ∈ I₁) (h₂ : ∀ a ∈ A, ∀ u ∈ I₂, a u ∈ I₂)
    (m₁ : ∃ u ∈ I₁, x u ≠ u) (m₂ : ∃ u ∈ I₂, x u ≠ u) : False := by
  have hzA : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.2 hxA
  have key : ∀ I : Subgroup W, (∀ a ∈ A, ∀ u ∈ I, a u ∈ I) → (∃ u ∈ I, x u ≠ u) →
      ∀ w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x), w ≠ 1 → w ∈ I := by
    intro I hI hmv w hw hw1
    obtain ⟨u, hu, hxu⟩ := hmv
    have hc : x u * u⁻¹ ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x) :=
      Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, u, Subgroup.mem_top _, rfl⟩
    have hc1 : x u * u⁻¹ ≠ 1 := fun h => hxu (mul_inv_eq_one.1 h)
    have hcI : x u * u⁻¹ ∈ I := I.mul_mem (hI x hxA u hu) (I.inv_mem hu)
    obtain ⟨g, hg, hgw⟩ := hreg _ hc w hw hc1 hw1
    rw [← hgw]
    exact hI g (hzA hg) _ hcI
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x), w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hw' : w ∈ I₁ ⊓ I₂ := ⟨key I₁ h₁ m₁ w hw hw1, key I₂ h₂ m₂ w hw hw1⟩
  rw [hinf] at hw'
  exact hw1 (Subgroup.mem_bot.1 hw')

theorem s16c1614_mem_right_of_internalDirect {A : Type*} [Group A] {K L X : Subgroup A}
    (hI : IsInternalDirect K L X) {x : A} (hx : x ∈ X)
    (hcop : Nat.Coprime (Nat.card K) (orderOf x)) : x ∈ L := by
  obtain ⟨hcomm, hdisj, hsup⟩ := hI
  have hKc : K ≤ Subgroup.centralizer (L : Set A) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hnorm : K ≤ Subgroup.normalizer (L : Set A) :=
    hKc.trans (Subgroup.centralizer_le_normalizer _)
  have hxs : x ∈ (↑(K ⊔ L) : Set A) := by
    rw [hsup]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K L hnorm] at hxs
  obtain ⟨k, hk, l, hl, rfl⟩ := hxs
  have hkl : Commute l k := (Subgroup.mem_centralizer_iff.1 (hKc hk)) l hl
  have h1 : (k * l) ^ orderOf (k * l) = 1 := pow_orderOf_eq_one _
  rw [hkl.symm.mul_pow] at h1
  have h2 : k ^ orderOf (k * l) = (l ^ orderOf (k * l))⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3 : k ^ orderOf (k * l) ∈ K ⊓ L :=
    ⟨K.pow_mem hk _, by rw [h2]; exact L.inv_mem (L.pow_mem hl _)⟩
  rw [hdisj] at h3
  have h4 : k ^ orderOf (k * l) = 1 := Subgroup.mem_bot.1 h3
  have h5 : orderOf k ∣ orderOf (k * l) := orderOf_dvd_of_pow_eq_one h4
  have h6 : orderOf k ∣ Nat.card K := by
    have h := orderOf_dvd_natCard (⟨k, hk⟩ : K)
    rwa [Subgroup.orderOf_mk] at h
  have h7 : orderOf k = 1 := by
    have h := Nat.dvd_gcd h6 h5
    rw [hcop.gcd_eq_one] at h
    exact Nat.dvd_one.1 h
  have h8 : k = 1 := orderOf_eq_one_iff.1 h7
  rw [h8]
  simpa using hl

theorem s16c1614_le_right_of_centralizes {A : Type*} [Group A] {K L X N : Subgroup A}
    (hI : IsInternalDirect K L X) (hN : N ≤ X) (hNK : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n)
    (hZ : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1) : N ≤ L := by
  obtain ⟨hcomm, hdisj, hsup⟩ := hI
  have hKc : K ≤ Subgroup.centralizer (L : Set A) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hnorm : K ≤ Subgroup.normalizer (L : Set A) :=
    hKc.trans (Subgroup.centralizer_le_normalizer _)
  intro n hn
  have hns : n ∈ (↑(K ⊔ L) : Set A) := by
    rw [hsup]
    exact hN hn
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K L hnorm] at hns
  obtain ⟨k, hk, l, hl, rfl⟩ := hns
  have hk1 : k = 1 := by
    apply hZ k hk
    intro k' hk'
    have h1 := hNK (k * l) hn k' hk'
    have h2 : l * k' = k' * l := (Subgroup.mem_centralizer_iff.1 (hKc hk')) l hl
    have h3 : k * l * k' = k * k' * l := by rw [mul_assoc, h2, ← mul_assoc]
    have h4 : k' * (k * l) = k' * k * l := by rw [mul_assoc]
    rw [h3, h4] at h1
    exact mul_right_cancel h1
  rw [hk1]
  simpa using hl

theorem s16c1614_false_of_sumOfNat {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
    {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hinv : ∀ U Z : Subgroup W, N A U Z → ∀ a ∈ A, ∀ u ∈ U, a u ∈ U)
    (hmv : ∀ U Z : Subgroup W, N A U Z → ∀ y ∈ A, y ≠ 1 → ∃ u ∈ U, y u ≠ u)
    (hsum : SumOfNat N A (⊤ : Subgroup W) ⊥ 2) {x : MulAut W} (hxA : x ∈ A) (hx1 : x ≠ 1)
    (hne : commSub (⊤ : Subgroup W) (Subgroup.zpowers x) ≠ ⊥)
    (hreg : ∀ w ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x),
      ∀ w' ∈ commSub (⊤ : Subgroup W) (Subgroup.zpowers x), w ≠ 1 → w' ≠ 1 →
        ∃ g ∈ Subgroup.zpowers x, g w = w') : False := by
  obtain ⟨I, -, hind, -, hN⟩ := hsum
  have hinf : I 0 ⊓ I 1 = ⊥ := by
    have h01 : I 1 ≤ ⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ 0), I j :=
      le_sup_of_le_right (le_iSup₂_of_le 1 (by decide) le_rfl)
    exact le_bot_iff.1 ((inf_le_inf_left _ h01).trans (hind 0))
  exact s16c1614_false_of_two_summands hxA hne hreg hinf (hinv _ _ (hN 0)) (hinv _ _ (hN 1))
    (hmv _ _ (hN 0) x hxA hx1) (hmv _ _ (hN 1) x hxA hx1)

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_false_of_case168_2Small_cartan (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hL : L ≤ D.M) (h : Case168_2Small D ⊥ V hV L)
    {x : MulAut (Vtil ⊥ V hV)} (hx : CartanBar1614 D V hV 3 x) : False := by
  obtain ⟨hsym, ⟨L₀, hI, hS⟩, -⟩ := h
  obtain ⟨hxM, hord, hcard, hreg⟩ := hx
  have hord7 : orderOf x = 7 := by simpa using hord
  have hx1 : x ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hord7
    exact absurd hord7 (by norm_num)
  obtain ⟨e⟩ := hsym
  have hKcard : Nat.card ↥(kBar D.M ⊥ V hV L) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 3)),
      Fintype.card_perm, Fintype.card_fin]
    rfl
  have hcop : Nat.Coprime (Nat.card ↥(kBar D.M ⊥ V hV L)) (orderOf x) := by
    rw [hKcard, hord7]
    norm_num
  have hxL₀ : x ∈ L₀ := s16c1614_mem_right_of_internalDirect hI hxM hcop
  have hZ : ∀ k ∈ kBar D.M ⊥ V hV L, (∀ k' ∈ kBar D.M ⊥ V hV L, k * k' = k' * k) → k = 1 := by
    intro k hk hkc
    have hcenter : ∀ σ : Equiv.Perm (Fin 3), (∀ τ, σ * τ = τ * σ) → σ = 1 := by decide
    have hctr : ∀ τ : Equiv.Perm (Fin 3), e ⟨k, hk⟩ * τ = τ * e ⟨k, hk⟩ := by
      intro τ
      obtain ⟨k', hk'⟩ := e.surjective τ
      rw [← hk', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hkc k' k'.2)
    have h1 : e ⟨k, hk⟩ = 1 := hcenter _ hctr
    have h2 : (⟨k, hk⟩ : ↥(kBar D.M ⊥ V hV L)) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  have hLM : lBar ⊥ V hV L ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hL
  have hLL₀ : lBar ⊥ V hV L ≤ L₀ := by
    refine s16c1614_le_right_of_centralizes hI hLM ?_ hZ
    intro n hn k hk
    exact (Subgroup.mem_centralizer_iff.1 hk.2) n hn
  have hxne : commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers x) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  have hL₀card7 : ¬ 7 ∣ Nat.card ↥L₀ → False := by
    intro hnd
    apply hnd
    have h1 := orderOf_dvd_natCard (⟨x, hxL₀⟩ : ↥L₀)
    rwa [Subgroup.orderOf_mk, hord7] at h1
  rcases hS with h6 | h7 | h4 | h6
  · obtain ⟨hs6, -, -⟩ := h6
    refine hL₀card7 ?_
    rw [s16c1610_card_of_isSym hs6]
    norm_num [Nat.factorial]
  · obtain ⟨hs7, ha7, hsum⟩ := h7
    have hcard5040 : Nat.card ↥L₀ = 5040 := by
      rw [s16c1610_card_of_isSym hs7]
      rfl
    have hcard2520 : Nat.card ↥(lBar ⊥ V hV L) = 2520 := s16c167_card_isAlt_seven ha7
    have hidx : ((lBar ⊥ V hV L).subgroupOf L₀).index = 2 := by
      have h1 := Subgroup.card_mul_index ((lBar ⊥ V hV L).subgroupOf L₀)
      have h2 : Nat.card ↥((lBar ⊥ V hV L).subgroupOf L₀) = 2520 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLL₀).toEquiv, hcard2520]
      rw [h2, hcard5040] at h1
      omega
    have hy7 : (⟨x, hxL₀⟩ : ↥L₀) ^ 7 = 1 := by
      apply Subtype.ext
      have h1 : x ^ 7 = 1 := by simpa [hord7] using pow_orderOf_eq_one x
      simpa using h1
    have hy : (⟨x, hxL₀⟩ : ↥L₀) ∈ (lBar ⊥ V hV L).subgroupOf L₀ := by
      have hsq := Subgroup.sq_mem_of_index_two hidx (⟨x, hxL₀⟩ : ↥L₀)
      have h8 : (⟨x, hxL₀⟩ : ↥L₀) = ((⟨x, hxL₀⟩ : ↥L₀) ^ 2) ^ 4 := by
        calc (⟨x, hxL₀⟩ : ↥L₀) = (⟨x, hxL₀⟩ : ↥L₀) ^ 7 * ⟨x, hxL₀⟩ := by rw [hy7, one_mul]
          _ = ((⟨x, hxL₀⟩ : ↥L₀) ^ 2) ^ 4 := by rw [← pow_succ, ← pow_mul]
      rw [h8]
      exact Subgroup.pow_mem _ hsq 4
    have hxL : x ∈ lBar ⊥ V hV L := Subgroup.mem_subgroupOf.1 hy
    exact s16c1614_false_of_sumOfNat
      (N := fun H U Z => AlternatingNatural H U Z 7)
      (fun U Z hN => s16c1614_invariant_of_alternatingNatural hN)
      (fun U Z hN y hy hy1 => s16c1614_moved_of_alternatingNatural_seven hN hy hy1)
      hsum hxL hx1 hxne hreg
  · obtain ⟨hL0, hLb, hsum⟩ := h4
    have h1 : Nat.card ↥L₀ = 20160 := s16c167_card_isLn_four hL0
    have h2 : Nat.card ↥(lBar ⊥ V hV L) = 20160 := s16c167_card_isLn_four hLb
    haveI : Finite ↥L₀ := Nat.finite_of_card_ne_zero (by rw [h1]; norm_num)
    have heq : lBar ⊥ V hV L = L₀ := Subgroup.eq_of_le_of_card_ge hLL₀ (by rw [h1, h2])
    have hxL : x ∈ lBar ⊥ V hV L := by
      rw [heq]
      exact hxL₀
    exact s16c1614_false_of_sumOfNat
      (N := fun H U Z => BinaryNaturalSL H U Z 4 1)
      (fun U Z hN => s16c1614_invariant_of_binaryNaturalSL hN)
      (fun U Z hN y hy hy1 => s16c1614_moved_of_binaryNaturalSL hN hy hy1)
      hsum hxL hx1 hxne hreg
  · obtain ⟨hO, hΩ, -⟩ := h6
    refine hL₀card7 ?_
    rw [s16c1610_card_of_isOMinus_six hO hΩ]
    norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
