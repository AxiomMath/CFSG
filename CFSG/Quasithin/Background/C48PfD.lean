module

public import CFSG.Quasithin.Background.C48PfB
public import CFSG.Quasithin.Background.C48PfFourMod
public import CFSG.Quasithin.Background.C48Asm

public section

namespace CFSG.Quasithin.C48Pf

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

private theorem card_evenWeight (m : ℕ) (hm : 0 < m) : Nat.card ↥(evenWeight m) = 2 ^ (m - 1) := by
  let f : (Fin m → ZMod 2) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i) (fun _ _ => Finset.sum_add_distrib)
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Pi.single ⟨0, hm⟩ c, ?_⟩
    simp [f]
  have hrange : f.range = ⊤ := AddMonoidHom.range_eq_top.2 hsurj
  have h1 := AddSubgroup.index_ker f
  rw [hrange] at h1
  have h2 := AddSubgroup.index_mul_card (H := f.ker)
  have hcard : Nat.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Nat.card_fun]
    simp
  have hidx : f.ker.index = 2 := by
    rw [h1]
    simp
  rw [hidx, hcard] at h2
  have hker : evenWeight m = f.ker := rfl
  rw [hker]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [pow_succ] at h2
  simp only [Nat.add_sub_cancel]
  omega

theorem card_altHeart_eight : Nat.card (AltHeart 8) = 2 ^ 6 := by
  have hsum : ∀ c : ZMod 2, ∑ _i : Fin 8, c = 0 := by decide
  have hmem : ∀ c : ZMod 2, (fun _ : Fin 8 => c) ∈ evenWeight 8 := fun c => by
    show ∑ _i : Fin 8, c = 0
    exact hsum c
  let e : ZMod 2 ≃ constWeight 8 :=
    { toFun := fun c => ⟨⟨fun _ => c, hmem c⟩, fun _ _ => rfl⟩
      invFun := fun x => (x.1 : Fin 8 → ZMod 2) 0
      left_inv := fun c => rfl
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact x.2 0 i }
  have hc : Nat.card (constWeight 8) = 2 := by
    rw [← Nat.card_congr e]
    simp
  have h1 : (constWeight 8).index * Nat.card (constWeight 8) = Nat.card ↥(evenWeight 8) :=
    AddSubgroup.index_mul_card (constWeight 8)
  rw [hc, card_evenWeight 8 (by norm_num)] at h1
  have h2 : Nat.card (AltHeart 8) = (constWeight 8).index := rfl
  rw [h2]
  omega

theorem eq_of_isPSL_two_one {m m' : ℕ} (hm : m = 3 ∨ m = 4) (hm' : m' = 3 ∨ m' = 4) {X : Type}
    [Group X] (h : IsPSL m 2 1 X) (h' : IsPSL m' 2 1 X) : m = m' := by
  have key : ∀ {n : ℕ}, (n = 3 ∨ n = 4) → IsPSL n 2 1 X →
      (n = 3 → Nat.card X = 168) ∧ (n = 4 → Nat.card X = 20160) := by
    intro n hn hX
    obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by omega : 1 ≤ n), hK]
    rcases hn with rfl | rfl
    · exact ⟨fun _ => by decide, fun h => absurd h (by norm_num)⟩
    · exact ⟨fun h => absurd h (by norm_num), fun _ => by decide⟩
  have k1 := key hm h
  have k2 := key hm' h'
  rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl
  · rfl
  · have := (k1.1 rfl).symm.trans (k2.2 rfl)
    norm_num at this
  · have := (k1.2 rfl).symm.trans (k2.1 rfl)
    norm_num at this
  · rfl

variable {G : Type} [Group G] [Finite G]

theorem c48C41FourStep_of (h22 : ASC22Three G) (h27 : ASC27Statement G) (h51 : AsB51)
    (hI16 : AsI16Cover) (hA8 : AsI16CoverA8) (hFour : FourModFact) : C48C41FourStep G := by
  intro H R M L V K h hK hchar hq hKM h41 h4
  have hL0 : L = conjClosure L M := h41.1
  have hM0K : conjClosure L M ≤ K := h41.2.1.trans h41.2.2.1.le
  obtain ⟨hVUK, hVO⟩ := le_commutator h22 h27 h hK hchar hq hKM h41 h4
  obtain ⟨hU, halt⟩ := alt15127_autOn h27 h51 hI16 hA8 h hK hchar hq hKM h41 h4
  have hred := isTwoReducedIn_U h27 h hK hchar hq hKM h41
  have hKU := le_sup_left.trans hred.2.1
  have hle := inf_centralizer_le h27 h hK hchar hq hKM h41 h4
  have hpsl := isPSL_autOn h27 h hK hchar hq hKM h41 h4
  have hP₀P : conjClosure L M ≤ M ⊓ K := le_inf (C2Nine.conjClosure_le_M h) hM0K
  have hPK : M ⊓ K ≠ K := fun hPK => hKM (by rw [← hPK]; exact inf_le_left)
  have hPN : M ⊓ K ≤ Subgroup.normalizer (conjClosure L M : Set G) :=
    inf_le_left.trans (le_normalizer_conjClosure L M)
  have hperf : ⁅conjClosure L M, conjClosure L M⁆ = conjClosure L M :=
    C2Nine.perfect_conjClosure_of_hyp h
  have hLR : conjClosure L M ≤ Subgroup.normalizer (R : Set G) := (c2_9_two h).1
  have hRV := C48.le_centralizer_V h
  have key : ∀ m : ℕ, (m = 3 ∨ m = 4) → IsPSL m 2 1 (ModO2 (conjClosure L M)) →
      (∃ k : ℕ, 1 ≤ k ∧ k ≤ 4 ∧ IsSumOfNaturalModules (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R))
          (StatedSL m (ZMod 2)) false k) ∨
        (m = 4 ∧ IsAltNaturalSection (L ⊔ R) V ⊥ (R.subgroupOf (L ⊔ R)) 8) := by
    intro m hm hpm
    rcases hFour G K _ (M ⊓ K) (conjClosure L M) V hU hKU hle hpsl halt h4.2.1 hPK hP₀P hPN
        hperf m hm hpm h.V_ne hVUK hVO h.V_comm with ⟨k, hk1, hk4, hs⟩ | ⟨h4m, ha⟩
    · rw [← C48.subgroupOf_conjClosure_eq h] at hs
      have hs' := C48.isSumOfNaturalModules_sup hs hLR hRV
      rw [← hL0] at hs'
      exact Or.inl ⟨k, hk1, hk4, hs'⟩
    · rw [← C48.subgroupOf_conjClosure_eq h] at ha
      have ha' := C48.isAltNaturalSection_sup ha hLR hRV
      rw [← hL0] at ha'
      exact Or.inr ⟨h4m, ha'⟩
  obtain ⟨m, hm, hpm⟩ : ∃ m : ℕ, (m = 3 ∨ m = 4) ∧ IsPSL m 2 1 (ModO2 (conjClosure L M)) := by
    rcases h4.2.2 with h3 | h4'
    · exact ⟨3, Or.inl rfl, h3⟩
    · exact ⟨4, Or.inr rfl, h4'⟩
  have hpmL : IsPSL m 2 1 (ModO2 L) := by
    rw [hL0]
    exact hpm
  refine ⟨⟨m, hm, hpmL, ?_⟩, ?_⟩
  · rcases key m hm hpm with ⟨k, hk1, -, hs⟩ | ⟨h4m, ha⟩
    · exact Or.inl ⟨k, hk1, hs⟩
    · exact Or.inr ⟨h4m, ha⟩
  · intro m' k' hm' hpm' hs'
    have hmm : m = m' := eq_of_isPSL_two_one hm hm' hpmL hpm'
    subst hmm
    have hc' := C48.card_of_isSumOfNaturalModules_bot hs'
    rw [ZMod.card, Fintype.card_fin] at hc'
    rcases key m hm hpm with ⟨k, -, hk4, hs⟩ | ⟨rfl, ha⟩
    · have hc := C48.card_of_isSumOfNaturalModules_bot hs
      rw [ZMod.card, Fintype.card_fin, hc'] at hc
      have := Nat.pow_right_injective le_rfl hc
      have hm0 : 0 < m := by omega
      have : k' = k := Nat.eq_of_mul_eq_mul_left hm0 this
      omega
    · exfalso
      obtain ⟨-, -, -, -, β, hβ, hβker, -⟩ := ha
      have hinj : Function.Injective β := by
        rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
      have hcV : Nat.card ↥V = 2 ^ 6 := by
        rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβ⟩).toEquiv]
        exact card_altHeart_eight
      rw [hcV] at hc'
      have := Nat.pow_right_injective le_rfl hc'
      omega

end CFSG.Quasithin.C48Pf
