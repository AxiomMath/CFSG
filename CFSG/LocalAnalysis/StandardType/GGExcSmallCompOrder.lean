module

public import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrderLength
public import CFSG.LocalAnalysis.StandardType.GGExcSmallCompOrderArith
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcToral

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

namespace SmallCompOrder


variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M}

theorem exists_card_componentRootSpan_counts [Finite K] (i : KernelComponent χ) :
    ∃ (d : ℕ) (c : ℕ → ℕ), d ≤ (posRoots (componentRoots χ i)).ncard ∧ c 0 = 1 ∧
      (∀ k ≤ (posRoots (componentRoots χ i)).ncard,
        c ((posRoots (componentRoots χ i)).ncard - k) = c k) ∧
      (∀ k, 1 ≤ k → c k ≤ d * c (k - 1)) ∧
      Nat.card (componentRootSpan K χ i) = Nat.card (componentTorus K χ i) *
        Nat.card K ^ (posRoots (componentRoots χ i)).ncard *
          ∑ k ∈ Finset.range ((posRoots (componentRoots χ i)).ncard + 1),
            c k * Nat.card K ^ k := by
  classical
  obtain ⟨s, hs, hcard⟩ := exists_card_componentRootSpan_eq (K := K) i
  set N := (posRoots (componentRoots χ i)).ncard with hNdef
  set f : WeylGroup τ → ℕ := fun w =>
    (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w).ncard with hfdef
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hfinΨ : (posRoots (componentRoots χ i)).Finite :=
    (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ.1
  have hf : ∀ w ∈ s, f w ≤ N := fun w _ => by
    have h := ncard_unionInversionRoots_le (χ := χ) ({i} : Set (KernelComponent χ)) w
    rwa [unionRoots_singleton_eq] at h
  set R : Finset (WeylGroup τ) := (simpleRoots (componentRoots χ i)).image rootReflection
    with hRdef
  refine ⟨R.card, fun k => (s.filter (fun w => f w = k)).card, ?_, ?_, ?_, ?_, ?_⟩
  · calc R.card ≤ (simpleRoots (componentRoots χ i)).card := Finset.card_image_le
      _ = ((simpleRoots (componentRoots χ i) : Finset (Fin τ.rank → ℤ)) :
          Set (Fin τ.rank → ℤ)).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ N := Set.ncard_le_ncard (fun β hβ => simpleRoot_mem_posRoots hβ) hfinΨ
  · exact card_filter_eq_zero_eq_one s f ((hs 1).2 (one_mem _))
      (ncard_unionInversionRoots_one _)
      fun w hw h0 => eq_one_of_ncard_unionInversionRoots_eq_zero _ ((hs w).1 hw) h0
  · obtain ⟨w₀, hw₀, hlong⟩ := exists_longest_ncard (χ := χ) i
    intro k hk
    exact card_filter_sub_eq s f N hf (w₀ := w₀)
      (fun w hw => ⟨(hs _).2 (mul_mem hw₀ ((hs w).1 hw)), hlong w ((hs w).1 hw)⟩) hk
  · intro k hk
    refine card_filter_le_mul s f R (fun w hw h1 => ?_) hk
    obtain ⟨β, hβ, h⟩ := exists_descent _ ((hs w).1 hw) h1
    have hβ' : β ∈ simpleRoots (componentRoots χ i) := by
      have h' := hβ
      rw [unionSimpleRoots_singleton_eq] at h'
      exact h'
    exact ⟨rootReflection β, Finset.mem_image_of_mem _ hβ',
      (hs _).2 (mul_mem ((hs w).1 hw) (rootReflection_mem_unionWeylGroup hβ)), h⟩
  · rw [hcard, sum_pow_eq_sum_card_filter s f N (Nat.card K) hf]

theorem card_center_dvd_card_componentTorus (i : KernelComponent χ) :
    Nat.card (Subgroup.center (componentRootSpan K χ i)) ∣ Nat.card (componentTorus K χ i) := by
  let f : Subgroup.center (componentRootSpan K χ i) →* componentTorus K χ i :=
    { toFun := fun z => ⟨((z : componentRootSpan K χ i) : ModGL τ K),
        CFSG.LieType.HighestRoot.coe_mem_componentTorus_of_mem_center z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun a b h => ?_
  have h' := congrArg (fun x : componentTorus K χ i => (x : ModGL τ K)) h
  exact Subtype.ext (Subtype.ext h')

theorem prime_dvd_sub_one_of_dvd_card_componentTorus [Finite K] (i : KernelComponent χ)
    {p : ℕ} (hp : p.Prime) (hpT : p ∣ Nat.card (componentTorus K χ i)) :
    p ∣ Nat.card K - 1 := by
  have := Fact.mk hp
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpT
  have h1 : (x : ModGL τ K) ^ Nat.card Kˣ = 1 :=
    LayerExc.pow_eq_one_of_mem_torusGroup (componentTorus_le_torusGroup K χ i x.2)
  have h2 : x ^ Nat.card Kˣ = 1 := Subtype.ext (by rw [Subgroup.coe_pow, h1]; rfl)
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rwa [hx, Nat.card_units] at h3

theorem ggNotExcThree_componentRootSpan_of_card [Finite K] (i : KernelComponent χ)
    (hK : Nat.card K = 4 ∨ Nat.card K = 8) :
    GGNotExcThreeOrder (ggCQ (componentRootSpan K χ i)) := by
  obtain ⟨d, c, hd, hc0, hsym, hstep, hcard⟩ := exists_card_componentRootSpan_counts (K := K) i
  obtain ⟨m, hm⟩ := card_center_dvd_card_componentTorus (K := K) (χ := χ) i
  have hZpos : 0 < Nat.card (Subgroup.center (componentRootSpan K χ i)) := Nat.card_pos
  have hTpos : 0 < Nat.card (componentTorus K χ i) := Nat.card_pos
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hS := card_eq_ggCQ_mul (componentRootSpan K χ i)
  have hggCQ : ggCQ (componentRootSpan K χ i) = m * Nat.card K ^
      (posRoots (componentRoots χ i)).ncard *
        ∑ k ∈ Finset.range ((posRoots (componentRoots χ i)).ncard + 1),
          c k * Nat.card K ^ k := by
    refine Nat.eq_of_mul_eq_mul_right hZpos ?_
    rw [← hS, hcard, hm]
    ring
  rw [hggCQ]
  refine ggNotExcThreeOrder_of_counts c hK hc0 hsym hstep hd (fun p hp hpm => ?_) hm0
  exact prime_dvd_sub_one_of_dvd_card_componentTorus i hp (hm ▸ Dvd.dvd.mul_left hpm _)

end SmallCompOrder

theorem ggExcSmallCompOrderInput_holds :
    GGExcSmallCompOrderInput := by
  intro τ K _ _ _ M _ χ i _ hs
  exact SmallCompOrder.ggNotExcThree_componentRootSpan_of_card i
    (by rcases hs with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])

end CFSG.StandardType
