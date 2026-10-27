module

public import CFSG.RankThree.PartOne.K133Spor.HNKlein

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.RankThree.PartOne.K133 Subgroup

@[expose] def PlaneFreeGroup (K : Type*) [Group K] : Prop :=
  ∀ x y u : K, orderOf x = 5 → orderOf y = 5 → y ∉ Subgroup.zpowers x → x * y = y * x →
    orderOf u = 2 → u * x = x * u → u * y = y * u → False

theorem hnClass_of_hom {G K : Type*} [Group G] [Finite G] [Group K] (a : G) (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (ψ : Subgroup.centralizer ({a} : Set G) →* K)
    (hker : ∀ y, ψ y = 1 → (y : G) = 1 ∨ (y : G) = a) (hfree : PlaneFreeGroup K) :
    HNClass a := by
  classical
  intro D hDab hD5 hDc hDa t' ht'a ht'2 ht'1 ht'ne hDt'
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hxD, hx1⟩ : ∃ x ∈ D, x ≠ 1 := by
    by_contra h
    push Not at h
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).mpr h
    rw [this, Subgroup.card_bot] at hDc
    omega
  have hxord : orderOf x = 5 := orderOf_eq_prime (hD5 x hxD) hx1
  obtain ⟨f, hfD, hfx⟩ : ∃ f ∈ D, f ∉ zpowers x := by
    by_contra h
    push Not at h
    have hle : D ≤ zpowers x := h
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hxord, hDc] at this
    omega
  have hf1 : f ≠ 1 := fun h => hfx (h ▸ one_mem _)
  have haD : ∀ y ∈ D, y ≠ 1 → y ≠ a := by
    intro y hy hy1 hya
    have h5 := hD5 y hy
    rw [hya] at h5
    have : a = 1 := by
      calc a = a ^ 5 * (a ^ 2)⁻¹ ^ 2 := by group
        _ = 1 := by rw [h5, ha2]; group
    exact ha1 this
  have hker_D : ∀ y : Subgroup.centralizer ({a} : Set G), (y : G) ∈ D → ψ y = 1 → (y : G) = 1 := by
    intro y hy hψ
    rcases hker y hψ with h | h
    · exact h
    · by_cases h1 : (y : G) = 1
      · exact h1
      · exact absurd h (haD _ hy h1)
  let xC : Subgroup.centralizer ({a} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.2 (hDa x hxD)⟩
  let fC : Subgroup.centralizer ({a} : Set G) :=
    ⟨f, Subgroup.mem_centralizer_singleton_iff.2 (hDa f hfD)⟩
  let tC : Subgroup.centralizer ({a} : Set G) :=
    ⟨t', Subgroup.mem_centralizer_singleton_iff.2 ht'a⟩
  have hψx5 : ψ xC ^ 5 = 1 := by
    rw [← map_pow]
    have : xC ^ 5 = 1 := Subtype.ext (hD5 x hxD)
    rw [this, map_one]
  have hψx1 : ψ xC ≠ 1 := fun h => hx1 (hker_D xC hxD h)
  have hψxord : orderOf (ψ xC) = 5 := orderOf_eq_prime hψx5 hψx1
  have hψf5 : ψ fC ^ 5 = 1 := by
    rw [← map_pow]
    have : fC ^ 5 = 1 := Subtype.ext (hD5 f hfD)
    rw [this, map_one]
  have hψf1 : ψ fC ≠ 1 := fun h => hf1 (hker_D fC hfD h)
  have hψford : orderOf (ψ fC) = 5 := orderOf_eq_prime hψf5 hψf1
  have hψt2 : ψ tC ^ 2 = 1 := by
    rw [← map_pow]
    have : tC ^ 2 = 1 := Subtype.ext ht'2
    rw [this, map_one]
  have hψt1 : ψ tC ≠ 1 := by
    intro h
    rcases hker tC h with h1 | h1
    · exact ht'1 h1
    · exact ht'ne h1
  have hψtord : orderOf (ψ tC) = 2 := orderOf_eq_prime hψt2 hψt1
  have hψfx : ψ fC ∉ zpowers (ψ xC) := by
    intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    apply hfx
    have hmemD : f * x ^ (-k) ∈ D := D.mul_mem hfD (D.zpow_mem (D.inv_mem hxD) k |> fun h' => by
      simpa [zpow_neg] using h')
    let yC : Subgroup.centralizer ({a} : Set G) := fC * xC ^ (-k)
    have hyD : (yC : G) ∈ D := hmemD
    have hψy : ψ yC = 1 := by
      show ψ (fC * xC ^ (-k)) = 1
      rw [map_mul, map_zpow, zpow_neg, hk]
      group
    have h' : f * x ^ (-k) = 1 := hker_D yC hyD hψy
    refine ⟨k, ?_⟩
    have : f = x ^ k := by
      calc f = (f * x ^ (-k)) * x ^ k := by simp [zpow_neg]
        _ = x ^ k := by rw [h']; group
    exact this.symm
  have hψxf : ψ xC * ψ fC = ψ fC * ψ xC := by
    have e : xC * fC = fC * xC := Subtype.ext (hDab x hxD f hfD)
    rw [← map_mul, ← map_mul, e]
  have hψtx : ψ tC * ψ xC = ψ xC * ψ tC := by
    have e : tC * xC = xC * tC := Subtype.ext (hDt' x hxD).symm
    rw [← map_mul, ← map_mul, e]
  have hψtf : ψ tC * ψ fC = ψ fC * ψ tC := by
    have e : tC * fC = fC * tC := Subtype.ext (hDt' f hfD).symm
    rw [← map_mul, ← map_mul, e]
  exact hfree _ _ _ hψxord hψford hψfx hψxf hψtord hψtx hψtf

end CFSG.RankThree.PartOne.K133Spor
