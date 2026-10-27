module

public import CFSG.Quasithin.EmptyFaithful.S153E53C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Exist

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_t₁ (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) (h52 : Concl15352 cx) :
    ∃ t₁ ∈ T, t₁ ∉ UCT153 T M V₁ Mc := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, -, -, -, -, -, hS, -, -, -⟩ := exists_bar_model cx
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T cx.c.hyp.isSylowTwoOf_autI
  have hK4 : IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) := by
    rcases h51.two with h | ⟨hab, -, -, -⟩
    · exact h.2.1
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := h52
      exact hne (B2F.isElemAbelian_comm hab ha hb)
  have hU4 : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := hK4.1
  by_contra hall
  push Not at hall
  have hTle : T ≤ UCT153 T M V₁ Mc := fun x hx => hall x hx
  have hUN : UH153 T M V₁ Mc ≤ Subgroup.normalizer (VZ T M : Set G) := U_le_N cx
  have hCN : T ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans (T_le_N cx)
  have h1 : autI hV T ≤ autI hV (UCT153 T M V₁ Mc) := autI_mono hV hTle
  have h2 : autI hV (UCT153 T M V₁ Mc) = autI hV (UH153 T M V₁ Mc) := by
    show autI hV (UH153 T M V₁ Mc ⊔ (T ⊓ Subgroup.centralizer (VZ T M : Set G))) = _
    rw [autI_sup hV hUN hCN, autI_eq_bot_of_le_centralizer hV inf_le_right, sup_bot_eq]
  have h3 := Subgroup.card_le_of_le (h2 ▸ h1)
  rw [hT8, hU4] at h3
  omega

theorem exists_y (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} (h53 : Concl15353One cx N₁ N₂) :
    ∃ y : G, y ∈ Yi153 T Mc M V₁ N₁ ∧ y ∉ pCoreOf 2 (Yi153 T Mc M V₁ N₁) := by
  have hV := cx.c.hyp.elemAbelian
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h53.iso₁
  have hN6 : 3 ∣ Nat.card ↥N₁ := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  obtain ⟨ν, hν3⟩ := exists_prime_orderOf_dvd_card' 3 hN6
  let ν' : MulAut (IntMod (VZ T M) hV) := (ν : MulAut ↥(VZ T M))
  have hν3' : orderOf ν' = 3 := by
    show orderOf (ν : MulAut ↥(VZ T M)) = 3
    rw [Subgroup.orderOf_coe]
    exact hν3
  obtain ⟨Ω, hΩ, -, hNΩ⟩ := h53.omega
  have hνΩ : (ν : MulAut ↥(VZ T M)) ∈ Ω := hNΩ ▸ (le_sup_left : N₁ ≤ N₁ ⊔ N₂) ν.2
  have hνM : ν' ∈ autI hV M := ((hΩ _).1 hνΩ).1
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hνY : ν' ∈ autI hV (Y153 Mc M) := by
    rw [hYbar]
    exact mem_oTwoUpper_of_odd hνM (by rw [hν3']; decide)
  have hνpre : ν' ∈ autI hV (preAut153 (VZ T M) (Y153 Mc M) N₁) := by
    rw [autI_preAut153 hV N₁]
    exact ⟨hνY, ν.2⟩
  obtain ⟨y₀, hy₀, hy₀ν⟩ := (mem_autI hV).1 hνpre
  obtain ⟨hy₀Y, hy₀N, hy₀c⟩ := mem_preAut153.1 hy₀
  have hy₀pre : (y₀ : G) ∈ Ni153 T Mc M V₁ N₁ :=
    mem_preAut153.2 ⟨Subgroup.mem_sup_left hy₀Y, hy₀N, hy₀c⟩
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (y₀ : G)).ne'
  set y₁ : G := (y₀ : G) ^ 2 ^ k with hy₁
  have hy₁ord : Odd (orderOf y₁) := by
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    rw [hy₁, orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm
  have hy₁Y : y₁ ∈ Y153 Mc M ⊓ Ni153 T Mc M V₁ N₁ :=
    ⟨(Y153 Mc M).pow_mem hy₀Y _, (Ni153 T Mc M V₁ N₁).pow_mem hy₀pre _⟩
  refine ⟨y₁, mem_oTwoUpper_of_odd hy₁Y hy₁ord, fun hmem => ?_⟩
  have hP : IsPGroup 2 ↥(pCoreOf 2 (Yi153 T Mc M V₁ N₁)) := pCoreOf_isPGroup 2 _
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y₁, hmem⟩
  rw [Subgroup.orderOf_mk] at hj
  have hj0 : j = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf y₁ := by rw [hj]; exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hy₁ord) (even_iff_two_dvd.mpr h2)
  rw [hj0, pow_zero, orderOf_eq_one_iff] at hj
  have hpow : ν' ^ 2 ^ k = 1 := by
    have h1 : convI hV (y₀ ^ 2 ^ k) = ν' ^ 2 ^ k := by
      rw [map_pow, hy₀ν]
    have h2 : ((y₀ ^ 2 ^ k : ↥(Subgroup.normalizer (VZ T M : Set G))) : G) = 1 := by
      rw [Subgroup.coe_pow]
      exact hj
    have h3 : y₀ ^ 2 ^ k = 1 := Subtype.ext h2
    rw [← h1, h3, map_one]
  have h4 : orderOf ν' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow
  rw [hν3'] at h4
  have h5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
  omega

end Exist

end S153E

end CFSG.Quasithin
