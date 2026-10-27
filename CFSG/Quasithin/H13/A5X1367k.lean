module

public import CFSG.Quasithin.H13.A5X1367j

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
variable [IsMulCommutative ↥S.Uv]

theorem ds3_dichotomy (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    {J G₁ G₂ : Subgroup (MulAut ↥S.Uv)} {W₁ W₂ : Subgroup ↥S.Uv} {y₁ y₂ : MulAut ↥S.Uv}
    (hD : DS3 J G₁ G₂ W₁ W₂ y₁ y₂)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv))) :
    (∀ g ∈ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv, DS3.FixY y₁ g) ∨
      ∃ t ∈ autOn S.Tv S.Uv, t * y₁ * t⁻¹ = y₂ ∨ t * y₁ * t⁻¹ = y₂⁻¹ := by
  set GS := autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv with hGS
  by_cases hall : ∀ t ∈ autOn S.Tv S.Uv, DS3.FixY y₁ t
  · left
    by_contra hcon
    push Not at hcon
    obtain ⟨g₀, hg₀, hg₀f⟩ := hcon
    have hsw₀ : g₀ * y₁ * g₀⁻¹ = y₂ ∨ g₀ * y₁ * g₀⁻¹ = y₂⁻¹ :=
      (hD.conj_cases (hGJ hg₀)).resolve_left hg₀f
    set N : Subgroup (MulAut ↥S.Uv) :=
      { carrier := {g | g ∈ GS ∧ DS3.FixY y₁ g}
        one_mem' := ⟨GS.one_mem, by simp [DS3.FixY]⟩
        mul_mem' := fun ha hb => ⟨GS.mul_mem ha.1 hb.1, DS3.fixY_mul ha.2 hb.2⟩
        inv_mem' := fun ha => ⟨GS.inv_mem ha.1, DS3.fixY_inv ha.2⟩ } with hN
    have hNG : N ≤ GS := fun x hx => hx.1
    have hTN : autOn S.Tv S.Uv ≤ N := fun x hx =>
      ⟨S.autOn_le_GvS S.Tv_le_Gv hx, hall x hx⟩
    have hswap : ∀ h ∈ GS, ¬ DS3.FixY y₁ h → DS3.FixY y₁ (h * g₀) := by
      intro h hh hhf
      have hsw : h * y₁ * h⁻¹ = y₂ ∨ h * y₁ * h⁻¹ = y₂⁻¹ :=
        (hD.conj_cases (hGJ hh)).resolve_left hhf
      have h2 := hD.swap_consistent (hGJ hh) hsw
      have e : h * g₀ * y₁ * (h * g₀)⁻¹ = h * (g₀ * y₁ * g₀⁻¹) * h⁻¹ := by group
      have hinv : h * y₂⁻¹ * h⁻¹ = (h * y₂ * h⁻¹)⁻¹ := by group
      unfold DS3.FixY
      rw [e]
      rcases hsw₀ with e0 | e0 <;> rw [e0]
      · exact h2
      · rw [hinv]
        rcases h2 with h2 | h2 <;> rw [h2]
        · exact Or.inr rfl
        · rw [inv_inv]; exact Or.inl rfl
    have hidx : (N.subgroupOf GS).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨g₀, hg₀⟩, fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      by_cases hb : DS3.FixY y₁ (b : MulAut ↥S.Uv)
      · have h1 : ¬ ((b * ⟨g₀, hg₀⟩ : ↥GS) : MulAut ↥S.Uv) ∈ N := by
          intro hbg
          apply hg₀f
          have := DS3.fixY_mul (DS3.fixY_inv hb) hbg.2
          simpa [mul_assoc] using this
        exact Or.inr ⟨⟨b.2, hb⟩, h1⟩
      · have h1 : ((b * ⟨g₀, hg₀⟩ : ↥GS) : MulAut ↥S.Uv) ∈ N :=
          ⟨GS.mul_mem b.2 hg₀, hswap b b.2 hb⟩
        exact Or.inl ⟨h1, fun hbN => hb hbN.2⟩
    have hsyl := S.isSylowTwoOf_TvS h1222 h517
    have hrel := Subgroup.relIndex_mul_relIndex (autOn S.Tv S.Uv) N GS hTN hNG
    have hNrel : N.relIndex GS = 2 := hidx
    rw [hNrel] at hrel
    have h3 : ¬ 2 ∣ (autOn S.Tv S.Uv).relIndex GS := hsyl.2.2
    exact h3 (hrel ▸ dvd_mul_left 2 _)
  · right
    push Not at hall
    obtain ⟨t, ht, htf⟩ := hall
    exact ⟨t, ht, (hD.conj_cases (hGJ (S.autOn_le_GvS S.Tv_le_Gv ht))).resolve_left htf⟩

theorem false_of_ds3 (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G)))
    (hVv : ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G))
    {J G₁ G₂ : Subgroup (MulAut ↥S.Uv)} {W₁ W₂ : Subgroup ↥S.Uv} {y₁ y₂ : MulAut ↥S.Uv}
    (hD : DS3 J G₁ G₂ W₁ W₂ y₁ y₂)
    (hJG : J ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv)
    (hGJ : autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ≤
      Subgroup.normalizer (J : Set (MulAut ↥S.Uv))) : False := by
  have hJ1 : J ≠ ⊥ := fun h => hD.y₁_ne_one (by
    have := hD.G₁_le hD.y₁mem
    rwa [h, Subgroup.mem_bot] at this)
  rcases S.ds3_dichotomy h1222 h517 hD hGJ with hfix | ⟨t, ht, hts⟩
  · exact S.false_of_ds3_noswap h1222 h517 hF hVv hD hJG hGJ hfix
  · exact S.false_of_ds3_swap h1222 h517 hF hD hJG hGJ hJ1 ht hts

end Setting

end CFSG.Quasithin.H13.A5
