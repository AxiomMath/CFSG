module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofHJ
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

@[expose] def Item2112TwoGroupHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → Nonempty (lBar L ≃* NativeSporadic.J2) →
      ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      ∀ x ∈ Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G),
        x * d * x⁻¹ = d → x * c * x⁻¹ ≠ c * d

@[expose] def Item2112NDW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → IsList218 L → ∀ d ∈ A, d ≠ 1 → IsCentral218 L d →
      Subgroup.normalizer (A : Set G) ⊓
          Subgroup.normalizer (Subgroup.closure ({c, d} : Set G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)

namespace Item2110Res2Proof

open Subgroup
open Item2113Res2Proof

variable {G : Type} [Group G]

theorem conj_mem_of_twoGroupW [Finite G] {A : Subgroup G} {c d ℓ : G} (h : DData c d ℓ)
    (hℓA : ℓ ∈ normalizer (A : Set G))
    (hTG : ∀ x ∈ normalizer (A : Set G),
      x ∈ normalizer (closure ({c, d} : Set G) : Set G) → x * d * x⁻¹ = d →
        x * c * x⁻¹ ≠ c * d)
    {x : G} (hxA : x ∈ normalizer (A : Set G))
    (hxD : x ∈ normalizer (closure ({c, d} : Set G) : Set G))
    (hxd : x ∈ normalizer ((zpowers d : Subgroup G) : Set G)) :
    x * c * x⁻¹ ∈ zpowers c := by
  have hℓN := mem_normalizer_of_inv h.ℓc h.ℓd
  obtain ⟨p, q, hp, hq, hM⟩ := exists_conj_kappa h.c3 h.d3 h.comm hxD
  have bad : ∀ g ∈ normalizer (A : Set G), g ∈ normalizer (closure ({c, d} : Set G) : Set G) →
      ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3, (∀ v, g * kappa c d v * g⁻¹ = kappa c d (f v)) →
        ¬ (f (0, 1) = (0, 1) ∧ f (1, 0) = (1, 1)) := by
    rintro g hgA hg f hf ⟨h01, h10⟩
    apply hTG g hgA hg
    · calc g * d * g⁻¹ = g * kappa c d (0, 1) * g⁻¹ := by rw [kappa_zero_one]
        _ = d := by rw [hf, h01, kappa_zero_one]
    · calc g * c * g⁻¹ = g * kappa c d (1, 0) * g⁻¹ := by rw [kappa_one_zero]
        _ = c * d := by rw [hf, h10, kappa_one_one]
  have hq1 : q.1 = 0 := by
    rw [← kappa_mem_zpowers_right_iff h.d3 h.inj, hq]
    exact (mem_normalizer_iff.mp hxd d).mp (mem_zpowers d)
  have hL := h.conj_ℓ
  have hLi := h.conj_ℓinv
  have hx2 := conj_kappa_mul hM hM
  have hxL := conj_kappa_mul hM hL
  have hxLx := conj_kappa_mul hxL hM
  have hw3 := conj_kappa_mul hxLx hLi
  have hw4 := conj_kappa_mul hw3 hw3
  have hx4 := conj_kappa_mul hx2 hx2
  have hxℓN := mul_mem hxD hℓN.1
  have hw3N := mul_mem (mul_mem hxℓN hxD) (inv_mem hℓN.1)
  have hxℓA := mul_mem hxA hℓA
  have hw3A := mul_mem (mul_mem hxℓA hxA) (inv_mem hℓA)
  have hp2 := fixC_matrix p q (h.lin_inj hM) hq1 (bad x hxA hxD _ hM)
    (bad _ (mul_mem hxA hxA) (mul_mem hxD hxD) _ hx2)
    (bad _ hw3A hw3N _ hw3) (bad _ (mul_mem hw3A hw3A) (mul_mem hw3N hw3N) _ hw4)
    (bad _ hxℓA hxℓN _ hxL)
    (bad _ (mul_mem (mul_mem hxA hxA) (mul_mem hxA hxA))
      (mul_mem (mul_mem hxD hxD) (mul_mem hxD hxD)) _ hx4)
  rw [← hp, kappa_mem_zpowers_left_iff h.c3 h.inj]
  exact hp2

theorem conj_mem_of_noFusion_at [Finite G] {c d ℓ : G} (h : DData c d ℓ) {x : G}
    (hxD : x ∈ normalizer (closure ({c, d} : Set G) : Set G))
    (hX : x ∈ normalizer ((zpowers d : Subgroup G) : Set G) → x * c * x⁻¹ ∈ zpowers c)
    (hNF₁ : ∀ y : G, y * c * y⁻¹ ∉ zpowers d) (hNF₂ : ∀ y : G, y * d * y⁻¹ ∉ zpowers c) :
    x * c * x⁻¹ ∈ zpowers c := by
  obtain ⟨p, q, hp, hq, hM⟩ := exists_conj_kappa h.c3 h.d3 h.comm hxD
  have hL := h.conj_ℓ
  have hx2 := conj_kappa_mul hM hM
  have hxL := conj_kappa_mul hM hL
  have hxLx := conj_kappa_mul hxL hM
  have c_not : ∀ y : G, ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3,
      (∀ v, y * kappa c d v * y⁻¹ = kappa c d (f v)) → (f (1, 0)).1 ≠ 0 := by
    intro y f hf h0
    apply hNF₁ y
    rw [← kappa_one_zero (c := c) (d := d), hf, kappa_mem_zpowers_right_iff h.d3 h.inj]
    exact h0
  have d_not : ∀ y : G, ∀ f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3,
      (∀ v, y * kappa c d v * y⁻¹ = kappa c d (f v)) → (f (0, 1)).2 ≠ 0 := by
    intro y f hf h0
    apply hNF₂ y
    rw [← kappa_zero_one (c := c) (d := d), hf, kappa_mem_zpowers_left_iff h.c3 h.inj]
    exact h0
  have hfix : q.1 = 0 → p.2 = 0 := by
    intro hq1
    have hxd : x ∈ normalizer ((zpowers d : Subgroup G) : Set G) := by
      apply mem_normalizer_zpowers
      rw [← hq, kappa_mem_zpowers_right_iff h.d3 h.inj]
      exact hq1
    have := hX hxd
    rwa [← hp, kappa_mem_zpowers_left_iff h.c3 h.inj] at this
  have hp2 := nd_matrix p q (h.lin_inj hM) hfix (c_not x _ hM) (d_not x _ hM) (c_not _ _ hx2)
    (d_not _ _ hx2) (c_not _ _ hxLx) (d_not _ _ hxLx)
  rw [← hp, kappa_mem_zpowers_left_iff h.c3 h.inj]
  exact hp2

theorem zpowers_eq_of_mem_cube {x y : G} (hx3 : x ^ 3 = 1) (hy : y ∈ zpowers x) (hy1 : y ≠ 1) :
    zpowers y = zpowers x := by
  apply le_antisymm (zpowers_le.mpr hy)
  rw [zpowers_le]
  rcases mem_zpowers_cube hx3 hy with h1 | h1 | h1
  · exact absurd h1 hy1
  · rw [h1]; exact mem_zpowers x
  · have : (x ^ 2) ^ 2 = x := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hx3, one_mul, pow_one]
    rw [← this, ← h1]
    exact pow_mem (mem_zpowers y) 2

theorem noFusion_zpowers [Finite G] (hNF : Item2112NoFusion) {A E U L : Subgroup G} {c d ℓ : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdcen : IsCentral218 L d) (hD : DData c d ℓ) :
    (∀ y : G, y * c * y⁻¹ ∉ zpowers d) ∧ (∀ y : G, y * d * y⁻¹ ∉ zpowers c) := by
  have hdinv : IsCentral218 L d⁻¹ :=
    Item2113Proof.isCentral218_of_zpowers_eq hdcen zpowers_inv
  have hNF₀ : ∀ y : G, y * c * y⁻¹ ≠ d :=
    hNF G A E U c L E U c L hpair hL hpair hL d hdA hd1 hdcen
  have hNF₀' : ∀ y : G, y * c * y⁻¹ ≠ d⁻¹ := hNF G A E U c L E U c L hpair hL hpair hL d⁻¹
    (inv_mem hdA) (inv_ne_one.mpr hd1) hdinv
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rcases mem_zpowers_cube hD.d3 hy with h1 | h1 | h1
    · apply hD.c1
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
    · exact hNF₀ y h1
    · exact hNF₀' y (h1.trans (sq_eq_inv_of_cube hD.d3))
  · rcases mem_zpowers_cube hD.c3 hy with h1 | h1 | h1
    · apply hD.d1
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simpa [mul_assoc] using this
    · apply hNF₀ y⁻¹
      have := congrArg (fun z => y⁻¹ * z * y) h1
      simp only [inv_inv]
      simpa [mul_assoc] using this.symm
    · apply hNF₀' y⁻¹
      rw [sq_eq_inv_of_cube hD.c3] at h1
      have h2 : y * d⁻¹ * y⁻¹ = c := by
        rw [show y * d⁻¹ * y⁻¹ = (y * d * y⁻¹)⁻¹ by group, h1, inv_inv]
      have := congrArg (fun z => y⁻¹ * z * y) h2
      simp only [inv_inv]
      simpa [mul_assoc] using this.symm

theorem twoGroupW_of_two [Finite G] (h2 : Item2110Two) {A E U L : Subgroup G} {c d ℓ : G}
    (hpair : Sec21Pair G A E U c L) (hL : IsList218 L) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hdcen : IsCentral218 L d) (hD : DData c d ℓ) :
    ∀ x ∈ normalizer (A : Set G), x ∈ normalizer (closure ({c, d} : Set G) : Set G) →
      x * d * x⁻¹ = d → x * c * x⁻¹ ≠ c * d := fun _ hxA _ hxd =>
  item2112TwoGroup_of_mem_W h2 hpair hL hdA hd1 hdcen hD.dc hxA hxd

section Pairs

theorem exists_inv_mem_W [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5)
    {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    (hS : Nonempty (starOf A L ≃* DihedralGroup 6) ∨
      Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3))) :
    ∃ ℓ ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ A ⊓ L, ℓ * x * ℓ⁻¹ = x⁻¹ := by
  have key : ∀ {ζ : MulAut A}, ζ ∈ starOf A L → (∀ x : A, (x : G) ∈ L → ζ x = x⁻¹) →
      ∃ ℓ ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ A ⊓ L, ℓ * x * ℓ⁻¹ = x⁻¹ := by
    rintro _ ⟨w, hwL, rfl⟩ hinv
    refine ⟨w, ⟨mem_subgroupOf.mp hwL, w.2⟩, fun x ⟨hxA, hxL⟩ => ?_⟩
    have h := congrArg Subtype.val (hinv ⟨x, hxA⟩ hxL)
    rwa [normalizerMonoidHom_apply_apply_coe] at h
  rcases hS with hS | hS
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1, hz2, hz1, -⟩ := dihedral_six_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 dihedral_six_central
    obtain ⟨-, hinv⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
      hζc
    exact key hζ hinv
  · obtain ⟨e⟩ := hS
    obtain ⟨h3, h1, hz2, hz1, -⟩ := gl_two_three_data
    obtain ⟨σ₀, hσ₀, hσ₀3, hσ₀1⟩ := exists_cube_of_mulEquiv e h3 h1
    obtain ⟨ζ, hζ, hζ2, hζ1, hζc⟩ := exists_central_of_mulEquiv e hz2 hz1 gl_two_three_central
    obtain ⟨-, hinv⟩ := card_nine_and_inv_of_central h211 h45 hpair hL hσ₀ hσ₀3 hσ₀1 hζ hζ2 hζ1
      hζc
    exact key hζ hinv

theorem exists_dData_W [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5)
    {A E U L : Subgroup G} {c d : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    (hS : Nonempty (starOf A L ≃* DihedralGroup 6) ∨
      Nonempty (starOf A L ≃* GL (Fin 2) (ZMod 3)))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdcen : IsCentral218 L d) :
    ∃ ℓ ∈ L ⊓ normalizer (A : Set G), DData c d ℓ := by
  obtain ⟨hcA, hc1, hLc, -, hcL⟩ := pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have hdL := Item2113Proof.mem_of_isCentral218 hdcen
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcd : Commute c d := congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  have hcd' : c ∉ zpowers d := fun h => hcL ((zpowers_le.mpr hdL) h)
  have hdc : d ∉ zpowers c := by
    intro h
    apply hcd'
    exact (zpowers_eq_of_mem_cube hc3 h hd1) ▸ mem_zpowers c
  obtain ⟨ℓ, hℓ, hinv⟩ := exists_inv_mem_W h211 h45 hpair hL hS
  have hℓd : ℓ * d * ℓ⁻¹ = d⁻¹ := hinv d ⟨hdA, hdL⟩
  have hℓc : ℓ * c * ℓ⁻¹ = c := by
    rw [mem_centralizer_singleton_iff.mp (hLc hℓ.1), mul_inv_cancel_right]
  exact ⟨ℓ, hℓ, ⟨hc3, hd3, hcd, hc1, hdc, hcd', hℓc, hℓd⟩⟩

theorem hj_or_dData_W [Finite G] (h211 : Item211) (h45 : Sec4.Item4_5)
    {A E U L : Subgroup G} {c d : G} (hpair : Sec21Pair G A E U c L) (hL : IsList218 L)
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdcen : IsCentral218 L d) :
    Nonempty (lBar L ≃* NativeSporadic.J2) ∨ ∃ ℓ ∈ L ⊓ normalizer (A : Set G), DData c d ℓ := by
  rcases starOf_cases_of_isList218 h211 hpair hL with ⟨-, hS⟩ | ⟨-, hS⟩ | ⟨hJ, -⟩
  · exact Or.inr (exists_dData_W h211 h45 hpair hL hS hdA hd1 hdcen)
  · exact Or.inr (exists_dData_W h211 h45 hpair hL (Or.inl hS) hdA hd1 hdcen)
  · exact Or.inl hJ

theorem item2112NDW_of
    (h211 : Item211) (h45 : Sec4.Item4_5) (h2 : Item2110Two)
    (hTGHJ : Item2112TwoGroupHJ) (hNF : Item2112NoFusion) : Item2112NDW := by
  intro G _ _ A E U c L hpair hL d hdA hd1 hdcen x ⟨hxA, hxD⟩
  have hReal : KF2112HJReal := kf2112HJReal_of Sec4.Sporadic.rank3II_4_15
  rcases hj_or_dData_W h211 h45 hpair hL hdA hd1 hdcen with hJ | ⟨ℓ, ⟨-, hℓA⟩, hD⟩
  · obtain ⟨ℓ, -, hD⟩ := exists_dData h211 h45 hReal hpair hL hdA hd1 hdcen
    have hTG' := hTGHJ G A E U c L hpair hL hJ d hdA hd1 hdcen
    obtain ⟨hNF₁, hNF₂⟩ := noFusion_zpowers hNF hpair hL hdA hd1 hdcen hD
    exact mem_normalizer_zpowers (hD.conj_mem_of_noFusion
      (fun y hy hyd => hD.conj_mem_of_twoGroup hTG' hy hyd) hNF₁ hNF₂ hxD)
  · obtain ⟨hNF₁, hNF₂⟩ := noFusion_zpowers hNF hpair hL hdA hd1 hdcen hD
    have hTGW := twoGroupW_of_two h2 hpair hL hdA hd1 hdcen hD
    exact mem_normalizer_zpowers (conj_mem_of_noFusion_at hD hxD
      (fun hxd => conj_mem_of_twoGroupW hD hℓA hTGW hxA hxD hxd) hNF₁ hNF₂)

end Pairs

end Item2110Res2Proof

end CFSG.RankThree.PartTwo.Sec21
