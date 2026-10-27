module

public import CFSG.Timmesfeld.Orders.ClassicalTransitive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open QuadraticMap CFSG.ClassicalGroups.Orthogonal Module

variable {K A : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup A] [Module K A]
  {Q : QuadraticForm K A}

theorem exists_sq_eq_of_charTwo (a : K) : ∃ c : K, c ^ 2 = a := by
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨c, by rw [hc, pow_two]⟩

theorem card_norm_eq_one [FiniteDimensional K A] (hA : finrank K A = 2)
    (hani : ∀ x, x ≠ 0 → Q x ≠ 0) : Nat.card {x : A // Q x = 1} = Nat.card K + 1 := by
  classical
  have := Fintype.ofFinite K
  have : Finite A := Module.finite_of_finite K
  have := Fintype.ofFinite A
  have hbij : Function.Bijective fun p : Kˣ × {x : A // Q x = 1} =>
      (⟨(p.1 : K) • (p.2 : A), smul_ne_zero p.1.ne_zero fun h0 => by
        have := p.2.2
        rw [h0, QuadraticMap.map_zero] at this
        exact zero_ne_one this⟩ : {y : A // y ≠ 0}) := by
    constructor
    · rintro ⟨c, x⟩ ⟨c', x'⟩ h
      have h' : (c : K) • (x : A) = (c' : K) • (x' : A) := congrArg Subtype.val h
      have hQ := congrArg Q h'
      rw [map_smul_eq_sq, map_smul_eq_sq, x.2, x'.2, mul_one, mul_one, CharTwo.sq_inj] at hQ
      have hcc : c = c' := Units.ext hQ
      subst hcc
      exact Prod.ext rfl (Subtype.ext (smul_right_injective A c.ne_zero h'))
    · rintro ⟨y, hy⟩
      obtain ⟨c, hc⟩ := exists_sq_eq_of_charTwo (Q y)
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hani y hy (by rw [← hc, zero_pow two_ne_zero])
      refine ⟨(Units.mk0 c hc0, ⟨c⁻¹ • y, ?_⟩), Subtype.ext ?_⟩
      · rw [map_smul_eq_sq, ← hc, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc0)]
      · change c • c⁻¹ • y = y
        rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have hcard := Nat.card_congr (Equiv.ofBijective _ hbij)
  have hne : Nat.card {y : A // y ≠ 0} = Nat.card K ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := K), hA]
  rw [Nat.card_prod, Nat.card_units, hne] at hcard
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have h1 : (Nat.card K - 1) * (Nat.card K + 1) = Nat.card K ^ 2 - 1 := by
    have : 1 ≤ Nat.card K := by omega
    zify [this, Nat.one_le_pow 2 _ (by omega : 0 < Nat.card K)]
    ring
  rw [← h1] at hcard
  exact Nat.eq_of_mul_eq_mul_left (by omega) hcard

theorem card_orthogonalGroup_of_anisotropic [FiniteDimensional K A] (hA : finrank K A = 2)
    (hani : ∀ x, x ≠ 0 → Q x ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * (Nat.card K + 1) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ : (polarBilin Q).Nondegenerate :=
    CFSG.LocalAnalysis.ComponentInitial.finite_anisotropic_plane_regular (by rw [hA]) hani
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : A, Q x₀ = 1 := by
    have : 0 < Nat.card {x : A // Q x = 1} := by rw [card_norm_eq_one hA hani]; omega
    obtain ⟨x⟩ := (Nat.card_pos_iff.mp this).1
    exact ⟨x, x.2⟩
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    rw [QuadraticMap.map_zero] at hx₀
    exact zero_ne_one hx₀
  have hQx₀ : Q x₀ ≠ 0 := by rw [hx₀]; exact one_ne_zero
  have hxx : polar Q x₀ x₀ = 0 := by rw [polar_self_eq_two_mul, h2, zero_mul]
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hx₀0
  set y₀ := (polar Q x₀ y)⁻¹ • y
  have hxy : polar Q x₀ y₀ = 1 := by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]
  have hyx : polar Q y₀ x₀ = 1 := by rw [polar_comm, hxy]
  have horbit : MulAction.orbit O x₀ = {x | Q x = 1} := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      change Q ((g : A ≃ₗ[K] A) x₀) = 1
      rw [map_of_mem g.2, hx₀]
    · intro hx
      by_cases hxe : x = x₀
      · exact ⟨1, by rw [hxe]; rfl⟩
      · have hsum : x₀ + x ≠ 0 := by
          intro h0
          have := add_eq_zero_iff_neg_eq.mp h0
          rw [neg_eq_self_of_two_eq_zero h2] at this
          exact hxe this.symm
        have hpol : polar Q x₀ x ≠ 0 := by
          have := hani _ hsum
          rwa [QuadraticMap.map_add Q x₀ x, hx₀, (hx : Q x = 1), one_add_one_eq_two, h2,
            zero_add] at this
        exact ⟨⟨reflect Q (x₀ + x), reflect_mem_orthogonalGroup Q _⟩,
          reflect_add_apply h2 (hx₀.trans ((hx : Q x = 1)).symm) hpol⟩
  have hli : LinearIndependent K ![x₀, y₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (polar Q x₀) hst
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxy,
      polar_zero_right] at h1
    have ht : t = 0 := by simpa using h1
    subst ht
    rw [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hst).resolve_right hx₀0, rfl⟩
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hA])
  have hb0 : b 0 = x₀ := by simp [b]
  have hb1 : b 1 = y₀ := by simp [b]
  have hext : ∀ g h : A ≃ₗ[K] A, g x₀ = h x₀ → g y₀ = h y₀ → g = h := by
    intro g h hg0 hg1
    apply LinearEquiv.toLinearMap_injective
    refine b.ext fun i => ?_
    fin_cases i
    · simpa [hb0] using hg0
    · simpa [hb1] using hg1
  set s := reflect Q x₀
  have hsO : s ∈ O := reflect_mem_orthogonalGroup Q x₀
  have hs0 : s x₀ = x₀ := by
    rw [reflect_apply hQx₀, hxx, zero_div, zero_smul, sub_zero]
  have hs1 : s y₀ = y₀ + x₀ := by
    rw [reflect_apply hQx₀, hxy, hx₀, div_one, one_smul, sub_eq_add_neg,
      neg_eq_self_of_two_eq_zero h2]
  have hstab : ∀ g ∈ O, g x₀ = x₀ → g = 1 ∨ g = s := by
    intro g hg hgx
    set z := g y₀ - y₀ with hzdef
    have hgy : g y₀ = y₀ + z := by rw [hzdef]; abel
    have hz1 : polar Q x₀ z = 0 := by
      rw [hzdef, polar_sub_right, hxy]
      nth_rewrite 1 [← hgx]
      rw [polar_map_of_mem hg, hxy, sub_self]
    have hz2 : Q z + polar Q y₀ z = 0 := by
      have := map_of_mem hg y₀
      rw [hgy, QuadraticMap.map_add Q y₀ z] at this
      linear_combination this
    have hzrepr := b.sum_repr z
    rw [Fin.sum_univ_two, hb0, hb1] at hzrepr
    have hu : b.repr z 1 = 0 := by
      have := congrArg (polar Q x₀) hzrepr
      rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hxx, hxy, hz1] at this
      simpa using this
    rw [hu, zero_smul, add_zero] at hzrepr
    have ht : b.repr z 0 * (b.repr z 0 + 1) = 0 := by
      rw [← hzrepr, map_smul_eq_sq, hx₀, polar_smul_right_eq, hyx] at hz2
      linear_combination hz2
    rcases mul_eq_zero.mp ht with ht0 | ht1
    · left
      refine hext g 1 (by rw [hgx]; rfl) ?_
      rw [hgy, ← hzrepr, ht0, zero_smul, add_zero]
      rfl
    · right
      have ht1' : b.repr z 0 = 1 := by
        have := eq_neg_of_add_eq_zero_left ht1
        rwa [neg_eq_self_of_two_eq_zero h2] at this
      refine hext g s (by rw [hgx, hs0]) ?_
      rw [hgy, ← hzrepr, ht1', one_smul, hs1]
  have hstab_card : Nat.card (MulAction.stabilizer O x₀) = 2 := by
    rw [Nat.card_eq_two_iff]
    have hsmem : (⟨s, hsO⟩ : O) ∈ MulAction.stabilizer O x₀ := by
      rw [MulAction.mem_stabilizer_iff]
      exact hs0
    refine ⟨1, ⟨⟨s, hsO⟩, hsmem⟩, fun h => ?_, ?_⟩
    · have := congrArg (fun g : MulAction.stabilizer O x₀ => ((g : O) : A ≃ₗ[K] A) y₀) h
      change y₀ = s y₀ at this
      rw [hs1, left_eq_add] at this
      exact hx₀0 this
    · ext ⟨⟨g, hg⟩, hgstab⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      have hgx : g x₀ = x₀ := (MulAction.mem_stabilizer_iff.mp hgstab : _)
      rcases hstab g hg hgx with rfl | rfl
      · left
        rfl
      · right
        rfl
  have hcard := (MulAction.stabilizer O x₀).card_mul_index
  rw [MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq, hstab_card] at hcard
  rw [← hcard]
  change 2 * Nat.card {x : A // Q x = 1} = _
  rw [card_norm_eq_one hA hani]

end CFSG.Timmesfeld.ClassicalOrders
