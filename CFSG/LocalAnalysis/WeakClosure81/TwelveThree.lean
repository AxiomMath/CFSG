module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveThreeA
public import CFSG.LocalAnalysis.WeakClosure81.TwelveThreeCyc

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

section Three

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {n m : ℕ}

theorem Setting12One.exists_inverted_element
    {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    (hZ : Module.finrank (ZMod 2) Z ≤ m) (hnm : n ≠ m) :
    (2 ≤ m ∧ m ∣ n ∧ m < n) ∧ ∃ a x : G, a ∈ A ∧ a ≠ 1 ∧ a * a = 1 ∧ a * x * a⁻¹ = x⁻¹ ∧
      Odd (orderOf x) ∧ orderOf x * (2 ^ m - 1) = 2 ^ n - 1 ∧
      Nat.Coprime (orderOf x) (2 ^ m - 1) ∧
      ∃ v ∈ commSub ρ.range, ρ x v = v ∧ ∃ y : G, ρ y v ≠ v := by
  haveI : Finite G := rankOne_finite h.type
  obtain ⟨L, hL⟩ := h.exists_minimal
  obtain ⟨hmn, hZm, -, t, TL, htL, ht2, htB, hTLle, hTLcyc, hTLcard, hTLinv, hTLreg, hTLcomm⟩ :=
    twelveTwo_two_general h hL hZ
  have hmn' : 2 ≤ m ∧ m ∣ n ∧ m < n := hmn.resolve_left (fun h' => hnm h'.symm)
  refine ⟨hmn', ?_⟩
  have hm2 : 2 ≤ m := hmn'.1
  have hn1 : 1 ≤ n := by omega
  obtain ⟨S, hS⟩ := exists_sylow_of_isBorelIn h.borel
  have htS : t ∉ normalizer (S : Set G) := hS ▸ htB
  obtain ⟨hTB, -, -, hTcyc, hTcard, hTinv, -⟩ := rankOne_cartan_spec h.type S ht2 htS
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hTLT : TL ≤ cartan (S : Subgroup G) t := by
    refine le_cartan_of_inverted (fun x hx => ?_) (fun x hx => ?_)
    · show x ∈ normalizer (S : Set G)
      rw [← hS]
      exact (hTLle hx).1
    · show t * x * t⁻¹ ∈ normalizer (S : Set G)
      rw [hti, hTLinv x hx, ← hS]
      exact (hTLle (TL.inv_mem hx)).1
  have hZinv : ∀ x ∈ cartan (S : Subgroup G) t, ∀ z ∈ Z, ρ x z ∈ Z := fun x hx z hz =>
    (h.stab x).1 (hS ▸ hTB hx) z hz
  have hZcard : Nat.card Z = 2 ^ m := by rw [card_submodule_eq_two_pow_finrank, hZm]
  obtain ⟨x₀, hx₀T, hx₀fix, hx₀ord, hx₀cop⟩ :=
    exists_centralizing_element_of_regular hTcyc hTcard hTLT hTLcard hZcard hZinv hTLreg
      (by omega) hn1
  have hApos : 1 < Nat.card A := by
    rw [h.A_card]
    exact Nat.one_lt_two_pow (by omega)
  haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 hApos
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    obtain ⟨a', ha'⟩ := exists_ne (1 : A)
    exact ⟨a', a'.2, fun h1 => ha' (Subtype.ext h1)⟩
  have ha2 : a * a = 1 := by simpa [sq] using h.A_elem.2 a haA
  have ht1 : t ≠ 1 := fun h1 => htB (h1 ▸ B.one_mem)
  obtain ⟨c, hc⟩ := isConj_iff.1 (rankOne_isConj_of_involutions h.type ht2 ht1 ha2 ha1)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hx₀inv : t * x₀ * t = x₀⁻¹ := hTinv x₀ hx₀T
  have horder : orderOf (c * x₀ * c⁻¹) = orderOf x₀ := by
    simpa [MulAut.conj_apply] using (MulAut.conj c).orderOf_eq x₀
  have hodd₀ : Odd (orderOf x₀) := by
    have hodd_n : Odd (2 ^ n - 1) := odd_two_pow_sub_one n hn1
    rw [← hx₀ord] at hodd_n
    exact (Nat.odd_mul.1 hodd_n).1
  have hconj : ∀ (u : G) (w : V), ρ (c * u * c⁻¹) (ρ c w) = ρ c (ρ u w) := by
    intro u w
    have e : c * u * c⁻¹ * c = c * u := by group
    calc ρ (c * u * c⁻¹) (ρ c w) = ρ (c * u * c⁻¹ * c) w := by
          rw [map_mul ρ (c * u * c⁻¹) c]
          rfl
      _ = ρ (c * u) w := by rw [e]
      _ = ρ c (ρ u w) := by
          rw [map_mul ρ c u]
          rfl
  refine ⟨a, c * x₀ * c⁻¹, haA, ha1, ha2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← hc]
    calc c * t * c⁻¹ * (c * x₀ * c⁻¹) * (c * t * c⁻¹)⁻¹ = c * (t * x₀ * t⁻¹) * c⁻¹ := by group
      _ = c * x₀⁻¹ * c⁻¹ := by rw [hti, hx₀inv]
      _ = (c * x₀ * c⁻¹)⁻¹ := by group
  · rw [horder]
    exact hodd₀
  · rw [horder]
    exact hx₀ord
  · rw [horder]
    exact hx₀cop
  · haveI : Nontrivial Z := Finite.one_lt_card_iff_nontrivial.1 (by
      rw [hZcard]
      exact Nat.one_lt_two_pow (by omega))
    obtain ⟨z', hz'⟩ := exists_ne (0 : Z)
    have hz₀ : (z' : V) ∈ Z := z'.2
    have hz₀ne : (z' : V) ≠ 0 := fun h0 => hz' (Subtype.ext h0)
    have hZle : Z ≤ commSub ρ.range := by
      rw [← hTLcomm]
      refine commSpace_le_iff.2 fun k hk u _ => ?_
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hk
      exact sub_mem_commSub ρ.range ⟨y, rfl⟩ u
    refine ⟨ρ c z', map_mem_commSub ρ.range ⟨c, rfl⟩ (hZle hz₀), ?_, ?_⟩
    · rw [hconj x₀ z', hx₀fix z' hz₀]
    · haveI : Nontrivial TL := Finite.one_lt_card_iff_nontrivial.1 (by
        rw [hTLcard]
        have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        omega)
      obtain ⟨y₀', hy₀'⟩ := exists_ne (1 : TL)
      have hy₀ : (y₀' : G) ∈ TL := y₀'.2
      have hy₀1 : (y₀' : G) ≠ 1 := fun h1 => hy₀' (Subtype.ext h1)
      refine ⟨c * y₀' * c⁻¹, fun hfix => ?_⟩
      rw [hconj] at hfix
      have hfix' : ρ y₀' z' = z' := (ρ c).injective hfix
      exact hz₀ne (hTLreg.1 y₀' hy₀ hy₀1 z' hz₀ hfix')

theorem twelveThree
    {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    (hZ : Module.finrank (ZMod 2) Z ≤ m) :
    n = m ∨ (n = 2 * m ∧ CFSG.Quasithin.IsPSL 2 2 n G) := by
  by_cases hnm : n = m
  · exact Or.inl hnm
  right
  haveI : Finite G := rankOne_finite h.type
  obtain ⟨⟨hm2, hmn, hmlt⟩, a, x, haA, ha1, ha2, hax, hxodd, hxord, hxcop, v, hv, hxv, y, hy⟩ :=
    h.exists_inverted_element hZ hnm
  have hn1 : 1 ≤ n := by omega
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hAH : A ≤ A ⊔ Subgroup.zpowers x := le_sup_left
  have hxH : x ∈ A ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  by_cases hHtop : A ⊔ Subgroup.zpowers x = ⊤
  · exfalso
    have hax2 : (a * x) * (a * x) = 1 := by
      calc a * x * (a * x) = (a * x * a⁻¹) * x := by rw [hai]; group
        _ = 1 := by rw [hax]; group
    have hax1 : a * x ≠ 1 := by
      intro h1
      have hxa : x = a := by rw [eq_inv_of_mul_eq_one_right h1, hai]
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [hxa, sq]; exact ha2)
      have hx1 : x = 1 := by
        have h1' : orderOf x = 1 := by
          rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
          · exact h'
          · rw [h'] at hxodd
            exact absurd hxodd (by decide)
        exact orderOf_eq_one_iff.1 h1'
      exact ha1 (by rw [← hxa, hx1])
    obtain ⟨g, hg⟩ := isConj_iff.1 (rankOne_isConj_of_involutions h.type ha2 ha1 hax2 hax1)
    have hprod : a * (g * a * g⁻¹) = x := by rw [hg, ← mul_assoc, ha2, one_mul]
    have hxmem : x ∈ A ⊔ A.map (MulAut.conj g).toMonoidHom := by
      have hga : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.2 ⟨a, haA, by simp [MulAut.conj_apply]⟩
      rw [← hprod]
      exact Subgroup.mul_mem_sup haA hga
    have hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ := by
      rw [eq_top_iff, ← hHtop]
      exact sup_le le_sup_left (Subgroup.zpowers_le.2 hxmem)
    have hfixed := h.fixed_of_gen_eq_top hgen haA ha1 hv (by rw [hprod]; exact hxv)
    exact hy (hfixed y)
  · have h4 : 4 ≤ Nat.card A := by
      rw [h.A_card]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    obtain ⟨E, hEA, hEel, hEcard⟩ := exists_four_subgroup h.A_elem h4
    rcases rankOne_subgroup_cases h.type hHtop (hEA.trans hAH) hEel hEcard with
      hbor | ⟨k, hk2, hkn, hklt, hkcases⟩
    · exfalso
      obtain ⟨S', hS'⟩ := hbor
      obtain ⟨S, hS⟩ := exists_sylow_of_isBorelIn h.borel
      have hA2 : IsPGroup 2 A := fun a₁ => ⟨1, by
        have h2 : a₁ ^ 2 = 1 := Subtype.ext (h.A_elem.2 a₁ a₁.2)
        simpa using h2⟩
      have hA1 : A ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card A = 1 := by rw [hbot, Subgroup.card_bot]
        omega
      have hAS : A ≤ (S : Subgroup G) := le_sylow_of_le_normalizer hA2 (hS ▸ h.A_le_B)
      have hAS' : A ≤ (S' : Subgroup G) := le_sylow_of_le_normalizer hA2 (hAH.trans hS')
      have hS'S : S' = S := rankOne_sylow_eq_of_ne_bot h.type hA1 hAS hAS'
      have hxN : x ∈ normalizer (S : Set G) := hS'S ▸ hS' hxH
      have hx1 : x = 1 :=
        eq_one_of_inverted_of_mem_normalizer S.isPGroup' (hAS haA) hxN hax hxodd
      have h1 : 2 ^ n - 1 = 2 ^ m - 1 := by rw [← hxord, hx1, orderOf_one, one_mul]
      have hn2 : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
      have hm2' : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
      have h2 : 2 ^ n = 2 ^ m := by omega
      exact hnm (Nat.pow_right_injective (le_refl 2) h2)
    · have hmk : m ∣ k :=
        h.m_dvd_of_subgroup hAH (hkcases.imp And.right And.right) hZ
      exact twelveThree_subfield hkcases hk2 hkn hklt (by omega) hmk hxH hxodd hxord hxcop

end Three

end CFSG.LocalAnalysis.WeakClosure81
