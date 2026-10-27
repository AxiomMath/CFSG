module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveThree
public import CFSG.LocalAnalysis.WeakClosure81.TwelveFourA
public import CFSG.LocalAnalysis.WeakClosure81.TwelveFourB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.GH74.Uniqueness.Bender

section Four

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {n m : ℕ}

@[expose] def InCalAMod (ρ : G →* LGL 2 V) (i : ℕ) (U : Subgroup G) : Prop :=
  U ≠ ⊥ ∧ IsElemAbelian 2 U ∧
    ∀ D : Subgroup G, D ≤ U → D.relIndex U < 2 ^ i → fixSub (U.map ρ) = fixSub (D.map ρ)

private theorem b12_TwelveFour_exists_ne_one {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m) [Finite G] :
    ∃ a ∈ A, a ≠ 1 := by
  have hApos : 1 < Nat.card A := by
    rw [h.A_card]
    calc 1 < 2 := by norm_num
      _ = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by have := h.one_lt_m; omega)
  haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 hApos
  obtain ⟨⟨a, haA⟩, ha1⟩ := exists_ne (1 : A)
  exact ⟨a, haA, fun h' => ha1 (Subtype.ext h')⟩

theorem Setting12One.two_pow_succ_le_card {ρ : G →* LGL 2 V}
    {B A : Subgroup G} {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    {U : Subgroup G} (hAU : A ≤ U) (hU : InCalAMod ρ (m + 1) U) : 2 ^ (m + 1) ≤ Nat.card U := by
  haveI : Finite G := rankOne_finite h.type
  by_contra hlt
  push Not at hlt
  have hrel : (⊥ : Subgroup G).relIndex U < 2 ^ (m + 1) := by
    rw [Subgroup.relIndex_bot_left]
    exact hlt
  have hfix := hU.2.2 ⊥ bot_le hrel
  rw [Subgroup.map_bot, fixSub_bot] at hfix
  obtain ⟨a, haA, ha1'⟩ := b12_TwelveFour_exists_ne_one h
  have hfixa : ∀ v : V, ρ a v = v := by
    intro v
    have hv : v ∈ fixSub (U.map ρ) := by rw [hfix]; trivial
    exact hv (ρ a) (Subgroup.mem_map_of_mem ρ (hAU haA))
  have hρ1 : ρ a = ρ 1 := by
    rw [map_one]
    exact LinearEquiv.ext hfixa
  exact ha1' (h.injective hρ1)

theorem twelveFour
    {ρ : G →* LGL 2 V} {B A : Subgroup G}
    {Z : Submodule (ZMod 2) V} (h : Setting12One ρ B Z A n m)
    (hCA : ∀ a ∈ A, a ≠ 1 → fixSub (A.map ρ) = fixSub ((zpowers a).map ρ))
    (hZ : Module.finrank (ZMod 2) Z ≤ m) {U : Subgroup G} (hAU : A ≤ U)
    (hUO : U ≤ pCoreOf 2 B) : ¬ InCalAMod ρ (m + 1) U := by
  intro hU
  haveI : Finite G := rankOne_finite h.type
  have hm1 : 1 < m := h.one_lt_m
  have hcard : 2 ^ (m + 1) ≤ Nat.card U := h.two_pow_succ_le_card hAU hU
  obtain ⟨S, hSB⟩ := exists_sylow_of_isBorelIn h.borel
  have hUS : U ≤ (S : Subgroup G) := by
    rw [hSB] at hUO
    exact hUO.trans (pCoreOf_normalizer_le_sylow S)
  have hnle : Nat.card U ≤ 2 ^ n := (rankOne_card_elemAbelian_le h.type hUS hU.2.1).1
  have hnm : n ≠ m := by
    intro hn
    rw [hn] at hnle
    have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have h2 : 0 < 2 ^ m := by positivity
    omega
  rcases twelveThree h hZ with hn | ⟨hn2, hPSL⟩
  · exact hnm hn
  obtain ⟨-, t, -, -, -, -, -, ht, htS, -, -⟩ := rankOne_exists_cartan h.type S
  obtain ⟨b, hbT, hSAC, hD1, hrelA, hrelD⟩ :=
    twelveFour_exists_conj hPSL S ht htS hAU hUS (by omega) h.A_card hcard hn2
  have hAD : fixSub (A.map ρ) = fixSub ((U ⊓ A.map (MulAut.conj b).toMonoidHom).map ρ) :=
    (hU.2.2 A hAU hrelA).symm.trans (hU.2.2 _ inf_le_left hrelD)
  have hSelem := rankOne_psl_sylow_elemAbelian hPSL S
  have hspec := rankOne_cartan_spec h.type S ht htS
  have hSsq : ∀ s ∈ (S : Subgroup G), s * s = 1 := fun s hs => by
    simpa [sq] using hSelem.1.2 s hs
  have htrans : ∀ s ∈ (S : Subgroup G), s ≠ 1 →
      ∃ x ∈ normalizer (S : Set G), ∃ a ∈ A, a ≠ 1 ∧ x * a * x⁻¹ = s := by
    intro s hs hs1
    obtain ⟨a, haA, ha1⟩ := b12_TwelveFour_exists_ne_one h
    obtain ⟨x, hx, -⟩ := rankOne_psl_cartan_regular hPSL S ht htS (hUS (hAU haA)) hs ha1 hs1
    exact ⟨x, hspec.1 x.2, a, haA, ha1, hx⟩
  have hW := fixSub_eq_of_conj_decomposition (hAU.trans hUS) inf_le_right hD1 hSAC hCA hAD
  have hquad : RepQuad ρ (S : Subgroup G) :=
    repQuad_of_fixSub_zpowers_le hSsq (fixSub_zpowers_le_of_trans hCA hW htrans)
  have hSB' : (S : Subgroup G) ≤ B := by
    rw [hSB]
    exact Subgroup.le_normalizer
  have h' : Setting12One ρ B Z (S : Subgroup G) n n :=
    ⟨h.type, h.borel, h.stab, hSB', hSelem.1, hSelem.2, by omega, hquad⟩
  obtain ⟨L, hL⟩ := h'.exists_minimal
  have hZn : Module.finrank (ZMod 2) Z ≤ n := by omega
  have hfin := (twelveTwo_two_general h' hL hZn).2.1
  omega

end Four

end CFSG.LocalAnalysis.WeakClosure81
