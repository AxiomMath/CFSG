module

public import CFSG.RankThree.GF2n.Stroth80.SL2KDescent
public import CFSG.RankThree.GF2n.Stroth80.Sec37Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.QuasithinUnique.Setup.SL2Modules SL2Descent
open scoped MatrixGroups

section Sylow

variable {k₀ : Type*} [Field k₀] {F : Type*} [Field F] [Fintype F] [CharP F 2] {W : Type*}
  [AddCommGroup W] [Module k₀ W] (ρ : Representation k₀ SL(2, F) W)

theorem card_fix_of_card_eq {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n)
    {P : Subgroup SL(2, F)} (hcard : Nat.card P = Fintype.card F) :
    Nat.card {w : W // ∀ g ∈ P, ρ g w = w} = Nat.card {w : W // ∀ t : F, ρ (uElt t) w = w} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q : Sylow 2 SL(2, F) :=
    Sylow.ofCard P (by rw [hcard, hF, factorization_card_sl2_prime hn hF])
  obtain ⟨g, hg⟩ := sylow_conj_description (p := 2) Q
  have hmem : ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ upperRootGroup F := hg
  have hmul : ∀ x y w, ρ (x * y) w = ρ x (ρ y w) := fun x y w => by
    rw [map_mul, Module.End.mul_apply]
  have h1 : ∀ w, ρ 1 w = w := fun w => by rw [map_one, Module.End.one_apply]
  let τ : W ≃ W :=
    { toFun := ρ g⁻¹
      invFun := ρ g
      left_inv := fun w => by rw [← hmul, mul_inv_cancel, h1]
      right_inv := fun w => by rw [← hmul, inv_mul_cancel, h1] }
  refine Nat.card_congr (Equiv.subtypeEquiv τ fun w => ?_)
  constructor
  · intro hfix t
    have hx : g * uElt t * g⁻¹ ∈ P := by
      rw [hmem, show g⁻¹ * (g * uElt t * g⁻¹) * g = uElt t by group]
      exact (mem_upperRootGroup_iff _).2 ⟨t, rfl⟩
    show ρ (uElt t) (ρ g⁻¹ w) = ρ g⁻¹ w
    rw [← hmul, show uElt t * g⁻¹ = g⁻¹ * (g * uElt t * g⁻¹) by group, hmul, hfix _ hx]
  · intro hfix x hx
    obtain ⟨t, ht⟩ := (mem_upperRootGroup_iff _).1 ((hmem x).1 hx)
    have he : x = g * uElt t * g⁻¹ := by rw [← ht]; group
    have h2 : ρ (uElt t) (ρ g⁻¹ w) = ρ g⁻¹ w := hfix t
    rw [he, hmul, hmul, h2, ← hmul, mul_inv_cancel, h1]

end Sylow


theorem sl2FixedLineDimStatement_holds : SL2FixedLineDimStatement := by
  intro k e hk he V _ _ _ ρ hirr P hP hPcard hline
  obtain ⟨b, hb0, hbfix, hbuniq⟩ := hline
  have hk0 : k ≠ 0 := by omega
  have hke : k * e ≠ 0 := Nat.mul_ne_zero hk0 (by omega)
  letI : Fintype (GaloisField 2 k) := Fintype.ofFinite _
  letI : Fintype (GaloisField 2 (k * e)) := Fintype.ofFinite _
  haveI : Finite V := Module.finite_of_finite (GaloisField 2 k)
  haveI : Nontrivial V := ⟨⟨b, 0, hb0⟩⟩
  have hK : Fintype.card (GaloisField 2 k) = 2 ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 k hk0]
  have hF : Fintype.card (GaloisField 2 (k * e)) = 2 ^ (k * e) := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (k * e) hke]
  by_cases htriv : ∀ g, ρ g = 1
  ·
    refine ⟨0, ?_⟩
    have hinv : ∀ g, ∀ v ∈ Submodule.span (GaloisField 2 k) {b}, ρ g v ∈
        Submodule.span (GaloisField 2 k) {b} := fun g v hv => by rw [htriv g]; exact hv
    rcases hirr _ hinv with h | h
    · exact absurd (Submodule.span_singleton_eq_bot.mp h) hb0
    · have := finrank_span_singleton (K := GaloisField 2 k) hb0
      rw [h, finrank_top] at this
      rw [zero_mul, pow_zero]
      exact this
  · push Not at htriv
    obtain ⟨κ'⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
      (K := GaloisField 2 k) (L := GaloisField 2 (k * e))
      (by rw [GaloisField.finrank 2 hk0, GaloisField.finrank 2 hke]; exact dvd_mul_right k e)
    let ρ' : Representation (GaloisField 2 k) SL(2, GaloisField 2 (k * e)) V :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ρ
    have hirr' : ρ'.IsIrreducible := by
      refine (isIrreducible_iff ρ').mpr ⟨inferInstance, fun W hW =>
        hirr W fun g v hv => hW g v hv⟩
    haveI : Fact ρ'.IsIrreducible := ⟨hirr'⟩
    have hnt' : ∃ g, ρ' g ≠ 1 := by
      obtain ⟨g, hg⟩ := htriv
      refine ⟨g, fun h => hg ?_⟩
      apply LinearEquiv.toLinearMap_injective
      exact h
    obtain ⟨f, J, hf1, hDk, hfn, hJne, hJn, hshift, hdim⟩ :=
      kDescent (ρ := ρ') hK (by omega) hF κ'.toRingHom hnt'
    have hfix := card_fixRoot_gen (ρ := ρ') hK (by omega) hF hnt'
    have hPfix := card_fix_of_card_eq ρ' (by omega) hF (P := P) (by rw [hPcard, hF])
    have hline : Nat.card {v : V // ∀ g ∈ P, ρ' g v = v} = 2 ^ k := by
      rw [← hK, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
        (fun s : GaloisField 2 k => (⟨s • b, fun g hg => by
          show ρ g (s • b) = s • b
          rw [map_smul, hbfix g hg]⟩ : {v : V // ∀ g ∈ P, ρ' g v = v})) ⟨?_, ?_⟩))
      · intro s s' h
        exact smul_left_injective (GaloisField 2 k) hb0 (congrArg Subtype.val h)
      · rintro ⟨v, hv⟩
        obtain ⟨s, hs⟩ := hbuniq v hv
        exact ⟨s, Subtype.ext hs.symm⟩
    have hf : f = 1 := by
      have h1 : 2 ^ (k * f) = 2 ^ k := by rw [← hDk, ← hfix, hPfix.symm.trans hline]
      have h2 := Nat.pow_right_injective le_rfl h1
      have : k * f = k * 1 := by rw [h2, mul_one]
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) this
    subst hf
    obtain ⟨x, hx⟩ := dvd_card_of_shift (Nat.pos_of_ne_zero hk0) hJn (by simpa using hshift)
    refine ⟨x, ?_⟩
    rw [hdim, one_mul, hx, mul_comm]

end CFSG.RankThree.GF2n.Stroth80
