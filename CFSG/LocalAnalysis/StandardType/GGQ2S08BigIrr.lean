module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreClassify
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

theorem ggQ2s08_big_irr (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n) (h3 : 3 ∣ n + 1)
    (h11 : 11 ≤ n) {W R : Subgroup (V ≃ₗ[ZMod 3] V)} (hWcard : Nat.card W = (n + 1).factorial)
    (hWR : W ≤ R) (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (hb : 8 * Nat.card R < 3 ^ (n * (n - 1) / 2))
    (hirr : ∀ S : Submodule (ZMod 3) V, (∀ a ∈ R, ∀ u ∈ S, a u ∈ S) → S = ⊥ ∨ S = ⊤) :
    False := by
  haveI : Module.Finite (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  haveI : Finite (V ≃ₗ[ZMod 3] V) := by
    have : Finite V := Module.finite_of_finite (ZMod 3)
    exact Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      fun _ _ h => LinearEquiv.ext (congrFun h)
  have h2fac : 2 ≤ (n + 1).factorial := by
    have h := Nat.factorial_le (show 2 ≤ n + 1 by omega)
    have h2 : (2 : ℕ).factorial = 2 := by decide
    rwa [h2] at h
  have hW2 : 2 ≤ Nat.card W := by rw [hWcard]; exact h2fac
  have hR2 : 2 ≤ Nat.card R := hW2.trans (Subgroup.card_le_of_le hWR)
  have hRne : R ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card R = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hex : ∃ r ∈ R, GGLinRefl r := by
    by_contra h
    apply hRne
    rw [hgen]
    have hset : {r : V ≃ₗ[ZMod 3] V | r ∈ R ∧ GGLinRefl r} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro r hr
      exact h ⟨r, hr.1, hr.2⟩
    rw [hset, Subgroup.closure_empty]
  have habs : ZS.AbsIrred 3 R := ggQ2s08core_absIrred_of_irred R hgen hex hirr
  have hpm1 : ∀ c : ZMod 3, c ≠ 0 ↔ (c = 1 ∨ c = -1) := by decide
  rcases hKG V n hn (by omega) R habs hgen with himp | hcard | hsym1 | hsym2
  ·
    obtain ⟨b, hbmono⟩ := ggRC_monomial_of_imprimitive hn R habs hgen himp
    have hle : R ≤ OrthF3.ggOrthSignedPerms b := by
      intro a ha
      obtain ⟨σ, c, hcne, hbc⟩ := hbmono a ha
      exact ⟨σ, c, fun i => (hpm1 (c i)).1 (hcne i), hbc⟩
    have hcardR : Nat.card R ∣ 2 ^ n * n.factorial := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [OrthF3.card_ggOrthSignedPerms b] at h
    have hcardW : (n + 1).factorial ∣ Nat.card R := by
      have h := Subgroup.card_dvd_of_le hWR
      rwa [hWcard] at h
    have hdiv : (n + 1).factorial ∣ 2 ^ n * n.factorial := hcardW.trans hcardR
    rw [Nat.factorial_succ] at hdiv
    have hdiv' : n.factorial * (n + 1) ∣ n.factorial * 2 ^ n := by
      rwa [mul_comm (n + 1) n.factorial, mul_comm (2 ^ n) n.factorial] at hdiv
    have hdvd : n + 1 ∣ 2 ^ n :=
      Nat.dvd_of_mul_dvd_mul_left (Nat.factorial_pos n) hdiv'
    have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (h3.trans hdvd)
    norm_num at h32
  · exact absurd hcard (not_le.mpr hb)
  · exact absurd h3 hsym1.1
  · obtain ⟨k, hk⟩ := h3
    obtain ⟨l, hl⟩ := hsym2.1
    omega

end CFSG.StandardType

end
