module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.theorem_7_14
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.theorem_7_15

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix IV, Lemma 1

This is the two-part statement on the authoritative PFpart2 PNG (printed
page 144). Part (a) is Isaacs Theorem 7.14; part (b) is Isaacs Corollary 7.15.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite

namespace CFSG.BenderSuzuki
namespace PFAppendixIV

open Section1 Section5
open BenderSuzuki.External.Isaacs.VII

universe u

set_option maxHeartbeats 800000 in
/-- Peterfalvi Appendix IV, Lemma 1(a). -/
public theorem lemma_1_a
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (S₀ : Finset (ClassFunction H))
    (psi chi₀ : ClassFunction H)
    (hchi₀ : chi₀ ∈ S₀)
    (hpsi_not_mem : psi ∉ S₀)
    (tau : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hirreducible₀ :
      ∀ chi : S₀, IsIrreducibleCharacterOnGroup (chi : ClassFunction H))
    (hpsi_irreducible : IsIrreducibleCharacterOnGroup psi)
    (hisometry :
      isCFLinearIsometryOnSpanOn (S₀.cons psi hpsi_not_mem) puncturedSet tau)
    (htarget :
      ∀ phi : ClassFunction H,
        integerSpanOn (S₀.cons psi hpsi_not_mem) puncturedSet phi →
          Theory.Character.IsVirtualCharacter (tau phi) ∧
            supportedOn (tau phi) puncturedSet)
    (hcoherent : IsCoherentTriple puncturedSet S₀ tau)
    (hdiv :
      ∃ d : ℕ, degree psi = (d : ℂ) * degree chi₀)
    (hgrowth :
      2 * (degree psi).re * (degree chi₀).re <
        ∑ chi : S₀, (degree (chi : ClassFunction H)).re ^ 2) :
    IsCoherentTriple puncturedSet (S₀.cons psi hpsi_not_mem) tau := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  have hcons : S₀.cons psi hpsi_not_mem = insert psi S₀ :=
    Finset.cons_eq_insert psi S₀ hpsi_not_mem
  rw [hcons] at hisometry htarget ⊢
  exact isaacs_theorem_7_14 H S₀ psi hpsi_not_mem
    ⟨chi₀, hchi₀⟩ tau hirreducible₀ hpsi_irreducible hisometry htarget
    hcoherent hdiv hgrowth

/-- Peterfalvi Appendix IV, Lemma 1(b), Isaacs Corollary 7.15. -/
public theorem lemma_1_b
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (S : Finset (ClassFunction H))
    (tau : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hcard : 2 ≤ S.card)
    (hirreducible :
      ∀ chi : S, IsIrreducibleCharacterOnGroup (chi : ClassFunction H))
    (hisometry : isCFLinearIsometryOnSpanOn S puncturedSet tau)
    (htarget :
      ∀ phi : ClassFunction H, integerSpanOn S puncturedSet phi →
        Theory.Character.IsVirtualCharacter (tau phi) ∧
          supportedOn (tau phi) puncturedSet)
    (hequal :
      ∀ chi psi : S,
        degree (chi : ClassFunction H) = degree (psi : ClassFunction H)) :
    IsCoherentTriple puncturedSet S tau := by
  exact isaacs_theorem_7_15 H S tau hirreducible hisometry htarget hequal hcard

/-- Peterfalvi Appendix IV, Lemma 1, with its two printed alternatives. -/
public theorem lemma_1
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (S : Finset (ClassFunction H))
    (tau : ClassFunction H →ₗ[ℂ] ClassFunction G)
    (hirreducible :
      ∀ chi : S, IsIrreducibleCharacterOnGroup (chi : ClassFunction H))
    (hisometry : isCFLinearIsometryOnSpanOn S puncturedSet tau)
    (htarget :
      ∀ phi : ClassFunction H, integerSpanOn S puncturedSet phi →
        Theory.Character.IsVirtualCharacter (tau phi) ∧
          supportedOn (tau phi) puncturedSet)
    (hcase :
      (∃ (S₀ : Finset (ClassFunction H)) (psi chi₀ : ClassFunction H),
        ∃ hpsi : psi ∉ S₀,
          S = S₀.cons psi hpsi ∧ chi₀ ∈ S₀ ∧
            IsCoherentTriple puncturedSet S₀ tau ∧
            (∃ d : ℕ, degree psi = (d : ℂ) * degree chi₀) ∧
            2 * (degree psi).re * (degree chi₀).re <
              ∑ chi : S₀, (degree (chi : ClassFunction H)).re ^ 2) ∨
       (2 ≤ S.card ∧
        ∀ chi psi : S,
          degree (chi : ClassFunction H) =
            degree (psi : ClassFunction H))) :
    IsCoherentTriple puncturedSet S tau := by
  classical
  rcases hcase with
    ⟨S₀, psi, chi₀, hpsi, rfl, hchi₀, hcoherent, hdiv, hgrowth⟩ |
      ⟨hcard, hequal⟩
  · apply lemma_1_a H S₀ psi chi₀ hchi₀ hpsi tau
    · intro chi
      exact hirreducible
        ⟨chi, Finset.mem_cons_of_mem chi.2⟩
    · exact hirreducible
        ⟨psi, Finset.mem_cons_self psi S₀⟩
    · exact hisometry
    · exact htarget
    · exact hcoherent
    · exact hdiv
    · exact hgrowth
  · exact lemma_1_b H S tau hcard hirreducible hisometry htarget hequal

end PFAppendixIV
end CFSG.BenderSuzuki



