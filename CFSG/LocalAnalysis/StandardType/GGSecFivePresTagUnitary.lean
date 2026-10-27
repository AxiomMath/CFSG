module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary

section Raw

open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.SpecialLinear Matrix

variable {F : Type*} [Field F] [CharP F 2] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

local macro "csimp" : tactic => `(tactic| simp (disch := omega) only [levelPerm, levelSign,
  Equiv.Perm.mul_apply, Equiv.swap_apply_def, shortSign, longSign, Fin.ext_iff, Fin.val_rev,
  val_lowIdx, Fin.val_mk, ite_eq_left, ite_eq_right, dite_eq_left, dite_eq_right, map_one, map_neg,
  map_inv₀, inv_inv, inv_one, neg_neg, mul_one, one_mul, mul_neg, neg_mul, ite_true, ite_false,
  dite_true, dite_false, true_or, or_true, CharTwo.neg_eq])

private theorem levelWeyl_mul_self_eq_one {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    (k : Fin (n / 2)) : levelWeyl hσ ζ k * levelWeyl hσ ζ k = 1 := by
  have hsq : (((levelWeyl hσ ζ k * levelWeyl hσ ζ k : SU σ n) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) =
      diagonal fun s => levelSign σ (ζ : F) k (levelPerm k s) * levelSign σ (ζ : F) k s := by
    rw [Subgroup.coe_mul, Units.val_mul, coe_levelWeyl hσ hζ, signedPerm_mul_signedPerm,
      levelPerm_mul_self, signedPerm_one]
  have hfun : (fun s => levelSign σ (ζ : F) k (levelPerm k s) * levelSign σ (ζ : F) k s) = 1 := by
    funext s
    show levelSign σ (ζ : F) k (levelPerm k s) * levelSign σ (ζ : F) k s = 1
    have hk := k.isLt
    have hs := s.isLt
    by_cases h : k.val + 1 < n / 2
    · have hc : s.val = k.val ∨ s.val = k.val + 1 ∨ s.val = n - 1 - k.val ∨
          s.val = n - 2 - k.val ∨
          (s.val ≠ k.val ∧ s.val ≠ k.val + 1 ∧ s.val ≠ n - 1 - k.val ∧
            s.val ≠ n - 2 - k.val) := by omega
      rcases hc with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩ <;> csimp
    · have hc : s.val = k.val ∨ s.val = n - 1 - k.val ∨
          (s.val ≠ k.val ∧ s.val ≠ n - 1 - k.val) := by omega
      rcases hc with h1 | h1 | ⟨h1, h2⟩ <;> csimp <;> field_simp
  refine Subtype.ext (Units.ext ?_)
  rw [hsq, hfun]
  show diagonal (1 : Fin n → F) = 1
  exact diagonal_one

end Raw


section Image

theorem ggPresentsG0_of_unitary_hom
    {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hn : 4 ≤ n)
    {G : Type} [Group G] (Ψ : Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n →* G)
    (hker : Ψ.ker ≤ Subgroup.center (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)) :
    GGPresentsG0 Ψ.range (Unitary.rootDatum hF n) .PSU n f Ψ := by
  have hadm : StatedLieAdmissible .PSU n 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_⟩
    intro h
    have h3 := congrArg Prod.fst h
    dsimp only at h3
    omega
  have hCT := (CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} hadm hF).1
  refine ⟨⟨hadm, ?_⟩, ⟨rfl, hker⟩, ?_, ?_⟩
  · change 2 ≤ n / 2
    omega
  · have hmap : (commutator (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution F 2 f) n)).map
        Ψ.rangeRestrict = commutator ↥Ψ.range := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 Ψ.rangeRestrict_surjective, commutator_def]
    rw [← hmap, hCT.2.1.1.commutator_eq_top, Subgroup.map_top,
      MonoidHom.range_eq_top.2 Ψ.rangeRestrict_surjective]
  · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple hCT.2.1
        Ψ.rangeRestrict_surjective (by rwa [MonoidHom.ker_rangeRestrict])) hCT.2.2

end Image

section Tag

variable {G : Type} [Group G] [Finite G]

theorem ggTagFacts_PSU {n f : ℕ} (hadm : StatedLieAdmissible .PSU n 2 f)
    (hrank : 3 ≤ bnRank .PSU n) : GGTagFacts .PSU n f := by
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := by have := hadm.2.2.1; omega
  have hcard : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 :=
    card_galoisField_two_mul 2 f hf
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero (F := GaloisField 2 (2 * f))
    (p := 2) (f := f) hcard
  have hD : ggU .PSU n f =
      ⟨Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f) n,
        Unitary.rootDatum hcard n⟩ := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte]
  unfold GGTagFacts
  rw [hD]
  refine ⟨?_, ?_⟩
  · have hrnk : 3 ≤ n / 2 := hrank
    show 2 ≤ n / 2
    omega
  · refine ggUniversalFacts_of_steinberg (D := Unitary.rootDatum hcard n)
      (n := levelWeyl (CFSG.LieType.BorelTits.unitaryInvolution_involutive hcard) ζ)
      (H := levelTorus (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * f)) 2 f))
      ?_ (Unitary.isCTGroupDatum hcard n hn ζ hζ)
      (Unitary.steinbergExtras hcard n hn ζ hζ) ?_
    · have hrnk : 3 ≤ n / 2 := hrank
      show 0 < n / 2
      omega
    · intro i
      exact levelWeyl_mul_self_eq_one (CFSG.LieType.BorelTits.unitaryInvolution_involutive hcard) hζ i

theorem ggSecFivePres_of_psi_PSU {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .PSU n 2 f) (hrank : 3 ≤ bnRank .PSU n)
    (ψ : (ggU .PSU n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .PSU n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .PSU n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_PSU hadm hrank) ψ hker hrange

end Tag

end CFSG.StandardType

end
